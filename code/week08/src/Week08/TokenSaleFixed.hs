{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

{-# OPTIONS_GHC -g -fplugin-opt PlutusTx.Plugin:coverage-all #-}

module Week08.TokenSaleFixed
    ( TokenSale (..)
    , TSRedeemer (..)
    , tsCovIdx
    , TSStartSchema
    , TSUseSchema
    , startEndpoint
    , useEndpoints
    , useEndpoints'
    ) where

import           Control.Monad                hiding (fmap)
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.Monoid                  (Last (..))
import           Data.Text                    (Text, pack)
import           GHC.Generics                 (Generic)
import           Plutus.Contract              as Contract
import           Plutus.Contract.StateMachine
import qualified PlutusTx
import           PlutusTx.Code                (getCovIdx)
import           PlutusTx.Coverage            (CoverageIndex)
import           PlutusTx.Prelude             hiding (Semigroup(..), check, unless)
import           Ledger                       hiding (singleton)
import           Ledger.Ada                   as Ada
import           Ledger.Constraints           as Constraints
import qualified Ledger.Typed.Scripts         as Scripts
import           Ledger.Value
import           Prelude                      (Semigroup (..), Show (..), uncurry)
import qualified Prelude

data TokenSale = TokenSale
    { tsSeller :: !PaymentPubKeyHash
    , tsToken  :: !AssetClass
    , tsTT     :: !ThreadToken
    } deriving (Show, Generic, FromJSON, ToJSON, Prelude.Eq)

PlutusTx.makeLift ''TokenSale

data TSRedeemer =
      SetPrice Integer
    | AddTokens Integer
    | BuyTokens Integer
    | Withdraw Integer Integer
    | Close
    deriving (Show, Prelude.Eq)

PlutusTx.unstableMakeIsData ''TSRedeemer

{-# INLINABLE lovelaces #-}
lovelaces :: Value -> Integer
lovelaces = Ada.getLovelace . Ada.fromValue

{-# INLINABLE transition #-}
transition :: TokenSale -> State Integer -> TSRedeemer -> Maybe (TxConstraints Void Void, State Integer)
transition ts s r = case (stateValue s, stateData s, r) of
    (v, _, SetPrice p)   | p >= 0                             -> Just ( Constraints.mustBeSignedBy (tsSeller ts)
                                                                      , State p v
                                                                      )
    (v, p, AddTokens n)  | n > 0                              -> Just ( mempty
                                                                      , State p $
                                                                          v                                       <>
                                                                          assetClassValue (tsToken ts) n
                                                                      )
    (v, p, BuyTokens n)  | n > 0                              -> Just ( mempty
                                                                      , State p $
                                                                          v                                       <>
                                                                          assetClassValue (tsToken ts) (negate n) <>
                                                                          lovelaceValueOf (n * p)
                                                                      )
    (v, p, Withdraw n l) | n >= 0 && l >= 0 &&
                           v `geq` (w <> toValue minAdaTxOut) -> Just ( Constraints.mustBeSignedBy (tsSeller ts)
                                                                      , State p $
                                                                          v                                       <>
                                                                          negate w
                                                                      )
      where
        w = assetClassValue (tsToken ts) n <>
            lovelaceValueOf l
    (v, p, Close)                                             -> Just ( mempty
                                                                      , State p $ foldMap spendValue $ flattenValue v
                                                                      )
      where
          spendValue :: (CurrencySymbol, TokenName, Integer) -> Value
          spendValue (c, t, _) = singleton c t 0
    _                                                         -> Nothing

{-# INLINABLE tsStateMachine #-}
tsStateMachine :: TokenSale -> StateMachine Integer TSRedeemer
tsStateMachine ts = mkStateMachine (Just $ tsTT ts) (transition ts) (const False)

{-# INLINABLE mkTSValidator #-}
mkTSValidator :: TokenSale -> Integer -> TSRedeemer -> ScriptContext -> Bool
mkTSValidator = mkValidator . tsStateMachine

type TS = StateMachine Integer TSRedeemer

tsTypedValidator :: TokenSale -> Scripts.TypedValidator TS
tsTypedValidator ts = Scripts.mkTypedValidator @TS
    ($$(PlutusTx.compile [|| mkTSValidator ||]) `PlutusTx.applyCode` PlutusTx.liftCode ts)
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @Integer @TSRedeemer

tsValidator :: TokenSale -> Validator
tsValidator = Scripts.validatorScript . tsTypedValidator

tsAddress :: TokenSale -> Ledger.Address
tsAddress = scriptAddress . tsValidator

tsClient :: TokenSale -> StateMachineClient Integer TSRedeemer
tsClient ts = mkStateMachineClient $ StateMachineInstance (tsStateMachine ts) (tsTypedValidator ts)

tsCovIdx :: CoverageIndex
tsCovIdx = getCovIdx $$(PlutusTx.compile [|| mkTSValidator ||])

mapErrorSM :: Contract w s SMContractError a -> Contract w s Text a
mapErrorSM = mapError $ pack . show

startTS :: AssetClass -> Contract (Last TokenSale) s Text ()
startTS token = do
    pkh <- Contract.ownPaymentPubKeyHash
    tt  <- mapErrorSM getThreadToken
    let ts = TokenSale
            { tsSeller = pkh
            , tsToken  = token
            , tsTT     = tt
            }
        client = tsClient ts
    void $ mapErrorSM $ runInitialise client 0 mempty
    tell $ Last $ Just ts
    logInfo $ "started token sale " ++ show ts

setPrice :: TokenSale -> Integer -> Contract w s Text ()
setPrice ts p = void $ mapErrorSM $ runStep (tsClient ts) $ SetPrice p

addTokens :: TokenSale -> Integer -> Contract w s Text ()
addTokens ts n = void $ mapErrorSM $ runStep (tsClient ts) $ AddTokens n

buyTokens :: TokenSale -> Integer -> Contract w s Text ()
buyTokens ts n = void $ mapErrorSM $ runStep (tsClient ts) $ BuyTokens n

withdraw :: TokenSale -> Integer -> Integer -> Contract w s Text ()
withdraw ts n l = void $ mapErrorSM $ runStep (tsClient ts) $ Withdraw n l

close :: TokenSale -> () -> Contract w s Text ()
close ts _ = void $ mapErrorSM $ runStep (tsClient ts) $ Close

type TSStartSchema =
        Endpoint "start"      (CurrencySymbol, TokenName)
type TSUseSchema =
        Endpoint "set price"  Integer
    .\/ Endpoint "add tokens" Integer
    .\/ Endpoint "buy tokens" Integer
    .\/ Endpoint "withdraw"   (Integer, Integer)
    .\/ Endpoint "close"      ()

startEndpoint :: Contract (Last TokenSale) TSStartSchema Text ()
startEndpoint = forever
              $ handleError logError
              $ awaitPromise
              $ endpoint @"start" $ startTS . AssetClass

useEndpoints' :: ( HasEndpoint "set price"  Integer            s
                 , HasEndpoint "add tokens" Integer            s
                 , HasEndpoint "buy tokens" Integer            s
                 , HasEndpoint "withdraw"   (Integer, Integer) s
                 , HasEndpoint "close"      ()                 s
                 )
              => TokenSale
              -> Contract () s Text ()
useEndpoints' ts = forever
                $ handleError logError
                $ awaitPromise
                $ setPrice' `select` addTokens' `select` buyTokens' `select` withdraw' `select` close'
  where
    setPrice'  = endpoint @"set price"  $ setPrice ts
    addTokens' = endpoint @"add tokens" $ addTokens ts
    buyTokens' = endpoint @"buy tokens" $ buyTokens ts
    withdraw'  = endpoint @"withdraw"   $ Prelude.uncurry $ withdraw ts
    close'     = endpoint @"close"      $ close ts

useEndpoints :: TokenSale -> Contract () TSUseSchema Text ()
useEndpoints = useEndpoints'
