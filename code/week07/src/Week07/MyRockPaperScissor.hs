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

module Week07.MyRockPaperScissor
    ( Game (..)
    , GameChoice (..)
    , FirstParams (..)
    , SecondParams (..)
    , GameSchema
    , Last (..)
    , ThreadToken
    , Text
    , endpoints
    ) where

import           Control.Monad                hiding (fmap)
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.Monoid                  (Last (..))
import           Data.Text                    (Text, pack)
import           GHC.Generics                 (Generic)
import           Ledger                       hiding (singleton)
import qualified Ledger.Ada                   as Ada
import           Ledger.Constraints           as Constraints
import           Ledger.Typed.Tx
import qualified Ledger.Typed.Scripts         as Scripts
import           Plutus.Contract              as Contract
import           Plutus.Contract.StateMachine
import qualified PlutusTx
import           PlutusTx.Prelude             hiding (Semigroup(..), check, unless)
import           Playground.Contract          (ToSchema)
import           Prelude                      (Semigroup (..), Show (..), String,)
import qualified Prelude

data Game = Game
    { gFirst          :: !PaymentPubKeyHash
    , gSecond         :: !PaymentPubKeyHash
    , gStake          :: !Integer
    , gPlayDeadline   :: !POSIXTime
    , gRevealDeadline :: !POSIXTime
    , gToken          :: !ThreadToken
    } deriving (Show, Generic, FromJSON, ToJSON, Prelude.Eq)

PlutusTx.makeLift ''Game

data GameChoice = Rock | Paper | Scissors
    deriving (Show, Generic, FromJSON, ToJSON, ToSchema, Prelude.Eq, Prelude.Ord)

{-# INLINABLE serialize #-}
serialize :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString -> GameChoice -> BuiltinByteString
serialize bsRock' _        _           Rock     = bsRock'
serialize _       bsPaper' _           Paper    = bsPaper'
serialize _       _        bsScissors' Scissors = bsScissors'

instance Eq GameChoice where
    {-# INLINABLE (==) #-}
    Rock     == Rock     = True
    Paper    == Paper    = True
    Scissors == Scissors = True
    _        == _        = False

PlutusTx.unstableMakeIsData ''GameChoice

data GameDatum =   GameDatum BuiltinByteString (Maybe GameChoice)
                 | GameDraw
                 | GameFinished
    deriving Show

instance Eq GameDatum where
    {-# INLINABLE (==) #-}
    GameDatum bs mc == GameDatum bs' mc' = (bs == bs') && (mc == mc')
    GameDraw        == GameDraw          = True
    GameFinished    == GameFinished      = True
    _               == _                 = False

PlutusTx.unstableMakeIsData ''GameDatum

data GameRedeemer = Play GameChoice | Reveal BuiltinByteString GameChoice | ClaimFirst | ClaimSecond
    deriving Show

PlutusTx.unstableMakeIsData ''GameRedeemer

data GameResult = First | Second | Draw

instance Eq GameResult where
    {-# INLINABLE (==) #-}
    First  == First  = True
    Second == Second = True
    Draw   == Draw   = True
    _      == _      = False

PlutusTx.makeLift ''GameResult

{-# INLINABLE beats #-}
beats :: GameChoice -> GameChoice -> GameResult
beats c        c'       | c == c' = Draw
beats Rock     Scissors           = First
beats Paper    Rock               = First
beats Scissors Paper              = First
beats _        _                  = Second

{-# INLINABLE lovelaces #-}
lovelaces :: Value -> Integer
lovelaces = Ada.getLovelace . Ada.fromValue

{-# INLINABLE gameDatum #-}
gameDatum :: TxOut -> (DatumHash -> Maybe Datum) -> Maybe GameDatum
gameDatum o f = do
    dh      <- txOutDatum o
    Datum d <- f dh
    PlutusTx.fromBuiltinData d

{-# INLINABLE transition #-}
transition :: Game -> State GameDatum -> GameRedeemer -> Maybe (TxConstraints Void Void, State GameDatum)
transition game s r = let st = gStake game; st' = st * 2; st'' = st in case (stateValue s, stateData s, r) of
    -- P1 have played, P2 plays
    (v, GameDatum bs Nothing, Play c)
        | lovelaces v == st                  -> Just ( Constraints.mustBeSignedBy (gSecond game)                    <>
                                                       Constraints.mustValidateIn (to $ gPlayDeadline game)
                                                     , State (GameDatum bs $ Just c) (Ada.lovelaceValueOf st')
                                                     )
    -- Both played, P1 reveals and game is draw
    (v, GameDatum _ (Just p2c), Reveal _ p1c)
        | lovelaces v == st' &&
          p1c `beats` p2c == Draw            -> Just ( Constraints.mustBeSignedBy (gFirst game)                     <>
                                                       Constraints.mustValidateIn (to $ gRevealDeadline game)
                                                     , State GameDraw (Ada.lovelaceValueOf st'')
                                                     )

    -- Both played, P1 reveals and he is the winner
    (v, GameDatum _ (Just p2c), Reveal _ p1c)
        | lovelaces v == st' &&
          p1c `beats` p2c == First           -> Just ( Constraints.mustBeSignedBy (gFirst game)                     <>
                                                       Constraints.mustValidateIn (to $ gRevealDeadline game)
                                                     , State GameFinished mempty
                                                     )

    -- Both played, P2 claims and game is draw
    (v, GameDraw, ClaimSecond)
        | lovelaces v == st''                -> Just ( Constraints.mustBeSignedBy (gSecond game)                    <>
                                                       Constraints.mustValidateIn (from $ 1 + gRevealDeadline game)
                                                     , State GameFinished mempty
                                                     )
    -- Both played and P2 claims (he's the winner or P1 lost)
    (v, GameDatum _ (Just _), ClaimSecond)
        | lovelaces v == st'                 -> Just ( Constraints.mustBeSignedBy (gSecond game)                    <>
                                                       Constraints.mustValidateIn (from $ 1 + gRevealDeadline game)
                                                     , State GameFinished mempty
                                                     )

    -- P1 played and P1 claims (P2 didn't played)
    (v, GameDatum _ Nothing, ClaimFirst)
        | lovelaces v == st                  -> Just ( Constraints.mustBeSignedBy (gFirst game)                     <>
                                                       Constraints.mustValidateIn (from $ 1 + gPlayDeadline game)
                                                     , State GameFinished mempty
                                                     )
    -- Otherwise
    _                                        -> Nothing

{-# INLINABLE final #-}
final :: GameDatum -> Bool
final GameFinished = True
final _            = False

{-# INLINABLE check #-}
check :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString -> GameDatum -> GameRedeemer -> ScriptContext -> Bool
check bsRock' bsPaper' bsScissors' (GameDatum bs (Just _)) (Reveal nonce p1c) _ =
    sha2_256 (nonce `appendByteString` serialize bsRock' bsPaper' bsScissors' p1c ) == bs
check _       _        _          _                         _                  _ = True

{-# INLINABLE gameStateMachine #-}
gameStateMachine :: Game -> BuiltinByteString -> BuiltinByteString -> BuiltinByteString -> StateMachine GameDatum GameRedeemer
gameStateMachine game bsRock' bsPaper' bsScissors' = StateMachine
    { smTransition  = transition game
    , smFinal       = final
    , smCheck       = check bsRock' bsPaper' bsScissors'
    , smThreadToken = Just $ gToken game
    }

{-# INLINABLE mkGameValidator #-}
mkGameValidator :: Game -> BuiltinByteString -> BuiltinByteString -> BuiltinByteString -> GameDatum -> GameRedeemer -> ScriptContext -> Bool
mkGameValidator game bsRock' bsPaper' bsScissors' = mkValidator $ gameStateMachine game bsRock' bsPaper' bsScissors'

type Gaming = StateMachine GameDatum GameRedeemer

bsRock, bsPaper, bsScissors :: BuiltinByteString
bsRock = "0"
bsPaper  = "1"
bsScissors = "3"

gameStateMachine' :: Game -> StateMachine GameDatum GameRedeemer
gameStateMachine' game = gameStateMachine game bsRock bsPaper bsScissors

typedGameValidator :: Game -> Scripts.TypedValidator Gaming
typedGameValidator game = Scripts.mkTypedValidator @Gaming
    ($$(PlutusTx.compile [|| mkGameValidator ||])
        `PlutusTx.applyCode` PlutusTx.liftCode game
        `PlutusTx.applyCode` PlutusTx.liftCode bsRock
        `PlutusTx.applyCode` PlutusTx.liftCode bsPaper
        `PlutusTx.applyCode` PlutusTx.liftCode bsScissors)
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @GameDatum @GameRedeemer

gameValidator :: Game -> Validator
gameValidator = Scripts.validatorScript . typedGameValidator

gameAddress :: Game -> Ledger.Address
gameAddress = scriptAddress . gameValidator

gameClient :: Game -> StateMachineClient GameDatum GameRedeemer
gameClient game = mkStateMachineClient $ StateMachineInstance (gameStateMachine' game) (typedGameValidator game)

data FirstParams = FirstParams
    { fpSecond         :: !PaymentPubKeyHash
    , fpStake          :: !Integer
    , fpPlayDeadline   :: !POSIXTime
    , fpRevealDeadline :: !POSIXTime
    , fpNonce          :: !BuiltinByteString
    , fpChoice         :: !GameChoice
    } deriving (Show, Generic, FromJSON, ToJSON, ToSchema)

mapError' :: Contract w s SMContractError a -> Contract w s Text a
mapError' = mapError $ pack . show

waitUntilTimeHasPassed :: AsContractError e => POSIXTime -> Contract w s e ()
waitUntilTimeHasPassed t = void $ awaitTime t >> waitNSlots 1

firstGame :: forall s. FirstParams -> Contract (Last ThreadToken) s Text ()
firstGame fp = do
    pkh <- Contract.ownPaymentPubKeyHash
    tt  <- mapError' getThreadToken
    let game   = Game
            { gFirst          = pkh
            , gSecond         = fpSecond fp
            , gStake          = fpStake fp
            , gPlayDeadline   = fpPlayDeadline fp
            , gRevealDeadline = fpRevealDeadline fp
            , gToken          = tt
            }
        client = gameClient game
        v      = Ada.lovelaceValueOf (fpStake fp)
        c      = fpChoice fp
        bs     = sha2_256 $ fpNonce fp `appendByteString` serialize bsRock bsPaper bsScissors c
    void $ mapError' $ runInitialise client (GameDatum bs Nothing) v
    logInfo @String $ "made first move: " ++ show (fpChoice fp)
    tell $ Last $ Just tt

    waitUntilTimeHasPassed $ fpPlayDeadline fp

    m <- mapError' $ getOnChainState client
    case m of
        Nothing     -> throwError "game output not found"
        Just (o, _) -> case tyTxOutData $ ocsTxOut o of

            GameDatum _ Nothing -> do
                logInfo @String "second player did not play"
                void $ mapError' $ runStep client ClaimFirst
                logInfo @String "first player reclaimed stake"

            GameDatum _ (Just c') | (c `beats` c') == Draw -> do
                logInfo @String "second player played and game is draw"
                void $ mapError' $ runStep client $ Reveal (fpNonce fp) c
                logInfo @String "first player revealed and took half of the stake"

            GameDatum _ (Just c') | (c `beats` c') == First -> do
                logInfo @String "second player played and lost"
                void $ mapError' $ runStep client $ Reveal (fpNonce fp) c
                logInfo @String "first player revealed and won"

            _ -> logInfo @String "second player played and won"

data SecondParams = SecondParams
    { spFirst          :: !PaymentPubKeyHash
    , spStake          :: !Integer
    , spPlayDeadline   :: !POSIXTime
    , spRevealDeadline :: !POSIXTime
    , spChoice         :: !GameChoice
    , spToken          :: !ThreadToken
    } deriving (Show, Generic, FromJSON, ToJSON)

secondGame :: forall w s. SecondParams -> Contract w s Text ()
secondGame sp = do
    pkh <- Contract.ownPaymentPubKeyHash
    let game   = Game
            { gFirst          = spFirst sp
            , gSecond         = pkh
            , gStake          = spStake sp
            , gPlayDeadline   = spPlayDeadline sp
            , gRevealDeadline = spRevealDeadline sp
            , gToken          = spToken sp
            }
        client = gameClient game
    m <- mapError' $ getOnChainState client
    case m of
        Nothing          -> logInfo @String "no running game found"
        Just (o, _) -> do
            logInfo @String "running game found"
            case tyTxOutData $ ocsTxOut o of
                GameDatum _ Nothing -> do
                    void $ mapError' $ runStep client $ Play $ spChoice sp
                    logInfo @String $ "made second move: " ++ show (spChoice sp)

                    waitUntilTimeHasPassed $ spRevealDeadline sp

                    m' <- mapError' $ getOnChainState client
                    case m' of
                        Nothing -> logInfo @String "first player won"
                        Just (o', _)  -> let claim = void $ mapError' $ runStep client ClaimSecond
                                             datum = tyTxOutData $ ocsTxOut o'
                                         in case datum of
                                              GameDraw -> do
                                                logInfo @String "first player moved and game is draw"
                                                claim
                                                logInfo @String "second player took half of the stake"
                                              _ -> do
                                                logInfo @String "first player didn't reveal"
                                                claim
                                                logInfo @String "second player won"
                _ -> throwError "unexpected datum"

type GameSchema = Endpoint "first" FirstParams .\/ Endpoint "second" SecondParams

endpoints :: Contract (Last ThreadToken) GameSchema Text ()
endpoints = awaitPromise (first `select` second) >> endpoints
  where
    first  = endpoint @"first"  firstGame
    second = endpoint @"second" secondGame
