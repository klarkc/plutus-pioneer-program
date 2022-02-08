module Week03.Converter ( posixTimeToSlotTestnetConverter, testnetSlotToEndPOSIXTime ) where 

import Ledger          ( POSIXTime(POSIXTime), Slot(Slot) )
import Ledger.TimeSlot ( SlotConfig(SlotConfig), posixTimeToEnclosingSlot, slotToEndPOSIXTime )

posixTimeToSlotTestnetConverter :: POSIXTime -> Slot
posixTimeToSlotTestnetConverter time = slotWhenSlotChangedTo1Sec + posixTimeToEnclosingSlot testnetConf time

timeWhenSlotChangedTo1Sec :: POSIXTime
timeWhenSlotChangedTo1Sec = POSIXTime 1595967616000  -- 2020/07/28 20:20:16 - epoch:74 - slot:1598400 - block:1597133  

slotWhenSlotChangedTo1Sec :: Slot
slotWhenSlotChangedTo1Sec = Slot 1598400

testnetConf :: SlotConfig
testnetConf = SlotConfig 1000 timeWhenSlotChangedTo1Sec

testnetSlotToEndPOSIXTime :: Slot -> POSIXTime
testnetSlotToEndPOSIXTime = slotToEndPOSIXTime testnetConf 
