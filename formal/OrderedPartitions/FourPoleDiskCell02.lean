import OrderedPartitions.FourPoleDiskCheck

namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem flatRight2 : flatDisk cell2 cell2.right (971777652543/1000000000000) (481114981273/125000000000) := by decide +kernel
theorem flatLeft2 : flatDisk cell2 cell2.left (205808819583/200000000000) (64947248851/15625000000) := by decide +kernel
end OrderedPartitions.FourPole.Box
