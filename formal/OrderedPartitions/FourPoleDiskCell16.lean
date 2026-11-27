import OrderedPartitions.FourPoleDiskCheck

namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem flatRight16 : flatDisk cell16 cell16.right (830000000001/1000000000000) (1038601500301/250000000000) := by decide +kernel
theorem flatLeft16 : flatDisk cell16 cell16.left (304272054259/250000000000) (665404541689/125000000000) := by decide +kernel
end OrderedPartitions.FourPole.Box
