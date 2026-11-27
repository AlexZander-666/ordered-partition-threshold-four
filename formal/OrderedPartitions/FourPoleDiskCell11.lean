import OrderedPartitions.FourPoleDiskCheck

namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem flatRight11 : flatDisk cell11 cell11.right (419387597871/500000000000) (1878951199847/1000000000000) := by decide +kernel
theorem flatLeft11 : flatDisk cell11 cell11.left (300080564167/250000000000) (1304173513887/250000000000) := by decide +kernel
end OrderedPartitions.FourPole.Box
