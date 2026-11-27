import OrderedPartitions.FourPoleDiskCheck

namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem flatRight3 : flatDisk cell3 cell3.right (29718842241/31250000000) (373312910897/100000000000) := by decide +kernel
theorem flatLeft3 : flatDisk cell3 cell3.left (210308530959/200000000000) (856408260961/200000000000) := by decide +kernel
end OrderedPartitions.FourPole.Box
