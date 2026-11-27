import OrderedPartitions.FourPoleDiskCheck

namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem flatRight12 : flatDisk cell12 cell12.right (417959374779/500000000000) (1617536850067/1000000000000) := by decide +kernel
theorem flatLeft12 : flatDisk cell12 cell12.left (602809661109/500000000000) (1312679590557/250000000000) := by decide +kernel
end OrderedPartitions.FourPole.Box
