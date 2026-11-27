import OrderedPartitions.FourPoleDiskCheck

namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem flatRight9 : flatDisk cell9 cell9.right (850318553187/1000000000000) (498895399659/200000000000) := by decide +kernel
theorem flatLeft9 : flatDisk cell9 cell9.left (590401601763/500000000000) (2544769989631/500000000000) := by decide +kernel
end OrderedPartitions.FourPole.Box
