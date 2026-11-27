import OrderedPartitions.FourPoleDiskCheck

namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem flatRight13 : flatDisk cell13 cell13.right (208477175977/250000000000) (1371520942589/1000000000000) := by decide +kernel
theorem flatLeft13 : flatDisk cell13 cell13.left (241902223421/200000000000) (5275521766793/1000000000000) := by decide +kernel
end OrderedPartitions.FourPole.Box
