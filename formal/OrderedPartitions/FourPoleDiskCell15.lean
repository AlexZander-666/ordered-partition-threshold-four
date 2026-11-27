import OrderedPartitions.FourPoleDiskCheck

namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem flatRight15 : flatDisk cell15 cell15.right (831407986457/1000000000000) (181983735699/200000000000) := by decide +kernel
theorem flatLeft15 : flatDisk cell15 cell15.left (303648234963/250000000000) (2653807853663/500000000000) := by decide +kernel
end OrderedPartitions.FourPole.Box
