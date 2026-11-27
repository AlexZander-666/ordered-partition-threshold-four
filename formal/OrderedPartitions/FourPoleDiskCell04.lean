import OrderedPartitions.FourPoleDiskCheck

namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem flatRight4 : flatDisk cell4 cell4.right (925007456779/1000000000000) (1785564507893/500000000000) := by decide +kernel
theorem flatLeft4 : flatDisk cell4 cell4.left (1081208209931/1000000000000) (2227429660277/500000000000) := by decide +kernel
end OrderedPartitions.FourPole.Box
