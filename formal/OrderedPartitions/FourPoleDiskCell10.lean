import OrderedPartitions.FourPoleDiskCheck

namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem flatRight10 : flatDisk cell10 cell10.right (210857830641/250000000000) (2184759299597/1000000000000) := by decide +kernel
theorem flatLeft10 : flatDisk cell10 cell10.left (238428768587/200000000000) (1290921435373/250000000000) := by decide +kernel
end OrderedPartitions.FourPole.Box
