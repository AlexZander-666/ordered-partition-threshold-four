import OrderedPartitions.FourPoleDiskCheck

namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem flatRight6 : flatDisk cell6 cell6.right (440150086123/500000000000) (3153427185391/1000000000000) := by decide +kernel
theorem flatLeft6 : flatDisk cell6 cell6.left (227454186647/200000000000) (4804698581289/1000000000000) := by decide +kernel
end OrderedPartitions.FourPole.Box
