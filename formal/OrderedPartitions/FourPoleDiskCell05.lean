import OrderedPartitions.FourPoleDiskCheck

namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem flatRight5 : flatDisk cell5 cell5.right (901342688311/1000000000000) (3385856868233/1000000000000) := by decide +kernel
theorem flatLeft5 : flatDisk cell5 cell5.left (221988651169/200000000000) (231535495689/50000000000) := by decide +kernel
end OrderedPartitions.FourPole.Box
