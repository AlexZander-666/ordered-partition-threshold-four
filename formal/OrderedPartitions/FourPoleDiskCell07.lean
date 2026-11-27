import OrderedPartitions.FourPoleDiskCheck

namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem flatRight7 : flatDisk cell7 cell7.right (866354835639/1000000000000) (365684432413/125000000000) := by decide +kernel
theorem flatLeft7 : flatDisk cell7 cell7.left (1156640488347/1000000000000) (4930860721271/1000000000000) := by decide +kernel
end OrderedPartitions.FourPole.Box
