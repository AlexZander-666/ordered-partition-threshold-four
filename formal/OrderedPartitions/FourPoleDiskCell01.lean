import OrderedPartitions.FourPoleDiskCheck

namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem flatRight1 : flatDisk cell1 cell1.right (245624186761/250000000000) (3906639599423/1000000000000) := by decide +kernel
theorem flatLeft1 : flatDisk cell1 cell1.left (101781537499/100000000000) (4095536925117/1000000000000) := by decide +kernel
end OrderedPartitions.FourPole.Box
