import OrderedPartitions.FourPoleDiskCheck

namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem flatRight8 : flatDisk cell8 cell8.right (171593005453/200000000000) (1366785998947/500000000000) := by decide +kernel
theorem flatLeft8 : flatDisk cell8 cell8.left (233793222891/200000000000) (1252945421469/250000000000) := by decide +kernel
end OrderedPartitions.FourPole.Box
