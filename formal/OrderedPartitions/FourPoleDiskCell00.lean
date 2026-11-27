import OrderedPartitions.FourPoleDiskCheck

namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem flatRight0 : flatDisk cell0 cell0.right (989743972641/1000000000000) (1972670256447/500000000000) := by decide +kernel
theorem flatLeft0 : flatDisk cell0 cell0.left (1010362337919/1000000000000) (202770524737/50000000000) := by decide +kernel
end OrderedPartitions.FourPole.Box
