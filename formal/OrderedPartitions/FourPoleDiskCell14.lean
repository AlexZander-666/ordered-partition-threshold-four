import OrderedPartitions.FourPoleDiskCheck

namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem flatRight14 : flatDisk cell14 cell14.right (832632517569/1000000000000) (1168467459691/1000000000000) := by decide +kernel
theorem flatLeft14 : flatDisk cell14 cell14.left (1212067290953/1000000000000) (5291709791987/1000000000000) := by decide +kernel
end OrderedPartitions.FourPole.Box
