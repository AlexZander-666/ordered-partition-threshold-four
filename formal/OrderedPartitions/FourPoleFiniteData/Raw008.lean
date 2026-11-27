import OrderedPartitions.FourPoleFiniteData.Raw000

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def coeffs8 : Coeffs := [
  521640,
  24125,
  70
]
def boxes8 : Boxes := [
  ((-2140823983,6659665),(-4281647965,13319331)), ((-2058677301,88806347),(-4117354601,177612695))
]
def history8 : List Coeffs := coeffs8 :: history7

def coeffs9 : Coeffs := [
  6717480,
  367639,
  2142
]
def boxes9 : Boxes := [
  ((-2133340877,14142771),(-4266681753,28285543)), ((-4097862929,197104367),(-256116433,12319023))
]
def history9 : List Coeffs := coeffs9 :: history8

def coeffs10 : Coeffs := [
  96117000,
  6075081,
  55482
]
def boxes10 : Boxes := [
  ((-2123966229,23517419),(-4247932457,47034839)), ((-4082153781,212813515),(-1020538445,53203379))
]
def history10 : List Coeffs := coeffs10 :: history9

def coeffs11 : Coeffs := [
  1512819000,
  108438463,
  1375110
]
def boxes11 : Boxes := [
  ((-4225411023,69556273),(-2112705511,34778137)), ((-1017554199,56187625),(-4070216795,224750501))
]
def history11 : List Coeffs := coeffs11 :: history10

def coeffs12 : Coeffs := [
  25975395600,
  2082064383,
  34072962,
  34650
]
def boxes12 : Boxes := [
  ((-2145149017,2334631),(-4290298033,4669263)), ((-4205926561,89040735),(-131435205,2782523)),
  ((-2029956055,117527593),(-4059912109,235055187))
]
def history12 : List Coeffs := coeffs12 :: history11

def coeffs13 : Coeffs := [
  483169486800,
  42823604045,
  863185466,
  2072070
]
def boxes13 : Boxes := [
  ((-4283107403,11859893),(-2141553701,5929947)), ((-4187043331,107923965),(-2093521665,53961983)),
  ((-4051527559,243439737),(-2025763779,121719869))
]
def history13 : List Coeffs := coeffs13 :: history12

def coeffs14 : Coeffs := [
  9678799930800,
  939869112939,
  22581728598,
  92198106
]
def boxes14 : Boxes := [
  ((-1068278567,5463257),(-4273114267,21853029)), ((-4169502831,125464465),(-2084751415,62732233)),
  ((-4044602783,250364513),(-2022301391,125182257))
]
def history14 : List Coeffs := coeffs14 :: history13

def coeffs15 : Coeffs := [
  207733600074000,
  21932787154421,
  613132635986,
  3671113446
]
def boxes15 : Boxes := [
  ((-4259982771,34984525),(-2129991385,17492263)), ((-4154100221,140867075),(-1038525055,35216769)),
  ((-4038678479,256288817),(-2019339239,128144409))
]
def history15 : List Coeffs := coeffs15 :: history14



end OrderedPartitions.FourPoleFinite
