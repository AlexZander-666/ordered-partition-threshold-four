import OrderedPartitions.FourPoleFiniteData.Pairs000
import OrderedPartitions.FourPoleFiniteData.Pairs008
import OrderedPartitions.FourPoleFiniteData.Pairs016
import OrderedPartitions.FourPoleFiniteData.Pairs024
import OrderedPartitions.FourPoleFiniteData.Pairs032
import OrderedPartitions.FourPoleFiniteData.Pairs040
import OrderedPartitions.FourPoleFiniteData.Pairs048
import OrderedPartitions.FourPoleFiniteData.Pairs056
import OrderedPartitions.FourPoleFiniteData.Pairs064
import OrderedPartitions.FourPoleFiniteData.Pairs072
import OrderedPartitions.FourPoleFiniteData.Pairs080
import OrderedPartitions.FourPoleFiniteData.Pairs088
import OrderedPartitions.FourPoleFiniteData.Pairs096
import OrderedPartitions.FourPoleFiniteData.Pairs104
import OrderedPartitions.FourPoleFiniteData.Pairs112
import OrderedPartitions.FourPoleFiniteData.Pairs120
import OrderedPartitions.FourPoleFiniteData.Pairs128
import OrderedPartitions.FourPoleFiniteData.Pairs136
import OrderedPartitions.FourPoleFiniteData.Pairs144
import OrderedPartitions.FourPoleFiniteData.Pairs152
import OrderedPartitions.FourPoleFiniteData.Pairs160
import OrderedPartitions.FourPoleFiniteData.Pairs168
import OrderedPartitions.FourPoleFiniteData.Pairs176
import OrderedPartitions.FourPoleFiniteData.Pairs184
import OrderedPartitions.FourPoleFiniteData.Pairs192
import OrderedPartitions.FourPoleFiniteData.Pairs200
import OrderedPartitions.FourPoleFiniteData.Pairs208
import OrderedPartitions.FourPoleFiniteData.Pairs216
import OrderedPartitions.FourPoleFiniteData.Pairs224
import OrderedPartitions.FourPoleFiniteData.Pairs232
import OrderedPartitions.FourPoleFiniteData.Pairs240
import OrderedPartitions.FourPoleFiniteData.Pairs248
import OrderedPartitions.FourPoleFiniteData.Pairs256
import OrderedPartitions.FourPoleFiniteData.Pairs264
import OrderedPartitions.FourPoleFiniteData.Pairs272
import OrderedPartitions.FourPoleFiniteData.Pairs280

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem original_gap1_finite (n : ℕ) (hi : n ≤ 287) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  by_cases h0 : n ≤ 7
  · exact range0Gap1 n (by omega) h0
  by_cases h8 : n ≤ 15
  · exact range8Gap1 n (by omega) h8
  by_cases h16 : n ≤ 23
  · exact range16Gap1 n (by omega) h16
  by_cases h24 : n ≤ 31
  · exact range24Gap1 n (by omega) h24
  by_cases h32 : n ≤ 39
  · exact range32Gap1 n (by omega) h32
  by_cases h40 : n ≤ 47
  · exact range40Gap1 n (by omega) h40
  by_cases h48 : n ≤ 55
  · exact range48Gap1 n (by omega) h48
  by_cases h56 : n ≤ 63
  · exact range56Gap1 n (by omega) h56
  by_cases h64 : n ≤ 71
  · exact range64Gap1 n (by omega) h64
  by_cases h72 : n ≤ 79
  · exact range72Gap1 n (by omega) h72
  by_cases h80 : n ≤ 87
  · exact range80Gap1 n (by omega) h80
  by_cases h88 : n ≤ 95
  · exact range88Gap1 n (by omega) h88
  by_cases h96 : n ≤ 103
  · exact range96Gap1 n (by omega) h96
  by_cases h104 : n ≤ 111
  · exact range104Gap1 n (by omega) h104
  by_cases h112 : n ≤ 119
  · exact range112Gap1 n (by omega) h112
  by_cases h120 : n ≤ 127
  · exact range120Gap1 n (by omega) h120
  by_cases h128 : n ≤ 135
  · exact range128Gap1 n (by omega) h128
  by_cases h136 : n ≤ 143
  · exact range136Gap1 n (by omega) h136
  by_cases h144 : n ≤ 151
  · exact range144Gap1 n (by omega) h144
  by_cases h152 : n ≤ 159
  · exact range152Gap1 n (by omega) h152
  by_cases h160 : n ≤ 167
  · exact range160Gap1 n (by omega) h160
  by_cases h168 : n ≤ 175
  · exact range168Gap1 n (by omega) h168
  by_cases h176 : n ≤ 183
  · exact range176Gap1 n (by omega) h176
  by_cases h184 : n ≤ 191
  · exact range184Gap1 n (by omega) h184
  by_cases h192 : n ≤ 199
  · exact range192Gap1 n (by omega) h192
  by_cases h200 : n ≤ 207
  · exact range200Gap1 n (by omega) h200
  by_cases h208 : n ≤ 215
  · exact range208Gap1 n (by omega) h208
  by_cases h216 : n ≤ 223
  · exact range216Gap1 n (by omega) h216
  by_cases h224 : n ≤ 231
  · exact range224Gap1 n (by omega) h224
  by_cases h232 : n ≤ 239
  · exact range232Gap1 n (by omega) h232
  by_cases h240 : n ≤ 247
  · exact range240Gap1 n (by omega) h240
  by_cases h248 : n ≤ 255
  · exact range248Gap1 n (by omega) h248
  by_cases h256 : n ≤ 263
  · exact range256Gap1 n (by omega) h256
  by_cases h264 : n ≤ 271
  · exact range264Gap1 n (by omega) h264
  by_cases h272 : n ≤ 279
  · exact range272Gap1 n (by omega) h272
  exact range280Gap1 n (by omega) hi

theorem original_gap2_finite (n : ℕ) (hi : n ≤ 287) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  by_cases h0 : n ≤ 7
  · exact range0Gap2 n (by omega) h0
  by_cases h8 : n ≤ 15
  · exact range8Gap2 n (by omega) h8
  by_cases h16 : n ≤ 23
  · exact range16Gap2 n (by omega) h16
  by_cases h24 : n ≤ 31
  · exact range24Gap2 n (by omega) h24
  by_cases h32 : n ≤ 39
  · exact range32Gap2 n (by omega) h32
  by_cases h40 : n ≤ 47
  · exact range40Gap2 n (by omega) h40
  by_cases h48 : n ≤ 55
  · exact range48Gap2 n (by omega) h48
  by_cases h56 : n ≤ 63
  · exact range56Gap2 n (by omega) h56
  by_cases h64 : n ≤ 71
  · exact range64Gap2 n (by omega) h64
  by_cases h72 : n ≤ 79
  · exact range72Gap2 n (by omega) h72
  by_cases h80 : n ≤ 87
  · exact range80Gap2 n (by omega) h80
  by_cases h88 : n ≤ 95
  · exact range88Gap2 n (by omega) h88
  by_cases h96 : n ≤ 103
  · exact range96Gap2 n (by omega) h96
  by_cases h104 : n ≤ 111
  · exact range104Gap2 n (by omega) h104
  by_cases h112 : n ≤ 119
  · exact range112Gap2 n (by omega) h112
  by_cases h120 : n ≤ 127
  · exact range120Gap2 n (by omega) h120
  by_cases h128 : n ≤ 135
  · exact range128Gap2 n (by omega) h128
  by_cases h136 : n ≤ 143
  · exact range136Gap2 n (by omega) h136
  by_cases h144 : n ≤ 151
  · exact range144Gap2 n (by omega) h144
  by_cases h152 : n ≤ 159
  · exact range152Gap2 n (by omega) h152
  by_cases h160 : n ≤ 167
  · exact range160Gap2 n (by omega) h160
  by_cases h168 : n ≤ 175
  · exact range168Gap2 n (by omega) h168
  by_cases h176 : n ≤ 183
  · exact range176Gap2 n (by omega) h176
  by_cases h184 : n ≤ 191
  · exact range184Gap2 n (by omega) h184
  by_cases h192 : n ≤ 199
  · exact range192Gap2 n (by omega) h192
  by_cases h200 : n ≤ 207
  · exact range200Gap2 n (by omega) h200
  by_cases h208 : n ≤ 215
  · exact range208Gap2 n (by omega) h208
  by_cases h216 : n ≤ 223
  · exact range216Gap2 n (by omega) h216
  by_cases h224 : n ≤ 231
  · exact range224Gap2 n (by omega) h224
  by_cases h232 : n ≤ 239
  · exact range232Gap2 n (by omega) h232
  by_cases h240 : n ≤ 247
  · exact range240Gap2 n (by omega) h240
  by_cases h248 : n ≤ 255
  · exact range248Gap2 n (by omega) h248
  by_cases h256 : n ≤ 263
  · exact range256Gap2 n (by omega) h256
  by_cases h264 : n ≤ 271
  · exact range264Gap2 n (by omega) h264
  by_cases h272 : n ≤ 279
  · exact range272Gap2 n (by omega) h272
  exact range280Gap2 n (by omega) hi

theorem original_gap3_finite (n : ℕ) (hi : n ≤ 287) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  by_cases h0 : n ≤ 7
  · exact range0Gap3 n (by omega) h0
  by_cases h8 : n ≤ 15
  · exact range8Gap3 n (by omega) h8
  by_cases h16 : n ≤ 23
  · exact range16Gap3 n (by omega) h16
  by_cases h24 : n ≤ 31
  · exact range24Gap3 n (by omega) h24
  by_cases h32 : n ≤ 39
  · exact range32Gap3 n (by omega) h32
  by_cases h40 : n ≤ 47
  · exact range40Gap3 n (by omega) h40
  by_cases h48 : n ≤ 55
  · exact range48Gap3 n (by omega) h48
  by_cases h56 : n ≤ 63
  · exact range56Gap3 n (by omega) h56
  by_cases h64 : n ≤ 71
  · exact range64Gap3 n (by omega) h64
  by_cases h72 : n ≤ 79
  · exact range72Gap3 n (by omega) h72
  by_cases h80 : n ≤ 87
  · exact range80Gap3 n (by omega) h80
  by_cases h88 : n ≤ 95
  · exact range88Gap3 n (by omega) h88
  by_cases h96 : n ≤ 103
  · exact range96Gap3 n (by omega) h96
  by_cases h104 : n ≤ 111
  · exact range104Gap3 n (by omega) h104
  by_cases h112 : n ≤ 119
  · exact range112Gap3 n (by omega) h112
  by_cases h120 : n ≤ 127
  · exact range120Gap3 n (by omega) h120
  by_cases h128 : n ≤ 135
  · exact range128Gap3 n (by omega) h128
  by_cases h136 : n ≤ 143
  · exact range136Gap3 n (by omega) h136
  by_cases h144 : n ≤ 151
  · exact range144Gap3 n (by omega) h144
  by_cases h152 : n ≤ 159
  · exact range152Gap3 n (by omega) h152
  by_cases h160 : n ≤ 167
  · exact range160Gap3 n (by omega) h160
  by_cases h168 : n ≤ 175
  · exact range168Gap3 n (by omega) h168
  by_cases h176 : n ≤ 183
  · exact range176Gap3 n (by omega) h176
  by_cases h184 : n ≤ 191
  · exact range184Gap3 n (by omega) h184
  by_cases h192 : n ≤ 199
  · exact range192Gap3 n (by omega) h192
  by_cases h200 : n ≤ 207
  · exact range200Gap3 n (by omega) h200
  by_cases h208 : n ≤ 215
  · exact range208Gap3 n (by omega) h208
  by_cases h216 : n ≤ 223
  · exact range216Gap3 n (by omega) h216
  by_cases h224 : n ≤ 231
  · exact range224Gap3 n (by omega) h224
  by_cases h232 : n ≤ 239
  · exact range232Gap3 n (by omega) h232
  by_cases h240 : n ≤ 247
  · exact range240Gap3 n (by omega) h240
  by_cases h248 : n ≤ 255
  · exact range248Gap3 n (by omega) h248
  by_cases h256 : n ≤ 263
  · exact range256Gap3 n (by omega) h256
  by_cases h264 : n ≤ 271
  · exact range264Gap3 n (by omega) h264
  by_cases h272 : n ≤ 279
  · exact range272Gap3 n (by omega) h272
  exact range280Gap3 n (by omega) hi

theorem original_gap4_finite (n : ℕ) (hi : n ≤ 287) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  by_cases h0 : n ≤ 7
  · exact range0Gap4 n (by omega) h0
  by_cases h8 : n ≤ 15
  · exact range8Gap4 n (by omega) h8
  by_cases h16 : n ≤ 23
  · exact range16Gap4 n (by omega) h16
  by_cases h24 : n ≤ 31
  · exact range24Gap4 n (by omega) h24
  by_cases h32 : n ≤ 39
  · exact range32Gap4 n (by omega) h32
  by_cases h40 : n ≤ 47
  · exact range40Gap4 n (by omega) h40
  by_cases h48 : n ≤ 55
  · exact range48Gap4 n (by omega) h48
  by_cases h56 : n ≤ 63
  · exact range56Gap4 n (by omega) h56
  by_cases h64 : n ≤ 71
  · exact range64Gap4 n (by omega) h64
  by_cases h72 : n ≤ 79
  · exact range72Gap4 n (by omega) h72
  by_cases h80 : n ≤ 87
  · exact range80Gap4 n (by omega) h80
  by_cases h88 : n ≤ 95
  · exact range88Gap4 n (by omega) h88
  by_cases h96 : n ≤ 103
  · exact range96Gap4 n (by omega) h96
  by_cases h104 : n ≤ 111
  · exact range104Gap4 n (by omega) h104
  by_cases h112 : n ≤ 119
  · exact range112Gap4 n (by omega) h112
  by_cases h120 : n ≤ 127
  · exact range120Gap4 n (by omega) h120
  by_cases h128 : n ≤ 135
  · exact range128Gap4 n (by omega) h128
  by_cases h136 : n ≤ 143
  · exact range136Gap4 n (by omega) h136
  by_cases h144 : n ≤ 151
  · exact range144Gap4 n (by omega) h144
  by_cases h152 : n ≤ 159
  · exact range152Gap4 n (by omega) h152
  by_cases h160 : n ≤ 167
  · exact range160Gap4 n (by omega) h160
  by_cases h168 : n ≤ 175
  · exact range168Gap4 n (by omega) h168
  by_cases h176 : n ≤ 183
  · exact range176Gap4 n (by omega) h176
  by_cases h184 : n ≤ 191
  · exact range184Gap4 n (by omega) h184
  by_cases h192 : n ≤ 199
  · exact range192Gap4 n (by omega) h192
  by_cases h200 : n ≤ 207
  · exact range200Gap4 n (by omega) h200
  by_cases h208 : n ≤ 215
  · exact range208Gap4 n (by omega) h208
  by_cases h216 : n ≤ 223
  · exact range216Gap4 n (by omega) h216
  by_cases h224 : n ≤ 231
  · exact range224Gap4 n (by omega) h224
  by_cases h232 : n ≤ 239
  · exact range232Gap4 n (by omega) h232
  by_cases h240 : n ≤ 247
  · exact range240Gap4 n (by omega) h240
  by_cases h248 : n ≤ 255
  · exact range248Gap4 n (by omega) h248
  by_cases h256 : n ≤ 263
  · exact range256Gap4 n (by omega) h256
  by_cases h264 : n ≤ 271
  · exact range264Gap4 n (by omega) h264
  by_cases h272 : n ≤ 279
  · exact range272Gap4 n (by omega) h272
  exact range280Gap4 n (by omega) hi

theorem original_finite (n gap : ℕ) (hi : n ≤ 287) (loG : 1 ≤ gap) (hiG : gap ≤ 4) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+gap) 4) := by
  interval_cases gap
  · exact original_gap1_finite n hi
  · exact original_gap2_finite n hi
  · exact original_gap3_finite n hi
  · exact original_gap4_finite n hi


#print axioms original_gap1_finite
#print axioms original_gap2_finite
#print axioms original_gap3_finite
#print axioms original_gap4_finite
#print axioms original_finite

end OrderedPartitions.FourPoleFinite
