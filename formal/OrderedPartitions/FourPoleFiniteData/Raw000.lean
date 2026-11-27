import OrderedPartitions.FourPoleFiniteRows

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def coeffs0 : Coeffs := [
  1
]
def boxes0 : Boxes := []
def history0 : List Coeffs := coeffs0 :: []

def coeffs1 : Coeffs := [
  1
]
def boxes1 : Boxes := []
def history1 : List Coeffs := coeffs1 :: history0

def coeffs2 : Coeffs := [
  3
]
def boxes2 : Boxes := []
def history2 : List Coeffs := coeffs2 :: history1

def coeffs3 : Coeffs := [
  13
]
def boxes3 : Boxes := []
def history3 : List Coeffs := coeffs3 :: history2

def coeffs4 : Coeffs := [
  74,
  1
]
def boxes4 : Boxes := [
  ((-2118850533,28633115),(-4237701065,57266231))
]
def history4 : List Coeffs := coeffs4 :: history3

def coeffs5 : Coeffs := [
  530,
  11
]
def boxes5 : Boxes := [
  ((-4207638941,87328355),(-1051909735,21832089))
]
def history5 : List Coeffs := coeffs5 :: history4

def coeffs6 : Coeffs := [
  4550,
  133
]
def boxes6 : Boxes := [
  ((-4172987657,121979639),(-521623457,15247455))
]
def history6 : List Coeffs := coeffs6 :: history5

def coeffs7 : Coeffs := [
  45570,
  1723
]
def boxes7 : Boxes := [
  ((-2069245551,78238097),(-4138491101,156476195))
]
def history7 : List Coeffs := coeffs7 :: history6



end OrderedPartitions.FourPoleFinite
