import OrderedPartitions.FourPoleBoxIndex

/-! Exact midpoint jets and the rational scalar Rouché majorant. -/
namespace OrderedPartitions.FourPole.Box

def polyCoeff (e : ℚ) (h : ℕ) : ℚ :=
  if h=0 then 1 else ((if 4≤h then 24*e^(h-4) else 0)-e^h)/(h.factorial:ℚ)

def jet (D : Disc) (e : ℚ) (m : ℕ) : ℚ×ℚ :=
  ((List.range (29-m)).reverse).foldl (fun v a ↦
    (v.1*D.x-v.2*D.y+polyCoeff e (m+a)*((m+a).factorial:ℚ)/(a.factorial:ℚ),
     v.1*D.y+v.2*D.x)) (0,0)

def exponentialCap (t : ℚ) : ℚ :=
  ((List.range 14).map fun i ↦ t^i/(i.factorial:ℚ)).sum+2*t^14/((14:ℕ).factorial:ℚ)

def positiveDerivative (d m : ℕ) (e w : ℚ) : ℚ :=
  ((List.range (min d m+1)).map fun a ↦
    let b := m-a
    let coeff := (m.choose a:ℚ)*(d.factorial:ℚ)/((d-a).factorial:ℚ)*w^(d-a)*e^b
    let part := ((List.range 21).map fun i ↦
      let moment := if d=4 then 24*((b+i).factorial:ℚ)/((b+i+4).factorial:ℚ) else 1
      moment*(w*e)^i/(i.factorial:ℚ)).sum
    coeff*(part+2*(w*e)^21/((21:ℕ).factorial:ℚ))).sum

def jetTail (e : ℚ) (m : ℕ) : ℚ :=
  2*(24*e^25+e^29)*2^(29-m)/((29-m).factorial:ℚ)

structure Witness where
  centerCap : ℚ
  lo0 : ℚ
  hi0 : ℚ
  lo1 : ℚ
  hi1 : ℚ
  lo2 : ℚ
  hi2 : ℚ
  deriving Repr

def enclosesJet (D : Disc) (e : ℚ) (m : ℕ) (lo hi : ℚ) : Bool :=
  let z := jet D e m
  let t := jetTail e m
  let upper := hi-t
  decide (0≤upper ∧ z.1^2+z.2^2 ≤ upper^2 ∧ (lo≤0 ∨ (lo+t)^2≤z.1^2+z.2^2))

/-- Compares a positive lower bound for the selected jet term with the full
budget of lower jets, cell displacement, and disk Taylor remainder. -/
def verifiedJet (c : Cell) (D : Disc) (H : Witness) : Bool :=
  let e := (c.lo+c.hi)/2
  let w := H.centerCap+D.r
  let m := D.mode
  let param := (c.hi-c.lo)/2*w*exponentialCap (c.hi*w)*(1+w^4/5)
  let rest := positiveDerivative 0 (m+1) c.hi w + positiveDerivative 4 (m+1) c.hi w
  let x := H.hi0 + (if m=2 then H.hi1*D.r else 0) + rest*D.r^(m+1)/((m+1).factorial:ℚ)+param
  let y := (if m=2 then H.lo2 else H.lo1)*D.r^m/(m.factorial:ℚ)
  decide (0≤H.centerCap ∧ D.x^2+D.y^2≤H.centerCap^2 ∧ w≤2 ∧ 0<c.lo ∧ c.lo≤c.hi ∧ c.hi≤6/5 ∧ x<y) &&
    enclosesJet D e 0 H.lo0 H.hi0 && enclosesJet D e 1 H.lo1 H.hi1 && enclosesJet D e 2 H.lo2 H.hi2

end OrderedPartitions.FourPole.Box
