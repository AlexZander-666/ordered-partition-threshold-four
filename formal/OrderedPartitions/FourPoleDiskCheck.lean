import OrderedPartitions.FourPoleRationalJets

/-! Rational-only alternate disk test using the degree-28 polynomial. -/
namespace OrderedPartitions.FourPole.Box
open Finset

def ratPower (D : Disc) : ℕ→ℚ×ℚ
  | 0 => (1,0)
  | i+1 => let (a,b) := ratPower D i; (a*D.x-b*D.y,a*D.y+b*D.x)

def ratShift (D : Disc) (e : ℚ) (h : ℕ) : ℚ×ℚ :=
  ∑ i∈range 29, let a := polyCoeff e i * (i.choose h:ℚ)
                let z := ratPower D (i-h)
                (a*z.1,a*z.2)

def ratSwing (lo hi mid : ℚ) (i : ℕ) : ℚ :=
  let s := fun a ↦ max (hi^a-mid^a) (mid^a-lo^a)
  (s i+(if 4 ≤ i then 24*s (i-4) else 0))/(i.factorial:ℚ)

def upperShift (D : Disc) (e : ℚ) (h : ℕ) : ℚ :=
  let (a,b) := ratShift D e h
  |a|+|b|

def flatDisk (c : Cell) (D : Disc) (cap L : ℚ) : Prop :=
  let e := (c.lo+c.hi)/2
  let W := cap+D.r
  let (a,b) := ratShift D e D.mode
  0<D.r ∧ 0<cap ∧ D.x^2+D.y^2≤cap^2 ∧ W≤2 ∧
  0<c.lo ∧ c.lo≤c.hi ∧ c.hi≤6/5 ∧ 0<D.mode ∧ D.mode<29 ∧
  0<L ∧ L^2≤a^2+b^2 ∧
  jetTail c.hi 0 + (∑ i∈range 29,ratSwing c.lo c.hi e i*W^i) +
    (∑ i∈(range 29).erase D.mode,upperShift D e i*D.r^i) < L*D.r^D.mode

instance (c : Cell) (D : Disc) (cap L : ℚ) : Decidable (flatDisk c D cap L) := by
  unfold flatDisk
  dsimp only
  infer_instance
end OrderedPartitions.FourPole.Box
