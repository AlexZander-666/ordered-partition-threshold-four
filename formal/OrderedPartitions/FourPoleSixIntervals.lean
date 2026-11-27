import OrderedPartitions.FourPoleRadialLog
import Mathlib.Tactic

noncomputable section
namespace OrderedPartitions.FourPole.SixIntervals

/-- Each rational entry bounds one cell of the small-parameter annulus. -/
structure Cell where
  lo : ℚ
  hi : ℚ
  radius : ℚ

def cells : Fin 6 → Cell := ![
  ⟨0,53/5000,1/2⟩, ⟨53/5000,23/2000,1/2⟩, ⟨23/2000,3/200,1/2⟩,
  ⟨3/200,1/32,1/2⟩, ⟨1/32,3/50,3/5⟩, ⟨3/50,101/1000,3/5⟩]

def u (p : Cell) := 3/10+p.radius*p.hi
def B (p : Cell) := p.radius+(u p)^2/(2*(1-u p*p.hi))
def low (p : Cell) := 2121320/10000000-B p*p.hi
def high (p : Cell) := 2121321/10000000+B p*p.hi
def sinFour (p : Cell) := 4*low p-(4*high p)^3*p.hi^2/6
def sinShort (p : Cell) := 7/10-3*high p*p.hi
def dMax (p : Cell) := (1+u p*p.hi)^3+p.hi/2
def dMin (p : Cell) := (1-u p*p.hi)^3-p.hi/2
def x (p : Cell) := 2*low p*max 3 (288*p.lo)
def trunc (x : ℚ) := 1+x+x^2/2+x^3/6+x^4/24+x^5/120
def amplitude (p : Cell) := dMax p/(dMin p*trunc (x p))
def residue (p : Cell) := 3/2*dMax p*p.hi^2/6
def tailE (p : Cell) := residue p*p.hi
def cosine (p : Cell) := amplitude p+tailE p
def short (p : Cell) := 2*(amplitude p+tailE p)/sinShort p
def fourth (p : Cell) := (12*high p*amplitude p+cosine p*(4*high p)^2*p.hi/2+2*residue p)/sinFour p

structure Valid (p : Cell) : Prop where
  bounds : 0≤p.lo ∧ p.lo<p.hi ∧ p.hi≤101/1000
  logr : u p*p.hi<1
  lower : 0<low p
  upper : high p*p.hi<1/25
  sin3 : 0<sinShort p
  sin4 : 0<sinFour p
  den : 0<dMin p
  contour : 450*(p.hi*(1+u p*p.hi)/3)^2≤3/2
  cosine : SixIntervals.cosine p<2/5
  short : (SixIntervals.cosine p)^2+(SixIntervals.short p)^2<1
  fourth : (SixIntervals.cosine p)^2+(SixIntervals.fourth p)^2<1
  disk : (p.radius=1/2 ∧ p.hi≤1/32) ∨ (p.radius=3/5 ∧ p.hi≤101/1000)

private def ok (p : Cell) : Prop :=
  (0≤p.lo ∧ p.lo<p.hi ∧ p.hi≤101/1000) ∧ u p*p.hi<1 ∧ 0<low p ∧ high p*p.hi<1/25 ∧
  0<sinShort p ∧ 0<sinFour p ∧ 0<dMin p ∧ 450*(p.hi*(1+u p*p.hi)/3)^2≤3/2 ∧
  cosine p<2/5 ∧ (cosine p)^2+(short p)^2<1 ∧ (cosine p)^2+(fourth p)^2<1 ∧
  ((p.radius=1/2 ∧ p.hi≤1/32) ∨ (p.radius=3/5 ∧ p.hi≤101/1000))

private instance (p : Cell) : Decidable (ok p) := by unfold ok;infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem pass : ∀ i : Fin 6, ok (cells i) := by decide +kernel

theorem valid (i : Fin 6) : Valid (cells i) := by
  obtain ⟨a,b,c,d,e,f,g,h,j,k,l,m⟩ := pass i
  exact ⟨a,b,c,d,e,f,g,h,j,k,l,m⟩

theorem cover {e : ℝ} (ep : 0≤e) (eh : e≤101/1000) :
    ∃ i : Fin 6, ((cells i).lo:ℝ)≤e ∧ e≤((cells i).hi:ℝ) := by
  by_cases h0 : e≤53/5000
  · exact ⟨0,by simpa [cells],by simpa [cells]⟩
  by_cases h1 : e≤23/2000
  · exact ⟨1,by simpa [cells] using (le_of_not_ge h0),by simpa [cells]⟩
  by_cases h2 : e≤3/200
  · exact ⟨2,by simpa [cells] using (le_of_not_ge h1),by simpa [cells]⟩
  by_cases h3 : e≤1/32
  · exact ⟨3,by simpa [cells] using (le_of_not_ge h2),by simpa [cells] using h3⟩
  by_cases h4 : e≤3/50
  · exact ⟨4,by simpa [cells] using (le_of_not_ge h3),by simpa [cells]⟩
  exact ⟨5,by simpa [cells] using (le_of_not_ge h4),by simpa [cells] using eh⟩

#print axioms valid
#print axioms cover
end OrderedPartitions.FourPole.SixIntervals
