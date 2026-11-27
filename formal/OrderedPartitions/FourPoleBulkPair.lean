import OrderedPartitions.FourPoleBulkCells
import OrderedPartitions.FourPoleCircleFloor

noncomputable section
namespace OrderedPartitions.FourPole.Box
open Complex

/-- Large-cell certificates provide the normalized physical upper pair, the
radial ratio, and either a positive angular margin or a vertical critical
coordinate with which the primary derivative vanishes. -/
structure BulkPair (e : ℝ) (z v w y : ℂ) : Prop where
  right_eq : z=(e:ℂ)*w
  left_eq : v=(e:ℂ)*y
  right_lt : ‖w‖<1
  left_gt : 1<‖y‖
  upper : 0<w.im
  right : w.im<w.re
  ratio : ‖w‖/‖y‖≤489/500
  left_norm : ‖v‖≤8/5
  left_real : |v.re|≤6/5
  modes : (1/50≤w.im ∧ 1/200≤w.re*w.im*(w.re-w.im)*(w.re+w.im)) ∨
    (1≤e ∧ ‖w‖/‖y‖≤93/100 ∧ 13/20≤w.re ∧ 1/2≤w.re-w.im)

private theorem coords (D : Disc) {w : ℂ} (inside : ‖w-center D‖≤(D.r:ℝ)) :
    |w.re-(D.x:ℝ)|≤(D.r:ℝ) ∧ |w.im-(D.y:ℝ)|≤(D.r:ℝ) := by
  exact ⟨by simpa [center] using (abs_re_le_norm _).trans inside,
         by simpa [center] using (abs_im_le_norm _).trans inside⟩

private theorem cn (D : Disc) : ‖center D‖^2=(D.x:ℝ)^2+(D.y:ℝ)^2 := by
  rw [Complex.sq_norm];simp [center,Complex.normSq,pow_two]

theorem get_bulk_pair {e : ℝ} (elo : 101/1000≤e) (ehi : e≤1143/1000) {z v : ℂ}
    (pol : CirclePoles (1-e^4/24) 3 z v) : ∃ w y : ℂ, BulkPair e z v w y := by
  obtain ⟨c,a,b,lo,hi,cell,dr,dl,⟨w0,w0i,w0z⟩,⟨y,yi,yz⟩⟩ := bulk_cover elo ehi
  obtain ⟨ap,ac,bp,bc,lr,rx,rat,_,rr,lcap,lpos,bx,mode⟩ := cell
  have ep : 0<e := by linarith
  have ez : (e:ℂ)≠0 := by exact_mod_cast ep.ne'
  have er (s : ℂ) : ‖(e:ℂ)*s‖=e*‖s‖ := by simp [abs_of_pos ep]
  have sc {s : ℂ} (g : scaledG e s=0) : G (1-e^4/24) ((e:ℂ)*s)=0 :=
    (mul_eq_zero.mp g).resolve_left (div_ne_zero (by norm_num) (pow_ne_zero _ ez))
  have w0b : ‖w0-center c.right‖≤(c.right.r:ℝ) := by simpa [dist_eq_norm] using (Metric.mem_ball.mp w0i).le
  have yb : ‖y-center c.left‖≤(c.left.r:ℝ) := by simpa [dist_eq_norm] using (Metric.mem_ball.mp yi).le
  obtain ⟨y1,yl,yu⟩ := left_location dl yb
  have w0r := (right_location dr w0b).1
  have a' : ‖center c.right‖≤(a:ℝ) := by
    have p : (0:ℝ)≤a := by exact_mod_cast ap
    have h := (Rat.cast_le (K:=ℝ)).mpr ac;push_cast at h
    nlinarith [cn c.right]
  have b' : (b:ℝ)≤‖center c.left‖ := by
    have h := (Rat.cast_le (K:=ℝ)).mpr bc;push_cast at h
    nlinarith [cn c.left,norm_nonneg (center c.left)]
  have ly : ‖y‖≤11/8 := by
    have cap := (Rat.cast_le (K:=ℝ)).mpr lcap
    have pos := (Rat.cast_le (K:=ℝ)).mpr lpos
    push_cast at cap pos
    have h : ‖center c.left‖≤11/8-(c.left.r:ℝ) := by nlinarith [cn c.left]
    have t := norm_add_le (y-center c.left) (center c.left)
    rw [sub_add_cancel] at t;linarith
  have ry : (b:ℝ)-(c.left.r:ℝ)≤‖y‖ := by
    have t := norm_sub_le y (y-center c.left);rw [sub_sub_cancel] at t;linarith
  have wy : (e:ℂ)*y=v := by
    have r : ((e:ℂ)*y).re<0 := by rw [re_ofReal_mul];exact mul_neg_of_pos_of_neg ep yl
    have u : 0<((e:ℂ)*y).im := by rw [im_ofReal_mul];exact mul_pos ep yu
    obtain E|E|E|E := pol.exhaustive _ (by rw [er];nlinarith only [mul_le_mul_of_nonneg_left ly ep.le,ehi]) (sc yz)
    · rw [E] at r;linarith [pol.right]
    · rw [E] at u;change 0< -z.im at u;linarith [pol.upperRight]
    · exact E
    · rw [E] at u;change 0< -v.im at u;linarith [pol.upperLeft]
  have chooseW : ∃ w : ℂ, (e:ℂ)*w=z ∧ ‖w-center c.right‖≤(c.right.r:ℝ) := by
    have p := (Rat.cast_le (K:=ℝ)).mpr rx;push_cast at p
    have w0p : 0<w0.re := by linarith [(abs_le.mp (coords _ w0b).1).1]
    have r : 0<((e:ℂ)*w0).re := by rw [re_ofReal_mul];exact mul_pos ep w0p
    obtain E|E|E|E := pol.exhaustive _ (by rw [er];nlinarith only [mul_le_mul_of_nonneg_left w0r.le ep.le,ehi]) (sc w0z)
    · exact ⟨w0,E,w0b⟩
    · have neg : w0.im<0 := by
        have s := congrArg Complex.im E
        change ((e:ℂ)*w0).im= -z.im at s
        rw [im_ofReal_mul] at s
        exact neg_of_mul_neg_right (by linarith [pol.upperRight] : e*w0.im<0) ep.le
      have sym : c.right.y=0 := by
        have keep := dr
        obtain ⟨_,_,_,_,one|two⟩ := keep
        · exact False.elim ((right_location dr w0b).2.2 one.1 |>.not_gt neg)
        · exact two.2
      have st : star (center c.right)=center c.right := by simp [center,sym]
      refine ⟨star w0,?_,?_⟩
      · have tt := congrArg star E
        simpa using tt
      · nth_rw 1 [←st];rw [←star_sub,norm_star];exact w0b
    · rw [E] at r;linarith [pol.left]
    · rw [E] at r;change 0<v.re at r;linarith [pol.left]
  obtain ⟨w,we,wb⟩ := chooseW
  obtain ⟨wt,wa,_⟩ := right_location dr wb
  have wp : 0<w.im := by
    have v := pol.upperRight;rw [←we,im_ofReal_mul] at v;exact pos_of_mul_pos_right v ep.le
  have t := norm_add_le (w-center c.right) (center c.right)
  rw [sub_add_cancel] at t
  have wr : ‖w‖≤(a:ℝ)+(c.right.r:ℝ) := by linarith
  have wratio {R : ℝ} (pos : 0≤R) (h : (a:ℝ)+(c.right.r:ℝ)≤R*((b:ℝ)-(c.left.r:ℝ))) : ‖w‖/‖y‖≤R :=
    (div_le_iff₀ (by linarith)).mpr (wr.trans (h.trans (mul_le_mul_of_nonneg_left ry pos)))
  have rv := (Rat.cast_le (K:=ℝ)).mpr rat
  push_cast at rv
  refine ⟨w,y,we.symm,wy.symm,wt,y1,wp,wa,wratio (by norm_num) rv,?_,?_,?_⟩
  · rw [←wy,er];nlinarith only [mul_le_mul_of_nonneg_left ly ep.le,ehi]
  · have bxx := (Rat.cast_le (K:=ℝ)).mpr bx
    push_cast at bxx
    have yx := (coords _ yb).1
    have yy := abs_add_le (y.re-(c.left.x:ℝ)) (c.left.x:ℝ)
    rw [sub_add_cancel] at yy
    rw [←wy,re_ofReal_mul,abs_mul,abs_of_pos ep]
    exact (mul_le_mul hi (show |y.re|≤|(c.left.x:ℝ)|+(c.left.r:ℝ) by linarith) (abs_nonneg _) (ep.le.trans hi)).trans bxx
  · obtain ⟨wx,wi⟩ := coords _ wb
    obtain ⟨xl,xh⟩ := abs_le.mp wx
    obtain ⟨yl,yh⟩ := abs_le.mp wi
    rcases mode with ⟨m1,m2,m3,m4⟩|⟨m1,m2,m3,m4⟩
    · left
      have m1' := (Rat.cast_le (K:=ℝ)).mpr m1
      have m2' := (Rat.cast_lt (K:=ℝ)).mpr m2
      have m3' := (Rat.cast_lt (K:=ℝ)).mpr m3
      have m4' := (Rat.cast_le (K:=ℝ)).mpr m4
      push_cast at m1' m2' m3' m4'
      refine ⟨by linarith, m4'.trans ?_⟩
      have xpos := wp.trans wa
      have yz : 0≤((c.right.x:ℝ)+(c.right.y:ℝ)-2*(c.right.r:ℝ)) := by linarith
      have dp : 0≤w.re-w.im := sub_nonneg.mpr wa.le
      have mxy := mul_le_mul (show (c.right.x:ℝ)-c.right.r≤w.re by linarith)
        (show (c.right.y:ℝ)-c.right.r≤w.im by linarith) (by linarith) xpos.le
      have md := mul_le_mul mxy (show (c.right.x:ℝ)-c.right.y-2*c.right.r≤w.re-w.im by linarith)
        m3'.le (mul_nonneg xpos.le wp.le)
      exact mul_le_mul md (by linarith) yz (mul_nonneg (mul_nonneg xpos.le wp.le) dp)
    · right
      have al := (Rat.cast_le (K:=ℝ)).mpr m1
      have rl := (Rat.cast_le (K:=ℝ)).mpr m2
      have xs := (Rat.cast_le (K:=ℝ)).mpr m3
      have df := (Rat.cast_le (K:=ℝ)).mpr m4
      push_cast at al rl xs df
      exact ⟨by linarith,wratio (by norm_num) rl,by linarith,by linarith⟩

#print axioms get_bulk_pair
end OrderedPartitions.FourPole.Box
