import OrderedPartitions.FourPolePhysicalCompact

namespace OrderedPartitions.FourPole.Box

def spatial (c : Cell) (a b : ℚ) : Prop :=
  0≤a ∧ c.right.x^2+c.right.y^2≤a^2 ∧ 0≤b ∧ b^2≤c.left.x^2+c.left.y^2 ∧
  0<b-c.left.r ∧ 13/20≤c.right.x-c.right.r ∧
  (a+c.right.r)≤(489/500)*(b-c.left.r) ∧
  c.hi≤1143/1000 ∧ 0≤c.left.r ∧ c.left.x^2+c.left.y^2≤(11/8-c.left.r)^2 ∧
  0≤11/8-c.left.r ∧ c.hi*(|c.left.x|+c.left.r)≤6/5 ∧
  ((c.right.y-c.right.r≥1/50 ∧ 0<c.right.x-c.right.r ∧
    0<c.right.x-c.right.y-2*c.right.r ∧
    (c.right.x-c.right.r)*(c.right.y-c.right.r)*(c.right.x-c.right.y-2*c.right.r)*
      (c.right.x+c.right.y-2*c.right.r)≥1/200) ∨
   (1≤c.lo ∧ a+c.right.r≤(93/100)*(b-c.left.r) ∧
     13/20≤c.right.x-c.right.r ∧ 1/2≤c.right.x-c.right.y-2*c.right.r))
instance (c : Cell) (a b : ℚ) : Decidable (spatial c a b) := by unfold spatial;infer_instance

theorem bulk2 : spatial cell2 (971777652543/1000000000000) (514522048957/500000000000) := by decide +kernel
theorem bulk3 : spatial cell3 (29718842241/31250000000) (525771327397/500000000000) := by decide +kernel
theorem bulk4 : spatial cell4 (925007456779/1000000000000) (108120820993/100000000000) := by decide +kernel
theorem bulk5 : spatial cell5 (901342688311/1000000000000) (277485813961/250000000000) := by decide +kernel
theorem bulk6 : spatial cell6 (440150086123/500000000000) (568635466617/500000000000) := by decide +kernel
theorem bulk7 : spatial cell7 (866354835639/1000000000000) (578320244173/500000000000) := by decide +kernel
theorem bulk8 : spatial cell8 (171593005453/200000000000) (584483057227/500000000000) := by decide +kernel
theorem bulk9 : spatial cell9 (850318553187/1000000000000) (47232128141/40000000000) := by decide +kernel
theorem bulk10 : spatial cell10 (210857830641/250000000000) (596071921467/500000000000) := by decide +kernel
theorem bulk11 : spatial cell11 (419387597871/500000000000) (1200322256667/1000000000000) := by decide +kernel
theorem bulk12 : spatial cell12 (417959374779/500000000000) (1205619322217/1000000000000) := by decide +kernel
theorem bulk13 : spatial cell13 (208477175977/250000000000) (75594444819/62500000000) := by decide +kernel
theorem bulk14 : spatial cell14 (832632517569/1000000000000) (151508411369/125000000000) := by decide +kernel
theorem bulk15 : spatial cell15 (831407986457/1000000000000) (1214592939851/1000000000000) := by decide +kernel
theorem bulk16 : spatial cell16 (830000000001/1000000000000) (243417643407/200000000000) := by decide +kernel

theorem bulk_cover {e : ℝ} (lo : 101/1000≤e) (hi : e≤1143/1000) :
    ∃ (c : Cell) (a b : ℚ), (c.lo:ℝ)≤e ∧ e≤(c.hi:ℝ) ∧ spatial c a b ∧
      rightTest c.right ∧ leftTest c.left ∧
      (∃ z∈Metric.ball (center c.right) (c.right.r:ℝ), scaledG e z=0) ∧
      (∃ v∈Metric.ball (center c.left) (c.left.r:ℝ), scaledG e v=0) := by
  by_cases h2 : e≤5447/32000
  · have left : (cell2.lo:ℝ)≤e := by norm_num [cell2]; linarith only [lo]
    have right : e≤(cell2.hi:ℝ) := by norm_num [cell2];exact h2
    exact ⟨cell2,_,_,left,right,bulk2,valid2.1,valid2.2,real_disk_zero flatRight2 left right,real_disk_zero flatLeft2 left right⟩
  by_cases h3 : e≤4947/16000
  · have left : (cell3.lo:ℝ)≤e := by norm_num [cell3]; exact le_of_not_ge h2
    have right : e≤(cell3.hi:ℝ) := by norm_num [cell3];exact h3
    exact ⟨cell3,_,_,left,right,bulk3,valid3.1,valid3.2,real_disk_zero flatRight3 left right,real_disk_zero flatLeft3 left right⟩
  by_cases h4 : e≤14341/32000
  · have left : (cell4.lo:ℝ)≤e := by norm_num [cell4]; exact le_of_not_ge h3
    have right : e≤(cell4.hi:ℝ) := by norm_num [cell4];exact h4
    exact ⟨cell4,_,_,left,right,bulk4,valid4.1,valid4.2,real_disk_zero flatRight4 left right,real_disk_zero flatLeft4 left right⟩
  by_cases h5 : e≤4697/8000
  · have left : (cell5.lo:ℝ)≤e := by norm_num [cell5]; exact le_of_not_ge h4
    have right : e≤(cell5.hi:ℝ) := by norm_num [cell5];exact h5
    exact ⟨cell5,_,_,left,right,bulk5,valid5.1,valid5.2,real_disk_zero flatRight5 left right,real_disk_zero flatLeft5 left right⟩
  by_cases h6 : e≤4647/6400
  · have left : (cell6.lo:ℝ)≤e := by norm_num [cell6]; exact le_of_not_ge h5
    have right : e≤(cell6.hi:ℝ) := by norm_num [cell6];exact h6
    exact ⟨cell6,_,_,left,right,bulk6,valid6.1,valid6.2,real_disk_zero flatRight6 left right,real_disk_zero flatLeft6 left right⟩
  by_cases h7 : e≤50917/64000
  · have left : (cell7.lo:ℝ)≤e := by norm_num [cell7]; exact le_of_not_ge h6
    have right : e≤(cell7.hi:ℝ) := by norm_num [cell7];exact h7
    exact ⟨cell7,_,_,left,right,bulk7,valid7.1,valid7.2,real_disk_zero flatRight7 left right,real_disk_zero flatLeft7 left right⟩
  by_cases h8 : e≤13841/16000
  · have left : (cell8.lo:ℝ)≤e := by norm_num [cell8]; exact le_of_not_ge h7
    have right : e≤(cell8.hi:ℝ) := by norm_num [cell8];exact h8
    exact ⟨cell8,_,_,left,right,bulk8,valid8.1,valid8.2,real_disk_zero flatRight8 left right,real_disk_zero flatLeft8 left right⟩
  by_cases h9 : e≤59811/64000
  · have left : (cell9.lo:ℝ)≤e := by norm_num [cell9]; exact le_of_not_ge h8
    have right : e≤(cell9.hi:ℝ) := by norm_num [cell9];exact h9
    exact ⟨cell9,_,_,left,right,bulk9,valid9.1,valid9.2,real_disk_zero flatRight9 left right,real_disk_zero flatLeft9 left right⟩
  by_cases h10 : e≤32129/32000
  · have left : (cell10.lo:ℝ)≤e := by norm_num [cell10]; exact le_of_not_ge h9
    have right : e≤(cell10.hi:ℝ) := by norm_num [cell10];exact h10
    exact ⟨cell10,_,_,left,right,bulk10,valid10.1,valid10.2,real_disk_zero flatRight10 left right,real_disk_zero flatLeft10 left right⟩
  by_cases h11 : e≤132963/128000
  · have left : (cell11.lo:ℝ)≤e := by norm_num [cell11]; exact le_of_not_ge h10
    have right : e≤(cell11.hi:ℝ) := by norm_num [cell11];exact h11
    exact ⟨cell11,_,_,left,right,bulk11,valid11.1,valid11.2,real_disk_zero flatRight11 left right,real_disk_zero flatLeft11 left right⟩
  by_cases h12 : e≤13741/12800
  · have left : (cell12.lo:ℝ)≤e := by norm_num [cell12]; exact le_of_not_ge h11
    have right : e≤(cell12.hi:ℝ) := by norm_num [cell12];exact h12
    exact ⟨cell12,_,_,left,right,bulk12,valid12.1,valid12.2,real_disk_zero flatRight12 left right,real_disk_zero flatLeft12 left right⟩
  by_cases h13 : e≤279267/256000
  · have left : (cell13.lo:ℝ)≤e := by norm_num [cell13]; exact le_of_not_ge h12
    have right : e≤(cell13.hi:ℝ) := by norm_num [cell13];exact h13
    exact ⟨cell13,_,_,left,right,bulk13,valid13.1,valid13.2,real_disk_zero flatRight13 left right,real_disk_zero flatLeft13 left right⟩
  by_cases h14 : e≤141857/128000
  · have left : (cell14.lo:ℝ)≤e := by norm_num [cell14]; exact le_of_not_ge h13
    have right : e≤(cell14.hi:ℝ) := by norm_num [cell14];exact h14
    exact ⟨cell14,_,_,left,right,bulk14,valid14.1,valid14.2,real_disk_zero flatRight14 left right,real_disk_zero flatLeft14 left right⟩
  by_cases h15 : e≤288161/256000
  · have left : (cell15.lo:ℝ)≤e := by norm_num [cell15]; exact le_of_not_ge h14
    have right : e≤(cell15.hi:ℝ) := by norm_num [cell15];exact h15
    exact ⟨cell15,_,_,left,right,bulk15,valid15.1,valid15.2,real_disk_zero flatRight15 left right,real_disk_zero flatLeft15 left right⟩
  have left : (cell16.lo:ℝ)≤e := by norm_num [cell16]; exact le_of_not_ge h15
  have right : e≤(cell16.hi:ℝ) := by norm_num [cell16];exact hi
  exact ⟨cell16,_,_,left,right,bulk16,valid16.1,valid16.2,real_disk_zero flatRight16 left right,real_disk_zero flatLeft16 left right⟩

#print axioms bulk_cover
end OrderedPartitions.FourPole.Box
