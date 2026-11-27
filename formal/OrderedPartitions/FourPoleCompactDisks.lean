import OrderedPartitions.FourPoleDiskCell00
import OrderedPartitions.FourPoleDiskCell01
import OrderedPartitions.FourPoleDiskCell02
import OrderedPartitions.FourPoleDiskCell03
import OrderedPartitions.FourPoleDiskCell04
import OrderedPartitions.FourPoleDiskCell05
import OrderedPartitions.FourPoleDiskCell06
import OrderedPartitions.FourPoleDiskCell07
import OrderedPartitions.FourPoleDiskCell08
import OrderedPartitions.FourPoleDiskCell09
import OrderedPartitions.FourPoleDiskCell10
import OrderedPartitions.FourPoleDiskCell11
import OrderedPartitions.FourPoleDiskCell12
import OrderedPartitions.FourPoleDiskCell13
import OrderedPartitions.FourPoleDiskCell14
import OrderedPartitions.FourPoleDiskCell15
import OrderedPartitions.FourPoleDiskCell16

import OrderedPartitions.FourPoleDiskSemantic

namespace OrderedPartitions.FourPole.Box
/-- Physical zero in each disk, uniformly across seventeen closed cells. -/
theorem true_disk_catalogue {ε : ℝ} (lo : 1/32 ≤ ε) (hi : ε ≤ 1143/1000) :
    ∃ (c : Cell), (c.lo:ℝ) ≤ ε ∧ ε ≤ (c.hi:ℝ) ∧
      rightTest c.right ∧ leftTest c.left ∧
      (∃ z∈Metric.ball (center c.right) (c.right.r:ℝ), scaledG ε z=0) ∧
      (∃ v∈Metric.ball (center c.left) (c.left.r:ℝ), scaledG ε v=0) := by
  by_cases h0 : ε ≤ (8447/128000)
  · have lo : (cell0.lo:ℝ)≤ε := by norm_num [cell0]; exact lo
    have hi : ε≤(cell0.hi:ℝ) := by norm_num [cell0]; exact h0
    exact ⟨cell0,lo,hi,valid0.1,valid0.2,real_disk_zero flatRight0 lo hi,real_disk_zero flatLeft0 lo hi⟩
  by_cases h1 : ε ≤ (6447/64000)
  · have lo : (cell1.lo:ℝ)≤ε := by norm_num [cell1]; exact le_of_not_ge h0
    have hi : ε≤(cell1.hi:ℝ) := by norm_num [cell1]; exact h1
    exact ⟨cell1,lo,hi,valid1.1,valid1.2,real_disk_zero flatRight1 lo hi,real_disk_zero flatLeft1 lo hi⟩
  by_cases h2 : ε ≤ (5447/32000)
  · have lo : (cell2.lo:ℝ)≤ε := by norm_num [cell2]; exact le_of_not_ge h1
    have hi : ε≤(cell2.hi:ℝ) := by norm_num [cell2]; exact h2
    exact ⟨cell2,lo,hi,valid2.1,valid2.2,real_disk_zero flatRight2 lo hi,real_disk_zero flatLeft2 lo hi⟩
  by_cases h3 : ε ≤ (4947/16000)
  · have lo : (cell3.lo:ℝ)≤ε := by norm_num [cell3]; exact le_of_not_ge h2
    have hi : ε≤(cell3.hi:ℝ) := by norm_num [cell3]; exact h3
    exact ⟨cell3,lo,hi,valid3.1,valid3.2,real_disk_zero flatRight3 lo hi,real_disk_zero flatLeft3 lo hi⟩
  by_cases h4 : ε ≤ (14341/32000)
  · have lo : (cell4.lo:ℝ)≤ε := by norm_num [cell4]; exact le_of_not_ge h3
    have hi : ε≤(cell4.hi:ℝ) := by norm_num [cell4]; exact h4
    exact ⟨cell4,lo,hi,valid4.1,valid4.2,real_disk_zero flatRight4 lo hi,real_disk_zero flatLeft4 lo hi⟩
  by_cases h5 : ε ≤ (4697/8000)
  · have lo : (cell5.lo:ℝ)≤ε := by norm_num [cell5]; exact le_of_not_ge h4
    have hi : ε≤(cell5.hi:ℝ) := by norm_num [cell5]; exact h5
    exact ⟨cell5,lo,hi,valid5.1,valid5.2,real_disk_zero flatRight5 lo hi,real_disk_zero flatLeft5 lo hi⟩
  by_cases h6 : ε ≤ (4647/6400)
  · have lo : (cell6.lo:ℝ)≤ε := by norm_num [cell6]; exact le_of_not_ge h5
    have hi : ε≤(cell6.hi:ℝ) := by norm_num [cell6]; exact h6
    exact ⟨cell6,lo,hi,valid6.1,valid6.2,real_disk_zero flatRight6 lo hi,real_disk_zero flatLeft6 lo hi⟩
  by_cases h7 : ε ≤ (50917/64000)
  · have lo : (cell7.lo:ℝ)≤ε := by norm_num [cell7]; exact le_of_not_ge h6
    have hi : ε≤(cell7.hi:ℝ) := by norm_num [cell7]; exact h7
    exact ⟨cell7,lo,hi,valid7.1,valid7.2,real_disk_zero flatRight7 lo hi,real_disk_zero flatLeft7 lo hi⟩
  by_cases h8 : ε ≤ (13841/16000)
  · have lo : (cell8.lo:ℝ)≤ε := by norm_num [cell8]; exact le_of_not_ge h7
    have hi : ε≤(cell8.hi:ℝ) := by norm_num [cell8]; exact h8
    exact ⟨cell8,lo,hi,valid8.1,valid8.2,real_disk_zero flatRight8 lo hi,real_disk_zero flatLeft8 lo hi⟩
  by_cases h9 : ε ≤ (59811/64000)
  · have lo : (cell9.lo:ℝ)≤ε := by norm_num [cell9]; exact le_of_not_ge h8
    have hi : ε≤(cell9.hi:ℝ) := by norm_num [cell9]; exact h9
    exact ⟨cell9,lo,hi,valid9.1,valid9.2,real_disk_zero flatRight9 lo hi,real_disk_zero flatLeft9 lo hi⟩
  by_cases h10 : ε ≤ (32129/32000)
  · have lo : (cell10.lo:ℝ)≤ε := by norm_num [cell10]; exact le_of_not_ge h9
    have hi : ε≤(cell10.hi:ℝ) := by norm_num [cell10]; exact h10
    exact ⟨cell10,lo,hi,valid10.1,valid10.2,real_disk_zero flatRight10 lo hi,real_disk_zero flatLeft10 lo hi⟩
  by_cases h11 : ε ≤ (132963/128000)
  · have lo : (cell11.lo:ℝ)≤ε := by norm_num [cell11]; exact le_of_not_ge h10
    have hi : ε≤(cell11.hi:ℝ) := by norm_num [cell11]; exact h11
    exact ⟨cell11,lo,hi,valid11.1,valid11.2,real_disk_zero flatRight11 lo hi,real_disk_zero flatLeft11 lo hi⟩
  by_cases h12 : ε ≤ (13741/12800)
  · have lo : (cell12.lo:ℝ)≤ε := by norm_num [cell12]; exact le_of_not_ge h11
    have hi : ε≤(cell12.hi:ℝ) := by norm_num [cell12]; exact h12
    exact ⟨cell12,lo,hi,valid12.1,valid12.2,real_disk_zero flatRight12 lo hi,real_disk_zero flatLeft12 lo hi⟩
  by_cases h13 : ε ≤ (279267/256000)
  · have lo : (cell13.lo:ℝ)≤ε := by norm_num [cell13]; exact le_of_not_ge h12
    have hi : ε≤(cell13.hi:ℝ) := by norm_num [cell13]; exact h13
    exact ⟨cell13,lo,hi,valid13.1,valid13.2,real_disk_zero flatRight13 lo hi,real_disk_zero flatLeft13 lo hi⟩
  by_cases h14 : ε ≤ (141857/128000)
  · have lo : (cell14.lo:ℝ)≤ε := by norm_num [cell14]; exact le_of_not_ge h13
    have hi : ε≤(cell14.hi:ℝ) := by norm_num [cell14]; exact h14
    exact ⟨cell14,lo,hi,valid14.1,valid14.2,real_disk_zero flatRight14 lo hi,real_disk_zero flatLeft14 lo hi⟩
  by_cases h15 : ε ≤ (288161/256000)
  · have lo : (cell15.lo:ℝ)≤ε := by norm_num [cell15]; exact le_of_not_ge h14
    have hi : ε≤(cell15.hi:ℝ) := by norm_num [cell15]; exact h15
    exact ⟨cell15,lo,hi,valid15.1,valid15.2,real_disk_zero flatRight15 lo hi,real_disk_zero flatLeft15 lo hi⟩
  have lo : (cell16.lo:ℝ)≤ε := by norm_num [cell16]; exact le_of_not_ge h15
  have hi : ε≤(cell16.hi:ℝ) := by norm_num [cell16]; exact hi
  exact ⟨cell16,lo,hi,valid16.1,valid16.2,real_disk_zero flatRight16 lo hi,real_disk_zero flatLeft16 lo hi⟩
#print axioms true_disk_catalogue
end OrderedPartitions.FourPole.Box
