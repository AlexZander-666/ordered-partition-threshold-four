import OrderedPartitions.FourPoleJet00
import OrderedPartitions.FourPoleJet01
import OrderedPartitions.FourPoleJet02
import OrderedPartitions.FourPoleJet03
import OrderedPartitions.FourPoleJet04
import OrderedPartitions.FourPoleJet05
import OrderedPartitions.FourPoleJet06
import OrderedPartitions.FourPoleJet07
import OrderedPartitions.FourPoleJet08
import OrderedPartitions.FourPoleJet09
import OrderedPartitions.FourPoleJet10
import OrderedPartitions.FourPoleJet11
import OrderedPartitions.FourPoleJet12
import OrderedPartitions.FourPoleJet13
import OrderedPartitions.FourPoleJet14
import OrderedPartitions.FourPoleJet15
import OrderedPartitions.FourPoleJet16

namespace OrderedPartitions.FourPole.Box
/-- Both disc tests, the certified rational midpoint jets and budgets, and
coverage of every real epsilon in the closed compact range. -/
theorem certified_catalogue {ε : ℝ} (lo : 1/32 ≤ ε) (hi : ε ≤ 1143/1000) :
    ∃ (c : Cell) (r l : Witness), (c.lo:ℝ) ≤ ε ∧ ε ≤ (c.hi:ℝ) ∧
      rightTest c.right ∧ leftTest c.left ∧ verifiedJet c c.right r ∧ verifiedJet c c.left l := by
  by_cases h0 : ε ≤ (8447/128000)
  · exact ⟨cell0,_,_,by norm_num [cell0]; exact lo,by norm_num [cell0]; exact h0,valid0.1,valid0.2,rightJets0,leftJets0⟩
  by_cases h1 : ε ≤ (6447/64000)
  · exact ⟨cell1,_,_,by norm_num [cell1]; exact le_of_not_ge h0,by norm_num [cell1]; exact h1,valid1.1,valid1.2,rightJets1,leftJets1⟩
  by_cases h2 : ε ≤ (5447/32000)
  · exact ⟨cell2,_,_,by norm_num [cell2]; exact le_of_not_ge h1,by norm_num [cell2]; exact h2,valid2.1,valid2.2,rightJets2,leftJets2⟩
  by_cases h3 : ε ≤ (4947/16000)
  · exact ⟨cell3,_,_,by norm_num [cell3]; exact le_of_not_ge h2,by norm_num [cell3]; exact h3,valid3.1,valid3.2,rightJets3,leftJets3⟩
  by_cases h4 : ε ≤ (14341/32000)
  · exact ⟨cell4,_,_,by norm_num [cell4]; exact le_of_not_ge h3,by norm_num [cell4]; exact h4,valid4.1,valid4.2,rightJets4,leftJets4⟩
  by_cases h5 : ε ≤ (4697/8000)
  · exact ⟨cell5,_,_,by norm_num [cell5]; exact le_of_not_ge h4,by norm_num [cell5]; exact h5,valid5.1,valid5.2,rightJets5,leftJets5⟩
  by_cases h6 : ε ≤ (4647/6400)
  · exact ⟨cell6,_,_,by norm_num [cell6]; exact le_of_not_ge h5,by norm_num [cell6]; exact h6,valid6.1,valid6.2,rightJets6,leftJets6⟩
  by_cases h7 : ε ≤ (50917/64000)
  · exact ⟨cell7,_,_,by norm_num [cell7]; exact le_of_not_ge h6,by norm_num [cell7]; exact h7,valid7.1,valid7.2,rightJets7,leftJets7⟩
  by_cases h8 : ε ≤ (13841/16000)
  · exact ⟨cell8,_,_,by norm_num [cell8]; exact le_of_not_ge h7,by norm_num [cell8]; exact h8,valid8.1,valid8.2,rightJets8,leftJets8⟩
  by_cases h9 : ε ≤ (59811/64000)
  · exact ⟨cell9,_,_,by norm_num [cell9]; exact le_of_not_ge h8,by norm_num [cell9]; exact h9,valid9.1,valid9.2,rightJets9,leftJets9⟩
  by_cases h10 : ε ≤ (32129/32000)
  · exact ⟨cell10,_,_,by norm_num [cell10]; exact le_of_not_ge h9,by norm_num [cell10]; exact h10,valid10.1,valid10.2,rightJets10,leftJets10⟩
  by_cases h11 : ε ≤ (132963/128000)
  · exact ⟨cell11,_,_,by norm_num [cell11]; exact le_of_not_ge h10,by norm_num [cell11]; exact h11,valid11.1,valid11.2,rightJets11,leftJets11⟩
  by_cases h12 : ε ≤ (13741/12800)
  · exact ⟨cell12,_,_,by norm_num [cell12]; exact le_of_not_ge h11,by norm_num [cell12]; exact h12,valid12.1,valid12.2,rightJets12,leftJets12⟩
  by_cases h13 : ε ≤ (279267/256000)
  · exact ⟨cell13,_,_,by norm_num [cell13]; exact le_of_not_ge h12,by norm_num [cell13]; exact h13,valid13.1,valid13.2,rightJets13,leftJets13⟩
  by_cases h14 : ε ≤ (141857/128000)
  · exact ⟨cell14,_,_,by norm_num [cell14]; exact le_of_not_ge h13,by norm_num [cell14]; exact h14,valid14.1,valid14.2,rightJets14,leftJets14⟩
  by_cases h15 : ε ≤ (288161/256000)
  · exact ⟨cell15,_,_,by norm_num [cell15]; exact le_of_not_ge h14,by norm_num [cell15]; exact h15,valid15.1,valid15.2,rightJets15,leftJets15⟩
  exact ⟨cell16,_,_,by norm_num [cell16]; exact le_of_not_ge h15,by norm_num [cell16]; exact hi,valid16.1,valid16.2,rightJets16,leftJets16⟩
#print axioms certified_catalogue
end OrderedPartitions.FourPole.Box
