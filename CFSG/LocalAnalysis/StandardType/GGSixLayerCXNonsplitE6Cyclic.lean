module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4Dvd
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Arith
public import CFSG.RankThree.PartOne.KE.CTCasesE6Eight
public import CFSG.RankThree.PartOne.KE.CTCasesE6Nine
public import CFSG.RankThree.PartOne.KE.CTCasesE6Twelve

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE

namespace E6Nonsplit

section Regular


theorem not_isComponentOf_centralizer_of_dvd_phi_regular {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {m : ℕ} (hm : m = 8 ∨ m = 9 ∨ m = 12)
    (hpm : (p : ℤ) ∣ (exhaustionPhi m).eval (Nat.card K : ℤ))
    {a : ↥(adjointGroup .E6 K)} (ha : orderOf a = p) {X : Subgroup ↥(adjointGroup .E6 K)} :
    ¬ IsComponentOf X (Subgroup.centralizer ({a} : Set ↥(adjointGroup .E6 K))) := by
  rcases hm with rfl | rfl | rfl
  · obtain ⟨-, -, T, hT, -, -, -, -, -, hcent⟩ :=
      E6_eight_cyclic_sylow cyclic_torus_prime_centralizers K hp hp3 hpm
    obtain ⟨g, -, hg⟩ := hcent a ha
    exact F4Nonsplit.not_isComponentOf_of_conj_centralizer_cyclic hT hg
  · obtain ⟨-, -, T, hT, -, -, -, -, -, hcent⟩ :=
      E6_nine_cyclic_sylow cyclic_torus_prime_centralizers K hp hp3 hpm
    obtain ⟨g, -, hg⟩ := hcent a ha
    exact F4Nonsplit.not_isComponentOf_of_conj_centralizer_cyclic hT hg
  · obtain ⟨-, -, T, hT, -, -, -, -, -, hcent⟩ :=
      E6_twelve_cyclic_sylow cyclic_torus_prime_centralizers K hp hp3 hpm
    obtain ⟨g, -, hg⟩ := hcent a ha
    exact F4Nonsplit.not_isComponentOf_of_conj_centralizer_cyclic hT hg

end Regular

end E6Nonsplit

end CFSG.StandardType
