module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront78Nar
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Core
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ElementaryCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F07

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def R77E2 (D : Data G) : Prop :=
  D.sig ⊆ D.sig1 → ∀ p ∈ D.sig, p ≠ 2 → CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M →
    ∀ r : ℕ, r.Prime → r ≠ 2 → r ∉ D.sig →
      ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian r E → Nat.card E = r ^ 2 →
        2 < CFSG.Open.pRank p (D.M ⊓ normalizer (E : Set G)) → rankThreeGamma 1 r E ≤ D.M


@[expose] def R77Use (D : Data G) : Prop :=
  R77E2 D ∧ R77E4 D


end CFSG.LocalAnalysis.UniquenessCase.UC22.F07

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem five_le_of_mem_uniqueFourSigma {M : Subgroup G} {p : ℕ} (hp : p ∈ uniqueFourSigma M)
    (h3 : 3 ∉ uniqueFourBeta G) : 5 ≤ p := by
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact h3 hp.1
  exact Nat.Prime.five_le_of_ne_two_of_ne_three hp.1.1 hp.1.2.1 hp3

@[expose] def Sec7Core4.ofSetup4Any (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    {p : ℕ} (hp : p ∈ uniqueFourSigma S.M) (hsp : IsStronglyPEmbedded p S.M) : Sec7Core4 G :=
  Sec7Core4.ofUnique hS hU S.M S.maxLocal p hp hsp

@[expose] def Sec7Core4.ofSetup4 (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    {p : ℕ} (hp : p ∈ uniqueFourSigma S.M) (hsp : IsStronglyPEmbedded p S.M)
    (h3 : 3 ∉ uniqueFourBeta G) : Sec7Core4 G :=
  Sec7Core4.ofSetup4Any hS hU S hp hsp

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (Conclusion76 StronglyEmbeddedFive Sec7Core4 five_le_of_mem_uniqueFourSigma)

variable {G : Type} [Group G] [Finite G]

theorem conclusion76_dataOfSetup4 (hSE : StronglyEmbeddedFive) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (h3 : 3 ∉ uniqueFourBeta G) {p : ℕ}
    (hp : p ∈ (dataOfSetup4 hS hU S).sig)
    (hsp : IsStronglyPEmbedded p (dataOfSetup4 hS hU S).M) :
    Conclusion76 (dataOfSetup4 hS hU S).M p :=
  (Sec7Core4.ofSetup4 hS hU S hp hsp h3).conclusion76 (five_le_of_mem_uniqueFourSigma hp h3) h3 hSE

theorem conclusion76_dataOfSetup4_of_k_eq_two (hSE : StronglyEmbeddedFive) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma)
    (h3k : S.InMSigma → (dataOfSetup4 hS hU S).k = 2 → 3 ∉ uniqueFourBeta G)
    (hk : (dataOfSetup4 hS hU S).k = 2) {p : ℕ} (hp : p ∈ (dataOfSetup4 hS hU S).sig)
    (hsp : IsStronglyPEmbedded p (dataOfSetup4 hS hU S).M) :
    Conclusion76 (dataOfSetup4 hS hU S).M p :=
  conclusion76_dataOfSetup4 hSE hS hU S (h3k hσ hk) hp hsp

end CFSG.LocalAnalysis.UniquenessCase.UC6
