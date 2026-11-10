module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PerfectCover.HopfFormula
import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.Assembly.RankThreeEven CFSG.RankThree.PerfectCover

@[expose] def L34CenterThreePrimeTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
    Nonempty (X ⧸ Subgroup.center X ≃* projSL 3 (GaloisField 2 2)) →
    ∀ Z : Subgroup X, Z ≤ Subgroup.center X → ¬ 3 ∣ Nat.card Z → IsPGroup 2 Z

namespace KS44

theorem card_center_dvd_card_hopfMultiplier {X : Type} [Group X] [Finite X]
    (hX : IsQuasisimple X) :
    Nat.card (Subgroup.center X) ∣ Nat.card (hopfMultiplier (X ⧸ Subgroup.center X)) := by
  have : Group.IsPerfect X := hX.1
  have hker : (QuotientGroup.mk' (Subgroup.center X)).ker ≤ Subgroup.center X :=
    (QuotientGroup.ker_mk' _).le
  obtain ⟨-, ⟨h, -, -, -, -, ⟨e', -⟩⟩, -, -⟩ :=
    perfect_central_kernel_quotient_of_schur_multiplier (QuotientGroup.mk' (Subgroup.center X))
      (QuotientGroup.mk'_surjective _) hker
  have hdvd : Nat.card (QuotientGroup.mk' (Subgroup.center X)).ker ∣
      Nat.card (hopfMultiplier (X ⧸ Subgroup.center X)) := by
    rw [← Nat.card_congr e'.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  rwa [QuotientGroup.ker_mk'] at hdvd

theorem isPGroup_two_of_le_center {X : Type} [Group X] [Finite X]
    (h48 : Nat.card (Subgroup.center X) ∣ 48) {Z : Subgroup X} (hZ : Z ≤ Subgroup.center X)
    (h3 : ¬ 3 ∣ Nat.card Z) : IsPGroup 2 Z := by
  have hdvd : Nat.card Z ∣ 2 ^ 4 * 3 := (Subgroup.card_dvd_of_le hZ).trans h48
  have hcop : Nat.Coprime (Nat.card Z) 3 :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))
  have h16 : Nat.card Z ∣ 2 ^ 4 := hcop.dvd_of_dvd_mul_right hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h16
  exact IsPGroup.of_card hk

noncomputable def projSLEquivStatedProj (K : Type) [Field K] :
    projSL 3 K ≃* Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSL 3 K) :=
  CFSG.PGLModel.projSLEquivStatedProj 3 K

theorem lieModel_of_mulEquiv_projSL {S : Type} [Group S]
    (e : S ≃* projSL 3 (GaloisField 2 2)) : CFSG.Models.LieModel S .PSL 3 2 2 := by
  have hadm : Assembly.LowTwoRank.StatedLieAdmissible .PSL 3 2 2 :=
    ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩
  refine ⟨hadm, Or.inl ⟨hadm, GaloisField 2 2, inferInstance, inferInstance, ?_,
    ⟨e.trans (projSLEquivStatedProj _)⟩⟩⟩
  rw [L34.card_galoisField_two_two]
  norm_num


end KS44

end CFSG.RankThree.PartTwo.KFacts
