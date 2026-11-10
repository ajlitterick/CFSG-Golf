module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KF.R8Final
public import CFSG.RankThree.PartOne.KFOUT3.KtyRow8
public import CFSG.RankThree.PartOne.S12.KFTransfer
public import CFSG.RankThree.PartOne.S13K.Pair134Embed
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)


@[expose] def KF1320L4' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (f : ℕ),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A → ¬ IsLThreeTypeAt p L →
    1 ≤ f → p ∣ 2 ^ f + 1 → StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f →
    Nonempty (reflectionGroup p E ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) →
      ∃ (r : ℕ) (F K₁ K₂ K₃ : Subgroup G), r.Prime ∧ r ∣ 2 ^ f - 1 ∧
        IsElementaryAbelian r F ∧ F ≤ lieGenerated p E ∧ K₁ ≤ lieGenerated p E ∧
        K₂ ≤ lieGenerated p E ∧ K₃ ≤ lieGenerated p E ∧
        K₁ ⊔ K₂ ⊔ K₃ = lieGenerated p E ∧
        StatedClassicalModel ↥K₁ .PSL 2 2 f ∧ StatedClassicalModel ↥K₂ .PSL 2 2 f ∧
        StatedClassicalModel ↥K₃ .PSL 2 2 (2 * f) ∧
        (K₁ ≤ Subgroup.centralizer (K₃ : Set G) ∧ K₁ ⊓ K₃ = ⊥) ∧
        CentrallyLThree f ↥(K₁ ⊔ K₂) ∧ StatedClassicalModel ↥(K₂ ⊔ K₃) .PSU 4 2 f ∧
        CTTorusCondition r F ![K₁, K₂, K₃] ∧ ¬ (F ⊓ K₂ ≤ Subgroup.centralizer (K₃ : Set G))

theorem q8_surj {K : Type} [Field K] [Finite K] [CharP K 2] : Function.Surjective (q8 K) :=
  (KFOUT3.m8Iso (K := K)).surjective

theorem prime_ne_two_of_dvd_two_pow_sub_one {r f : ℕ} (hf1 : 1 ≤ f) (hrf : r ∣ 2 ^ f - 1) :
    r ≠ 2 := by
  rintro rfl
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have : Odd (2 ^ f - 1) :=
    Nat.Even.sub_odd hq1 (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  exact (Nat.not_even_iff_odd.2 this) (even_iff_two_dvd.2 hrf)


end CFSG.RankThree.PartOne.K1320
