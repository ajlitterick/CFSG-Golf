module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicStandard17U
public import CFSG.LocalAnalysis.SectionRank.SectionAssembly

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J4

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic


@[expose] def J4NoDoubleCover : Prop :=
  CFSG.Monster.Schur.NoPerfectDoubleCover (Blueprint.NativeSporadic.Carrier .J4)

theorem isSporadic_J4_of_quot (hM : J4NoDoubleCover) {A : Type} [Group A] [Finite A]
    (hA : commutator A = ⊤)
    (e : A ⧸ center A ≃* Blueprint.NativeSporadic.Carrier .J4) :
    Blueprint.NativeSporadic.IsSporadic A .J4 := by
  have hodd : Odd (Nat.card (center A)) := oddMultiplier_of_noPerfectDoubleCover hM A hA ⟨e⟩
  have : Group.IsPerfect A := Group.isPerfect_def.mpr hA
  let π : A →* Blueprint.NativeSporadic.J4 := e.toMonoidHom.comp (QuotientGroup.mk' (center A))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = center A := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (center A) x) = 1 ↔ x ∈ center A
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hbot : π.ker = ⊥ :=
    CFSG.SectionRank.J4_perfect_odd_cover_trivial CFSG.SectionRank.j4OrderHyp π hπ hker.le
      (hker ▸ hodd)
  exact ⟨MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).mp hbot, hπ⟩⟩


end CFSG.ComponentClassification.RankTwoSporadic.J4
