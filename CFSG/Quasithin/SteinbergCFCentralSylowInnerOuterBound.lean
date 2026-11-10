module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.Quasithin.SteinbergCF

open CFSG Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

variable {H : Type*} [Group H]

@[expose] noncomputable def conjCenterQuotientHom (L : Subgroup H) [L.Normal] :
    H →* MulAut (L ⧸ center L) :=
  (centerQuotientHom L).comp MulAut.conjNormal

theorem conjCenterQuotientHom_apply_mk (L : Subgroup H) [L.Normal] (g : H) (x : L) :
    conjCenterQuotientHom L g (QuotientGroup.mk' (center L) x) =
      QuotientGroup.mk' (center L) (MulAut.conjNormal g x) :=
  onCenterQuotient_apply_mk _ x

theorem center_eq_bot_of_simple {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hQ : ∃ a b : Q, a * b ≠ b * a) : center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hQ
    have ha : a ∈ center Q := h ▸ mem_top a
    exact absurd (mem_center_iff.mp ha b).symm hab

theorem conj_injective_of_center_eq_bot {Q : Type*} [Group Q] (hQ : center Q = ⊥) :
    Function.Injective (MulAut.conj : Q →* MulAut Q) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hmem : a ∈ center Q := mem_center_iff.mpr fun g => by
    have h := DFunLike.congr_fun ha g
    rw [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * a = a * g * a⁻¹ * a := by rw [h]
      _ = a * g := by group
  rw [hQ, mem_bot] at hmem
  exact hmem


end CFSG.Quasithin.SteinbergCF
