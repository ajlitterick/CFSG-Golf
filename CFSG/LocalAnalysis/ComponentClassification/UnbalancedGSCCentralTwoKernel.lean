module

public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFourGroup
public import CFSG.LocalAnalysis.LyonsUnitaryFour.CentralHall
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.ComponentClassification.UnbalancedGS

namespace CentralTwoActionKernel

open Subgroup
open scoped commutatorElement

section General

variable {G : Type*} [Group G]

instance oddCore_characteristic : (oddCore G).Characteristic := by
  rw [oddCore_eq_piCore]
  infer_instance

@[expose] noncomputable def descendHom (N : Subgroup G) [N.Characteristic] :
    MulAut G →* MulAut (G ⧸ N) where
  toFun φ := QuotientGroup.congr N N φ ((Subgroup.characteristic_iff_map_eq.mp inferInstance) φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl


end General

variable {H : Type*} [Group H] (E : Subgroup H) [E.Normal]

abbrev OddQuot := ↥E ⧸ oddCore ↥E

abbrev OddQuotT := OddQuot E ⧸ center (OddQuot E)

@[expose] noncomputable def actA : H →* MulAut (OddQuot E) :=
  (descendHom (oddCore E)).comp MulAut.conjNormal

@[expose] noncomputable def betaHom : H →* MulAut (OddQuotT E) :=
  (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom (OddQuot E)).comp (actA E)


abbrev oddCoreIn : Subgroup H := (oddCore E).map E.subtype

instance oddCoreIn_normal : (oddCoreIn E).Normal :=
  ConjAct.normal_of_characteristic_of_normal


omit [E.Normal] in
theorem oddCoreIn_le : oddCoreIn E ≤ E := map_subtype_le _


theorem card_sup_mul_card_inf_of_commute [Finite H] (L R : Subgroup H)
    (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup H) * Nat.card (L ⊓ R : Subgroup H) = Nat.card L * Nat.card R := by
  let μ : L × R →* H := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : H) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup H) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : H), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : H)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  rw [mul_comm]
  exact this


theorem conj_eq_one_iff_mem_center {G : Type*} [Group G] (g : G) :
    MulAut.conj g = 1 ↔ g ∈ center G := by
  constructor
  · intro h
    refine mem_center_iff.mpr fun z => ?_
    have h2 := congrArg (fun φ : MulAut G => φ z) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc z * g = g * z * g⁻¹ * g := by rw [h2]
      _ = g * z := by group
  · intro h
    refine MulEquiv.ext fun z => ?_
    rw [MulAut.conj_apply, MulAut.one_apply, ← mem_center_iff.mp h z, mul_inv_cancel_right]


end CentralTwoActionKernel

open Subgroup CentralTwoActionKernel
open scoped commutatorElement


end CFSG.ComponentClassification.UnbalancedGS
