module

public import CFSG.Quasithin.Background.A1cA133Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LinearGroups
open scoped MatrixGroups commutatorElement

namespace A1c

section Prelim


theorem matrix_eq_one_or_neg_one_of_sq_eq_one {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {M : Matrix (Fin 2) (Fin 2) F} (hM : M * M = 1) (hdet : M.det = 1) : M = 1 ∨ M = -1 := by
  by_contra hcon
  push Not at hcon
  have h3 := det_eq_neg_one_of_sq_eq_one hM hcon.1 hcon.2
  rw [hdet] at h3
  apply h2
  linear_combination h3


theorem neg_one_ne_one_GL_three : (-1 : GL (Fin 2) (ZMod 3)) ≠ 1 := by
  intro h
  have := congrArg (fun g : GL (Fin 2) (ZMod 3) => ((g : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0)) h
  simp at this
  revert this
  decide

end Prelim

section ActGL

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [Group L] [Finite L]

theorem exists_actGL {P : Subgroup L} [P.Normal] (hP : IsPOnePlusTwo p ↥P) :
    ∃ Θ : L →* GL (Fin 2) (ZMod p),
      (∀ g, Θ g = 1 ↔ ∀ y ∈ P, g * y * g⁻¹ * y⁻¹ ∈ centerOf P) ∧
      (∀ g, Θ g = -1 ↔ ∀ y ∈ P, g * y * g⁻¹ * y ∈ centerOf P) := by
  classical
  obtain ⟨hext, hPcard, hPexp⟩ := hP
  have := hext
  have hVel : CFSG.IsElementaryAbelian p (↥P ⧸ Subgroup.center ↥P) :=
    CFSG.IsExtraspecial.quotient_elementary_abelian p ↥P
  have hVcomm : ∀ a b : ↥P ⧸ Subgroup.center ↥P, a * b = b * a := fun a b => mul_comm' a b
  have hVpow : ∀ a : ↥P ⧸ Subgroup.center ↥P, a ^ p = 1 := fun a =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (CFSG.IsElementaryAbelian.exponent_dvd_p p _) a
  have hVcard : Nat.card (↥P ⧸ Subgroup.center ↥P) = p ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥P)
    rw [hPcard, CFSG.IsExtraspecial.center_order_p p ↥P] at h1
    have h3 : p ^ 3 = p ^ 2 * p := by ring
    exact (Nat.eq_of_mul_eq_mul_right hp.out.pos (h3.symm.trans h1)).symm
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := p) hVcomm hVpow hVcard
  let ε := CFSG.SectionRank.Ccomm.elemAutEquivGL e
  refine ⟨ε.toMonoidHom.comp (actV P), fun g => ?_, fun g => ?_⟩
  · rw [← actV_eq_one_iff]
    show ε (actV P g) = 1 ↔ _
    rw [← map_one ε]
    exact ε.injective.eq_iff
  · rw [← actV_eq_inv_iff]
    exact CFSG.SectionRank.Ccomm.elemAutEquivGL_eq_neg_one_iff e (actV P g)


end ActGL

end A1c

open A1c

section Main3


end Main3

end CFSG.Quasithin
