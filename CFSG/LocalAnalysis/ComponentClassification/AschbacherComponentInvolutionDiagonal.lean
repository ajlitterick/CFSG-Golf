module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentActionFourData
public import CFSG.LocalAnalysis.ComponentClassification.SwappedQuasisimpleProduct

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherComponentInvolution

open CFSG.Open
open AschbacherComponentAction

variable {G : Type*} [Group G]

theorem fixed_conjugation_eq_centralizer (a : G) :
    FixedCommutingProduct.fixedSubgroup (MulAut.conj a) =
      Subgroup.centralizer ({a} : Set G) := by
  ext x
  change a * x * a⁻¹ = x ↔ x ∈ Subgroup.centralizer ({a} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  · intro h
    rw [← h, mul_inv_cancel_right]


variable [Finite G]

theorem moved_component_derived_centralizer (L : Subgroup G) (a : G)
    (hL : IsComponentOf L ⊤) (ha : orderOf a = 2)
    (hmoved : rightComponent L a ≠ L)
    (hcommutes : ⁅L, L.map (MulAut.conj a).toMonoidHom⁆ = ⊥) :
    ⁅⁅L, Subgroup.zpowers a⁆ ⊓ Subgroup.centralizer ({a} : Set G),
      ⁅L, Subgroup.zpowers a⁆ ⊓ Subgroup.centralizer ({a} : Set G)⁆ =
        (InvolutionDiagonal.homomorphism L (MulAut.conj a) hcommutes).range := by
  have hsquare : a * a = 1 := by
    have hpower := pow_orderOf_eq_one a
    rwa [ha, pow_two] at hpower
  have hinvolutive : Function.Involutive (MulAut.conj a) := by
    intro x
    exact involution_conjugation_twice a x hsquare
  rw [moved_component_commutator L a hL hsquare hmoved,
    rightComponent_involution L a hsquare, ← fixed_conjugation_eq_centralizer a]
  exact SwappedQuasisimpleProduct.derived_product_fixed_eq_diagonal L hL.2.2
    (MulAut.conj a) hinvolutive hcommutes


end CFSG.ComponentClassification.AschbacherComponentInvolution
