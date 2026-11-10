module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowGeometry

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.NormalGraph

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.InvolutionFusion

variable {G : Type*} [Group G]

theorem no_central_vertex (D : Set G) (horder : ∀ x ∈ D, orderOf x = 2)
    (hdisconnected : ¬ (graph D horder).Preconnected) {z : G} (hz : z ∈ D) :
    z ∉ Subgroup.center G := by
  intro hcentral
  apply hdisconnected
  intro x y
  have hxz : Commute (x : G) z := Subgroup.mem_center_iff.mp hcentral x
  have hyz : Commute (y : G) z := Subgroup.mem_center_iff.mp hcentral y
  exact (reachable_of_commute D horder x ⟨z, hz⟩ hxz).trans
    (reachable_of_commute D horder y ⟨z, hz⟩ hyz).symm

theorem commute_of_involution_product_central {x y : G} (hx : orderOf x = 2)
    (hy : orderOf y = 2) (hcentral : x * y ∈ Subgroup.center G) : Commute x y := by
  let first : Involution G := ⟨x, hx⟩
  let second : Involution G := ⟨y, hy⟩
  have hfix : (MulAut.conj x) (x * y) = x * y := by
    apply (conj_eq_iff_centralizer x (x * y)).mpr
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hcentral x)
  have hflip := product_conjugate_inv first second
  change (MulAut.conj x) (x * y) = (x * y)⁻¹ at hflip
  have heq : x * y = (x * y)⁻¹ := hfix.symm.trans hflip
  change x * y = y * x
  simpa only [mul_inv_rev, inv_eq_self_of_orderOf_eq_two hx,
    inv_eq_self_of_orderOf_eq_two hy] using heq

theorem quotient_injective_on_vertices (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) :
    Set.InjOn (QuotientGroup.mk' Z) D := by
  intro x hx y hy heq
  have hxinv : x⁻¹ = x := inv_eq_self_of_orderOf_eq_two (horder x hx)
  have hxyZ : x * y ∈ Z := by
    have h := QuotientGroup.eq.mp heq
    rwa [hxinv] at h
  by_contra hne
  have hcomm := commute_of_involution_product_central (horder x hx) (horder y hy) (hZ hxyZ)
  exact no_central_vertex D horder hdisconnected (hproduct x hx y hy hne hcomm) (hZ hxyZ)

theorem quotient_vertices_order_two (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hdisconnected : ¬ (graph D horder).Preconnected)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) :
    ∀ q ∈ (QuotientGroup.mk' Z) '' D, orderOf q = 2 := by
  rintro _ ⟨x, hx, rfl⟩
  apply orderOf_eq_prime_iff.mpr
  refine ⟨?_, ?_⟩
  · have hxpow := pow_orderOf_eq_one x
    rw [horder x hx] at hxpow
    simpa only [map_pow, map_one] using congrArg (QuotientGroup.mk' Z) hxpow
  · intro hone
    exact no_central_vertex D horder hdisconnected hx
      (hZ ((QuotientGroup.eq_one_iff x).mp hone))


end CFSG.ShultStronglyClosedTI.NormalGraph
