module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBA5Vertex

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

namespace DSBJZ2

variable {G : Type} [Group G]

theorem omega_le_of_inv {X K : Subgroup G} (h : ∀ x ∈ X, x ^ 2 = 1 → x ∈ K) :
    dsOmega1 X ≤ K := by
  unfold dsOmega1
  exact (Subgroup.closure_le K).2 fun _ hx => h _ hx.1 hx.2

theorem mem_omega_of {X : Subgroup G} {x : G} (hx : x ∈ X) (hx2 : x ^ 2 = 1) :
    x ∈ dsOmega1 X := by
  unfold dsOmega1
  exact Subgroup.subset_closure ⟨hx, hx2⟩


theorem omega_centerOf_le (X : Subgroup G) : dsOmega1 (centerOf X) ≤ centerOf X :=
  omega_le_of_inv fun _ hx _ => hx

theorem le_normalizer_of_conj {H X : Subgroup G}
    (h : ∀ g ∈ H, ∀ x ∈ X, g * x * g⁻¹ ∈ X) : H ≤ Subgroup.normalizer (X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  have := h g⁻¹ (H.inv_mem hg) (g * x * g⁻¹) hx
  simpa [mul_assoc] using this


theorem dsConjClosure_le' {Y X K : Subgroup G} (h : ∀ y ∈ Y, ∀ z ∈ X, y * z * y⁻¹ ∈ K) :
    dsConjClosure Y X ≤ K := by
  unfold dsConjClosure
  refine iSup₂_le fun y hy => ?_
  rintro _ ⟨z, hz, rfl⟩
  exact h y hy z hz

theorem conj_mem_dsConjClosure {Y X : Subgroup G} {y z : G} (hy : y ∈ Y) (hz : z ∈ X) :
    y * z * y⁻¹ ∈ dsConjClosure Y X := by
  have hmem : y * z * y⁻¹ ∈ X.map (MulAut.conj y).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  have hle : X.map (MulAut.conj y).toMonoidHom ≤ dsConjClosure Y X :=
    le_iSup₂ (f := fun w (_ : w ∈ Y) => X.map (MulAut.conj w).toMonoidHom) y hy
  exact hle hmem


end DSBJZ2


end CFSG.GH74.QTGen4.DSGen4
