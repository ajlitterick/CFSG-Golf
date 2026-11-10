module

public import CFSG.ClassicalInvolution.Generic.Generation.Defs

public section

namespace CFSG.ClassicalInvolution.Generic

variable {F : Type*} [Field F] {G : Type*} [Group G]

theorem mul_comm_of_sq_eq_one {E : Subgroup G} (hE : ∀ x ∈ E, x * x = 1) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x := by
  have h1 : (x * y) * (x * y) = 1 := hE _ (E.mul_mem hx hy)
  have h2 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h1
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hE x hx),
    inv_eq_of_mul_eq_one_right (hE y hy)] at h2
  exact h2.symm


namespace ToralFrame

variable {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}


end ToralFrame

variable (Ω : Set (Subgroup G)) (E : Subgroup G)

@[expose] def ToralIndependence : Prop :=
  ∀ V : Subgroup G, V ≤ E → ∀ v ∈ V, ∀ w ∈ V, v ≠ 1 → w ≠ 1 → v ≠ w →
    ∀ x ∈ E, x ≠ 1 → centLayer Ω x ≤ centSpan Ω V


variable {Ω E} {S : Set (Subgroup G)}


theorem ToralIndependence.centSpan_eq (h : ToralIndependence Ω E) {V : Subgroup G} (hV : V ≤ E)
    {v w : G} (hv : v ∈ V) (hw : w ∈ V) (hv1 : v ≠ 1) (hw1 : w ≠ 1) (hvw : v ≠ w) :
    centSpan Ω V = centSpan Ω E :=
  le_antisymm (centSpan_mono hV) <|
    centSpan_le fun _ hx hx1 => h V hV v hv w hw hv1 hw1 hvw _ hx hx1

theorem ToralIndependence.normalizer_le (h : ToralIndependence Ω E) (hΩ : ConjInvariant Ω)
    {V : Subgroup G} (hV : V ≤ E) {v w : G} (hv : v ∈ V) (hw : w ∈ V) (hv1 : v ≠ 1)
    (hw1 : w ≠ 1) (hvw : v ≠ w) :
    Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (centSpan Ω E : Set G) := by
  have := normalizer_le_normalizer_centSpan hΩ V
  rwa [h.centSpan_eq hV hv hw hv1 hw1 hvw] at this


end CFSG.ClassicalInvolution.Generic
