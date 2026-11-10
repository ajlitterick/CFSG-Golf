module

public import Mathlib.LinearAlgebra.BilinearForm.Properties

public noncomputable section

namespace CFSG.Certificates

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def glPullback (g : LinearMap.GeneralLinearGroup K V) (q : V → K) : V → K :=
  q ∘ ⇑((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)

theorem glPullback_apply (g : LinearMap.GeneralLinearGroup K V) (q : V → K) (u : V) :
    glPullback g q u = q (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) u) := rfl

theorem gl_apply_inv_apply (g : LinearMap.GeneralLinearGroup K V) (u : V) :
    (g : V →ₗ[K] V) (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) u) = u := by
  change ((g * g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) u = u
  rw [mul_inv_cancel]
  rfl

theorem gl_inv_apply_apply (g : LinearMap.GeneralLinearGroup K V) (u : V) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) ((g : V →ₗ[K] V) u) = u := by
  change ((g⁻¹ * g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) u = u
  rw [inv_mul_cancel]
  rfl

theorem glPullback_one (q : V → K) : glPullback 1 q = q := by
  funext u
  rw [glPullback_apply, inv_one]
  rfl

theorem glPullback_mul (g h : LinearMap.GeneralLinearGroup K V) (q : V → K) :
    glPullback (g * h) q = glPullback g (glPullback h q) := by
  funext u
  rw [glPullback_apply, glPullback_apply, glPullback_apply, mul_inv_rev]
  rfl

theorem glPullback_eq_self_iff (g : LinearMap.GeneralLinearGroup K V) (q : V → K) :
    glPullback g q = q ↔ ∀ u, q ((g : V →ₗ[K] V) u) = q u := by
  constructor
  · intro h u
    have := congrFun h ((g : V →ₗ[K] V) u)
    rwa [glPullback_apply, gl_inv_apply_apply, eq_comm] at this
  · intro h
    funext u
    rw [glPullback_apply, ← h, gl_apply_inv_apply]

@[expose] def pullbackPerm (G : Subgroup (LinearMap.GeneralLinearGroup K V)) (X : Set (V → K))
    (hX : ∀ g ∈ G, ∀ q ∈ X, glPullback g q ∈ X) : G →* Equiv.Perm X where
  toFun g :=
    { toFun := fun q => ⟨glPullback g q, hX g g.2 q q.2⟩
      invFun := fun q => ⟨glPullback (g : LinearMap.GeneralLinearGroup K V)⁻¹ q,
        hX _ (G.inv_mem g.2) q q.2⟩
      left_inv := fun q => Subtype.ext (by
        change glPullback _ (glPullback _ _) = _
        rw [← glPullback_mul, inv_mul_cancel, glPullback_one])
      right_inv := fun q => Subtype.ext (by
        change glPullback _ (glPullback _ _) = _
        rw [← glPullback_mul, mul_inv_cancel, glPullback_one]) }
  map_one' := Equiv.ext fun q => Subtype.ext (glPullback_one q.1)
  map_mul' g h := Equiv.ext fun q => Subtype.ext (glPullback_mul g h q.1)

theorem pullbackPerm_apply (G : Subgroup (LinearMap.GeneralLinearGroup K V)) (X : Set (V → K))
    (hX : ∀ g ∈ G, ∀ q ∈ X, glPullback g q ∈ X) (g : G) (q : X) :
    (pullbackPerm G X hX g q : V → K) = glPullback g q := rfl


theorem commute_polarOperator_of_pullback {B : LinearMap.BilinForm K V} (hB : B.Nondegenerate)
    {g : LinearMap.GeneralLinearGroup K V}
    (hgB : ∀ u w, B ((g : V →ₗ[K] V) u) ((g : V →ₗ[K] V) w) = B u w)
    {q : V → K} {β : LinearMap.BilinForm K V} (hβ : ∀ u w, β u w = q (u + w) - q u - q w)
    {T : Module.End K V} (hT : ∀ u w, B u (T w) = β u w) (hq : glPullback g q = q) :
    T * (g : V →ₗ[K] V) = (g : V →ₗ[K] V) * T := by
  have hq' := (glPullback_eq_self_iff g q).1 hq
  have hβg : ∀ u w, β ((g : V →ₗ[K] V) u) ((g : V →ₗ[K] V) w) = β u w := by
    intro u w
    rw [hβ, hβ, ← map_add, hq', hq', hq']
  apply LinearMap.ext
  intro w
  apply sub_eq_zero.1
  apply hB.2
  intro x
  rw [← gl_apply_inv_apply g x, map_sub, Module.End.mul_apply, Module.End.mul_apply, hT, hgB, hT,
    hβg, sub_self]

theorem eq_smul_id_of_pullback_eq {B : LinearMap.BilinForm K V} (hB : B.Nondegenerate)
    {g : LinearMap.GeneralLinearGroup K V}
    (hgB : ∀ u w, B ((g : V →ₗ[K] V) u) ((g : V →ₗ[K] V) w) = B u w) {ι : Type*}
    {q : ι → V → K} {β : ι → LinearMap.BilinForm K V}
    (hβ : ∀ i u w, β i u w = q i (u + w) - q i u - q i w) {T : ι → Module.End K V}
    (hT : ∀ i u w, B u (T i w) = β i u w)
    (hcent : {S : Module.End K V | ∀ i, S * T i = T i * S} =
      Set.range fun c : K => c • (LinearMap.id : V →ₗ[K] V))
    (hq : ∀ i, glPullback g (q i) = q i) : ∃ c : K, (g : V →ₗ[K] V) = c • LinearMap.id := by
  have hmem : (g : V →ₗ[K] V) ∈ {S : Module.End K V | ∀ i, S * T i = T i * S} := fun i =>
    (commute_polarOperator_of_pullback hB hgB (hβ i) (hT i) (hq i)).symm
  rw [hcent] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc.symm⟩


end CFSG.Certificates
