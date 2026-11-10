module

public import CFSG.Assembly.LowTwoRankDefs

public noncomputable section

namespace CFSG.Blueprint.EvenSource

open CFSG.Assembly.LowTwoRank Module

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]

@[expose] def sourceScalars : Subgroup (LinearMap.GeneralLinearGroup K V) :=
  (Units.map (algebraMap K (Module.End K V)).toMonoidHom).range

theorem sourceScalars_le_center :
    sourceScalars K V ≤ Subgroup.center (LinearMap.GeneralLinearGroup K V) := by
  rintro _ ⟨c, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  change (g : Module.End K V) * algebraMap K (Module.End K V) c =
    algebraMap K (Module.End K V) c * g
  exact (Algebra.commutes _ _).symm

instance sourceScalars_normal : (sourceScalars K V).Normal :=
  Subgroup.normal_of_le_center (sourceScalars_le_center K V)


variable {K V}

theorem coe_apply_inv_apply (g : LinearMap.GeneralLinearGroup K V) (x : V) :
    (g : Module.End K V) (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) x) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, Module.End.one_apply]


@[expose] def sourceOrthogonal (Q : V → K) : Subgroup (LinearMap.GeneralLinearGroup K V) where
  carrier := {g | ∀ x, Q ((g : Module.End K V) x) = Q x}
  mul_mem' := by
    intro a b ha hb x
    rw [Units.val_mul, Module.End.mul_apply, ha, hb]
  one_mem' := fun x => rfl
  inv_mem' := by
    intro g hg x
    rw [← hg, coe_apply_inv_apply]


@[expose] def IsSourceQuadratic (Q : V → K) : Prop :=
  (∀ (a : K) x, Q (a • x) = a ^ 2 * Q x) ∧
    (∃ B : LinearMap.BilinForm K V, ∀ x y, B x y = Q (x + y) - Q x - Q y) ∧
    {x | Q x = 0 ∧ ∀ y, Q (x + y) - Q x - Q y = 0} = ({0} : Set V)

@[expose] def sourceWittIndex (Q : V → K) : ℕ :=
  sSup {d | ∃ W : Submodule K V, (∀ w ∈ W, Q w = 0) ∧ finrank K W = d}

theorem sourceWittIndex_bddAbove [FiniteDimensional K V] (Q : V → K) :
    BddAbove {d | ∃ W : Submodule K V, (∀ w ∈ W, Q w = 0) ∧ finrank K W = d} := by
  refine ⟨finrank K V, ?_⟩
  rintro _ ⟨W, -, rfl⟩
  exact Submodule.finrank_le W

theorem IsSourceQuadratic.map_zero {Q : V → K} (hQ : IsSourceQuadratic Q) : Q 0 = 0 := by
  have h := hQ.1 0 0
  rwa [zero_smul, zero_pow two_ne_zero, zero_mul] at h

theorem exists_sourceWittIndex [FiniteDimensional K V] {Q : V → K} (hQ : Q 0 = 0) :
    ∃ W : Submodule K V, (∀ w ∈ W, Q w = 0) ∧ finrank K W = sourceWittIndex Q := by
  have hne : ({d | ∃ W : Submodule K V, (∀ w ∈ W, Q w = 0) ∧ finrank K W = d} : Set ℕ).Nonempty :=
    ⟨0, ⊥, fun w hw => by rw [(Submodule.mem_bot K).mp hw]; exact hQ, finrank_bot K V⟩
  exact Nat.sSup_mem hne (sourceWittIndex_bddAbove Q)

theorem le_sourceWittIndex [FiniteDimensional K V] (Q : V → K) {W : Submodule K V}
    (hW : ∀ w ∈ W, Q w = 0) : finrank K W ≤ sourceWittIndex Q :=
  le_csSup (sourceWittIndex_bddAbove Q) ⟨W, hW, rfl⟩


end CFSG.Blueprint.EvenSource
