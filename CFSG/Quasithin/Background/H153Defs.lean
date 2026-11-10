module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.AppendixH.H14.Vocab
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open scoped Pointwise

namespace CFSG.Quasithin.H153

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Open

@[expose] def natHomI' (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type*) [Field K] :
    GL ι K →* MulAut (Multiplicative (ι → K)) where
  toFun g :=
    { toFun := fun v => Multiplicative.ofAdd ((g : Matrix ι ι K).mulVec (Multiplicative.toAdd v))
      invFun := fun v => Multiplicative.ofAdd
        (((g⁻¹ : GL ι K) : Matrix ι ι K).mulVec (Multiplicative.toAdd v))
      left_inv := fun v => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_mulVec]
      right_inv := fun v => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_mulVec]
      map_mul' := fun v w => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_add] }
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp [Matrix.mulVec_mulVec]

@[expose] def natSubI' (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type*) [Field K]
    (S : Subgroup (GL ι K)) : Subgroup (MulAut (Multiplicative (ι → K))) :=
  S.map (natHomI' ι K)


@[expose] def IsO23' (G N : Subgroup S24) : Prop :=
  N ≤ G ∧ (∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N) ∧ pCoreOf 2 G ≤ N ∧
    (∀ n ∈ N, ∃ k : ℕ, n ^ (3 ^ k) ∈ pCoreOf 2 G) ∧
    ∀ N' : Subgroup S24, N' ≤ G → (∀ g ∈ G, ∀ n ∈ N', g * n * g⁻¹ ∈ N') → pCoreOf 2 G ≤ N' →
      (∀ n ∈ N', ∃ k : ℕ, n ^ (3 ^ k) ∈ pCoreOf 2 G) → N' ≤ N

@[expose] def FullTranspCenter' {V : Type*} [CommGroup V] (G X : Subgroup (MulAut V))
    (A V₁ : Subgroup V) : Prop :=
  (∀ g ∈ X, ∀ x ∈ A, g x * x⁻¹ ∈ V₁) ∧
  (∀ τ : MulAut ↥A, (∀ x : ↥A, ((τ x : ↥A) : V) * ((x : ↥A) : V)⁻¹ ∈ V₁) →
    ∃ g ∈ X, ∀ x : ↥A, g (x : V) = ((τ x : ↥A) : V)) ∧
  (∀ g ∈ X, (∀ x ∈ A, g x = x) → g = 1) ∧
  (∀ h ∈ G, ∀ g ∈ X, h * g * h⁻¹ ∈ X)


end CFSG.Quasithin.H153
