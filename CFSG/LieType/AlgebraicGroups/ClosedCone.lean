module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.LinearAlgebra.Dual.Lemmas

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u v w

variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V] {W : Type w} [AddCommGroup W] [Module k W]

variable (k) in
@[expose] def polyEval (v : V) : MvPolynomial (Module.Dual k V) k →ₐ[k] k :=
  MvPolynomial.aeval fun φ => φ v

@[simp]
theorem polyEval_X (v : V) (φ : Module.Dual k V) : polyEval k v (MvPolynomial.X φ) = φ v :=
  MvPolynomial.aeval_X _ _

variable (k) in
@[expose] def zeroSet (S : Set (MvPolynomial (Module.Dual k V) k)) : Set V :=
  {v | ∀ f ∈ S, polyEval k v f = 0}

theorem mem_zeroSet {S : Set (MvPolynomial (Module.Dual k V) k)} {v : V} :
    v ∈ zeroSet k S ↔ ∀ f ∈ S, polyEval k v f = 0 :=
  Iff.rfl

variable (k) in
@[expose] def IsZariskiClosed (C : Set V) : Prop :=
  ∃ S : Set (MvPolynomial (Module.Dual k V) k), C = zeroSet k S


theorem polyEval_rename_comp (f : W →ₗ[k] V) (w : W) (p : MvPolynomial (Module.Dual k V) k) :
    polyEval k w (MvPolynomial.rename (fun φ : Module.Dual k V => φ ∘ₗ f) p) =
      polyEval k (f w) p := by
  simp only [polyEval, MvPolynomial.aeval_rename]
  rfl

theorem IsZariskiClosed.preimage {C : Set V} (hC : IsZariskiClosed k C) (f : W →ₗ[k] V) :
    IsZariskiClosed k (f ⁻¹' C) := by
  obtain ⟨S, rfl⟩ := hC
  refine ⟨MvPolynomial.rename (fun φ : Module.Dual k V => φ ∘ₗ f) '' S, Set.ext fun w => ?_⟩
  simp only [Set.mem_preimage, mem_zeroSet, Set.forall_mem_image, polyEval_rename_comp]


end CFSG.LieType.AlgebraicGroups.ClosedCone
