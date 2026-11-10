module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationTorusRoots

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.CurtisTits

section Torus

variable {K : Type*} [Group K] {k : Type*} [Field k] {D : UniversalRootDatum K}
  {x : (Fin D.rank → ℤ) → k → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}

@[expose] def hElt {r : ℕ} (x : (Fin r → ℤ) → k → K) (i : Fin r) (s : kˣ) : K :=
  weylElement x i s * (weylElement x i 1)⁻¹


variable {X : Type*} [Group X]

theorem ActsByScalar.inv' {u l : k → X} {e : X} {a : kˣ} (he : ActsByScalar u l e a) :
    ActsByScalar u l e⁻¹ a⁻¹ := by
  refine ⟨fun c => ?_, fun c => ?_⟩
  · have h := he.1 ((a⁻¹ : kˣ) * c)
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h
    rw [← h]
    group
  · have h := he.2 ((a : k) * c)
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at h
    rw [inv_inv, ← h]
    group


end Torus

end CFSG.ClassicalInvolution.Balance
