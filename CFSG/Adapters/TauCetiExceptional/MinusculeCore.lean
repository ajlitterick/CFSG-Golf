module

public import CFSG.Adapters.TauCetiExceptional.MinusculeBigCell

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg
  CFSG.TauCetiBridge.BigCell

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (hA : TauCeti.IsFiniteType τ.cartan)
  (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) (hord : DegOrdered D)

@[expose] def ratMats :
    Set (Matrix (Fin D.d) (Fin D.d) ℚ) :=
  {z | ∃ g : hV.minGroup ℚ, natMat ℚ (hV.endo ℚ g) = z}


theorem evalMat_rename {A : Type*} [CommRing A] {n m : ℕ} (f : Fin m × Fin m → Fin n × Fin n)
    (Y : Matrix (Fin n) (Fin n) A) (P : MvPolynomial (Fin m × Fin m) ℤ) :
    evalMat Y (MvPolynomial.rename f P) =
      evalMat (Matrix.of fun a b => Y (f (a, b)).1 (f (a, b)).2) P := by
  simp only [evalMat, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename]
  rfl

theorem submatrix_toMat
    {n : ℕ} (lab : Fin n ≃ Fin D.d) (K : Type*) [Field K]
    (h : hV.minGroup K) :
    ((toMat lab K h : Matrix.GeneralLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K).submatrix lab.symm lab.symm = natMat K (hV.endo K h) := by
  ext a b
  rw [Matrix.submatrix_apply, toMat_apply, natMat_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]


end CFSG.TauCetiBridge.Minuscule
