module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.Hilbert90

public section

namespace CFSG.GH74.GLS.IVK.H90

variable {F : Type*} [Field F]

@[expose] def Ai (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F) : ℕ → Matrix (Fin 2) (Fin 2) F
  | 0 => 1
  | n + 1 => A * (Ai σ A n).map σ

@[expose] def sv (σ : F ≃+* F) (i : ℕ) (w : Fin 2 → F) : Fin 2 → F := fun j => (σ ^ i) (w j)

@[expose] def tr (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F) (r : ℕ) (w : Fin 2 → F) : Fin 2 → F :=
  ∑ i ∈ Finset.range r, (Ai σ A i).mulVec (sv σ i w)

@[expose] def σv (σ : F ≃+* F) : (Fin 2 → F) →+ (Fin 2 → F) :=
  AddMonoidHom.mk' (fun u j => σ (u j)) (by intro a b; ext j; simp)

theorem Ai_eq (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F) (n : ℕ) :
    Ai σ A n = HardMathSupport.Foote.ModuleExclusions.Ai σ A n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change A * (Ai σ A n).map σ = A * (HardMathSupport.Foote.ModuleExclusions.Ai σ A n).map σ
    rw [ih]


theorem sigma_pow_linearIndependent (σ : F ≃+* F) (r : ℕ) (hr : orderOf σ = r) :
    LinearIndependent F (fun i : Fin r => ((fun u : Fˣ => (σ ^ (i : ℕ)) (u : F)) : Fˣ → F)) :=
  HardMathSupport.Foote.ModuleExclusions.sigma_pow_linearIndependent σ r hr


theorem speiser (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F) (r : ℕ) (hr : orderOf σ = r)
    (hr0 : 0 < r) (hA : Ai σ A r = 1) :
    ∃ B : Matrix (Fin 2) (Fin 2) F, B.det ≠ 0 ∧ A * B.map σ = B :=
  HardMathSupport.Foote.ModuleExclusions.speiser σ A r hr hr0 (by rwa [← Ai_eq])


theorem exists_prod_pow_eq [Finite F] (σ : F ≃+* F) (c : F) (hc : σ c = c) (hc0 : c ≠ 0) :
    ∃ l : F, l ≠ 0 ∧ ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) l = c :=
  HardMathSupport.Foote.ModuleExclusions.exists_prod_pow_eq σ c hc hc0


end CFSG.GH74.GLS.IVK.H90
