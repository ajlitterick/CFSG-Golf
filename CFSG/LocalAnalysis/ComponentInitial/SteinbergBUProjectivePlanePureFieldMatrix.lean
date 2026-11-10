module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix LinearFlag

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def twistedProd (σ : K ≃+* K) (M : GL (Fin n) K) : ℕ → GL (Fin n) K
  | 0 => 1
  | k + 1 => twistedProd σ M k * GeneralLinearGroup.map ((σ ^ k : K ≃+* K) : K →+* K) M

theorem twistedProd_zero (σ : K ≃+* K) (M : GL (Fin n) K) : twistedProd σ M 0 = 1 :=
  rfl

theorem twistedProd_succ (σ : K ≃+* K) (M : GL (Fin n) K) (k : ℕ) :
    twistedProd σ M (k + 1) =
      twistedProd σ M k * GeneralLinearGroup.map ((σ ^ k : K ≃+* K) : K →+* K) M :=
  rfl

theorem conjAut_mul_fieldAut_pow (σ : K ≃+* K) (M : GL (Fin n) K) (k : ℕ) :
    (conjAut n K M * fieldAut n K σ) ^ k =
      conjAut n K (twistedProd σ M k) * fieldAut n K (σ ^ k) := by
  induction k with
  | zero => rw [pow_zero, twistedProd_zero, pow_zero, map_one, map_one, mul_one]
  | succ k ih =>
    rw [pow_succ, ih, conjAut_mul_fieldAut_mul, twistedProd_succ, ← pow_succ]

theorem map_map_ringEquiv (σ τ : K ≃+* K) (A : GL (Fin n) K) :
    GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.map (τ : K →+* K) A) =
      GeneralLinearGroup.map ((σ * τ : K ≃+* K) : K →+* K) A :=
  Units.ext (Matrix.ext fun _ _ => rfl)


@[expose] def lastFixedPerm (p : ℕ) (τ : Equiv.Perm (Fin (p - 1))) : Equiv.Perm (Fin p) :=
  τ.extendDomain (Fin.castLEquiv (Nat.sub_le p 1))

@[expose] def signedPermMatrixInt (p : ℕ) (τ : Equiv.Perm (Fin (p - 1))) :
    Matrix (Fin p) (Fin p) ℤ :=
  (lastFixedPerm p τ).permMatrix ℤ *
    diagonal (fun i : Fin p => if (i : ℕ) = p - 1 then ((Equiv.Perm.sign τ : ℤˣ) : ℤ) else 1)

variable (K) in
@[expose] def signedPermMatrix (p : ℕ) (τ : Equiv.Perm (Fin (p - 1))) : Matrix (Fin p) (Fin p) K :=
  (signedPermMatrixInt p τ).map (Int.castRingHom K)


end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
