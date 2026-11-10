module

public import CFSG.LocalAnalysis.SteinbergCCDempwolffBasic
public import CFSG.LocalAnalysis.SteinbergCCDempwolffData
public import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.LocalAnalysis.DempwolffFive

open Matrix CFSG.Sporadic.Th.Native

@[expose] def arrFun (a : Array ℕ) (i : Fin 240) : Fin 240 :=
  ⟨a.getD i.1 0 % 240, Nat.mod_lt _ (by norm_num)⟩

@[expose] def invPerm (a : Array ℕ) (h : ∀ i, arrFun a (arrFun a i) = i) :
    Equiv.Perm (Fin 240) :=
  ⟨arrFun a, arrFun a, h, h⟩

set_option maxHeartbeats 800000 in
theorem rootPermArr_invol : ∀ k : Fin 12, ∀ i : Fin 240,
    arrFun (rootPermArr.getD k #[]) (arrFun (rootPermArr.getD k #[]) i) = i := by
  intro k
  fin_cases k <;> decide +kernel

theorem negArr_invol : ∀ i : Fin 240, arrFun negArr (arrFun negArr i) = i := by
  decide +kernel

@[expose] def gp (k : ℕ) : Equiv.Perm (Fin 240) :=
  if h : k < 12 then invPerm (rootPermArr.getD k #[]) (rootPermArr_invol ⟨k, h⟩) else 1

@[expose] def negP : Equiv.Perm (Fin 240) := invPerm negArr negArr_invol

@[expose] def blockPerm (t : ℕ) (j : Fin 31) : Equiv.Perm (Fin 240) :=
  match (blockWords.getD t #[]).getD j.1 (false, []) with
  | (s, w) => (if s then negP else 1) * (w.map gp).prod

abbrev Blk := Equiv.Perm (Fin 240)

@[expose] def ψ : G →* MulAut (Fin 31 → Blk) where
  toFun g :=
    { toFun := fun k j => k (g⁻¹ • j)
      invFun := fun k j => k (g • j)
      left_inv := fun k => funext fun j => by
        change k (g⁻¹ • g • j) = k j
        rw [inv_smul_smul]
      right_inv := fun k => funext fun j => by
        change k (g • g⁻¹ • j) = k j
        rw [smul_inv_smul]
      map_mul' := fun _ _ => rfl }
  map_one' := MulEquiv.ext fun k => funext fun j => by
    change k (1⁻¹ • j) = k j
    rw [inv_one, one_smul]
  map_mul' g h := MulEquiv.ext fun k => funext fun j => by
    change k ((g * h)⁻¹ • j) = k (h⁻¹ • (g⁻¹ • j))
    rw [_root_.mul_inv_rev, mul_smul]

abbrev M := (Fin 31 → Blk) ⋊[ψ] G

@[expose] def ψ' : Equiv.Perm (Fin 31) →* MulAut (Fin 31 → Blk) where
  toFun σ :=
    { toFun := fun k j => k (σ⁻¹ j)
      invFun := fun k j => k (σ j)
      left_inv := fun k => funext fun j => by
        change k (σ.symm (σ j)) = k j
        rw [Equiv.symm_apply_apply]
      right_inv := fun k => funext fun j => by
        change k (σ (σ.symm j)) = k j
        rw [Equiv.apply_symm_apply]
      map_mul' := fun _ _ => rfl }
  map_one' := MulEquiv.ext fun k => funext fun j => rfl
  map_mul' σ τ := MulEquiv.ext fun k => funext fun j => rfl

abbrev M' := (Fin 31 → Blk) ⋊[ψ'] Equiv.Perm (Fin 31)


end CFSG.LocalAnalysis.DempwolffFive
