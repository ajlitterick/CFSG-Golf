module

public import CFSG.Sporadic.Recognition.McLMultiplierInputs
public import CFSG.Sporadic.McL.Action

public section

namespace CFSG.Sporadic.Recognition.McLMultiplier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.McL CFSG.LieType.Multipliers
open CFSG.Sporadic.McL.Native (orbitData genTables)

@[expose] noncomputable def mclGenG (z : ℤ) : J :=
  if z = 1 ∨ z = -1 then a else if z = 2 then b else b⁻¹


@[expose] noncomputable def mclGenE (k : ℕ) : J :=
  wordG mclGenG (mclGenWord k)

@[expose] noncomputable def mclGen (i : Fin 6) : J :=
  mclGenE i.val


theorem lift_mclGen_mem_closure (v : FreeGroup (Fin 6)) :
    FreeGroup.lift mclGen v ∈ Subgroup.closure (Set.range mclGen) := by
  induction v using FreeGroup.induction_on with
  | one => simp
  | of i =>
    rw [FreeGroup.lift_apply_of]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  | inv_of i =>
    rw [map_inv, FreeGroup.lift_apply_of]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_range_self i))
  | mul _ _ h₁ h₂ => rw [map_mul]; exact Subgroup.mul_mem _ h₁ h₂


end CFSG.Sporadic.Recognition.McLMultiplier
