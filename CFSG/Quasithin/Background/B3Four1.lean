module

public import CFSG.Quasithin.Background.B3FourData
public import CFSG.Quasithin.Background.B3Flag
public import CFSG.Quasithin.Background.B3O2
public import CFSG.Quasithin.Background.B3VMod

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ} {k : Mod}


@[expose] def Hg (n : ℕ) (b : Bool) : Subgroup (Gp n) :=
  if b then ⊤ else alternatingGroup (Fin n)


@[expose] noncomputable def Tgrp (n : ℕ) (b : Bool) : Subgroup (Gp n) := subOf n (Tgl n b)


@[expose] noncomputable def stabW (H : Subgroup (Gp n)) (W : Subgroup (Mod.V n k)) :
    Subgroup (Gp n) where
  carrier := {h | h ∈ H ∧ ∀ w, w ∈ W ↔ Mod.act n k h w ∈ W}
  one_mem' := ⟨H.one_mem, fun w => by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨H.mul_mem ha.1 hb.1, fun w => by
    rw [map_mul, MulAut.mul_apply]
    exact (hb.2 w).trans (ha.2 _)⟩
  inv_mem' := fun {a} ha => ⟨H.inv_mem ha.1, fun w => by
    have h1 := ha.2 (Mod.act n k a⁻¹ w)
    have h2 : Mod.act n k a (Mod.act n k a⁻¹ w) = w := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [h2] at h1
    exact h1.symm⟩


end CFSG.Quasithin.B3
