module

public import CFSG.Quasithin.Background.RonanH143E2

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH154

open CFSG.Open CFSG.Quasithin.RonanH143

@[expose] def dot5 (h u : ℕ) : Bool :=
  ((h &&& u).testBit 0) ^^ ((h &&& u).testBit 1) ^^ ((h &&& u).testBit 2) ^^
    ((h &&& u).testBit 3) ^^ ((h &&& u).testBit 4)

@[expose] def xorSub (S : Finset (Fin 32)) (h0 : (0 : Fin 32) ∈ S)
    (hS : ∀ s ∈ S, ∀ t ∈ S, xor32 s t ∈ S) : Subgroup P24 where
  carrier := {g | ∃ u ∈ S, g = nq2Perm u}
  mul_mem' := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨xor32 s t, hS s hs t ht, nq2Perm_mul s t⟩
  one_mem' := ⟨0, h0, nq2Perm_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, inv_eq_of_mul_eq_one_right (nq2Perm_sq t)⟩


end CFSG.Quasithin.RonanH154
