
module

public import CFSG.Sporadic.Schreier.J4SCommGenBase

public import CFSG.Sporadic.Schreier.J4SLocalNodesBase1
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SCommGenInputs
public import Certificates.Certificate2169
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.SmallF2.Native MulAction

section Generic

variable {G : Type*} [Group G]

end Generic

abbrev P1 : Subgroup (MulAut N) := P ⊓ stabilizer (MulAut N) (ηN 1)


theorem η_inv (b : ℕ) : (η b)⁻¹ = η b := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← η_xor, Nat.xor_self, η_zero]

theorem η_xorSub_mem {D : Subgroup J} :
    ∀ (ws : List ℕ), (∀ w ∈ ws, η w ∈ D) → ∀ m, η (xorSub ws m) ∈ D
  | [], _, _ => by rw [xorSub, η_zero]; exact D.one_mem
  | w :: ws, h, m => by
    rw [xorSub, η_xor]
    refine D.mul_mem ?_ (η_xorSub_mem ws (fun w' hw' => h w' (List.mem_cons_of_mem _ hw')) _)
    split_ifs
    · exact h w List.mem_cons_self
    · rw [η_zero]; exact D.one_mem


end CFSG.Sporadic.J4Schreier
