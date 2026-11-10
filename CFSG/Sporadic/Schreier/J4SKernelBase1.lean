
module

public import CFSG.Sporadic.Schreier.J4SKernelBase

public import CFSG.Sporadic.Schreier.J4SFiveBase1
public meta import CFSG.Sporadic.J4.PrimSpec
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import Certificates.Certificate2173
public meta import CFSG.Sporadic.Schreier.J4SPrimes

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.LocalAnalysis.ComponentInitial MulAction

theorem conj_mem_N_of_mem_H : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N := fun _ hh n hn =>
  (Subgroup.mem_normalizer_iff.1 (H_le_normalizer hh) n).1 hn

theorem N_comm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
  intro a ha b hb
  obtain ⟨i, -, rfl⟩ := exists_η_eq ha
  obtain ⟨k, -, rfl⟩ := exists_η_eq hb
  rw [← η_xor, ← η_xor, Nat.xor_comm]

theorem isPGroup_N : IsPGroup 2 N := IsPGroup.of_card card_N


end CFSG.Sporadic.J4Schreier
