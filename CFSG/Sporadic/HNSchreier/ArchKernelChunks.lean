module
public import CFSG.Sporadic.HNSchreier.ArchKernelChecks

public section
namespace CFSG.Sporadic.HNSchreier.Native.Kernel

theorem allInKernel_eq_true {lo hi : Nat} {p : Nat → Bool} :
    allInKernel lo hi p = true ↔ ∀ i, lo ≤ i → i < hi → p i = true := by
  rw [← allIn_kernel]
  unfold CFSG.Sporadic.Th.Native.allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hlo hhi
    have := h ⟨i - lo, by omega⟩ (List.mem_finRange _)
    simpa [Nat.add_sub_cancel' hlo] using this
  · rintro h ⟨k, hk⟩ _
    exact h (lo + k) (by omega) (by omega)


end CFSG.Sporadic.HNSchreier.Native.Kernel
