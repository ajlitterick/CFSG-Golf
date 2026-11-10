module

public import Certificates.Data.Kernel.PermCent.ForceCV
public import CFSG.Certificates.Kernel.PermCent.CVSound
public import CFSG.Certificates.Kernel.Census.CatFacts.PkWordSound

public section

namespace CFSG.Certificates.Kernel.PkCV

open CFSG.Certificates.Kernel.PkEnum

variable {n : Nat}

theorem forceC_eq {β : Sort _} (a : CV n) (k : CV n → β) : forceC a k = k a := by
  unfold forceC
  rw [forceD_eq]

theorem forceCL_eq {β : Sort _} : ∀ (l : List (CV n)) (k : List (CV n) → β), forceCL l k = k l
  | [], _ => rfl
  | a :: l, k => by
    rw [forceCL, forceC_eq, forceCL_eq l]

theorem memC_val (a : CV n) (L : List (CV n)) : memC a.1 L = decide (a ∈ L) := by
  rw [Bool.eq_iff_iff, memC, List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨c, hc, h⟩
    rw [Nat.beq_eq] at h
    rwa [Subtype.ext h]
  · exact fun h => ⟨a, h, Nat.beq_refl a.1⟩


end CFSG.Certificates.Kernel.PkCV

end
