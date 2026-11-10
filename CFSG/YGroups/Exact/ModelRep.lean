module

public import CFSG.YGroups.Exact.Model

public section

namespace CFSG.YGroups

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.YGroups.ModelNative
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)


theorem yModelHom_injective_and_card_of_le {p q r n : ℕ} {O : Array (Array ℕ)} {B : ℕ}
    (hcard : Finite (YGroup p q r) ∧ Nat.card (YGroup p q r) ≤ B)
    (hsize : O.size = ngen p q r) (hrel : ∀ w ∈ yRels p q r, evalWord (arrGen n O) w = 1)
    (hlow : B ≤ Nat.card (arrClosure n O)) :
    Function.Injective (yModelHom (arrGen n O) hrel) ∧ Nat.card (YGroup p q r) = B := by
  have := hcard.1
  refine injective_and_card_of_model _ hcard.2 ?_
  rw [range_yModelHom, ← hsize, arrGen_image_eq]
  exact hlow


end CFSG.YGroups
