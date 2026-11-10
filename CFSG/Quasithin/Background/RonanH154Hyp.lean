module

public import CFSG.Quasithin.Background.RonanH154Chain
public import CFSG.Quasithin.Background.RonanH154Xor
import CFSG.Quasithin.Background.RonanH154HypK

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH154

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf


@[expose] def FixedOK (h : ℕ) (L : List ℕ) : Prop :=
  ∀ m < 2 ^ 10, (∀ u < 32, dot5 h u = false → act10 (nq2Arr u) m = m) → m ∈ combos L

instance (h : ℕ) (L : List ℕ) : Decidable (FixedOK h L) := by
  unfold FixedOK
  infer_instance


end CFSG.Quasithin.RonanH154
