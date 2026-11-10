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


theorem e4_set_closed : ∀ u v : Fin 32, ∀ s ∈ ({0, u, v, xor32 u v} : Finset (Fin 32)),
    ∀ t ∈ ({0, u, v, xor32 u v} : Finset (Fin 32)),
      xor32 s t ∈ ({0, u, v, xor32 u v} : Finset (Fin 32)) := by
  intro u v s hs t ht
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hs ht ⊢
  exact HypK.xor32_closed4 u v s t hs ht


@[expose] def E4 (u v : Fin 32) : Subgroup P24 :=
  xorSub {0, u, v, xor32 u v} (by simp) (e4_set_closed u v)


end CFSG.Quasithin.RonanH154
