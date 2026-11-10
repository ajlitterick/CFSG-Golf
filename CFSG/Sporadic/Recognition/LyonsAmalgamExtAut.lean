module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Tactic.Group

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup

section Aut

variable {E : Type*} [Group E] (Y : Subgroup E) [Y.Normal]

theorem ker_conjNormal_eq_centralizer :
    (MulAut.conjNormal : E →* MulAut Y).ker = centralizer (Y : Set E) := by
  ext e
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have := congrArg (fun σ : MulAut Y => ((σ ⟨y, hy⟩ : Y) : E)) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc y * e = (e * y * e⁻¹) * e := by rw [this]
      _ = e * y := by group
  · intro h
    ext y
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [← h y y.2]
    group

theorem conjNormal_injective_of_centralizer_eq_bot (hC : centralizer (Y : Set E) = ⊥) :
    Function.Injective (MulAut.conjNormal : E →* MulAut Y) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_conjNormal_eq_centralizer, hC]

theorem conjNormal_bijective_of_card_le [Finite (MulAut Y)] (hC : centralizer (Y : Set E) = ⊥)
    (hcard : Nat.card (MulAut Y) ≤ Nat.card E) :
    Function.Bijective (MulAut.conjNormal : E →* MulAut Y) :=
  (conjNormal_injective_of_centralizer_eq_bot Y hC).bijective_of_nat_card_le hcard

@[expose] noncomputable def conjNormalEquiv [Finite (MulAut Y)]
    (hC : centralizer (Y : Set E) = ⊥) (hcard : Nat.card (MulAut Y) ≤ Nat.card E) :
    E ≃* MulAut Y :=
  MulEquiv.ofBijective (MulAut.conjNormal : E →* MulAut Y)
    (conjNormal_bijective_of_card_le Y hC hcard)


end Aut

end CFSG.Sporadic.Recognition.LyonsSims
