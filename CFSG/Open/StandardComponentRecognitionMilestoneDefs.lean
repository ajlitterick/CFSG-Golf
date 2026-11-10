module

public import CFSG.Open.Defs
public import CFSG.Foundations.FullStandardCore

public section

namespace CFSG.Open

@[expose] def standardComponentIsStandard {G : Type*} [Group G] (L : Subgroup G) : Prop :=
  full_standard% FullStandardCore (IsQuasisimple L)
    (fun H g => H.map (MulAut.conj g).toMonoidHom) L

theorem standardComponentIsStandard_eq_fullStandardCore {G : Type*} [Group G] (L : Subgroup G) :
    standardComponentIsStandard L =
      FullStandardCore (IsQuasisimple L) (fun H g => H.map (MulAut.conj g).toMonoidHom) L :=
  rfl

@[expose] def standardComponentOddCore (H : Type*) [Group H] : Subgroup H :=
  sSup {N : Subgroup H | N.Normal ∧ Odd (Nat.card N)}


end CFSG.Open
