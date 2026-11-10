module

public import CFSG.CGT.Stroth77.Section225FamilyTwo
public import CFSG.CGT.Stroth77.Section224UniformSq

public section

namespace CFSG.CGT.Stroth77

open Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X : StrothAmbient G}


theorem action_rho_eq_type200 (τ : StrothTypeIndex) (hrel : τ.m + 2 = τ.n) :
    τ.action.ρ = Type200.ρM := by
  cases τ with
  | t100 m =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type100.k] at hrel
  | t101 s =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type101.k] at hrel
  | t110 t =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type110.k] at hrel
  | t111 t =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type111.k] at hrel
  | t120 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type120.k] at hrel
  | t121 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type121.k] at hrel
  | t130 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type130.k] at hrel
  | t131 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type131.k] at hrel
  | t200 m => rfl
  | t201 m => rfl
  | t210 m hm => rfl
  | t211 m hm => rfl
  | t220 s hs => rfl
  | t221 s hs => rfl
  | t230 s hs => rfl
  | t231 s hs => rfl
  | t300 n =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type300.k] at hrel
  | t310 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type310.k] at hrel
  | t320 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type320.k,
      Type32x.k] at hrel
  | t330 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type330.k,
      Type32x.k] at hrel
  | t321 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type321.k] at hrel
  | t331 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type331.k] at hrel


end CFSG.CGT.Stroth77

end
