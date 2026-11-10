module

public import CFSG.Quasithin.Background.A1a
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E2

variable {Γ : Type} [Group Γ]

@[expose] def IsExtraspecialPlus {Γ' : Type*} [Group Γ'] (m : ℕ) (D : Subgroup Γ') : Prop :=
  CFSG.IsExtraspecial 2 ↥D ∧ Nat.card D = 2 ^ (1 + 2 * m) ∧
    ∃ E : Subgroup Γ', E ≤ D ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ (m + 1)

@[expose] def E217Concl (H T V : Subgroup Γ) : Prop :=
  let Y := conjClosure V H
  (∃ D : Subgroup Γ, D ≤ Y ∧ Y ≤ Subgroup.normalizer (D : Set Γ) ∧ IsExtraspecialPlus 2 D ∧
    ∃ φ : ↥Y →* Equiv.Perm (Fin 3), Function.Surjective φ ∧ φ.ker = D.subgroupOf Y) ∨
  ((∃ D : Subgroup Γ, D ≤ Y ∧ Y ≤ Subgroup.normalizer (D : Set Γ) ∧ IsExtraspecialPlus 3 D ∧
    ∃ (L : Type) (_ : Group L), IsPSL 3 2 1 L ∧
      ((∃ φ : ↥Y →* L, Function.Surjective φ ∧ φ.ker = D.subgroupOf Y) ∨
        ∃ φ : ↥Y →* Multiplicative (ZMod 2) × L, Function.Surjective φ ∧
          φ.ker = D.subgroupOf Y)) ∧
    8 ≤ (T ⊓ Subgroup.centralizer (V : Set Γ)).relIndex T)


end E2

end CFSG.Quasithin
