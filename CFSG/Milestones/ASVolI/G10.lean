module

public import CFSG.Quasithin.Background.G10Basic
import CFSG.Quasithin.Background.G10Fourteen
import CFSG.Quasithin.Background.G105Core
import CFSG.Quasithin.Background.RonanG1016Final
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G10Stmts
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ASVolI.ChG

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]


end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.G11 CFSG.ASVolI.ChG
open scoped commutatorElement


@[expose] def G_10_4 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)), G101Hyp B Γ v₁ W X X₀ →
      ∀ H : Subgroup (GLV V), H ≤ Γ → (∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) → H ≠ ⊥ →
      ∀ U : Submodule (ZMod 2) V, U ≠ ⊥ → U ≠ ⊤ → IsIrr (H ⊔ X) U →
        (H = Γ ∨ (v₁ ∉ U ∧ commSpace X U ≠ ⊥)) →
          Module.finrank (ZMod 2) V = 4 ∧ Module.finrank (ZMod 2) U = 2 ∧ Group.IsSolvable ↥Γ

theorem as_G_10_4 : G_10_4 :=
  CFSG.Quasithin.g10_4 CFSG.Quasithin.G11.g10_3 CFSG.Quasithin.G11.SzG11S.b49


section G107

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]


end G107


@[expose] def G_10_10 : Prop := G1010Stmt

theorem as_G_10_10 : G_10_10 :=
  CFSG.Quasithin.G11.g10_10_of_g10_4 as_G_10_4

@[expose] def G_10_11 : Prop := G1011Stmt

theorem as_G_10_11 : G_10_11 := CFSG.Quasithin.G11.g10_11 as_G_10_10

@[expose] def G_10_12 : Prop := G1012Stmt

theorem as_G_10_12 : G_10_12 := CFSG.Quasithin.G11.g10_12 as_G_10_11


@[expose] def G_10_14 : Prop := G1014Stmt

theorem as_G_10_14 : G_10_14 := CFSG.Quasithin.G11.g10_14 as_G_10_12


end CFSG.ASVolI
