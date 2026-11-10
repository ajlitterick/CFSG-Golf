module

public import CFSG.Quasithin.Background.JonesParshallBasic
public import CFSG.Open.GriessSchurMultipliersMilestoneDefs
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Vol2.Ch3Basic

public section

namespace CFSG.Quasithin.ASInputs

open CFSG.Open CFSG.QuasithinUnique

@[expose] def E111Hyp (G : Type) [Group G] (n : ℕ) : Prop :=
  ∀ (H K : Subgroup G), K ≤ H → ∀ [(K.subgroupOf H).Normal], CFSG.Open.IsSubnormal H ⊤ →
    IsSimpleGroup (↥H ⧸ K.subgroupOf H) → (∃ a b : ↥H ⧸ K.subgroupOf H, a * b ≠ b * a) →
    ∀ B : Subgroup (MulAut (↥H ⧸ K.subgroupOf H)), IsPGroup 2 B →
      IsSylowIn 2 (B ⊓ (MulAut.conj : ↥H ⧸ K.subgroupOf H →* _).range)
        (MulAut.conj : ↥H ⧸ K.subgroupOf H →* _).range →
      E1.nParam ((MulAut.conj : ↥H ⧸ K.subgroupOf H →* _).range ⊔ B) ≤ (n : ℕ∞)

@[expose] def AS_E_1_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ), 1 ≤ n → E111Hyp G n →
    E1.nParam (⊤ : Subgroup G) ≤ (n : ℕ∞)


abbrev FStar (G : Type) [Group G] : Type := ↥(CFSG.generalizedFitting G)


@[expose] def AS_I_1_3_Sp4 : Prop :=
  ∀ (e : ℕ), 2 ≤ e → ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ e →
    ∀ (L : Type) [Group L] [Finite L] (φ : L →* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)),
      Function.Surjective φ → commutator L = ⊤ → φ.ker ≤ Subgroup.center L →
        Function.Injective φ

end CFSG.Quasithin.ASInputs
