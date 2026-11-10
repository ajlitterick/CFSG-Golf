module

public import CFSG.Open.FusionDefs
public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

abbrev sec19BPrime {G : Type} [Group G] (K : Subgroup G) (S : Sylow 2 G) (W L : Subgroup G) :
    Subgroup G :=
  (S : Subgroup G) ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
    Subgroup.centralizer (W : Set G) ⊓ centralizerModOdd ⊤ L

abbrev sec19T {G : Type} [Group G] (K : Subgroup G) (z : G) (S : Sylow 2 G) : Subgroup G :=
  (S : Subgroup G) ⊓ centralizerModOdd ⊤ (sec19X K z)


variable (p f : ℕ) [Fact p.Prime]


@[expose] def GoldschmidtB1Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (S : Sylow 2 G) (B : Subgroup G), B ≤ (S : Subgroup G) → B ≠ ⊥ →
      fusionStronglyClosed (B : Set G) (S : Subgroup G) →
        (CFSG.perfectResidual (Subgroup.centralizer (B : Set G))).map
          (Subgroup.centralizer (B : Set G)).subtype = ⊥


end CFSG.ClassicalInvolution.Disconnected.AschTight.S19B
