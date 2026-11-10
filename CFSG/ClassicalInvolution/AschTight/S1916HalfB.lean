module

public import CFSG.ClassicalInvolution.AschTight.S1916Fus
public import CFSG.ClassicalInvolution.AschTight.S1911C8b

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G}

theorem Ctx12.card_Q [IsSimpleGroup G] (c : Ctx12 p f K z S W L t) :
    Nat.card ↥((S : Subgroup G) ⊓ sec19Y K z) = 2 * Nat.card ↥(W ⊓ sec19Y K z) := by
  rw [S1911.card_inf_sec19Y c.data, c.card, c.card_R]


end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
