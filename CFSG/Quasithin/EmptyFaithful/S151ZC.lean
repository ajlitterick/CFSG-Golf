module

public import CFSG.Quasithin.EmptyFaithful.S151ZB
public import CFSG.Quasithin.EmptyFaithful.S151ZA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem par2_le_M (h118 : TheoremC118) (h126 : TheoremC126)
    {T Mc M Z₁ Z₂ V₁ V₂ L P : Subgroup G} (hc : Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L)
    (hL : CharTwo L) (hpar : Par2 L (s1516 T Z₁) P) (hbig : ParBig L P)
    (hnot : ¬ P ≤ mZ1516 Mc Z₁) : P ≤ M := by
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hHG : P ⊔ s1516 T Z₁ ≤ g1_1516 Z₁ := sup_le (hpar.le.trans hLG) (s1516_le_g1 T Z₁)
  rcases star_general h118 h126 hc le_sup_right hHG (hpar.charTwo hL) hpar.isMinParabolic
      (hpar.not_C126Third hL hbig) with h | h
  · exact le_sup_left.trans h
  · exact (hnot (le_sup_left.trans h)).elim

structure OtherPar (L B M' P : Subgroup G) : Prop where
  max : IsMaxSubgroupIn L P
  ge : B ≤ P
  ne : P ≠ M'
  only : ∀ K : Subgroup G, IsMaxSubgroupIn L K → B ≤ K → K = M' ∨ K = P
  card3 : Nat.card ↥P = 3 * Nat.card ↥B
  nn : ¬ P ≤ Subgroup.normalizer (B : Set G)
  big : ParBig L P


@[expose] def Input15122Rank2Lat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L B : Subgroup G),
    (IsLnBlock L 3 ∨ IsAltBlockType L 6 ∨ IsG2Block L) → IsSylowTwoOf B L →
      L ⊓ Subgroup.normalizer (B : Set G) ≤ B ∧
      ∀ M' : Subgroup G, IsMaxSubgroupIn L M' → B ≤ M' → ∃ P : Subgroup G, OtherPar L B M' P


end CFSG.Quasithin
