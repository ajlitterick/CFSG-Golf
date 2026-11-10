module

public import CFSG.Quasithin.EmptyFaithful.T1515cE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

structure Ctx15122 (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G) : Prop where
  ctx : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂
  h17 : Lemma15117Concl T M Z₁
  h18 : Lemma15118Concl T Mc M Z₁
  h19 : Lemma15119Used T Mc M Z₁ V₂
  hL : IsL1519 Mc Z₁ L
  h20 : Lemma15120Concl T Mc M Z₁ L
  h21 : Lemma15121Concl Mc Z₁ L

@[expose] def Input15122Dichotomy : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L ∨ IsComponentOf L (g1_1516 Z₁)

omit [Finite G] in
theorem not_caseTwoA_15122 {T Mc Z₁ L : Subgroup G} (hL : IsL1519 Mc Z₁ L)
    (h21 : Lemma15121Concl Mc Z₁ L) (hchar : CharTwo L) : ¬ Case15120TwoA T Mc Z₁ L := by
  rintro ⟨hblock, htype, -⟩
  apply hL.not_le
  exact h21 hL.comp (Or.inl ⟨hchar, ⟨hblock.1, le_of_mem_cComp hL.comp,
    (isSubnormal_iff_subgroupOf (le_of_mem_cComp hL.comp)).mp (subnormal_of_mem_cComp hL.comp)⟩,
    htype⟩)

@[expose] def Input15122NoBorel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) →
    ¬ Case15120ThreeA Mc Z₁ L ∧ ¬ Case15120ThreeB Mc Z₁ L

@[expose] def Input15122A7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → Case15120TwoB T Mc Z₁ L → IsAltBlockType L 7 →
    Case15122One T M Mc Z₁ L

@[expose] def Input15122Rank2Block : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → Case15120TwoB T Mc Z₁ L →
    (IsLnBlock L 3 ∨ IsAltBlockType L 6 ∨ IsG2Block L) → Case15122Two T M Mc Z₁ L


@[expose] def Input15122ThreeC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → Case15120ThreeC T Mc Z₁ L → Case15122Four T M Mc Z₁ L


@[expose] def Input15122ThreeE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → Case15120ThreeE T Mc Z₁ L → Case15122Seven T M Mc Z₁ L


end CFSG.Quasithin
