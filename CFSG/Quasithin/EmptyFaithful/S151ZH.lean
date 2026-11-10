module

public import CFSG.Quasithin.EmptyFaithful.S151ZE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem zb_pCore_le_center {X : Type} [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X) :
    CFSG.pCore 2 X ≤ Subgroup.center X := by
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq (CFSG.pCore 2 X) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 (⊤ : Subgroup X) := h ▸ CFSG.pCore_isPGroup (p := 2) (G := X)
    have := (hp.of_equiv Subgroup.topEquiv).isNilpotent
    have : Group.IsPerfect X := ⟨hq.1⟩
    have : Nontrivial X := CFSG.ComponentClassification.Quasisimple.nontrivial hq
    exact Group.IsPerfect.not_isSolvable X inferInstance

theorem zb_center_eq_pCore [Finite G] {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hZ : IsPGroup 2 ↥(Subgroup.center ↥L)) : Subgroup.center ↥L = CFSG.pCore 2 ↥L := by
  refine le_antisymm ?_ (zb_pCore_le_center hq)
  exact CFSG.LieType.BorelTits.le_pCore 2 inferInstance hZ

@[expose] def SporadicSix (X : Type) [Group X] : Prop :=
  IsSporadic .J2 X ∨ IsSporadic .He X ∨ IsSporadic .M12 X ∨ IsSporadic .M22 X ∨
    IsSporadic .M23 X ∨ IsSporadic .M24 X

theorem zb_sporadicSix_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : SporadicSix X) :
    SporadicSix Y := by
  have key : ∀ s, IsSporadic s X → IsSporadic s Y := fun s hs => hs.map fun f => e.symm.trans f
  rcases h with h | h | h | h | h | h
  · exact Or.inl (key _ h)
  · exact Or.inr (Or.inl (key _ h))
  · exact Or.inr (Or.inr (Or.inl (key _ h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (key _ h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key _ h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (key _ h)))))

@[expose] def Input15122ThreeD' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) → Case15120ThreeD T Mc Z₁ L →
    Lemma15118Extra T Mc M Z₁ → Case15122Five T M Mc Z₁ L ∨ Case15122Six T Mc Z₁ L

@[expose] def SporadicSixNotA38 : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G), SporadicSix (↥L ⧸ CFSG.pCore 2 ↥L) →
    ¬ A38Types (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def Input15122ThreeDHSRu : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) → Case15120ThreeD T Mc Z₁ L →
    Lemma15118Extra T Mc M Z₁ →
    ¬ (IsSporadic .HS (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .Ru (↥L ⧸ CFSG.pCore 2 ↥L))

@[expose] def Input15122ThreeDM11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) → Case15120ThreeD T Mc Z₁ L →
    IsSporadic .M11 (↥L ⧸ CFSG.pCore 2 ↥L) → Case15122Six T Mc Z₁ L


@[expose] def Input15122ThreeDZL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) → Case15120ThreeD T Mc Z₁ L →
    SporadicSix (↥L ⧸ CFSG.pCore 2 ↥L) → ZL2 (s1516 T Z₁) L


theorem lemma15122InputU_of_corrected_inputs (nDich : Input15122Dichotomy) (nNoB : Input15122NoBorel)
    (nA7 : Input15122A7) (nR2 : Input15122Rank2Block) (nL45 : Input15122L45Block')
    (nC : Input15122ThreeC) (nD : Input15122ThreeD') (nE : Input15122ThreeE) : Lemma15122InputU := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h20 h21 hx
  have hc : Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L := ⟨hC, h17, h18, h19, hL, h20, h21⟩
  rcases nDich G T Mc M Z₁ Z₂ V₁ V₂ L hc with hchar | hcomp
  · obtain ⟨-, hcases⟩ := h20.two hchar
    rcases hcases with h | h | h
    · exact (not_caseTwoA_15122 hL h21 hchar h).elim
    · rcases h.2.1 hL.comp with h7 | h3 | h6 | hg
      · exact Or.inl (nA7 G T Mc M Z₁ Z₂ V₁ V₂ L hc h h7)
      · exact Or.inr (Or.inl (nR2 G T Mc M Z₁ Z₂ V₁ V₂ L hc h (Or.inl h3)))
      · exact Or.inr (Or.inl (nR2 G T Mc M Z₁ Z₂ V₁ V₂ L hc h (Or.inr (Or.inl h6))))
      · exact Or.inr (Or.inl (nR2 G T Mc M Z₁ Z₂ V₁ V₂ L hc h (Or.inr (Or.inr hg))))
    · exact Or.inr (Or.inr (Or.inl (nL45 G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar h)))
  · obtain ⟨-, hcases⟩ := h20.three hcomp
    rcases hcases with h | h | h | h | h
    · exact ((nNoB G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp).1 h).elim
    · exact ((nNoB G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp).2 h).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl (nC G T Mc M Z₁ Z₂ V₁ V₂ L hc h))))
    · rcases nD G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h hx with h5 | h6
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (nE G T Mc M Z₁ Z₂ V₁ V₂ L hc h))))))

end CFSG.Quasithin
