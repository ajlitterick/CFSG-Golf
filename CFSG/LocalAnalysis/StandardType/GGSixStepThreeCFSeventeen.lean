module

public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFComp
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitness
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGSixSeventeenPair (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (f : ℕ) (b : G) (L₁ : Subgroup G) : Prop :=
  b ∈ Bs ∧ b ≠ 1 ∧ IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) ∧
    ¬ GGSixSeventeenExcluded p t f L₁

@[expose] def GGSixSeventeenDirect (p : ℕ) (Bs D G₀ : Subgroup G) (e : G) : Prop :=
  e ∈ Bs ∧ e ≠ 1 ∧ ((∃ m ∈ Subgroup.normalizer (Bs : Set G), m⁻¹ * e * m ∈ D) ∨
    ∃ L₂ : Subgroup G, IsComponentOf L₂ (G₀ ⊓ Subgroup.centralizer {e}) ∧
      Nat.card (Bs ⊓ Subgroup.centralizer (L₂ : Set G) : Subgroup G) ≤ p ^ 2)

@[expose] def GGSixSeventeenSixteen (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (f : ℕ) (e : G) : Prop :=
  ∃ L₂ L₃ : Subgroup G, GGSixSeventeenPair p B Bs x L D J t f e L₂ ∧
    GGSixSeventeenPair p B Bs x L D J t f e L₃ ∧
    ∃ e' ∈ L₂ ⊔ L₃, GGSixSeventeenDirect p Bs D (ggG0 p B x L D J) e'

end Defs

section Pair

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {t : StatedLieTag} {f : ℕ} {b : G} {L₁ : Subgroup G}

namespace GGSixSeventeenPair

theorem isComponentOf_inf (h : GGSixSeventeenPair p B Bs x L D J t f b L₁) :
    IsComponentOf L₁ (ggM p B x L D J ⊓ Subgroup.centralizer {b}) := by
  obtain ⟨-, -, ⟨hle, hsn, hq⟩, -⟩ := h
  have hle' : ggG0 p B x L D J ⊓ Subgroup.centralizer {b} ≤
      ggM p B x L D J ⊓ Subgroup.centralizer {b} :=
    inf_le_inf_right _ Subgroup.le_normalizer
  exact ⟨hle.trans hle', ggIsSubnormal_trans hsn
    (ggIsSubnormal_of_normal hle' (ggStepTwo_inf_normal _ b)), hq⟩

theorem le_ggM (h : GGSixSeventeenPair p B Bs x L D J t f b L₁) : L₁ ≤ ggM p B x L D J :=
  h.isComponentOf_inf.1.trans inf_le_left

theorem le_centralizer (h : GGSixSeventeenPair p B Bs x L D J t f b L₁) :
    L₁ ≤ Subgroup.centralizer {b} :=
  h.2.2.1.1.trans inf_le_right

theorem isComponentOf_centralizer (h : GGSixSeventeenPair p B Bs x L D J t f b L₁)
    (hsn : IsSubnormal L₁ (Subgroup.centralizer {b})) :
    IsComponentOf L₁ (Subgroup.centralizer {b}) :=
  ⟨h.le_centralizer, hsn, h.2.2.1.2.2⟩

end GGSixSeventeenPair

end Pair

section Inputs


@[expose] def GGSixSeventeenWitnessInputFor (P : StatedLieTag → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), P t →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ : Subgroup G), GGSixSeventeenPair p B Bs x L D J t f b L₁ →
        (∃ L₂ : Subgroup G, IsComponentOf L₂ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) ∧
          Nat.card (Bs ⊓ Subgroup.centralizer (L₂ : Set G) : Subgroup G) ≤ p ^ 2) ∨
        ∃ e ∈ L₁, GGSixSeventeenDirect p Bs D (ggG0 p B x L D J) e ∨
          (e ∈ Bs ∧ e ≠ 1 ∧ GGSixSeventeenSixteen p B Bs x L D J t f e)

@[expose] def GGSixSeventeenLinearTypeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ → GGSixLinearCase p t n f →
      ∀ (b : G) (L₁ : Subgroup G), GGSixSeventeenPair p B Bs x L D J t f b L₁ → GGTypeAk f L₁

theorem ggSixSeventeenWitnessInput_of_families
    (hlin : GGSixSeventeenWitnessInputFor GGLinearUnitaryTag)
    (hcl : GGSixSeventeenWitnessInputFor GGOtherClassicalTag)
    (hex : GGSixSeventeenWitnessInputFor GGExceptionalTag) :
    GGSixSeventeenWitnessInputFor fun _ => True := by
  intro G _ _ p B Bs x L D J t n f ψ _
  by_cases h₁ : GGLinearUnitaryTag t
  · exact hlin G p B Bs x L D J t n f ψ h₁
  by_cases h₂ : GGOtherClassicalTag t
  · exact hcl G p B Bs x L D J t n f ψ h₂
  exact hex G p B Bs x L D J t n f ψ ⟨h₁, h₂⟩

end Inputs

section Steps

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}


theorem ggSixSeventeenDirect_controls (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (s2 : GGSixStepTwo p B Bs x L D J) {e : G}
    (he : GGSixSeventeenDirect p Bs D (ggG0 p B x L D J) e) :
    GGControlsStrongFusion (ggM p B x L D J) (Subgroup.zpowers e) := by
  obtain ⟨heB, he1, ⟨m, hm, hmD⟩ | ⟨L₂, hL₂, hcard⟩⟩ := he
  · obtain ⟨-, -, -, -, -, -, -, hNBs⟩ := hctx.2
    refine s1.2.1.of_map_conj_le (hNBs hm) ?_
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    simpa [MulAut.conj_apply] using hmD
  · exact (s2 e heB he1 L₂ hL₂ hcard).2

theorem ggSixSeventeen_fusion_of_centralizer_le (h610 : GGSixBstarUniqueV2Input)
    (h611 : GGSixLSixElevenInput) (h612 : GGSixLSixTwelveInput) (h613t : GGSixTrialityInput)
    (hlin : GGSixSeventeenLinearTypeInput)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) {b : G} {L₁ : Subgroup G}
    (hpair : GGSixSeventeenPair p B Bs x L D J t f b L₁)
    (hC : Subgroup.centralizer {b} ≤ ggM p B x L D J) :
    GGControlsStrongFusion (ggM p B x L D J) (Subgroup.zpowers b) := by
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨-, hBs, -⟩, -, -, -, -, ⟨hBsM, -⟩, -, -⟩ := hctx.2
  have hb : orderOf b = p := orderOf_eq_prime (hBs.2 b hpair.1) hpair.2.1
  refine (ggControlsStrongFusion_zpowers_iff (hb ▸ hp)).mpr ⟨hBsM hpair.1, fun g hg => ?_⟩
  by_contra hgM
  have hZ := s1.1
  have hU := h610 G p B Bs x L D J t n f ψ hctx hZ
  rcases h611 G p B Bs x L D J t n f ψ hctx hZ hU b hpair.1 hC g hg hgM with hl | ht
  · exact (h612 G p B Bs x L D J t n f ψ hctx hZ hU b hpair.1 hC g hg hgM hl).2 L₁ hpair.2.2.1
      (hlin G p B Bs x L D J t n f ψ hctx hZ hl b L₁ hpair)
  · exact hgM (h613t G p B Bs x L D J t n f ψ hctx hZ hU
      (fun d hd hd1 => s1.2.1.centralizer_le hd hd1) b hpair.1 hC g hg ht)


end Steps

end CFSG.StandardType
