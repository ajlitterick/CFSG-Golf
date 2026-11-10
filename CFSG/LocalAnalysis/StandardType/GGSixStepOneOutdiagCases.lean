module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagInputs
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompKd
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompCentre
public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section Cases

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.zpowers_eq_of_mem (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) {d : G}
    (hdx : d ∈ Subgroup.zpowers x) (hd1 : d ≠ 1) :
    Subgroup.zpowers d = Subgroup.zpowers x := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hxB : x ∈ B := h.sstar.2.1
  have hox : orderOf x = p := orderOf_eq_prime (h.sstar.1.1.2 x hxB) h.sstar.2.2.1
  have hdD : d ∈ D := (Subgroup.zpowers_le.mpr h.x_mem_d) hdx
  have hod : orderOf d = p := orderOf_eq_prime (h.d_elem.2 d hdD) hd1
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdx) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hox, hod]

theorem GGSixCtxV2.ggKd_eq_of_mem_zpowers (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) {d : G}
    (hdx : d ∈ Subgroup.zpowers x) (hd1 : d ≠ 1) : ggKd p B x L D J d = L := by
  have hC : Subgroup.centralizer ({d} : Set G) = Subgroup.centralizer ({x} : Set G) := by
    rw [← ggCentralizer_zpowers_eq, ← ggCentralizer_zpowers_eq, h.zpowers_eq_of_mem hdx hd1]
  have hL : IsComponentOf L (ggG0 p B x L D J ⊓ Subgroup.centralizer {d}) := by
    rw [hC]
    exact CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le h.sstar.2.2.2.1
      (le_inf le_sup_left h.sstar.2.2.2.1.1) inf_le_right
  exact ggKd_eq_of_le_component hL h.j_comp.2.2 (h.j_le_inf.trans inf_le_left)


end Cases

section Inputs

@[expose] def GGSixKdNbrInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    (∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) →
      ∀ d ∈ D, d ∉ Subgroup.zpowers x →
        ¬ D ≤ Subgroup.centralizer (ggKd p B x L D J d : Set G) →
          GGNbr p B x D J d (ggKd p B x L D J d)


end Inputs

section Main


theorem ggSixInnerOnKdInput_of_nbr (hN : GGInndiagNormalInput) (hc₀ : GGFieldNbrCanonicalInput)
    (hc₁ : GGProp41Input) (hc₂ : GGCor42Input) (hnb : GGSixKdNbrInput) :
    GGSixInnerOnKdInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx h65 _ _ d hd hd1 X _ hXN _ _ hXD
  have hcfg := hctx.config
  have hAll := hc₂ G p B Bs x L D J hcfg (hc₁ G p B Bs x L D J hcfg (hc₀ G p B Bs x L D J hcfg))
  have hO : ∀ lab, LargeEvenInLambda2 lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I) :=
    fun _ hlab => largeEvenLabelAll_outdiag_simple hlab
  by_cases hdx : d ∈ Subgroup.zpowers x
  · rw [hctx.ggKd_eq_of_mem_zpowers hdx hd1] at hXN ⊢
    exact le_sup_centralizer_of_innerDiagOn hO hN hAll.1 hctx.d_le_bstar hXN hXD
  · by_cases hDK : D ≤ Subgroup.centralizer (ggKd p B x L D J d : Set G)
    · refine le_trans ?_ le_sup_right
      rw [← hXD, Subgroup.commutator_le]
      intro a ha δ hδ
      rw [commutatorElement_def]
      exact mul_mem (ggConj_mem_centralizer_of_mem_normalizer (hXN ha) (hDK hδ))
        (inv_mem (hDK hδ))
    · exact le_sup_centralizer_of_innerDiagOn hO hN
        (hAll.2 d _ (hnb G p B Bs x L D J t n f ψ hctx h65 d hd hdx hDK)) hctx.d_le_bstar hXN hXD


end Main

end CFSG.StandardType
