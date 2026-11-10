module

public import CFSG.Quasithin.EmptyFaithful.S14117Star
public import CFSG.Quasithin.Background.C2Bridge
public import CFSG.Quasithin.Background.C2Seven
public import CFSG.Quasithin.Background.C2Six
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
public import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem charTwo_of_isSubnormal_of_charTwo {H K : Subgroup G} (hK : CharTwo K) (h : IsSubnormal H K) :
    CharTwo H := by
  induction h with
  | refl => exact hK
  | step hle hN _ ih => exact CFSG.Quasithin.CT.CharTwo.of_normal (ih hK) hle hN

theorem charTwo_of_inM {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) :
    CharTwo M := by
  obtain ⟨S, hS⟩ := h.exists_sylow
  have hSM : (S : Subgroup G) ≤ M := hS ▸ hM.2
  exact h.qtke.2.1 M hM.1.1 ⟨S, hSM⟩

omit [Finite G] in
theorem inf_normalizer_le_cgsIn_of_char {M R C : Subgroup G} (hCR : C ≤ R) (hC : C ≠ ⊥)
    (hchar : (C.subgroupOf R).Characteristic) :
    M ⊓ Subgroup.normalizer (C : Set G) ≤ cgsIn M R :=
  le_iSup_of_le C (le_iSup_of_le hCR (le_iSup_of_le hC (le_iSup_of_le hchar le_rfl)))

omit [Finite G] in
theorem vY_ne_bot_of_isShort2 {L : Subgroup G} (hL : IsShort2 L) : VY L ≠ ⊥ := by
  intro hVY
  obtain ⟨-, -, ⟨hUQ, hU2⟩, -, hZU, -⟩ := hL
  have hUZ : blockU L ≤ omegaOneCenterOf (pCoreOf 2 L) := fun x hx =>
    Subgroup.subset_closure ⟨hUQ hx, hU2 x hx⟩
  have hcomm : ⁅blockU L, L⁆ = ⊥ := by
    have h1 := Subgroup.commutator_mono hUZ (le_refl L)
    have h2 : ⁅omegaOneCenterOf (pCoreOf 2 L), L⁆ = ⊥ := hVY
    rw [h2] at h1
    exact le_bot_iff.mp h1
  have hUC : blockU L ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  exact hZU.not_ge (le_inf le_rfl hUC)

theorem isFaithfulLocal_of_isShort2 {T Mc M L : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hM : InM T M) (hL : L ∈ cComp M) (hB : IsShort2 L) : quasithinIsFaithfulLocal T L := by
  have hMne : pCoreOf 2 M ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hM.1.1
  have hloc : quasithinIsLocal T L :=
    isLocal_of_mem_cComp_of_sylow (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow hM.2) hMne hL
  exact isFaithfulLocal_iff_isXf.mpr ⟨hloc, ⟨ne_bot_of_mem_cComp hL,
    eq_oTwoUpper_of_perfect (perfect_of_mem_cComp hL), hB.2.1⟩, vY_ne_bot_of_isShort2 hB⟩


theorem isQuasisimple_pCore_quotient {M L : Subgroup G} {L' : Subgroup ↥M}
    (hL : L = L'.map M.subtype)
    (hK : CFSG.IsQuasisimple ↥(L'.map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥M))))
    (hsub : IsSubnormal L M) :
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hLM : L ≤ M := A4.subnormal_le hsub
  have hLmem : ∀ x : G, x ∈ L ↔ ∃ l' ∈ L', (l' : G) = x := by
    intro x
    rw [hL]
    exact Subgroup.mem_map
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥L →* OTwoQuot M, ∀ l : ↥L,
      ψ l = (QuotientGroup.mk (Subgroup.inclusion hLM l) : OTwoQuot M) :=
    ⟨(QuotientGroup.mk' (CFSG.Open.pCore 2 ↥M)).comp (Subgroup.inclusion hLM), fun l => rfl⟩
  have hPL : ∀ l : ↥L, (l : G) ∈ pCoreOf 2 L ↔ (l : G) ∈ pCoreOf 2 M := by
    intro l
    constructor
    · intro hl
      exact A4.pCoreOf_le_of_subnormal 2 hsub hl
    · intro hl
      have hnorm : L ≤ Subgroup.normalizer ((L ⊓ pCoreOf 2 M : Subgroup G) : Set G) := fun x hx =>
        Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hx, le_normalizer_pCoreOf 2 M (hLM hx)⟩
      have hle : L ⊓ pCoreOf 2 M ≤ pCoreOf 2 L :=
        le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm
          ((pCoreOf_isPGroup 2 M).to_le inf_le_right)
      exact hle ⟨l.2, hl⟩
  have hker : CFSG.pCore 2 ↥L = ψ.ker := by
    ext l
    rw [C2Six.mem_pCore_two_iff, hPL, MonoidHom.mem_ker, hψ]
    exact (mk_eq_one_iff_mem_pCoreOf (Subgroup.inclusion hLM l)).symm
  have hrange : ψ.range = L'.map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥M)) := by
    ext q
    constructor
    · rintro ⟨l, rfl⟩
      obtain ⟨l', hl', hl'l⟩ := (hLmem l).mp l.2
      refine Subgroup.mem_map.mpr ⟨l', hl', ?_⟩
      have h1 : Subgroup.inclusion hLM l = l' := Subtype.ext hl'l.symm
      exact (congrArg (QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥M)) h1.symm).trans (hψ l).symm
    · intro hq
      obtain ⟨l', hl', rfl⟩ := Subgroup.mem_map.mp hq
      exact ⟨⟨l'.1, (hLmem l'.1).mpr ⟨l', hl', rfl⟩⟩, (hψ _).trans rfl⟩
  have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      ↥(L'.map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥M))) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hK

omit [Finite G] in
theorem mem_of_mk_mem_imageOTwoQuot {M X : Subgroup G} (hOX : pCoreOf 2 M ≤ X) {z : ↥M}
    (hz : (QuotientGroup.mk z : OTwoQuot M) ∈ imageOTwoQuot M X) : (z : G) ∈ X := by
  obtain ⟨x, hx, hxX, hxz⟩ := mem_imageOTwoQuot_iff.mp hz
  have h1 : (⟨x, hx⟩ : ↥M)⁻¹ * z ∈ CFSG.Open.pCore 2 ↥M := QuotientGroup.eq.mp hxz
  have h2 : x⁻¹ * (z : G) ∈ pCoreOf 2 M := by
    unfold pCoreOf
    exact Subgroup.mem_map.mpr ⟨_, h1, rfl⟩
  have h3 : x⁻¹ * (z : G) ∈ X := hOX h2
  have e : (z : G) = x * (x⁻¹ * z) := by group
  rw [e]
  exact X.mul_mem hxX h3


end CFSG.Quasithin
