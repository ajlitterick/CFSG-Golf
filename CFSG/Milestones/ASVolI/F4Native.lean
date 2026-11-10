module

public import CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPointSubgroup
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ModelRad
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNGen
public import CFSG.GH74.GLS.SP.Local.SPLFaith
public import CFSG.Quasithin.Recognition.CertG2TwoOuter
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctSys
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctRGD2
public import CFSG.LieType.Chevalley.LangRootRankOneTorus
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4StdTwoCls
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Orient3
public import CFSG.LocalAnalysis.EvenBN.Tits.Model.Centralizers
public import CFSG.Quasithin.Recognition.CertTwoF4AmalgamLocal
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocStd

public section

namespace CFSG.ASVolI

open CFSG.Open
section PartBurnsideF4hCl

section Generic


theorem burnsideF4h_cl_map_inf_of_ker_le {G G' : Type} [Group G] [Group G'] (f : G →* G')
    {A C : Subgroup G} (hA : f.ker ≤ A) : (A ⊓ C).map f = A.map f ⊓ C.map f := by
  refine le_antisymm (Subgroup.map_inf_le _ _ _) ?_
  rintro x ⟨⟨a, ha, rfl⟩, ⟨c, hc, hca⟩⟩
  have hk : a⁻¹ * c ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hca, inv_mul_cancel]
  have hcA : c ∈ A := by
    have := A.mul_mem ha (hA hk)
    rwa [mul_inv_cancel_left] at this
  exact ⟨c, ⟨hcA, hc⟩, hca⟩


end Generic

section Symplectic

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem burnsideF4h_cl_sp_stab_inf (K : Type) [Field K] :
    stabilizer 2 K (flag 2 K 1) ⊓ stabilizer 2 K (flag 2 K 2) = borelSubgroup 2 K := by
  ext g
  rw [Subgroup.mem_inf, mem_borelSubgroup]
  constructor
  · rintro ⟨h1, h2⟩ i hi1 hi2
    interval_cases i
    · exact h1
    · exact h2
  · intro h
    exact ⟨h 1 le_rfl (by norm_num), h 2 (by norm_num) le_rfl⟩


end Symplectic

section SymplecticRoot

open Matrix CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag


end SymplecticRoot

section SymplecticMarking

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher


end SymplecticMarking

section Linear

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag


end Linear

section LinearMarking

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank


end LinearMarking

end PartBurnsideF4hCl

section PartBurnsideF4hClU_dedup

section HypParabolics

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {ε : ℕ}


end HypParabolics

section Transport

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}


variable (h : UnitaryFieldData p f K) {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K}


end Transport

section RootGroup

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LinearGroups
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}


end RootGroup

section U4

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ASVolI.ChF.ClassicalRoots

variable {p e : ℕ} {H : Type} [Group H] (marking : Marking .U4 p e H)


end U4

section U5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ASVolI.ChF.ClassicalRoots

variable {p e : ℕ} {H : Type} [Group H] (marking : Marking .U5 p e H)


end U5

section


end

section


end

end PartBurnsideF4hClU_dedup

section PartBurnsideF4hG2

section Words

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


end Words

section NoCert

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]


end NoCert

section Basic

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]


end Basic

section Transport

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable
  {K : Type} [Field K]


end Transport

section System

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.Quasithin.H13.F431.G2 CFSG.Quasithin.H13.F431.BN

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

theorem burnsideF4h_g2_torus_eq_bot (hK : Nat.card K = 2) (i : Fin 2) :
    torus (τ := Tag.G2) K i = ⊥ := by
  have h1 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.1 h1).1
  unfold torus
  rw [eq_bot_iff]
  rintro _ ⟨t, rfl⟩
  rw [Subsingleton.elim t 1, map_one]
  exact Subgroup.one_mem _

theorem burnsideF4h_g2_faithful_two (hK : Nat.card K = 2) :
    FaithfulOnBuilding (hexQuotPre (g2Data K)).B (hexQuotPre (g2Data K)).N
      (hexQuotPre (g2Data K)).w₁ (hexQuotPre (g2Data K)).w₂ := by
  haveI := (hexQuotRGD2 (g2Data K)).cartan_normal
  refine (hexQuotRGD2 (g2Data K)).faithful (hexQuotRGD2_gen (g2Data K)) ?_
  intro g hg _
  have h0 : (⨆ i : Fin 2, torus (τ := Tag.G2) K i) = ⊥ := by
    rw [iSup_eq_bot]
    exact burnsideF4h_g2_torus_eq_bot hK
  rw [h0, Subgroup.map_bot] at hg
  exact Subgroup.mem_bot.1 hg

theorem burnsideF4h_g2_faithful (K : Type) [Field K] [Finite K] :
    FaithfulOnBuilding (hexQuotPre (g2Data K)).B (hexQuotPre (g2Data K)).N
      (hexQuotPre (g2Data K)).w₁ (hexQuotPre (g2Data K)).w₂ := by
  by_cases h2 : Nat.card K = 2
  · exact burnsideF4h_g2_faithful_two h2
  · have hlt : 1 < Nat.card K := Finite.one_lt_card
    have h3 : 3 ≤ Nat.card K := by omega
    haveI := isSimpleGroup_g2Model h3
    exact (hexQuotPre (g2Data K)).faithful_of_isSimpleGroup

@[expose] noncomputable def burnsideF4h_g2_sys (K : Type) [Field K] [Finite K] :
    RankTwoSystem (AdjointQuotient .G2 K) 6 :=
  (hexQuotPre (g2Data K)).toSystem (burnsideF4h_g2_faithful K)


theorem burnsideF4h_g2_sys_U [Finite K] :
    (burnsideF4h_g2_sys K).U = (posUnipotentSub Tag.G2 K).map (proj K) := by
  rw [posUnipotentSub_eq]
  rfl


end System

section Generic

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN


end Generic

section Sylow

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.Quasithin.H13.F431.G2 CFSG.Quasithin.H13.F431.BN

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

theorem burnsideF4h_g2_sys_U_sylow [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    ChF.IsSylowOf p (burnsideF4h_g2_sys K).U ⊤ := by
  obtain ⟨w₀, hw₀⟩ :=
    Finite.exists_max fun w : WeylGroup Tag.G2 => (coxeterSystem Tag.G2).length w
  obtain ⟨S, hS⟩ := (exceptional_ordinary_Sylow_opposition Tag.G2 K p w₀ hw₀).1
  have hU : (burnsideF4h_g2_sys K).U = (S : Subgroup ↥(adjointGroup Tag.G2 K)).map
      (mk K).toMonoidHom := by
    rw [burnsideF4h_g2_sys_U, hS, mk_toMonoidHom]
  rw [hU]
  refine ⟨le_top, S.isPGroup'.map _, ?_⟩
  rw [Subgroup.relIndex_top_right]
  have hidx : ((S : Subgroup ↥(adjointGroup Tag.G2 K)).map (mk K).toMonoidHom).index =
      (S : Subgroup ↥(adjointGroup Tag.G2 K)).index :=
    Subgroup.index_map_equiv _ (mk K)
  rw [hidx]
  exact S.not_dvd_index

end Sylow

section RootData

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


end RootData

section Normalizer

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]


end Normalizer

section


end

end PartBurnsideF4hG2

section PartBurnsideF4hG2b

section Generic

variable {G G' : Type*} [Group G] [Group G']


end Generic

section U33Perm

open CFSG.Quasithin CFSG.Sporadic.Bridge


end U33Perm

section U33

open CFSG.Quasithin CFSG.Sporadic.Bridge

set_option linter.unusedSectionVars false


end U33

section SmallModel

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG U33G u33GenPG
  g2Hom g2Hom_injective g2_derived_eq_range g2L g2L_one g2L_zero g2L_zero_eq_img g2Img_mem_range
  g2Rho g2Rho_sq g2_cover_mod two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two u33El
  g2L_mem_adjointGroup g2HomC g2IndexTwoData)

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

theorem burnsideF4h_g2_center_u33 : Subgroup.center U33G = ⊥ := by
  haveI := isSimpleGroup_u33Pres
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center U33G) with h | h
  · exact h
  · exfalso
    have hc : u33GenPG 0 ∈ Subgroup.center U33G := by rw [h]; trivial
    have := Subgroup.mem_center_iff.1 hc (u33GenPG 3)
    have h' := congrArg u33PresHom this
    simp only [map_mul, u33PresHom_genPG] at h'
    exact (by decide +kernel : u33GenP 3 * u33GenP 0 ≠ u33GenP 0 * u33GenP 3) h'

@[expose] noncomputable def burnsideF4h_g2_iota (h2 : (2 : K) = 0)
    (hk2 : ∀ c : K, c = 0 ∨ c = 1) : U33G →* ChF.G2Native.Derived K :=
  (g2Hom h2).codRestrict _ (fun x => by
    rw [g2_derived_eq_range h2 hk2]; exact ⟨x, rfl⟩)

theorem burnsideF4h_g2_iota_injective (h2 : (2 : K) = 0) (hk2 : ∀ c : K, c = 0 ∨ c = 1) :
    Function.Injective (burnsideF4h_g2_iota h2 hk2) :=
  fun a b hab => g2Hom_injective h2 (congrArg Subtype.val hab)

theorem burnsideF4h_g2_iota_surjective (h2 : (2 : K) = 0) (hk2 : ∀ c : K, c = 0 ∨ c = 1) :
    Function.Surjective (burnsideF4h_g2_iota h2 hk2) := by
  rintro ⟨d, hd⟩
  rw [g2_derived_eq_range h2 hk2] at hd
  obtain ⟨u, hu⟩ := hd
  exact ⟨u, Subtype.ext hu⟩

theorem burnsideF4h_g2_center_derived [Finite K] (hK : Nat.card K = 2) :
    Subgroup.center (ChF.G2Native.Derived K) = ⊥ := by
  have h2 := two_eq_zero_of_card_two hK
  have hk2 := eq_zero_or_eq_one_of_card_two hK
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨u, rfl⟩ := burnsideF4h_g2_iota_surjective h2 hk2 c
  have hu : u ∈ Subgroup.center U33G := by
    rw [Subgroup.mem_center_iff]
    intro v
    have := Subgroup.mem_center_iff.1 hc (burnsideF4h_g2_iota h2 hk2 v)
    exact burnsideF4h_g2_iota_injective h2 hk2 (by simpa [map_mul] using this)
  rw [burnsideF4h_g2_center_u33, Subgroup.mem_bot] at hu
  rw [hu, map_one]
  exact Subgroup.one_mem _

theorem burnsideF4h_g2_mk_derived_injective [Finite K] (hK : Nat.card K = 2) :
    Function.Injective (QuotientGroup.mk' (Subgroup.center (ChF.G2Native.Derived K))) := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', burnsideF4h_g2_center_derived hK]

theorem burnsideF4h_g2_psi_bijective [Finite K] (hK : Nat.card K = 2) :
    Function.Bijective ((QuotientGroup.mk' (Subgroup.center (ChF.G2Native.Derived K))).comp
      (burnsideF4h_g2_iota (two_eq_zero_of_card_two hK) (eq_zero_or_eq_one_of_card_two hK))) :=
  ⟨(burnsideF4h_g2_mk_derived_injective hK).comp (burnsideF4h_g2_iota_injective _ _),
    (QuotientGroup.mk'_surjective _).comp (burnsideF4h_g2_iota_surjective _ _)⟩

@[expose] noncomputable def burnsideF4h_g2_psi (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) : U33G ≃* ChF.G2Native.SmallModel K :=
  MulEquiv.ofBijective _ (burnsideF4h_g2_psi_bijective hK)

theorem burnsideF4h_g2_card_small [Finite K] (hK : Nat.card K = 2) :
    Nat.card (ChF.G2Native.SmallModel K) = 6048 :=
  (Nat.card_congr (burnsideF4h_g2_psi K hK).toEquiv).symm.trans CFSG.Quasithin.card_u33Pres

@[expose] noncomputable def burnsideF4h_g2_incl (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) : ChF.G2Native.SmallModel K →* ChF.G2Native.FullModel K :=
  QuotientGroup.lift (Subgroup.center (ChF.G2Native.Derived K))
    ((QuotientGroup.mk' (Subgroup.center (ChF.G2Native.Parent K))).comp
      (ChF.G2Native.derivedInclusion K))
    (by
      rw [burnsideF4h_g2_center_derived hK]
      intro x hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact Subgroup.one_mem _)

theorem burnsideF4h_g2_incl_mk [Finite K] (hK : Nat.card K = 2) (d : ChF.G2Native.Derived K) :
    burnsideF4h_g2_incl K hK (d : ChF.G2Native.SmallModel K) =
      ((ChF.G2Native.derivedInclusion K d : ChF.G2Native.Parent K) :
        ChF.G2Native.FullModel K) := rfl

theorem burnsideF4h_g2_incl_mem [Finite K] (hK : Nat.card K = 2)
    (L : Subgroup (ChF.G2Native.Parent K)) (s : ChF.G2Native.SmallModel K) :
    burnsideF4h_g2_incl K hK s ∈ ChF.G2Native.fullLocal K L ↔
      s ∈ ChF.G2Native.smallLocal K L := by
  have hP : Subgroup.center (ChF.G2Native.Parent K) = ⊥ := center_adjointGroup_eq_bot
  have hD := burnsideF4h_g2_center_derived hK
  induction s using QuotientGroup.induction_on with
  | H d =>
    rw [burnsideF4h_g2_incl_mk]
    unfold ChF.G2Native.fullLocal ChF.G2Native.smallLocal ChF.G2Native.derivedLocal
    constructor
    · rintro ⟨p, hp, hpd⟩
      rw [QuotientGroup.mk'_apply] at hpd
      have h1 := QuotientGroup.eq.1 hpd
      rw [hP, Subgroup.mem_bot] at h1
      have h2 : p = ChF.G2Native.derivedInclusion K d := by
        have := congrArg (fun z => p * z) h1
        simpa using this.symm
      refine ⟨d, ?_, rfl⟩
      show ChF.G2Native.derivedInclusion K d ∈ L
      rw [← h2]
      exact hp
    · rintro ⟨d', hd', hd'd⟩
      rw [QuotientGroup.mk'_apply] at hd'd
      have h1 := QuotientGroup.eq.1 hd'd
      rw [hD, Subgroup.mem_bot] at h1
      have h2 : d' = d := by
        have := congrArg (fun z => d' * z) h1
        simpa using this.symm
      refine ⟨ChF.G2Native.derivedInclusion K d, ?_, rfl⟩
      rw [← h2]
      exact hd'


theorem burnsideF4h_g2_smallLocal_bot :
    ChF.G2Native.smallLocal K ⊥ = ⊥ := by
  unfold ChF.G2Native.smallLocal ChF.G2Native.derivedLocal
  have : (⊥ : Subgroup (ChF.G2Native.Parent K)).comap (ChF.G2Native.derivedInclusion K) = ⊥ := by
    rw [eq_bot_iff]
    intro d hd
    rw [Subgroup.mem_comap, Subgroup.mem_bot] at hd
    rw [Subgroup.mem_bot]
    have h1 : ((ChF.G2Native.derivedInclusion K d : ChF.G2Native.Parent K) : ModGL Tag.G2 K) =
        ((1 : ChF.G2Native.Parent K) : ModGL Tag.G2 K) := by rw [hd]
    exact Subtype.ext h1
  rw [this, Subgroup.map_bot]

theorem burnsideF4h_g2_incl_injective [Finite K] (hK : Nat.card K = 2) :
    Function.Injective (burnsideF4h_g2_incl K hK) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro s hs
  have h1 : burnsideF4h_g2_incl K hK s ∈ ChF.G2Native.fullLocal K ⊥ := by
    rw [MonoidHom.mem_ker] at hs
    rw [hs]
    exact Subgroup.one_mem _
  rw [burnsideF4h_g2_incl_mem, burnsideF4h_g2_smallLocal_bot] at h1
  exact h1


theorem burnsideF4h_g2_incl_psi [Finite K] (hK : Nat.card K = 2) :
    (burnsideF4h_g2_incl K hK).comp (burnsideF4h_g2_psi K hK).toMonoidHom =
      (QuotientGroup.mk' (Subgroup.center (ChF.G2Native.Parent K))).comp
        (g2HomC (two_eq_zero_of_card_two hK)) := by
  ext u
  rfl

theorem burnsideF4h_g2_incl_index [Finite K] (hK : Nat.card K = 2) :
    (burnsideF4h_g2_incl K hK).range.index = 2 := by
  have h2 := two_eq_zero_of_card_two hK
  have hk2 := eq_zero_or_eq_one_of_card_two hK
  have hrange : (burnsideF4h_g2_incl K hK).range =
      (g2HomC h2).range.map (QuotientGroup.mk' (Subgroup.center (ChF.G2Native.Parent K))) := by
    ext q
    constructor
    · rintro ⟨s, rfl⟩
      obtain ⟨u, rfl⟩ := (burnsideF4h_g2_psi K hK).surjective s
      have e := congrArg (fun f => f u) (burnsideF4h_g2_incl_psi hK)
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] at e
      rw [e]
      exact ⟨g2HomC h2 u, ⟨u, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      refine ⟨burnsideF4h_g2_psi K hK u, ?_⟩
      have e := congrArg (fun f => f u) (burnsideF4h_g2_incl_psi hK)
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] at e
      rw [e]
  rw [hrange]
  have hP : Subgroup.center (ChF.G2Native.Parent K) = ⊥ := center_adjointGroup_eq_bot
  have e : ((g2HomC h2).range.map
      (QuotientGroup.mk' (Subgroup.center (ChF.G2Native.Parent K)))).index =
      (g2HomC h2).range.index :=
    Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk', hP]; exact bot_le)
  rw [e]
  exact (g2IndexTwoData h2 hk2).index_range


end SmallModel

section SmallCard

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]


end SmallCard

section


end

section


end

section


end

section


end

end PartBurnsideF4hG2b

section PartBurnsideF4hRee

section BNGeneric

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN
open scoped Pointwise

variable {X : Type} [Group X] {n : ℕ}


theorem burnsideF4h_ree_eq_one_of_conj_mem (D : RankTwoSystem X n) {g : X}
    (h : ∀ x : X, x * g * x⁻¹ ∈ D.B) : g = 1 := by
  apply D.faithful
  have key : ∀ (Pp : Subgroup X), D.B ≤ Pp → ∀ x : X,
      (Pp : Set X) * ({x} : Set X) * ({g} : Set X) = (Pp : Set X) * ({x} : Set X) := by
    intro Pp hPp x
    ext y
    constructor
    · intro hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hy
      obtain ⟨p, hp, c, hc, rfl⟩ := Set.mem_mul.1 ha
      rw [Set.mem_singleton_iff] at hb hc
      rw [hb, hc]
      exact Set.mem_mul.2 ⟨p * (x * g * x⁻¹), Pp.mul_mem hp (hPp (h x)), x, rfl, by group⟩
    · intro hy
      obtain ⟨p, hp, c, hc, rfl⟩ := Set.mem_mul.1 hy
      rw [Set.mem_singleton_iff] at hc
      rw [hc]
      refine Set.mem_mul.2 ⟨p * (x * g * x⁻¹)⁻¹ * x, Set.mem_mul.2
        ⟨p * (x * g * x⁻¹)⁻¹, Pp.mul_mem hp (Pp.inv_mem (hPp (h x))), x, rfl, rfl⟩, g, rfl, ?_⟩
      group
  intro v hv
  rcases hv with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact key D.P₁ (B_le_P D true) x
  · exact key D.P₂ (B_le_P D false) x

theorem burnsideF4h_ree_center_eq_bot (D : RankTwoSystem X n) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hc : ∀ g : X, g * z * g⁻¹ = z := fun g => by
    rw [Subgroup.mem_center_iff.1 hz g, mul_inv_cancel_right]
  have hzN : z ∈ Subgroup.normalizer (D.U : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have e : z * u * z⁻¹ = u := by
      rw [← Subgroup.mem_center_iff.1 hz u, mul_inv_cancel_right]
    rw [e]
  apply burnsideF4h_ree_eq_one_of_conj_mem D
  intro x
  rw [hc x, ← normalizer_U_eq_B D]
  exact hzN


end BNGeneric

section Transport


theorem burnsideF4h_ree_exists_quotEquiv {G : Type} [Group G] (hz : Subgroup.center G = ⊥) :
    ∃ e : G ≃* (G ⧸ Subgroup.center G), ∀ x : G, e x = (x : G ⧸ Subgroup.center G) :=
  ⟨MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center G))
    ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk', hz]),
      QuotientGroup.mk'_surjective _⟩, fun _ => rfl⟩


end Transport

local instance burnsideF4h_ree_neZero_rank : NeZero CFSG.Blueprint.Chevalley.Tag.F4.rank :=
  ⟨by decide⟩

section WeylBasic

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

variable {tag : Tag} {K : Type}
  [Field K]


end WeylBasic

section WeylTransport

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

variable
    {tag : Tag} {K : Type} [Field K]


end WeylTransport

section F4Words

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K]


end F4Words

section BNSup

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN


end BNSup

section Main

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4
  CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Quasithin.H13.F431.BN

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem burnsideF4h_ree_reeGroup_eq : reeGroup K a = F4.reeGamma K a :=
  (reeGamma_eq_reeFixedGroup (t := F4) (K := K) (a := a)).symm


theorem burnsideF4h_ree_units_subsingleton (hK : Nat.card K = 2) : Subsingleton Kˣ := by
  have h2 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  exact (Nat.card_eq_one_iff_unique.1 h2).1

theorem burnsideF4h_ree_torusGroup_eq_bot (hK : Nat.card K = 2) {τ : Tag} :
    torusGroup τ K = ⊥ := by
  haveI := burnsideF4h_ree_units_subsingleton hK
  rw [eq_bot_iff, torusGroup, Subgroup.closure_le]
  rintro _ ⟨⟨i, u⟩, rfl⟩
  rw [Subsingleton.elim u 1]
  simp [torusElt_one]

theorem burnsideF4h_ree_octH_eq_bot (hK : Nat.card K = 2) : octH K 0 = ⊥ := by
  unfold octH ReeTag.reeFixedTorus
  rw [burnsideF4h_ree_torusGroup_eq_bot hK, bot_inf_eq, Subgroup.bot_subgroupOf]

theorem burnsideF4h_ree_faithful (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    FaithfulOnBuilding ((octRGD2 hK).toPre (octGen (octRGD2 hK))).B
      ((octRGD2 hK).toPre (octGen (octRGD2 hK))).N
      ((octRGD2 hK).toPre (octGen (octRGD2 hK))).w₁
      ((octRGD2 hK).toPre (octGen (octRGD2 hK))).w₂ := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · haveI := (octRGD2 hK).cartan_normal
    have hK2 : Nat.card K = 2 := by simpa using hK
    exact (octRGD2 hK).faithful (octGen (octRGD2 hK)) (fun g hg _ => by
      rw [burnsideF4h_ree_octH_eq_bot hK2, Subgroup.mem_bot] at hg
      exact hg)
  · haveI : IsSimpleGroup (Gm K a) := isSimpleGroup_gm ha hK
    exact PreRankTwoSystem.faithful_of_isSimpleGroup _

@[expose] noncomputable def burnsideF4h_ree_system (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    RankTwoSystem (Gm K a) 8 :=
  ((octRGD2 hK).toPre (octGen (octRGD2 hK))).toSystem (burnsideF4h_ree_faithful hK)


theorem burnsideF4h_ree_center_eq_bot_of_equiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : Subgroup.center G = ⊥) : Subgroup.center H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e.symm z ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun g => by
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.1 hz (e g)
  rw [h, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot, ← MulEquiv.apply_symm_apply e z, hz', map_one]

theorem burnsideF4h_ree_center_trivial (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Subgroup.center ↥(reeGroup K a) = ⊥ := by
  let e0 : Gm K a ≃* ↥(reeGroup K a) := MulEquiv.subgroupCongr burnsideF4h_ree_reeGroup_eq.symm
  exact burnsideF4h_ree_center_eq_bot_of_equiv e0
    (burnsideF4h_ree_center_eq_bot (burnsideF4h_ree_system hK))

theorem burnsideF4h_ree_exists_iso (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ Φ : Gm K a ≃* (reeGroup K a ⧸ Subgroup.center (reeGroup K a)),
      ∀ (P : Subgroup (Gm K a)) (R : Subgroup (ModGL Tag.F4 K)),
        (∀ y : Gm K a, y ∈ P ↔ (y : ModGL F4.tag K) ∈ R) →
          centralImage (reeGroup K a) R = P.map Φ.toMonoidHom := by
  obtain ⟨q, hq⟩ := burnsideF4h_ree_exists_quotEquiv (burnsideF4h_ree_center_trivial hK)
  let e0 : Gm K a ≃* ↥(reeGroup K a) := MulEquiv.subgroupCongr burnsideF4h_ree_reeGroup_eq.symm
  refine ⟨e0.trans q, fun P R hPR => ?_⟩
  ext z
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨e0.symm g, (hPR _).2 hg, ?_⟩
    show q (e0 (e0.symm g)) = QuotientGroup.mk' _ g
    rw [MulEquiv.apply_symm_apply, hq]
    rfl
  · rintro ⟨y, hy, rfl⟩
    refine ⟨e0 y, (hPR y).1 hy, ?_⟩
    show QuotientGroup.mk' _ (e0 y) = q (e0 y)
    rw [hq]
    rfl


end Main

section LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}


end LongRoot


section ShortRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}


end ShortRoot


section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4


end

section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4


end

end PartBurnsideF4hRee

section PartBurnsideF4hInvRee

section Abstract


end Abstract

local instance burnsideF4h_invree_neZero_rank : NeZero CFSG.Blueprint.Chevalley.Tag.F4.rank :=
  ⟨by decide⟩

section WeylBasic

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

variable {tag : Tag} {K : Type}
  [Field K]


end WeylBasic

section WeylTransport

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

variable
    {tag : Tag} {K : Type} [Field K]


end WeylTransport

section F4Words

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K]


end F4Words

section WeylConj

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots

variable {tag : Tag} {K : Type}
  [Field K]


end WeylConj

section LongShort

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}


end LongShort


section LongShortB

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}


end LongShortB

section GLevel

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}


end GLevel

section GroupTools


end GroupTools

section TitsModel

open CFSG.Sporadic.Schreier.Tits

set_option linter.unusedSectionVars false


end TitsModel

section Small

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}


end Small

section Chart

open CFSG.ASVolI.ChF


end Chart

section Marking

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}


end Marking

section Final

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4


end Final

end PartBurnsideF4hInvRee

section PartBurnsideF4hTits

section LieLattice

theorem burnsideF4h_tits_isLieParabolics {X : Type} [Group X] {p : ℕ} {S H N : Subgroup X}
    (hp : IsPGroup p S) (hidx : ¬ p ∣ S.index)
    (hnorm : Subgroup.normalizer (S : Set X) ≤ S) (hSH : S ≤ H) (hSN : S ≤ N)
    (hHN : ¬ H ≤ N) (hNH : ¬ N ≤ H)
    (hlat : ∀ Y : Subgroup X, S ≤ Y → Y = S ∨ Y = H ∨ Y = N ∨ Y = ⊤) :
    ChF.IsLieParabolics p ⊤ S H N := by
  have hHtop : H ≠ ⊤ := fun h => hNH (h ▸ le_top)
  have hNtop : N ≠ ⊤ := fun h => hHN (h ▸ le_top)
  have hSH' : S ≠ H := fun h => hHN (h ▸ hSN)
  have hSN' : S ≠ N := fun h => hNH (h ▸ hSH)
  refine ⟨⟨S, ⟨le_top, hp, ?_⟩, ?_⟩, fun h => hHN (h ▸ le_rfl), ?_, fun Q => ⟨?_, ?_⟩⟩
  · rwa [Subgroup.relIndex_top_right]
  · rw [top_inf_eq]
    exact le_antisymm Subgroup.le_normalizer hnorm
  · rcases hlat (H ⊓ N) (le_inf hSH hSN) with h | h | h | h
    · exact h
    · exact absurd (inf_eq_left.1 h) hHN
    · exact absurd (inf_eq_right.1 h) hNH
    · exact absurd (inf_eq_top_iff.1 h).1 hHtop
  · rintro ⟨hSQ, -, hQtop, hmax⟩
    rcases hlat Q hSQ with rfl | rfl | rfl | rfl
    · exact absurd (hmax H (lt_of_le_of_ne hSH hSH') le_top) hHtop
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hQtop
  · rintro (rfl | rfl)
    · refine ⟨hSH, le_top, hHtop, fun R hR _ => ?_⟩
      rcases hlat R (hSH.trans hR.le) with rfl | rfl | rfl | rfl
      · exact absurd (lt_of_lt_of_le hR hSH) (lt_irrefl _)
      · exact absurd hR (lt_irrefl _)
      · exact absurd hR.le hHN
      · rfl
    · refine ⟨hSN, le_top, hNtop, fun R hR _ => ?_⟩
      rcases hlat R (hSN.trans hR.le) with rfl | rfl | rfl | rfl
      · exact absurd (lt_of_lt_of_le hR hSN) (lt_irrefl _)
      · exact absurd hR.le hNH
      · exact absurd hR (lt_irrefl _)
      · rfl

theorem burnsideF4h_tits_map_symm_map {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (A : Subgroup X) : (A.map e.toMonoidHom).map e.symm.toMonoidHom = A := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id A
  ext x
  simp

theorem burnsideF4h_tits_isLieParabolics_map {X Y : Type} [Group X] [Group Y] {p : ℕ}
    (e : X ≃* Y) {S H N : Subgroup X}
    (hp : IsPGroup p S) (hidx : ¬ p ∣ S.index)
    (hnorm : Subgroup.normalizer (S : Set X) ≤ S) (hSH : S ≤ H) (hSN : S ≤ N)
    (hHN : ¬ H ≤ N) (hNH : ¬ N ≤ H)
    (hlat : ∀ Y : Subgroup X, S ≤ Y → Y = S ∨ Y = H ∨ Y = N ∨ Y = ⊤) :
    ChF.IsLieParabolics p ⊤ (S.map e.toMonoidHom) (H.map e.toMonoidHom)
      (N.map e.toMonoidHom) := by
  refine burnsideF4h_tits_isLieParabolics (hp.map e.toMonoidHom) ?_ ?_
    (Subgroup.map_mono hSH) (Subgroup.map_mono hSN)
    (fun h => hHN ((Subgroup.map_le_map_iff_of_injective e.injective).1 h))
    (fun h => hNH ((Subgroup.map_le_map_iff_of_injective e.injective).1 h)) ?_
  · have h : (S.map e.toMonoidHom).index = S.index := Subgroup.index_map_equiv S e
    rw [h]
    exact hidx
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hnorm
  · intro Z hZ
    have hZ' : S ≤ Z.map e.symm.toMonoidHom := by
      rw [← burnsideF4h_tits_map_symm_map e S]
      exact Subgroup.map_mono hZ
    have hback : (Z.map e.symm.toMonoidHom).map e.toMonoidHom = Z :=
      burnsideF4h_tits_map_symm_map e.symm Z
    rcases hlat _ hZ' with h | h | h | h
    · exact Or.inl (by rw [← hback, h])
    · exact Or.inr (Or.inl (by rw [← hback, h]))
    · exact Or.inr (Or.inr (Or.inl (by rw [← hback, h])))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [← hback, h, Subgroup.map_top_of_surjective _ e.surjective]

end LieLattice

section ModelD

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits


theorem burnsideF4h_tits_card_SD : Nat.card titsSD = 2048 := by
  rw [card_subgroupOf_titsD titsS_le_titsD, titsQS_facts.2.2.2]

theorem burnsideF4h_tits_card_HD : Nat.card titsHD = 10240 := by
  rw [card_subgroupOf_titsD titsH_le_titsD, titsQH_facts.2.2.2]

theorem burnsideF4h_tits_card_ND : Nat.card titsND = 6144 := by
  rw [card_subgroupOf_titsD titsN_le_titsD, titsQN_facts.2.2.2]

theorem burnsideF4h_tits_SD_le_HD : titsSD ≤ titsHD := fun _ hx => titsS_le_titsH hx

theorem burnsideF4h_tits_SD_le_ND : titsSD ≤ titsND := fun _ hx => titsS_le_titsN hx

theorem burnsideF4h_tits_not_HD_le_ND : ¬ titsHD ≤ titsND := fun h => by
  have := Subgroup.card_dvd_of_le h
  rw [burnsideF4h_tits_card_HD, burnsideF4h_tits_card_ND] at this
  omega

theorem burnsideF4h_tits_not_ND_le_HD : ¬ titsND ≤ titsHD := fun h => by
  have := Subgroup.card_dvd_of_le h
  rw [burnsideF4h_tits_card_HD, burnsideF4h_tits_card_ND] at this
  omega

theorem burnsideF4h_tits_relIndex_of_card {X : Type} [Group X] {A B : Subgroup X} (h : A ≤ B)
    {a b r : ℕ} (ha : Nat.card A = a) (hb : Nat.card B = b) (ha0 : 0 < a) (hab : b = r * a) :
    A.relIndex B = r := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [inf_eq_left.2 h, ha, hb, hab] at h1
  exact Nat.eq_of_mul_eq_mul_right ha0 h1

theorem burnsideF4h_tits_relIndex_SD_HD : titsSD.relIndex titsHD = 5 :=
  burnsideF4h_tits_relIndex_of_card burnsideF4h_tits_SD_le_HD burnsideF4h_tits_card_SD
    burnsideF4h_tits_card_HD (by norm_num) (by norm_num)

theorem burnsideF4h_tits_relIndex_SD_ND : titsSD.relIndex titsND = 3 :=
  burnsideF4h_tits_relIndex_of_card burnsideF4h_tits_SD_le_ND burnsideF4h_tits_card_SD
    burnsideF4h_tits_card_ND (by norm_num) (by norm_num)

theorem burnsideF4h_tits_SD_isPGroup : IsPGroup 2 titsSD :=
  IsPGroup.of_card (n := 11) (by rw [burnsideF4h_tits_card_SD]; norm_num)

theorem burnsideF4h_tits_SD_index : ¬ 2 ∣ titsSD.index := by
  change ¬ 2 ∣ (titsS.subgroupOf titsD).index
  rw [titsS_index]
  decide

theorem burnsideF4h_tits_lie_map {X : Type} [Group X] (e : ↥titsD ≃* X) :
    ChF.IsLieParabolics 2 ⊤ (titsSD.map e.toMonoidHom) (titsHD.map e.toMonoidHom)
      (titsND.map e.toMonoidHom) :=
  burnsideF4h_tits_isLieParabolics_map e burnsideF4h_tits_SD_isPGroup burnsideF4h_tits_SD_index
    titsSD_normalizer_le burnsideF4h_tits_SD_le_HD burnsideF4h_tits_SD_le_ND
    burnsideF4h_tits_not_HD_le_ND burnsideF4h_tits_not_ND_le_HD titsD_overgroups

end ModelD

section ModelM

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits


theorem burnsideF4h_tits_Dm_perfect :
    ⁅titsD.subgroupOf twoF4M, titsD.subgroupOf twoF4M⁆ = titsD.subgroupOf twoF4M := by
  apply Subgroup.map_injective twoF4M.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le titsD_le_twoF4M]
  exact titsD_commutator

theorem burnsideF4h_tits_Dm_eq_commutator :
    titsD.subgroupOf twoF4M = ⁅(⊤ : Subgroup ↥twoF4M), (⊤ : Subgroup ↥twoF4M)⁆ := by
  apply le_antisymm
  · calc titsD.subgroupOf twoF4M = ⁅titsD.subgroupOf twoF4M, titsD.subgroupOf twoF4M⁆ :=
          burnsideF4h_tits_Dm_perfect.symm
      _ ≤ ⁅(⊤ : Subgroup ↥twoF4M), (⊤ : Subgroup ↥twoF4M)⁆ :=
          Subgroup.commutator_mono le_top le_top
  · haveI : (titsD.subgroupOf twoF4M).Normal := twoF4D_normal
    have hc2 : Nat.card (↥twoF4M ⧸ titsD.subgroupOf twoF4M) = 2 := by
      rw [← Subgroup.index_eq_card, index_titsD_twoF4M]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI hcyc : IsCyclic (↥twoF4M ⧸ titsD.subgroupOf twoF4M) := isCyclic_of_prime_card hc2
    have hcomm : commutator ↥twoF4M ≤ titsD.subgroupOf twoF4M := by
      rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
      exact ⟨⟨fun a b => hcyc.commGroup.mul_comm a b⟩⟩
    exact hcomm

theorem burnsideF4h_tits_commutator_map {G : Type} [Group G] (Γ : Subgroup G)
    (Φ : ↥Γ ≃* ↥twoF4M) :
    ((⁅Γ, Γ⁆).subgroupOf Γ).map Φ.toMonoidHom = titsD.subgroupOf twoF4M := by
  have h1 : (⁅(⊤ : Subgroup ↥Γ), (⊤ : Subgroup ↥Γ)⁆).map Γ.subtype = ⁅Γ, Γ⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hCg : (⁅Γ, Γ⁆).subgroupOf Γ = ⁅(⊤ : Subgroup ↥Γ), (⊤ : Subgroup ↥Γ)⁆ := by
    rw [← h1]
    exact Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective _
  rw [hCg, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ Φ.surjective,
    ← burnsideF4h_tits_Dm_eq_commutator]

theorem burnsideF4h_tits_commutator_equiv {G : Type} [Group G] (Γ : Subgroup G)
    (Φ : ↥Γ ≃* ↥twoF4M) :
    ∃ Θ : ↥⁅Γ, Γ⁆ ≃* ↥titsD, ∀ x : ↥⁅Γ, Γ⁆,
      ((Θ x : ↥titsD) : Equiv.Perm (Fin 1755)) =
        ((Φ ⟨x, Subgroup.commutator_le_self Γ x.2⟩ : ↥twoF4M) : Equiv.Perm (Fin 1755)) :=
  ⟨(Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self Γ)).symm.trans
    ((Φ.subgroupMap _).trans ((MulEquiv.subgroupCongr (burnsideF4h_tits_commutator_map Γ Φ)).trans
      (Subgroup.subgroupOfEquivOfLe titsD_le_twoF4M))), fun _ => rfl⟩


theorem burnsideF4h_tits_center_titsD : Subgroup.center ↥titsD = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have h := twoF4_centD (⟨x.1, titsD_le_twoF4M x.2⟩ : ↥twoF4M) (fun d hd => by
    have h1 := Subgroup.mem_center_iff.1 hx ⟨d.1, hd⟩
    apply Subtype.ext
    exact (congrArg Subtype.val h1).symm)
  have h2 := congrArg Subtype.val h
  exact Subtype.ext h2

theorem burnsideF4h_tits_center_eq_bot {X : Type} [Group X] (Φ : X ≃* ↥twoF4M) :
    Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have h1 : Φ x = 1 := twoF4_centD (Φ x) (fun d _ => by
    obtain ⟨y, rfl⟩ := Φ.surjective d
    calc Φ x * Φ y = Φ (x * y) := (map_mul Φ x y).symm
      _ = Φ (y * x) := by rw [← Subgroup.mem_center_iff.1 hx y]
      _ = Φ y * Φ x := map_mul Φ y x)
  exact Φ.injective (h1.trans (map_one Φ).symm)

theorem burnsideF4h_tits_center_eq_bot_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have h1 : e x ∈ Subgroup.center Y := Subgroup.mem_center_iff.2 fun y => by
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y']
  rw [h, Subgroup.mem_bot] at h1
  exact e.injective (h1.trans (map_one e).symm)

end ModelM

section IndexTwo

open CFSG.Quasithin

variable {M : Type*} [Group M] (d : IndexTwoLatticeData M)

theorem burnsideF4h_tits_extSub_inf_D {H : Subgroup M} (hHD : H ≤ d.D)
    {hq : d.q ∈ Subgroup.normalizer (H : Set M)} {hq2 : d.q * d.q ∈ H} :
    extSub H d.q hq hq2 ⊓ d.D = H := by
  ext x
  constructor
  · rintro ⟨hx, hxD⟩
    exact d.mem_of_mem_ext_of_mem_D hHD hx hxD
  · intro hx
    exact ⟨le_extSub hx, hHD hx⟩

theorem burnsideF4h_tits_relIndex_extSub {H : Subgroup M} (hHD : H ≤ d.D)
    {hq : d.q ∈ Subgroup.normalizer (H : Set M)} {hq2 : d.q * d.q ∈ H} :
    H.relIndex (extSub H d.q hq hq2) = 2 :=
  relIndex_extSub fun h => d.q_not_mem (hHD h)

theorem burnsideF4h_tits_D_relIndex_extSub {H : Subgroup M} (hHD : H ≤ d.D)
    {hq : d.q ∈ Subgroup.normalizer (H : Set M)} {hq2 : d.q * d.q ∈ H} :
    d.D.relIndex (extSub H d.q hq hq2) = 2 := by
  rw [← Subgroup.inf_relIndex_right, inf_comm, burnsideF4h_tits_extSub_inf_D d hHD]
  exact burnsideF4h_tits_relIndex_extSub d hHD

end IndexTwo

section Quotient

open CFSG.Blueprint CFSG.ASVolI.ChF.ExceptionalRoots

variable {G : Type} [Group G]

theorem burnsideF4h_tits_exists_derivedEquiv (Γ C : Subgroup G) (hD : ⁅Γ, Γ⁆ = C)
    (hZ : Subgroup.center ↥C = ⊥) :
    ∃ e : DerivedCentralQuotient Γ ≃* ↥C,
      ∀ x : ↥⁅Γ, Γ⁆, ((e (QuotientGroup.mk x) : ↥C) : G) = (x : G) := by
  subst hD
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot, fun x => rfl⟩

@[expose] noncomputable def burnsideF4h_tits_incl (Γ : Subgroup G)
    (eC : DerivedCentralQuotient Γ ≃* ↥⁅Γ, Γ⁆) :
    DerivedCentralQuotient Γ →* (↥Γ ⧸ Subgroup.center ↥Γ) :=
  (QuotientGroup.mk' (Subgroup.center ↥Γ)).comp
    ((Subgroup.inclusion (Subgroup.commutator_le_self Γ)).comp eC.toMonoidHom)

theorem burnsideF4h_tits_incl_mk (Γ : Subgroup G) (eC : DerivedCentralQuotient Γ ≃* ↥⁅Γ, Γ⁆)
    (heC : ∀ x : ↥⁅Γ, Γ⁆, ((eC (QuotientGroup.mk x) : ↥⁅Γ, Γ⁆) : G) = (x : G))
    (x : ↥⁅Γ, Γ⁆) :
    burnsideF4h_tits_incl Γ eC (QuotientGroup.mk x) =
      (QuotientGroup.mk (⟨(x : G), Subgroup.commutator_le_self Γ x.2⟩ : ↥Γ) :
        ↥Γ ⧸ Subgroup.center ↥Γ) := by
  show QuotientGroup.mk (Subgroup.inclusion (Subgroup.commutator_le_self Γ)
    (eC (QuotientGroup.mk x))) = _
  congr 1
  exact Subtype.ext (heC x)

theorem burnsideF4h_tits_mk_injective (Γ : Subgroup G) (hZ : Subgroup.center ↥Γ = ⊥) :
    Function.Injective (QuotientGroup.mk' (Subgroup.center ↥Γ)) :=
  (MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk', hZ])

theorem burnsideF4h_tits_incl_injective (Γ : Subgroup G) (hZ : Subgroup.center ↥Γ = ⊥)
    (eC : DerivedCentralQuotient Γ ≃* ↥⁅Γ, Γ⁆) :
    Function.Injective (burnsideF4h_tits_incl Γ eC) :=
  (burnsideF4h_tits_mk_injective Γ hZ).comp
    ((Subgroup.inclusion_injective (Subgroup.commutator_le_self Γ)).comp eC.injective)

theorem burnsideF4h_tits_map_incl (Γ : Subgroup G) (hZ : Subgroup.center ↥Γ = ⊥)
    (eC : DerivedCentralQuotient Γ ≃* ↥⁅Γ, Γ⁆)
    (heC : ∀ x : ↥⁅Γ, Γ⁆, ((eC (QuotientGroup.mk x) : ↥⁅Γ, Γ⁆) : G) = (x : G))
    (X : Subgroup G) :
    (derivedImage Γ X).map (burnsideF4h_tits_incl Γ eC) =
      (burnsideF4h_tits_incl Γ eC).range ⊓ centralImage Γ X := by
  ext y
  constructor
  · rintro ⟨q, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨⟨_, rfl⟩, ⟨⟨(x : G), Subgroup.commutator_le_self Γ x.2⟩, hx, ?_⟩⟩
    exact (burnsideF4h_tits_incl_mk Γ eC heC x).symm
  · rintro ⟨⟨q, rfl⟩, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g, hg, hgq⟩ := hy
    rw [burnsideF4h_tits_incl_mk Γ eC heC x] at hgq
    have hgx : g = ⟨(x : G), Subgroup.commutator_le_self Γ x.2⟩ :=
      burnsideF4h_tits_mk_injective Γ hZ hgq
    have hxX : (x : G) ∈ X := by
      have : (g : G) ∈ X := hg
      rw [hgx] at this
      exact this
    exact ⟨QuotientGroup.mk x, ⟨x, hxX, rfl⟩, rfl⟩

theorem burnsideF4h_tits_range_incl (Γ : Subgroup G) (eC : DerivedCentralQuotient Γ ≃* ↥⁅Γ, Γ⁆) :
    (burnsideF4h_tits_incl Γ eC).range =
      ((⁅Γ, Γ⁆).subgroupOf Γ).map (QuotientGroup.mk' (Subgroup.center ↥Γ)) := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨Subgroup.inclusion (Subgroup.commutator_le_self Γ) (eC q), (eC q).2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨eC.symm ⟨(g : G), hg⟩, ?_⟩
    show QuotientGroup.mk (Subgroup.inclusion (Subgroup.commutator_le_self Γ)
      (eC (eC.symm ⟨(g : G), hg⟩))) = _
    rw [MulEquiv.apply_symm_apply]
    rfl

theorem burnsideF4h_tits_centralImage_eq (Γ X : Subgroup G) :
    centralImage Γ X = (X.subgroupOf Γ).map (QuotientGroup.mk' (Subgroup.center ↥Γ)) := rfl

end Quotient

section DerivedTransport

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Blueprint CFSG.ASVolI.ChF.ExceptionalRoots


theorem burnsideF4h_tits_map_derived {G : Type} [Group G] (Γ X : Subgroup G)
    (Φ : ↥Γ ≃* ↥twoF4M) (Θ : ↥⁅Γ, Γ⁆ ≃* ↥titsD)
    (hΘ : ∀ x : ↥⁅Γ, Γ⁆, ((Θ x : ↥titsD) : Equiv.Perm (Fin 1755)) =
        ((Φ ⟨x, Subgroup.commutator_le_self Γ x.2⟩ : ↥twoF4M) : Equiv.Perm (Fin 1755)))
    (eC : DerivedCentralQuotient Γ ≃* ↥⁅Γ, Γ⁆)
    (heC : ∀ x : ↥⁅Γ, Γ⁆, ((eC (QuotientGroup.mk x) : ↥⁅Γ, Γ⁆) : G) = (x : G))
    {Y' : Subgroup ↥twoF4M} {Y : Subgroup (Equiv.Perm (Fin 1755))}
    (hX : (X.subgroupOf Γ).map Φ.toMonoidHom = Y')
    (hY : ∀ m : ↥twoF4M, (m : Equiv.Perm (Fin 1755)) ∈ titsD →
      (m ∈ Y' ↔ (m : Equiv.Perm (Fin 1755)) ∈ Y)) :
    (derivedImage Γ X).map (eC.trans Θ).toMonoidHom = Y.subgroupOf titsD := by
  ext d
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
  set x := Θ.symm d with hx
  have hxd : Θ x = d := by rw [hx, MulEquiv.apply_symm_apply]
  have hsymm : (eC.trans Θ).symm d = QuotientGroup.mk x := by
    rw [MulEquiv.symm_trans_apply, ← hx]
    apply eC.injective
    rw [MulEquiv.apply_symm_apply]
    exact Subtype.ext (heC x).symm
  rw [hsymm]
  have hmk : QuotientGroup.mk x ∈ derivedImage Γ X ↔ (x : G) ∈ X := by
    constructor
    · rintro ⟨x', hx', hx'x⟩
      have h1 : eC (QuotientGroup.mk x') = eC (QuotientGroup.mk x) := congrArg eC hx'x
      have h2 : (x' : G) = (x : G) := by
        have := congrArg Subtype.val h1
        rwa [heC, heC] at this
      have : (x' : G) ∈ X := hx'
      rwa [h2] at this
    · intro h
      exact ⟨x, h, rfl⟩
  rw [hmk]
  have hΦ : (x : G) ∈ X ↔ Φ ⟨x, Subgroup.commutator_le_self Γ x.2⟩ ∈ Y' := by
    rw [← hX, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact Iff.rfl
  rw [hΦ, hY _ (by rw [← hΘ]; exact (Θ x).2), ← hΘ, hxd]

end DerivedTransport

section Assembly

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Blueprint CFSG.ASVolI.ChF.ExceptionalRoots

set_option linter.unusedSectionVars false


theorem burnsideF4h_tits_mem_lattice_S (m : ↥twoF4M) (hm : (m : Equiv.Perm (Fin 1755)) ∈ titsD) :
    m ∈ twoF4Lattice.S ↔ (m : Equiv.Perm (Fin 1755)) ∈ titsS := by
  have h : twoF4Data.Sx ⊓ twoF4Data.D = twoF4Data.S := twoF4Data.toLattice_inf_D_S
  constructor
  · intro hS
    have h1 : m ∈ twoF4Data.Sx ⊓ twoF4Data.D := ⟨hS, hm⟩
    rw [h] at h1
    exact h1
  · intro hS
    exact twoF4Data.S_le_Sx hS

theorem burnsideF4h_tits_mem_lattice_P₁ (m : ↥twoF4M) (hm : (m : Equiv.Perm (Fin 1755)) ∈ titsD) :
    m ∈ twoF4Lattice.P₁ ↔ (m : Equiv.Perm (Fin 1755)) ∈ titsH := by
  have h : twoF4Data.P₁x ⊓ twoF4Data.D = twoF4Data.P₁ :=
    burnsideF4h_tits_extSub_inf_D twoF4Data twoF4Data.P₁_le_D
  constructor
  · intro hS
    have h1 : m ∈ twoF4Data.P₁x ⊓ twoF4Data.D := ⟨hS, hm⟩
    rw [h] at h1
    exact h1
  · intro hS
    show m ∈ twoF4Data.P₁x
    exact mem_extSub.2 (Or.inl hS)

theorem burnsideF4h_tits_mem_lattice_P₂ (m : ↥twoF4M) (hm : (m : Equiv.Perm (Fin 1755)) ∈ titsD) :
    m ∈ twoF4Lattice.P₂ ↔ (m : Equiv.Perm (Fin 1755)) ∈ titsN := by
  have h : twoF4Data.P₂x ⊓ twoF4Data.D = twoF4Data.P₂ :=
    burnsideF4h_tits_extSub_inf_D twoF4Data twoF4Data.P₂_le_D
  constructor
  · intro hS
    have h1 : m ∈ twoF4Data.P₂x ⊓ twoF4Data.D := ⟨hS, hm⟩
    rw [h] at h1
    exact h1
  · intro hS
    show m ∈ twoF4Data.P₂x
    exact mem_extSub.2 (Or.inl hS)

theorem burnsideF4h_tits_relIndex_D_S : (titsD.subgroupOf twoF4M).relIndex twoF4Lattice.S = 2 :=
  burnsideF4h_tits_D_relIndex_extSub twoF4Data twoF4Data.S_le_D (hq := twoF4Data.q_norm_S)
    (hq2 := twoF4Data.q_mul_self_mem_S)

theorem burnsideF4h_tits_relIndex_D_P₁ :
    (titsD.subgroupOf twoF4M).relIndex twoF4Lattice.P₁ = 2 :=
  burnsideF4h_tits_D_relIndex_extSub twoF4Data twoF4Data.P₁_le_D (hq := twoF4Data.q_norm_P₁)
    (hq2 := twoF4Data.q_mul_self_mem_P₁)

theorem burnsideF4h_tits_relIndex_D_P₂ :
    (titsD.subgroupOf twoF4M).relIndex twoF4Lattice.P₂ = 2 :=
  burnsideF4h_tits_D_relIndex_extSub twoF4Data twoF4Data.P₂_le_D (hq := twoF4Data.q_norm_P₂)
    (hq2 := twoF4Data.q_mul_self_mem_P₂)

theorem burnsideF4h_tits_relIndex_range {G : Type} [Group G] (Γ X : Subgroup G)
    (Φ : ↥Γ ≃* ↥twoF4M) (hZ : Subgroup.center ↥Γ = ⊥)
    (eC : DerivedCentralQuotient Γ ≃* ↥⁅Γ, Γ⁆) :
    (burnsideF4h_tits_incl Γ eC).range.relIndex (centralImage Γ X) =
      (titsD.subgroupOf twoF4M).relIndex ((X.subgroupOf Γ).map Φ.toMonoidHom) := by
  rw [burnsideF4h_tits_range_incl, burnsideF4h_tits_centralImage_eq,
    Subgroup.relIndex_map_map_of_injective _ _ (burnsideF4h_tits_mk_injective Γ hZ),
    ← burnsideF4h_tits_commutator_map Γ Φ,
    Subgroup.relIndex_map_map_of_injective _ _ Φ.injective]

theorem burnsideF4h_tits_assembly {G : Type} [Group G] (Γ B P₁ P₂ L Sh : Subgroup G)
    (Φ : ↥Γ ≃* ↥twoF4M)
    (hB : (B.subgroupOf Γ).map Φ.toMonoidHom = twoF4Lattice.S)
    (hP₁ : (P₁.subgroupOf Γ).map Φ.toMonoidHom = twoF4Lattice.P₁)
    (hP₂ : (P₂.subgroupOf Γ).map Φ.toMonoidHom = twoF4Lattice.P₂) :
    ChF.IsLieParabolics 2 (⊤ : Subgroup (DerivedCentralQuotient Γ))
      (derivedImage Γ B) (derivedImage Γ P₁) (derivedImage Γ P₂) ∧
    (derivedImage Γ B).relIndex (derivedImage Γ P₁) = 5 ∧
    (derivedImage Γ B).relIndex (derivedImage Γ P₂) = 3 ∧
    ∃ inclusion : DerivedCentralQuotient Γ →* (↥Γ ⧸ Subgroup.center ↥Γ),
      Function.Injective inclusion ∧ inclusion.range.index = 2 ∧
      (∀ d : ↥⁅Γ, Γ⁆, ∀ p : ↥Γ, (p : G) = d.val →
          inclusion (QuotientGroup.mk d) = QuotientGroup.mk p) ∧
      (derivedImage Γ B).map inclusion = inclusion.range ⊓ centralImage Γ B ∧
      (derivedImage Γ P₁).map inclusion = inclusion.range ⊓ centralImage Γ P₁ ∧
      (derivedImage Γ P₂).map inclusion = inclusion.range ⊓ centralImage Γ P₂ ∧
      (derivedImage Γ L).map inclusion = inclusion.range ⊓ centralImage Γ L ∧
      (derivedImage Γ Sh).map inclusion = inclusion.range ⊓ centralImage Γ Sh ∧
      ((derivedImage Γ B).map inclusion).relIndex (centralImage Γ B) = 2 ∧
      ((derivedImage Γ P₁).map inclusion).relIndex (centralImage Γ P₁) = 2 ∧
      ((derivedImage Γ P₂).map inclusion).relIndex (centralImage Γ P₂) = 2 := by
  obtain ⟨Θ, hΘ⟩ := burnsideF4h_tits_commutator_equiv Γ Φ
  have hZ' : Subgroup.center ↥⁅Γ, Γ⁆ = ⊥ :=
    burnsideF4h_tits_center_eq_bot_of_equiv Θ burnsideF4h_tits_center_titsD
  obtain ⟨eC, heC⟩ := burnsideF4h_tits_exists_derivedEquiv Γ ⁅Γ, Γ⁆ rfl hZ'
  have hZ : Subgroup.center ↥Γ = ⊥ := burnsideF4h_tits_center_eq_bot Φ
  have hBD : (derivedImage Γ B).map (eC.trans Θ).toMonoidHom = titsSD :=
    burnsideF4h_tits_map_derived Γ B Φ Θ hΘ eC heC hB burnsideF4h_tits_mem_lattice_S
  have hP₁D : (derivedImage Γ P₁).map (eC.trans Θ).toMonoidHom = titsHD :=
    burnsideF4h_tits_map_derived Γ P₁ Φ Θ hΘ eC heC hP₁ burnsideF4h_tits_mem_lattice_P₁
  have hP₂D : (derivedImage Γ P₂).map (eC.trans Θ).toMonoidHom = titsND :=
    burnsideF4h_tits_map_derived Γ P₂ Φ Θ hΘ eC heC hP₂ burnsideF4h_tits_mem_lattice_P₂
  have hback := burnsideF4h_tits_map_symm_map (eC.trans Θ)
  have hinj : Function.Injective (eC.trans Θ).toMonoidHom := (eC.trans Θ).injective
  refine ⟨?_, ?_, ?_, burnsideF4h_tits_incl Γ eC, burnsideF4h_tits_incl_injective Γ hZ eC, ?_,
    ?_, burnsideF4h_tits_map_incl Γ hZ eC heC B, burnsideF4h_tits_map_incl Γ hZ eC heC P₁,
    burnsideF4h_tits_map_incl Γ hZ eC heC P₂, burnsideF4h_tits_map_incl Γ hZ eC heC L,
    burnsideF4h_tits_map_incl Γ hZ eC heC Sh, ?_, ?_, ?_⟩
  · have h := burnsideF4h_tits_lie_map (eC.trans Θ).symm
    rwa [← hBD, ← hP₁D, ← hP₂D, hback, hback, hback] at h
  · rw [← Subgroup.relIndex_map_map_of_injective _ _ hinj, hBD, hP₁D]
    exact burnsideF4h_tits_relIndex_SD_HD
  · rw [← Subgroup.relIndex_map_map_of_injective _ _ hinj, hBD, hP₂D]
    exact burnsideF4h_tits_relIndex_SD_ND
  · rw [burnsideF4h_tits_range_incl, Subgroup.index_map_of_bijective
        ⟨burnsideF4h_tits_mk_injective Γ hZ, QuotientGroup.mk'_surjective _⟩,
      ← Subgroup.index_map_of_bijective (f := Φ.toMonoidHom) Φ.bijective,
      burnsideF4h_tits_commutator_map Γ Φ, index_titsD_twoF4M]
  · intro d p hp
    rw [burnsideF4h_tits_incl_mk Γ eC heC d]
    congr 1
    exact Subtype.ext hp.symm
  · rw [burnsideF4h_tits_map_incl Γ hZ eC heC, Subgroup.inf_relIndex_right,
      burnsideF4h_tits_relIndex_range Γ B Φ hZ eC, hB]
    exact burnsideF4h_tits_relIndex_D_S
  · rw [burnsideF4h_tits_map_incl Γ hZ eC heC, Subgroup.inf_relIndex_right,
      burnsideF4h_tits_relIndex_range Γ P₁ Φ hZ eC, hP₁]
    exact burnsideF4h_tits_relIndex_D_P₁
  · rw [burnsideF4h_tits_map_incl Γ hZ eC heC, Subgroup.inf_relIndex_right,
      burnsideF4h_tits_relIndex_range Γ P₂ Φ hZ eC, hP₂]
    exact burnsideF4h_tits_relIndex_D_P₂

end Assembly


local instance burnsideF4h_tits_neZero_rank : NeZero CFSG.Blueprint.Chevalley.Tag.F4.rank :=
  ⟨by decide⟩

section WeylBasic

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley

variable {tag : Tag} {K : Type}
  [Field K]

theorem burnsideF4h_tits_weylWordOperator_eq (word : List (Fin tag.rank)) :
    weylWordOperator tag K word =
      ((((word.map fun i => weylElt tag K i 1).reverse).prod : (Module.End K (RootModule tag K))ˣ) :
        Module.End K (RootModule tag K)) := by
  unfold weylWordOperator
  have h := map_list_prod (Units.coeHom (Module.End K (RootModule tag K)))
    ((word.map fun i => weylElt tag K i 1).reverse)
  simp only [Units.coeHom_apply, List.map_reverse, List.map_map] at h
  rw [h]
  rfl

theorem burnsideF4h_tits_rootSubgroup_le_absoluteRoot {α : Fin tag.rank → ℤ} (hα : IsRoot tag α) :
    rootSubgroup tag K α ≤ absoluteRoot tag K α := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  refine Subgroup.subset_closure ⟨(pinnedData tag α).2.2 • c, (pinnedData tag α).1,
    (pinnedData tag α).2.1.map tag.idx, pinnedWeyl tag K α, ?_, ?_, ?_⟩
  · rw [List.foldl_map]
    exact foldl_reflect_pinnedData hα
  · rw [burnsideF4h_tits_weylWordOperator_eq]
    congr 1
    unfold pinnedWeyl
    rw [List.map_map]
    rfl
  · rfl

theorem burnsideF4h_tits_absoluteTorus_eq : absoluteTorus tag K = torusGroup tag K := by
  unfold absoluteTorus torusGroup
  congr 1
  ext e
  constructor
  · rintro ⟨i, p, h⟩
    exact ⟨(i, p), (Units.ext h).symm⟩
  · rintro ⟨⟨i, p⟩, rfl⟩
    exact ⟨i, p, rfl⟩

theorem burnsideF4h_tits_relativeWeyl_eq (word : List (Fin tag.rank)) :
    relativeWeyl tag K word =
      Subgroup.zpowers ((word.map fun i => weylElt tag K i 1).reverse.prod) := by
  unfold relativeWeyl
  rw [Subgroup.zpowers_eq_closure]
  congr 1
  ext e
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [burnsideF4h_tits_weylWordOperator_eq]
  exact ⟨fun h => Units.ext h, fun h => h ▸ rfl⟩

theorem burnsideF4h_tits_comm_zero_three :
    weylElt Tag.F4 K 3 1 * weylElt Tag.F4 K 0 1 = weylElt Tag.F4 K 0 1 * weylElt Tag.F4 K 3 1 := by
  have h := prod_alternatingWord_weylElt Tag.F4 K (0 : Fin Tag.F4.rank) 3
  have e : Tag.F4.cartan 0 3 * Tag.F4.cartan 3 0 = 0 := by decide
  rw [e] at h
  simp [TauCeti.coxeterOrder_zero, CoxeterSystem.alternatingWord] at h
  exact h.symm

theorem burnsideF4h_tits_braid_one_two :
    (weylElt Tag.F4 K 2 1 * weylElt Tag.F4 K 1 1 * weylElt Tag.F4 K 2 1 * weylElt Tag.F4 K 1 1) =
      weylElt Tag.F4 K 1 1 * weylElt Tag.F4 K 2 1 * weylElt Tag.F4 K 1 1 * weylElt Tag.F4 K 2 1 := by
  have h := prod_alternatingWord_weylElt Tag.F4 K (1 : Fin Tag.F4.rank) 2
  have e : Tag.F4.cartan 1 2 * Tag.F4.cartan 2 1 = 2 := by decide
  rw [e] at h
  simp [TauCeti.coxeterOrder_two, CoxeterSystem.alternatingWord] at h
  simpa only [mul_assoc] using h.symm

end WeylBasic

section WeylTransport

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley

variable
    {tag : Tag} {K : Type} [Field K]

theorem burnsideF4h_tits_absoluteRoot_le {α : Fin tag.rank → ℤ} (hα : IsRoot tag α) :
    absoluteRoot tag K α ≤ rootSubgroup tag K α := by
  refine (Subgroup.closure_le _).2 ?_
  rintro e ⟨c, seed, word, actor, hfold, hact, he⟩
  have hactor : actor = (word.map fun i => weylElt tag K i 1).reverse.prod :=
    Units.ext (hact.trans (burnsideF4h_tits_weylWordOperator_eq word))
  have he' : e = actor * xUnit tag K seed c * actor⁻¹ := Units.ext he
  have h1 : xUnit tag K seed c ∈ rootSubgroup tag K (Pi.single seed 1) := by
    rw [← pinnedX_single]
    exact Subgroup.subset_closure ⟨c, rfl⟩
  have h2 := map_conj_prod_weylElt_rootSubgroup K word.reverse (isRoot_single tag seed)
  rw [wordProd_reverse_smul, hfold] at h2
  have h3 : e ∈ (rootSubgroup tag K (Pi.single seed 1)).map
      (MulAut.conj (word.reverse.map fun i => weylElt tag K i 1).prod).toMonoidHom := by
    refine ⟨xUnit tag K seed c, h1, ?_⟩
    rw [he', hactor, List.map_reverse]
    rfl
  rw [h2] at h3
  exact h3

theorem burnsideF4h_tits_absoluteRoot_eq {α : Fin tag.rank → ℤ} (hα : IsRoot tag α) :
    absoluteRoot tag K α = rootSubgroup tag K α :=
  le_antisymm (burnsideF4h_tits_absoluteRoot_le hα) (burnsideF4h_tits_rootSubgroup_le_absoluteRoot hα)

theorem burnsideF4h_tits_absoluteBorel_eq : absoluteBorel tag K = borelGroup tag K := by
  unfold absoluteBorel borelGroup absolutePositive posUnipotent rootSpan
  rw [sup_comm, burnsideF4h_tits_absoluteTorus_eq]
  congr 1
  exact iSup_congr fun α => iSup_congr fun hα => burnsideF4h_tits_absoluteRoot_eq hα.1

end WeylTransport

section F4Words

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution

variable
  {K : Type} [Field K]

theorem burnsideF4h_tits_weylOne_eq :
    weylOne K = weylElt Tag.F4 K 0 1 * weylElt Tag.F4 K 3 1 := by
  have hred : (coxeterSystem Tag.F4).IsReduced ([0, 3] : List (Fin Tag.F4.rank)) :=
    CFSG.LieType.Simplicity.isReduced_reeOrbitWord ReeTag.F4 (0 : Fin Tag.F4.rank)
  have h := canonicalRep_wordProd (R := K) (cs := coxeterSystem Tag.F4) hred
  have e : weylOne K =
      canonicalRep (coxeterSystem Tag.F4) K ((coxeterSystem Tag.F4).wordProd [0, 3]) := rfl
  rw [e, h]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rfl

theorem burnsideF4h_tits_weylTwo_eq :
    weylTwo K = weylElt Tag.F4 K 1 1 * weylElt Tag.F4 K 2 1 * weylElt Tag.F4 K 1 1 *
      weylElt Tag.F4 K 2 1 := by
  have hred : (coxeterSystem Tag.F4).IsReduced ([1, 2, 1, 2] : List (Fin Tag.F4.rank)) :=
    CFSG.LieType.Simplicity.isReduced_reeOrbitWord ReeTag.F4 (1 : Fin Tag.F4.rank)
  have h := canonicalRep_wordProd (R := K) (cs := coxeterSystem Tag.F4) hred
  have e : weylTwo K =
      canonicalRep (coxeterSystem Tag.F4) K ((coxeterSystem Tag.F4).wordProd [1, 2, 1, 2]) := rfl
  rw [e, h]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

theorem burnsideF4h_tits_wordUnit_zero :
    (([0, 3] : List (Fin Tag.F4.rank)).map fun i => weylElt Tag.F4 K i 1).reverse.prod =
      weylOne K := by
  rw [burnsideF4h_tits_weylOne_eq]
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.prod_cons, List.prod_nil, mul_one]
  exact burnsideF4h_tits_comm_zero_three

theorem burnsideF4h_tits_wordUnit_one :
    (([1, 2, 1, 2] : List (Fin Tag.F4.rank)).map fun i => weylElt Tag.F4 K i 1).reverse.prod =
      weylTwo K := by
  rw [burnsideF4h_tits_weylTwo_eq]
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have h := burnsideF4h_tits_braid_one_two (K := K)
  simp only [mul_assoc] at h
  exact h

end F4Words

section BN

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN

theorem burnsideF4h_tits_P_eq_sup {X : Type} [Group X] {n : ℕ} (D : RankTwoSystem X n) (i : Bool)
    {m : X} (hm : m ∈ D.N)
    (hw : ((⟨m, hm⟩ : D.N) : WeylGroup D.B D.N) = gen D.w₁ D.w₂ i) :
    P D i = D.B ⊔ Subgroup.zpowers m := by
  apply le_antisymm
  · intro x hx
    rcases (mem_P_iff D).1 hx with hB | hd
    · exact Subgroup.mem_sup_left hB
    · obtain ⟨b, hb, b', hb', rfl⟩ := (mem_dc_of_lift hw).1 hd
      exact mul_mem (mul_mem (Subgroup.mem_sup_left hb)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers m))) (Subgroup.mem_sup_left hb')
  · refine sup_le (B_le_P D i) ?_
    rw [Subgroup.zpowers_le]
    exact (mem_P_iff D).2 (Or.inr ((mem_dc_of_lift hw).2
      ⟨1, D.B.one_mem, 1, D.B.one_mem, by simp⟩))

end BN

section Main

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem burnsideF4h_tits_reeGroup_eq : reeGroup K a = F4.reeGamma K a :=
  (reeGamma_eq_reeFixedGroup (t := F4) (K := K) (a := a)).symm

theorem burnsideF4h_tits_reeBorel_eq : reeBorel K a = F4.reeFixedBorel K a := by
  unfold ChF.ExceptionalRoots.reeBorel
  rw [burnsideF4h_tits_absoluteBorel_eq, burnsideF4h_tits_reeGroup_eq]
  exact inf_comm _ _

theorem burnsideF4h_tits_reeParabolic_one :
    ChF.ExceptionalRoots.reeParabolic K a 1 =
      F4.reeFixedBorel K a ⊔ Subgroup.zpowers (weylTwo K) := by
  unfold ChF.ExceptionalRoots.reeParabolic
  rw [burnsideF4h_tits_reeBorel_eq]
  have h1 : (if (1 : Fin 2) = 0 then [0, 3] else [1, 2, 1, 2] : List (Fin Tag.F4.rank)) =
      [1, 2, 1, 2] := by decide
  rw [h1, burnsideF4h_tits_relativeWeyl_eq, burnsideF4h_tits_wordUnit_one]
  congr 1
  refine inf_eq_right.2 ?_
  refine Subgroup.zpowers_le.2 ?_
  have h : weylTwo K ∈ F4.reeGamma K a := (octR1 K a).2
  rw [burnsideF4h_tits_reeGroup_eq]
  exact h

theorem burnsideF4h_tits_reeParabolic_zero :
    ChF.ExceptionalRoots.reeParabolic K a 0 =
      F4.reeFixedBorel K a ⊔ Subgroup.zpowers (weylOne K) := by
  unfold ChF.ExceptionalRoots.reeParabolic
  rw [burnsideF4h_tits_reeBorel_eq]
  have h1 : (if (0 : Fin 2) = 0 then [0, 3] else [1, 2, 1, 2] : List (Fin Tag.F4.rank)) =
      [0, 3] := by decide
  rw [h1, burnsideF4h_tits_relativeWeyl_eq, burnsideF4h_tits_wordUnit_zero]
  congr 1
  refine inf_eq_right.2 ?_
  refine Subgroup.zpowers_le.2 ?_
  have h : weylOne K ∈ F4.reeGamma K a := (octR2 K a).2
  rw [burnsideF4h_tits_reeGroup_eq]
  exact h

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN in
theorem burnsideF4h_tits_mem_sup_iff (y : Gm K a) (r : Gm K a) :
    y ∈ (octH K a ⊔ Ug K a) ⊔ Subgroup.zpowers r ↔
      (y : ModGL F4.tag K) ∈ F4.reeFixedBorel K a ⊔ Subgroup.zpowers (r : ModGL F4.tag K) := by
  have hB : (octH K a ⊔ Ug K a).map (F4.reeGamma K a).subtype = F4.reeFixedBorel K a := by
    rw [sup_octH_Ug]
    exact Subgroup.map_subgroupOf_eq_of_le reeFixedBorel_le_reeGamma
  rw [← Subgroup.mem_map_iff_mem (F4.reeGamma K a).subtype_injective, Subgroup.map_sup, hB,
    MonoidHom.map_zpowers]
  rfl

end Main

section BNZero

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem burnsideF4h_tits_units_subsingleton (hK : Nat.card K = 2) : Subsingleton Kˣ := by
  have h2 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  exact (Nat.card_eq_one_iff_unique.1 h2).1

theorem burnsideF4h_tits_torusGroup_eq_bot (hK : Nat.card K = 2) {τ : Tag} :
    torusGroup τ K = ⊥ := by
  haveI := burnsideF4h_tits_units_subsingleton hK
  rw [eq_bot_iff, torusGroup, Subgroup.closure_le]
  rintro _ ⟨⟨i, u⟩, rfl⟩
  rw [Subsingleton.elim u 1]
  simp [torusElt_one]

theorem burnsideF4h_tits_octH_eq_bot (hK : Nat.card K = 2) : octH K 0 = ⊥ := by
  unfold octH ReeTag.reeFixedTorus
  rw [burnsideF4h_tits_torusGroup_eq_bot hK, bot_inf_eq, Subgroup.bot_subgroupOf]

@[expose] noncomputable def burnsideF4h_tits_system (hK : Nat.card K = 2) :
    RankTwoSystem (Gm K 0) 8 :=
  haveI hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  haveI := (octRGD2 hK').cartan_normal
  ((octRGD2 hK').toPre (octGen (octRGD2 hK'))).toSystem
    ((octRGD2 hK').faithful (octGen (octRGD2 hK')) (fun g hg _ => by
      rw [burnsideF4h_tits_octH_eq_bot hK, Subgroup.mem_bot] at hg
      exact hg))

end BNZero

section YamNoSimple

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Sec53F.Yam
open scoped Pointwise

theorem burnsideF4h_tits_eq_one_of_conj_mem {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n)
    {g : X} (h : ∀ x : X, x * g * x⁻¹ ∈ D.B) : g = 1 := by
  apply D.faithful
  have key : ∀ (Pp : Subgroup X), D.B ≤ Pp → ∀ x : X,
      (Pp : Set X) * ({x} : Set X) * ({g} : Set X) = (Pp : Set X) * ({x} : Set X) := by
    intro Pp hPp x
    ext y
    constructor
    · intro hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hy
      obtain ⟨p, hp, c, hc, rfl⟩ := Set.mem_mul.1 ha
      rw [Set.mem_singleton_iff] at hb hc
      rw [hb, hc]
      exact Set.mem_mul.2 ⟨p * (x * g * x⁻¹), Pp.mul_mem hp (hPp (h x)), x, rfl, by group⟩
    · intro hy
      obtain ⟨p, hp, c, hc, rfl⟩ := Set.mem_mul.1 hy
      rw [Set.mem_singleton_iff] at hc
      rw [hc]
      refine Set.mem_mul.2 ⟨p * (x * g * x⁻¹)⁻¹ * x, Set.mem_mul.2
        ⟨p * (x * g * x⁻¹)⁻¹, Pp.mul_mem hp (Pp.inv_mem (hPp (h x))), x, rfl, rfl⟩, g, rfl, ?_⟩
      group
  intro v hv
  rcases hv with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact key D.P₁ (B_le_P D true) x
  · exact key D.P₂ (B_le_P D false) x

theorem burnsideF4h_tits_noNormal {X : Type} [Group X] [Finite X] {n : ℕ} (D : RankTwoSystem X n)
    (hU : IsSylowTwoOf D.U ⊤) (R : Subgroup X) (hR : R.Normal) (h2 : IsPGroup 2 R) : R = ⊥ := by
  have hidx : ¬ 2 ∣ D.U.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hU.2.2
  let S : Sylow 2 X := hU.2.1.toSylow hidx
  have hUR : D.U ≤ Subgroup.normalizer (R : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hR]
    exact le_top
  have hsup : IsPGroup 2 (R ⊔ D.U : Subgroup X) := h2.to_sup_of_normal_left' hU.2.1 hUR
  have hRU : R ≤ D.U := le_sup_left.trans (S.is_maximal' hsup le_sup_right).le
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  apply burnsideF4h_tits_eq_one_of_conj_mem D
  intro x
  exact D.U_le_B (hRU (hR.conj_mem r hr x))

theorem burnsideF4h_tits_yamStd {X : Type} [Group X] [Finite X] {n : ℕ} (D : RankTwoSystem X n)
    (hU : IsSylowTwoOf D.U ⊤) : YamStd X D.U D.P₁ D.P₂ where
  sylow := hU
  no_normal := burnsideF4h_tits_noNormal D hU
  ne := P₁_ne_P₂ D
  le₀ := (normalizer_U_eq_B D).le.trans (B_le_P D true)
  le₁ := (normalizer_U_eq_B D).le.trans (B_le_P D false)
  coatom₀ := isCoatom_P D true
  coatom₁ := isCoatom_P D false
  above := fun _ hA hne => over_of_ne_top D ((normalizer_U_eq_B D).symm.le.trans hA) hne
  twoLoc₀ := ⟨Q D true, Q_ne_bot D hU true, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P D true),
    (normalizer_Q D hU true).symm⟩
  twoLoc₁ := ⟨Q D false, Q_ne_bot D hU false, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P D false),
    (normalizer_Q D hU false).symm⟩

end YamNoSimple

section YamZero

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem burnsideF4h_tits_mem_P₁_iff (hK : Nat.card K = 2) (y : Gm K 0) :
    y ∈ (burnsideF4h_tits_system hK).P₁ ↔
      (y : ModGL F4.tag K) ∈ ChF.ExceptionalRoots.reeParabolic K 0 1 := by
  haveI hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  have hm : octR1 K 0 ∈ (burnsideF4h_tits_system hK).N := (octRGD2 hK').r₁_mem_N
  rw [burnsideF4h_tits_reeParabolic_one]
  have hP := burnsideF4h_tits_P_eq_sup (burnsideF4h_tits_system hK) true (m := octR1 K 0) hm rfl
  show y ∈ CFSG.Quasithin.H13.F431.BN.P (burnsideF4h_tits_system hK) true ↔ _
  rw [hP]
  exact burnsideF4h_tits_mem_sup_iff y (octR1 K 0)

theorem burnsideF4h_tits_mem_P₂_iff (hK : Nat.card K = 2) (y : Gm K 0) :
    y ∈ (burnsideF4h_tits_system hK).P₂ ↔
      (y : ModGL F4.tag K) ∈ ChF.ExceptionalRoots.reeParabolic K 0 0 := by
  haveI hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  have hm : octR2 K 0 ∈ (burnsideF4h_tits_system hK).N := (octRGD2 hK').r₂_mem_N
  rw [burnsideF4h_tits_reeParabolic_zero]
  have hP := burnsideF4h_tits_P_eq_sup (burnsideF4h_tits_system hK) false (m := octR2 K 0) hm rfl
  show y ∈ CFSG.Quasithin.H13.F431.BN.P (burnsideF4h_tits_system hK) false ↔ _
  rw [hP]
  exact burnsideF4h_tits_mem_sup_iff y (octR2 K 0)

theorem burnsideF4h_tits_yamPair (hK : Nat.card K = 2) :
    CFSG.Quasithin.IsYAmalgamPair (Ug K 0) (burnsideF4h_tits_system hK).P₁
      (burnsideF4h_tits_system hK).P₂ := by
  haveI hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  haveI : Finite (Gm K 0) := Subtype.finite
  exact (burnsideF4h_tits_yamStd (burnsideF4h_tits_system hK) (isSylowTwoOf_Ug hK')).isYAmalgamPair

end YamZero

section Model

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.RuType CFSG.Sporadic.Schreier.Tits
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Quasithin.H13.F431.TwoF4

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime]

@[expose] noncomputable def burnsideF4h_tits_modelEquiv (hK : Nat.card K = 2) :
    Gm K 0 ≃* ↥twoF4M :=
  haveI : Fact (Nat.card K = 2) := ⟨hK⟩
  ((reeFixedEquivReeGamma K 0).symm.trans (titsIso (K := K))).trans
    (MulEquiv.subgroupCongr twoF4M_eq_titsA.symm)

theorem burnsideF4h_tits_key (hK : Nat.card K = 2) :
    ∃ Φ : Gm K 0 ≃* ↥twoF4M, (Ug K 0).map Φ.toMonoidHom = twoF4Lattice.S ∧
      (((burnsideF4h_tits_system hK).P₁.map Φ.toMonoidHom = twoF4Lattice.P₁ ∧
        (burnsideF4h_tits_system hK).P₂.map Φ.toMonoidHom = twoF4Lattice.P₂) ∨
       ((burnsideF4h_tits_system hK).P₁.map Φ.toMonoidHom = twoF4Lattice.P₂ ∧
        (burnsideF4h_tits_system hK).P₂.map Φ.toMonoidHom = twoF4Lattice.P₁)) := by
  have hY := burnsideF4h_tits_yamPair hK
  let φ := burnsideF4h_tits_modelEquiv hK
  have hpair' := IsYAmalgamPair.map φ hY
  obtain ⟨ρ, hρ⟩ := exists_mulEquiv_map_sylow twoF4Lattice.isSylowTwoOf_top hpair'.1
  let f : Gm K 0 ≃* ↥twoF4M := φ.trans ρ
  have hmap : ∀ M : Subgroup (Gm K 0),
      (M.map φ.toMonoidHom).map ρ.toMonoidHom = M.map f.toMonoidHom := fun M =>
    Subgroup.map_map _ _ _
  have hUf : (Ug K 0).map f.toMonoidHom = twoF4Lattice.S := by
    rw [← hmap]
    exact hρ
  have hpairf := IsYAmalgamPair.map ρ hpair'
  rw [hρ, hmap, hmap] at hpairf
  have hlocal : ∀ M : Subgroup (Gm K 0),
      (M = (burnsideF4h_tits_system hK).P₁ ∨ M = (burnsideF4h_tits_system hK).P₂) →
      (M.map f.toMonoidHom = twoF4Lattice.P₁ ∨ M.map f.toMonoidHom = twoF4Lattice.P₂) := by
    intro M hM
    obtain ⟨hmax, hnorm⟩ := (hpairf.2.2 (M.map f.toMonoidHom)).2
      (by rcases hM with rfl | rfl <;> simp)
    exact twoF4Lattice.eq_P₁_or_P₂_of_maxTwoLocal hmax (Subgroup.le_normalizer.trans hnorm)
  have hne : (burnsideF4h_tits_system hK).P₁.map f.toMonoidHom ≠
      (burnsideF4h_tits_system hK).P₂.map f.toMonoidHom := fun h =>
    hY.2.1 (Subgroup.map_injective f.injective h)
  refine ⟨f, hUf, ?_⟩
  rcases hlocal _ (Or.inl rfl) with h1 | h1 <;> rcases hlocal _ (Or.inr rfl) with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

end Model

section Orient

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem burnsideF4h_tits_reeLocalParabolic_zero :
    F4.reeLocalParabolic K a ⟨0, by decide⟩ =
      F4.reeFixedBorel K a ⊔ Subgroup.zpowers (weylOne K) := by
  rw [← F4.reeParabolic_singleton (K := K) (a := a) (j := ⟨0, by decide⟩)]
  unfold ReeTag.reeParabolic
  rw [Set.image_singleton, ← Subgroup.zpowers_eq_closure]

theorem burnsideF4h_tits_rankOneGroupOne_le (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneGroupOne K a ≤ F4.reeLocalParabolic K a ⟨0, by decide⟩ := by
  rw [rankOneGroupOne, Subgroup.closure_le]
  rintro g ((hg | hT) | rfl)
  · exact reeFixedBorel_le_reeGamma_inf_parabolicSubgroup _
      (reeFixedPosUnipotent_le_reeFixedBorel (reeFixedOrbitUnipotent_le_reeFixedPosUnipotent _ hg))
  · exact reeFixedBorel_le_reeGamma_inf_parabolicSubgroup _
      (reeFixedTorus_le_reeFixedBorel (rankOneTorusOne_le hK hT))
  · exact canonicalRep_fixedOrbitElement_mem_reeGamma_inf _

theorem burnsideF4h_tits_three_dvd_P₂ (hK : Nat.card K = 2) :
    3 ∣ Nat.card (burnsideF4h_tits_system hK).P₂ := by
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  have hR : (rankOneGroupOne K 0).subgroupOf (F4.reeGamma K 0) ≤
      (burnsideF4h_tits_system hK).P₂ := by
    intro y hy
    rw [burnsideF4h_tits_mem_P₂_iff hK y, burnsideF4h_tits_reeParabolic_zero,
      ← burnsideF4h_tits_reeLocalParabolic_zero]
    exact burnsideF4h_tits_rankOneGroupOne_le hK' (Subgroup.mem_subgroupOf.1 hy)
  have hc : Nat.card ((rankOneGroupOne K 0).subgroupOf (F4.reeGamma K 0)) = 6 := by
    have h1 := card_rankOneGroupOne (K := K) (a := 0) hK'
    have h2 := Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (rankOneGroupOne_le_reeGamma hK')).toEquiv
    exact h2.trans (h1.trans (by norm_num))
  have h := Subgroup.card_dvd_of_le hR
  rw [hc] at h
  exact dvd_trans (by norm_num) h

end Orient

section OrientModel

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits

set_option linter.unusedSectionVars false


theorem burnsideF4h_tits_card_lattice_P₁ : Nat.card twoF4Lattice.P₁ = 20480 := by
  have h1 : twoF4Data.P₁.relIndex twoF4Data.P₁x = 2 :=
    burnsideF4h_tits_relIndex_extSub twoF4Data twoF4Data.P₁_le_D (hq := twoF4Data.q_norm_P₁)
      (hq2 := twoF4Data.q_mul_self_mem_P₁)
  have h2 := Subgroup.relIndex_mul_card (H := twoF4Data.P₁) (K := twoF4Data.P₁x)
  have hle : twoF4Data.P₁ ≤ twoF4Data.P₁x :=
    le_extSub (hq := twoF4Data.q_norm_P₁) (hq2 := twoF4Data.q_mul_self_mem_P₁)
  rw [inf_eq_left.2 hle, h1] at h2
  have h3 : Nat.card twoF4Data.P₁ = 10240 := by
    show Nat.card (titsH.subgroupOf twoF4M) = 10240
    rw [card_subgroupOf_eq titsH_le_twoF4M, titsQH_facts.2.2.2]
  rw [h3] at h2
  show Nat.card twoF4Data.P₁x = 20480
  omega

end OrientModel

section OrientKey

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin
  CFSG.Sporadic.Schreier.Tits

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem burnsideF4h_tits_keyOriented (hK : Nat.card K = 2) :
    ∃ Φ : Gm K 0 ≃* ↥twoF4M, (Ug K 0).map Φ.toMonoidHom = twoF4Lattice.S ∧
      (burnsideF4h_tits_system hK).P₁.map Φ.toMonoidHom = twoF4Lattice.P₁ ∧
      (burnsideF4h_tits_system hK).P₂.map Φ.toMonoidHom = twoF4Lattice.P₂ := by
  obtain ⟨Φ, hU, h | h⟩ := burnsideF4h_tits_key hK
  · exact ⟨Φ, hU, h⟩
  · exfalso
    have h3 := burnsideF4h_tits_three_dvd_P₂ hK
    rw [← Subgroup.card_map_of_injective (f := Φ.toMonoidHom) Φ.injective, h.2,
      burnsideF4h_tits_card_lattice_P₁] at h3
    norm_num at h3

theorem burnsideF4h_tits_map_trans {A B C : Type} [Group A] [Group B] [Group C] (e : A ≃* B)
    (f : B ≃* C) (X : Subgroup A) :
    X.map (e.trans f).toMonoidHom = (X.map e.toMonoidHom).map f.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem burnsideF4h_tits_mem_Ug_iff (hK : Nat.card K = 2) (y : Gm K 0) :
    y ∈ Ug K 0 ↔ (y : ModGL F4.tag K) ∈ reeBorel K 0 := by
  have h1 : y ∈ Ug K 0 ↔ y ∈ (F4.reeFixedBorel K 0).subgroupOf (F4.reeGamma K 0) := by
    rw [← sup_octH_Ug, burnsideF4h_tits_octH_eq_bot hK, bot_sup_eq]
  rw [h1, Subgroup.mem_subgroupOf, burnsideF4h_tits_reeBorel_eq]
  exact Iff.rfl

theorem burnsideF4h_tits_gammaEquiv (hK : Nat.card K = 2) :
    ∃ Φ : ↥(reeGroup K 0) ≃* ↥twoF4M,
      ((reeBorel K 0).subgroupOf (reeGroup K 0)).map Φ.toMonoidHom = twoF4Lattice.S ∧
      ((reeParabolic K 0 1).subgroupOf (reeGroup K 0)).map Φ.toMonoidHom = twoF4Lattice.P₁ ∧
      ((reeParabolic K 0 0).subgroupOf (reeGroup K 0)).map Φ.toMonoidHom = twoF4Lattice.P₂ := by
  obtain ⟨Φ, hU, hP₁, hP₂⟩ := burnsideF4h_tits_keyOriented hK
  let e1 : ↥(reeGroup K 0) ≃* Gm K 0 := MulEquiv.subgroupCongr burnsideF4h_tits_reeGroup_eq
  have hB0 : ((reeBorel K 0).subgroupOf (reeGroup K 0)).map e1.toMonoidHom = Ug K 0 := by
    ext y
    rw [Subgroup.mem_map_equiv, burnsideF4h_tits_mem_Ug_iff hK y]
    exact Iff.rfl
  have hP₁0 : ((reeParabolic K 0 1).subgroupOf (reeGroup K 0)).map e1.toMonoidHom =
      (burnsideF4h_tits_system hK).P₁ := by
    ext y
    rw [Subgroup.mem_map_equiv, burnsideF4h_tits_mem_P₁_iff hK y]
    exact Iff.rfl
  have hP₂0 : ((reeParabolic K 0 0).subgroupOf (reeGroup K 0)).map e1.toMonoidHom =
      (burnsideF4h_tits_system hK).P₂ := by
    ext y
    rw [Subgroup.mem_map_equiv, burnsideF4h_tits_mem_P₂_iff hK y]
    exact Iff.rfl
  refine ⟨e1.trans Φ, ?_, ?_, ?_⟩
  · rw [burnsideF4h_tits_map_trans, hB0, hU]
  · rw [burnsideF4h_tits_map_trans, hP₁0, hP₁]
  · rw [burnsideF4h_tits_map_trans, hP₂0, hP₂]

end OrientKey

section


theorem burnsideF4h_titsParentAssembly (K : Type) [Field K] [Finite K] [CharP K 2] :
    ChF.NativeFrame.titsParentAssemblyGoal K := by
  intro hscope
  haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := ‹CharP K 2›
  have hK : Nat.card K = 2 := by simpa [ChF.ExceptionalRoots.ReeScope] using hscope
  obtain ⟨Φ, hB, hP₁, hP₂⟩ := burnsideF4h_tits_gammaEquiv hK
  exact burnsideF4h_tits_assembly _ _ _ _ _ _ Φ hB hP₁ hP₂

end


section InvChart

open CFSG.ASVolI.ChF


end InvChart

section InvModel

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Blueprint CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LocalAnalysis.EvenBN.Tits.Model

set_option linter.unusedSectionVars false


end InvModel

section WordAppend

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {tag : Tag} {K : Type}
  [Field K]


end WordAppend

section WeylConj

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots

variable {tag : Tag} {K : Type}
  [Field K]


end WeylConj

section LongShort

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}


end LongShort


section LongShortB

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}


end LongShortB

section InvGamma

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4 CFSG.LocalAnalysis.EvenBN.TwoF4

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime]


end InvGamma

section InvMain

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin

set_option linter.unusedSectionVars false


end InvMain

section


end

end PartBurnsideF4hTits

section PartBurnsideF4hTri

section Weyl

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots

variable {τ : Tag} {K : Type} [Field K]


end Weyl

section RootGroups

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots

variable {τ : Tag} {K : Type} [Field K]


end RootGroups

section Triality

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots

local instance burnsideF4h_tri_neZeroRankD4 : NeZero Tag.D4.rank := ⟨by decide⟩

local instance burnsideF4h_tri_neZeroRankD4tag : NeZero TwistTag.D4.tag.rank := ⟨by decide⟩


section Reps

variable {K : Type} [Field K]


end Reps

section Commute

variable {K : Type} [Field K]


end Commute

section Borel

variable {K : Type} [Field K]


end Borel

section Parabolics

variable {K : Type} [Field K]


end Parabolics

end Triality

section Quotient

open CFSG.Blueprint CFSG.ASVolI.ChF.ExceptionalRoots

variable {M : Type} [Group M]

theorem burnsideF4h_tri_exists_derivedEquiv (Γ C : Subgroup M) (hD : ⁅Γ, Γ⁆ = C)
    (hZ : Subgroup.center ↥C = ⊥) :
    ∃ e : DerivedCentralQuotient Γ ≃* ↥C,
      ∀ x : ↥⁅Γ, Γ⁆, ((e (QuotientGroup.mk x) : ↥C) : M) = (x : M) := by
  subst hD
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot, fun x => rfl⟩

theorem burnsideF4h_tri_map_derivedImage (Γ C P : Subgroup M) (hD : ⁅Γ, Γ⁆ = C)
    (e : DerivedCentralQuotient Γ ≃* ↥C)
    (he : ∀ x : ↥⁅Γ, Γ⁆, ((e (QuotientGroup.mk x) : ↥C) : M) = (x : M)) :
    (derivedImage Γ P).map e.toMonoidHom = P.subgroupOf C := by
  ext y
  constructor
  · rintro ⟨q, ⟨x, hx, rfl⟩, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have hxP : (x : M) ∈ P := hx
    exact (he x).symm ▸ hxP
  · intro hy
    have hyP : (y : M) ∈ P := hy
    have hyD : (y : M) ∈ ⁅Γ, Γ⁆ := hD ▸ y.2
    refine ⟨QuotientGroup.mk ⟨(y : M), hyD⟩, ⟨⟨(y : M), hyD⟩, hyP, rfl⟩, ?_⟩
    exact Subtype.ext (he ⟨(y : M), hyD⟩)

end Quotient

section Scope

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots

variable {K : Type} [Field K] [Finite K]

theorem burnsideF4h_tri_twisted_eq {p d : ℕ} (hp : p.Prime) (hd : 1 ≤ d)
    (hK : Nat.card K = (p ^ d) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ d)) :
    twistedFixedGroup TwistTag.D4 K σ.toRingHom =
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  have hchar : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
      (k := d * 3) (by omega) (by rw [hK, pow_mul])
  have hpar : ringChar K = 2 ∨ ∃ n, Odd n ∧ ∀ c, σ c = c ^ n := by
    rcases hp.eq_two_or_odd' with h2 | hodd
    · exact Or.inl (by rw [ringChar.eq K p, h2])
    · exact Or.inr ⟨p ^ d, hodd.pow, hσ⟩
  exact twistedFixedGroup_eq_graphFixedRootGroup_triality σ hσ3 hpar

theorem burnsideF4h_tri_commutator_eq {p d : ℕ} (hp : p.Prime) (hd : 1 ≤ d)
    (hK : Nat.card K = (p ^ d) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ d)) :
    ⁅graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom⁆ =
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  by_cases h2 : ringChar K = 2
  · have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
    have hq2 : 2 ≤ p ^ d := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 ≤ 2 ^ 3 := by norm_num
        _ ≤ (p ^ d) ^ 3 := Nat.pow_le_pow_left hq2 3
    exact commutator_graphFixedRootGroup_triality_char_two h2 σ hσ3 h4
  · exact (odd_diagram_fixed_root_group_perfect TwistTag.D4 K h2 σ).1


end Scope

section Lattice

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable {K : Type} [Field K]


end Lattice

section LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots

local instance burnsideF4h_tri_neZeroRankD4' : NeZero Tag.D4.rank := ⟨by decide⟩


variable {K : Type} [Field K]


end LongRoot


section Transport


end Transport

section Embedding

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots

variable {K : Type} [Field K] [Finite K]

theorem burnsideF4h_tri_exists_embedding {p d : ℕ} (hp : p.Prime) (hd : 1 ≤ d)
    (hK : Nat.card K = (p ^ d) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ d)) :
    ∃ f : DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ.toRingHom) →*
        ModGL TwistTag.D4.tag K,
      Function.Injective f ∧ f.range = graphFixedRootGroup TwistTag.D4 K σ.toRingHom ∧
      ∀ P : Subgroup (ModGL TwistTag.D4.tag K),
        (derivedImage (twistedFixedGroup TwistTag.D4 K σ.toRingHom) P).map f =
          P ⊓ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  have hΓ := burnsideF4h_tri_twisted_eq hp hd hK σ hσ
  have hD : ⁅twistedFixedGroup TwistTag.D4 K σ.toRingHom,
      twistedFixedGroup TwistTag.D4 K σ.toRingHom⁆ =
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rw [hΓ]
    exact burnsideF4h_tri_commutator_eq hp hd hK σ hσ
  obtain ⟨e, he⟩ := burnsideF4h_tri_exists_derivedEquiv _ _ hD
    (exceptional_fixed_center_trivial TwistTag.D4 K σ)
  refine ⟨(graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype.comp e.toMonoidHom,
    Subtype.coe_injective.comp e.injective, ?_, fun P => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · rw [← Subgroup.map_map, burnsideF4h_tri_map_derivedImage _ _ P hD e he,
      Subgroup.subgroupOf_map_subtype]

end Embedding

section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots


end

end PartBurnsideF4hTri

section PartBurnsideF4hInvD4

section Abstract

open CFSG.ASVolI.ChF

variable {C : Type} [Group C]


variable {E : Type} [Group E] {core : Subgroup E}


end Abstract

section Weyl

set_option linter.unusedSectionVars false

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots

variable {τ : Tag} {K : Type} [Field K]


end Weyl

section RootGroups

set_option linter.unusedSectionVars false

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots

variable {τ : Tag} {K : Type} [Field K]


end RootGroups

open CFSG.Blueprint CFSG.Blueprint.Chevalley in
local instance burnsideF4h_invd4_neZeroRankD4 : NeZero Tag.D4.rank := ⟨by decide⟩

open CFSG.Blueprint CFSG.Blueprint.Chevalley in
local instance burnsideF4h_invd4_neZeroRankD4tag : NeZero TwistTag.D4.tag.rank := ⟨by decide⟩

section Triality

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots


section Reps


end Reps

section Commute


end Commute

end Triality

section Quotient

open CFSG.Blueprint CFSG.ASVolI.ChF.ExceptionalRoots


end Quotient

section Words


open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


end Words

section Model


open CFSG.ASVolI.ChF CFSG.Quasithin.H13.F431.D4q.Struct CFSG.Quasithin.H13.F431.D4q.Loc
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


section RootTraces

open CFSG.ASVolI.ChF.ExceptionalRoots CFSG.ComponentClassification.RankTwoExceptional.D4


end RootTraces

end Model

section


open CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ExceptionalRoots CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.Quasithin.H13.F431.D4q.Loc CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley in

end

end PartBurnsideF4hInvD4

section PartBurnsideF4hAsm


end PartBurnsideF4hAsm


section


end

section


end

section


end

section


end

section


end

end CFSG.ASVolI
