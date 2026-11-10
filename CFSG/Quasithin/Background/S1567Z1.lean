module

public import CFSG.Quasithin.Background.S1567Z6
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Conj

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise


namespace S1567

section B

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem pCore_G0_le_TE (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (htriple : F6.IsGoldschmidtTripleIn (G0_153 T Mc M E s) (G1_153 T Mc M E s) (G2_153 T E)) :
    pCoreOf 2 (G0_153 T Mc M E s) ≤ TE153 T E := by
  have hTEsyl : IsSylowTwoOf (TE153 T E) (G0_153 T Mc M E s) := by
    have := htriple.2.2.2
    rwa [G1_inf_G2 c L r66 r67 gl] at this
  have hQD : pCoreOf 2 (G0_153 T Mc M E s) ≤ G0_153 T Mc M E s := pCoreOf_le 2 _
  exact A4.le_of_normal_of_isSylowTwoOf hTEsyl hQD
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hQD).mpr (le_normalizer_pCoreOf 2 _))
    (pCoreOf_isPGroup 2 _)

theorem pCore_G0_le_centralizer_F (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (htriple : F6.IsGoldschmidtTripleIn (G0_153 T Mc M E s) (G1_153 T Mc M E s) (G2_153 T E)) :
    pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (FE153 E s : Set G) := by
  have hG1D : G1_153 T Mc M E s ≤ G0_153 T Mc M E s := le_sup_left
  have hQT := pCore_G0_le_TE c L r66 r67 gl htriple
  have hQG1 : pCoreOf 2 (G0_153 T Mc M E s) ≤ G1_153 T Mc M E s := hQT.trans le_sup_right
  have hQn : G1_153 T Mc M E s ≤ Subgroup.normalizer (pCoreOf 2 (G0_153 T Mc M E s) : Set G) :=
    hG1D.trans (le_normalizer_pCoreOf 2 _)
  have hQ1 : pCoreOf 2 (G0_153 T Mc M E s) ≤ pCoreOf 2 (G1_153 T Mc M E s) :=
    le_pCoreOf_of_le_normalizer 2 hQG1 hQn (pCoreOf_isPGroup 2 _)
  rw [G1_eq_conj r66 gl, ← CFSG.QuasithinUnique.C5.conjSubgroup_pCoreOf, r66.pCore_YETE,
    CFSG.QuasithinUnique.C5.conjSubgroup_inf, CFSG.QuasithinUnique.C5.conjSubgroup_centralizer] at hQ1
  exact hQ1.trans inf_le_right

theorem TE_inf_centralizer_E_F_le (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) :
    TE153 T E ⊓ Subgroup.centralizer (E : Set G) ⊓ Subgroup.centralizer (FE153 E s : Set G) ≤
      Subgroup.centralizer (VZ T M : Set G) := by
  have hsT : s ∈ T := gl.s_mem.1
  have hTEn : T ≤ Subgroup.normalizer (TE153 T E : Set G) := T_le_normalizer_TE r66
  have hss : s * s ∈ TE153 T E := by
    rcases coset_of_relIndex_two r66.relIndex_two (T.mul_mem hsT hsT) hsT gl.s_not_mem with h | h
    · exact h
    · exact absurd (by simpa using h) gl.s_not_mem
  have hssE : s * s ∈ Subgroup.normalizer (E : Set G) := hss.2
  have hFE : conjSubgroup (FE153 E s) s = E := by
    show conjSubgroup (conjSubgroup E s) s = E
    rw [conjSubgroup_conjSubgroup]
    exact conjSubgroup_eq_iff_mem_normalizer.mpr hssE
  have hFg : ∀ g ∈ TE153 T E, conjSubgroup (FE153 E s) g = FE153 E s := by
    intro g hg
    show conjSubgroup (conjSubgroup E s) g = conjSubgroup E s
    rw [conjSubgroup_conjSubgroup]
    have hg' : s * g * s⁻¹ ∈ TE153 T E := (Subgroup.mem_normalizer_iff.mp (hTEn hsT) g).mp hg
    have : s * g = (s * g * s⁻¹) * s := by group
    rw [this, ← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.mpr hg'.2]
  by_contra hN
  set N : Subgroup G := TE153 T E ⊓ Subgroup.centralizer (E : Set G) ⊓
    Subgroup.centralizer (FE153 E s : Set G) with hNdef
  have hNT : N ≤ T := (inf_le_left.trans inf_le_left).trans inf_le_left
  have hTEN : TE153 T E ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    rw [← conjSubgroup_eq_iff_mem_normalizer, hNdef, CFSG.QuasithinUnique.C5.conjSubgroup_inf,
      CFSG.QuasithinUnique.C5.conjSubgroup_inf, CFSG.QuasithinUnique.C5.conjSubgroup_centralizer,
      CFSG.QuasithinUnique.C5.conjSubgroup_centralizer,
      conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hg),
      conjSubgroup_eq_iff_mem_normalizer.mpr hg.2, hFg g hg]
  have hsN : s ∈ Subgroup.normalizer (N : Set G) := by
    rw [← conjSubgroup_eq_iff_mem_normalizer, hNdef, CFSG.QuasithinUnique.C5.conjSubgroup_inf,
      CFSG.QuasithinUnique.C5.conjSubgroup_inf, CFSG.QuasithinUnique.C5.conjSubgroup_centralizer,
      CFSG.QuasithinUnique.C5.conjSubgroup_centralizer,
      conjSubgroup_eq_iff_mem_normalizer.mpr (hTEn hsT), hFE]
    show TE153 T E ⊓ Subgroup.centralizer (conjSubgroup E s : Set G) ⊓ Subgroup.centralizer (E : Set G) = _
    exact inf_right_comm _ _ _
  have hTN : T ≤ Subgroup.normalizer (N : Set G) := by
    intro x hx
    rcases coset_of_relIndex_two r66.relIndex_two hx hsT gl.s_not_mem with h | h
    · exact hTEN h
    · have : x = (x * s⁻¹) * s := by group
      rw [this]
      exact (Subgroup.normalizer _).mul_mem (hTEN h) hsN
  obtain ⟨q, hqN, -, -, e, he, hne⟩ := exists_central_move c L hNT hTN hN
  apply hne
  have h1 := Subgroup.mem_centralizer_iff.mp hqN.1.2 e he
  calc q * e * q⁻¹ = (e * q) * q⁻¹ := by rw [h1]
    _ = e := by group


end B

end S1567


end CFSG.Quasithin
