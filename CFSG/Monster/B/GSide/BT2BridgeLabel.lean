module

public import CFSG.Monster.B.GSide.BT2Reduce
public import CFSG.Monster.B.GSide.TriangleData
public import CFSG.Monster.B.GSide.TwoDNative

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Amalgam

theorem exists_cvMul_triangle
    {a b c a' b' c' : CVert} (h : IsCTriangle a b c)
    (h' : IsCTriangle a' b' c') (ht : triType a b c = triType a' b' c') :
    ∃ s : Shat, cvMul a s = a' ∧ cvMul b s = b' ∧ cvMul c s = c' := by
  obtain ⟨s, hsa, hsb⟩ := cvMul_edge_transitive h.1 h'.1
  have hc : cgraph.Adj a' (cvMul c s) := by
    rw [← hsa]
    exact (cgraph_adj_cvMul _ _ _).2 h.2.1
  have ht' : triType a' b' (cvMul c s) = triType a' b' c' := by
    rw [← ht, ← triType_cvMul a b c s, hsa, hsb]
  obtain ⟨t, hta, htb, htc⟩ := exists_cvMul_eq_of_triType_eq h'.1 hc h'.2.1 ht'
  exact ⟨s * t, by rw [cvMul_mul, hsa, hta], by rw [cvMul_mul, hsb, htb], by rw [cvMul_mul, htc]⟩

theorem clabel_mul_cvMul
    (a b c : CVert) (s : Shat) :
    clabel (cvMul a s) * clabel (cvMul b s) * clabel (cvMul c s) =
      ((s : Dfull))⁻¹ * (clabel a * clabel b * clabel c) * s := by
  rw [clabel_cvMul, clabel_cvMul, clabel_cvMul]
  group

theorem exists_clabel_eq_of_isType1782
    {a b c : CVert} (h : IsType1782 a b c) :
    ∃ d : CVert, clabel a * clabel b * clabel c = clabel d := by
  obtain ⟨s, hsa, hsb, hsc⟩ :=
    exists_cvMul_triangle h.1 (isCTriangle_cu 0) (h.2.trans triType_cu.1.symm)
  obtain ⟨g', -, -, -, hg'⟩ := exists_fourth_vertex
  have hg : clabel g' = clabel cv0 * clabel cw0 * clabel (cu 0) := by
    have e := congrArg Subtype.val hg'
    simpa only [coe_clabelS, Subgroup.coe_mul] using e
  refine ⟨cvMul g' s⁻¹, ?_⟩
  rw [clabel_cvMul, hg, ← hsa, ← hsb, ← hsc, clabel_mul_cvMul]
  simp only [Subgroup.coe_inv, inv_inv]
  group

theorem isConj_clabelS_cV0
    (d : CVert) : IsConj (clabelS d) (cV0 : Shat) := by
  obtain ⟨g, rfl⟩ := cvMul_transitive cv0 d
  refine isConj_iff.2 ⟨g, ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_clabelS, clabel_cvMul, coe_cV0_dfull,
    clabel_cv0]
  group

theorem rankS_clabelS_eq
    (d : CVert) : rankS (clabelS d) = 1860 :=
  (rankS_conj (isConj_clabelS_cV0 d)).trans rankS_cV0

theorem t2D_ne_clabel
    (d : CVert) : t2D ≠ clabel d := by
  intro h
  have e : t2DS = clabelS d := Subtype.ext h
  have h1 := rankS_clabelS_eq d
  rw [← e, rankS_t2DS] at h1
  exact absurd h1 (by decide)

theorem exists_mem_cSigma_clabel
    {v : Fin 8 → ZMod 2} (hv : qPoly v = 0) :
    ∃ b ∈ cSigma 1, clabel b = cQ * Psi v := by
  obtain ⟨x, hx, hxe⟩ := mem_orbit_of_qPoly hv
  refine ⟨cvOf ⟨x⁻¹, Xgrp_le_Shat (Xgrp.inv_mem hx)⟩,
    mem_cSigma_one.2 ⟨_, Xgrp.inv_mem hx, rfl⟩, ?_⟩
  rw [clabel_cvOf]
  simpa only [inv_inv] using hxe

@[expose] def sigVert
    (v : Fin 8 → ZMod 2) : CVert :=
  if hv : qPoly v = 0 then (exists_mem_cSigma_clabel hv).choose else cv0

theorem sigVert_mem
    {v : Fin 8 → ZMod 2} (hv : qPoly v = 0) : sigVert v ∈ cSigma 1 := by
  simp only [sigVert, hv, ↓reduceDIte]
  exact (exists_mem_cSigma_clabel hv).choose_spec.1

theorem clabel_sigVert
    {v : Fin 8 → ZMod 2} (hv : qPoly v = 0) :
    clabel (sigVert v) = cQ * Psi v := by
  simp only [sigVert, hv, ↓reduceDIte]
  exact (exists_mem_cSigma_clabel hv).choose_spec.2

theorem clabel_injective_native :
    Function.Injective clabel :=
  fun _ _ h => native_global_label_bijection_and_full_vertex_centralizer.1 h

theorem sigVert_eq_iff
    {v w : Fin 8 → ZMod 2} (hv : qPoly v = 0) (hw : qPoly w = 0) :
    sigVert v = sigVert w ↔ v = w := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have e := congrArg clabel h
  rw [clabel_sigVert hv, clabel_sigVert hw] at e
  exact cPsi_injective e

theorem eq_sigVert_of_mem
    {b : CVert} (hb : b ∈ cSigma 1) :
    ∃ v : Fin 8 → ZMod 2, qPoly v = 0 ∧ b = sigVert v := by
  obtain ⟨x, hx, rfl⟩ := mem_cSigma_one.1 hb
  have hmem : (x : Dfull)⁻¹ * cQ * ((x : Dfull)⁻¹)⁻¹ ∈
      {y : Dfull | ∃ z ∈ Xgrp, z * cQ * z⁻¹ = y} := ⟨_, Xgrp.inv_mem hx, rfl⟩
  rw [orbit_cQ] at hmem
  obtain ⟨v, hv, hve⟩ := hmem
  simp only at hve
  refine ⟨v, hv, clabel_injective_native ?_⟩
  rw [clabel_sigVert hv, clabel_cvOf, hve, inv_inv]

theorem sigVert_zero :
    sigVert 0 = cv0 := by
  have h0 : qPoly (0 : Fin 8 → ZMod 2) = 0 := by decide
  refine clabel_injective_native ?_
  rw [clabel_sigVert h0, Psi_zero', mul_one, clabel_cv0]

theorem qPoly_e0 : qPoly (Pi.single 0 1 : Fin 8 → ZMod 2) = 0 := by decide

theorem sigVert_e0 :
    sigVert (Pi.single 0 1) = cw0 := by
  refine clabel_injective_native ?_
  rw [clabel_sigVert qPoly_e0, Psi_single, clabel_cw0]
  rfl

theorem commute_cQ_Psi
    (v : Fin 8 → ZMod 2) : cQ * Psi v = Psi v * cQ := by
  have h := T9S_comm cV0_mem_T9S (A8S_le_T9S (PsiS_mem_A8S v))
  have e := congrArg Subtype.val h
  simp only [Subgroup.coe_mul, coe_cV0_dfull] at e
  exact e

theorem clabel_mul_sigVert
    {u v w : Fin 8 → ZMod 2} (hu : qPoly u = 0) (hv : qPoly v = 0)
    (hw : qPoly w = 0) :
    clabel (sigVert u) * clabel (sigVert v) * clabel (sigVert w) = cQ * Psi (u + v + w) := by
  rw [clabel_sigVert hu, clabel_sigVert hv, clabel_sigVert hw, Psi_add, Psi_add]
  have hcu := commute_cQ_Psi u
  have hcv := commute_cQ_Psi v
  calc cQ * Psi u * (cQ * Psi v) * (cQ * Psi w) = cQ * (Psi u * cQ) * Psi v * (cQ * Psi w) := by
        group
    _ = cQ * (cQ * Psi u) * Psi v * (cQ * Psi w) := by rw [← hcu]
    _ = (cQ * cQ) * (Psi u * Psi v * cQ) * Psi w := by group
    _ = (cQ * cQ) * (cQ * (Psi u * Psi v)) * Psi w := by
        rw [← Psi_add, ← commute_cQ_Psi (u + v)]
    _ = cQ * (Psi u * Psi v * Psi w) := by rw [cQ_mul_self]; group

abbrev eOne : Fin 8 → ZMod 2 := Pi.single 1 1

abbrev eOnePlus : Fin 8 → ZMod 2 := Pi.single 1 1 + vPlus

theorem qPoly_eOne : qPoly eOne = 0 := by decide

theorem qPoly_eOnePlus : qPoly eOnePlus = 0 := by decide

theorem isCTriangle_tStar :
    IsCTriangle cv0 (sigVert eOne) (sigVert eOnePlus) := by
  have h0 : qPoly (0 : Fin 8 → ZMod 2) = 0 := by decide
  have hm0 : cv0 ∈ cSigma 1 := sigVert_zero ▸ sigVert_mem h0
  have hm1 := sigVert_mem qPoly_eOne
  have hm2 := sigVert_mem qPoly_eOnePlus
  have n01 : cv0 ≠ sigVert eOne := by
    rw [← sigVert_zero, Ne, sigVert_eq_iff h0 qPoly_eOne]
    decide
  have n02 : cv0 ≠ sigVert eOnePlus := by
    rw [← sigVert_zero, Ne, sigVert_eq_iff h0 qPoly_eOnePlus]
    decide
  have n12 : sigVert eOne ≠ sigVert eOnePlus := by
    rw [Ne, sigVert_eq_iff qPoly_eOne qPoly_eOnePlus]
    decide
  exact ⟨cSigma_isClique hm0 hm1 n01, cSigma_isClique hm0 hm2 n02, cSigma_isClique hm1 hm2 n12⟩

theorem clabel_mul_tStar :
    clabel cv0 * clabel (sigVert eOne) * clabel (sigVert eOnePlus) = t2D := by
  have h0 : qPoly (0 : Fin 8 → ZMod 2) = 0 := by decide
  rw [← sigVert_zero, clabel_mul_sigVert h0 qPoly_eOne qPoly_eOnePlus, t2D]
  congr 2
  decide

theorem not_isType1782_tStar :
    ¬ IsType1782 cv0 (sigVert eOne) (sigVert eOnePlus) := by
  intro h
  obtain ⟨d, hd⟩ := exists_clabel_eq_of_isType1782 h
  rw [clabel_mul_tStar] at hd
  exact t2D_ne_clabel d hd

theorem triType_tStar :
    triType cv0 (sigVert eOne) (sigVert eOnePlus) = 44352 := by
  obtain ⟨M, -⟩ := exists_rootModel cv0
  exact (triType_eq_or M isCTriangle_tStar).resolve_left
    fun h => not_isType1782_tStar ⟨isCTriangle_tStar, h⟩

theorem isType1782_of_clabel_eq
    {a b c d : CVert} (h : IsCTriangle a b c)
    (hd : clabel a * clabel b * clabel c = clabel d) : IsType1782 a b c := by
  refine ⟨h, ?_⟩
  by_contra hne
  obtain ⟨M, -⟩ := exists_rootModel a
  have ht : triType a b c = 44352 := (triType_eq_or M h).resolve_left hne
  obtain ⟨s, hsa, hsb, hsc⟩ :=
    exists_cvMul_triangle h isCTriangle_tStar (ht.trans triType_tStar.symm)
  have e := clabel_mul_cvMul a b c s
  rw [hsa, hsb, hsc, clabel_mul_tStar, hd, ← clabel_cvMul] at e
  exact t2D_ne_clabel _ e

theorem isType1782_sigVert
    {u v w : Fin 8 → ZMod 2} (hu : qPoly u = 0) (hv : qPoly v = 0)
    (hw : qPoly w = 0) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : qPoly (u + v + w) = 0) :
    IsType1782 (sigVert u) (sigVert v) (sigVert w) := by
  have h : IsCTriangle (sigVert u) (sigVert v) (sigVert w) :=
    ⟨cSigma_isClique (sigVert_mem hu) (sigVert_mem hv) ((sigVert_eq_iff hu hv).not.2 huv),
      cSigma_isClique (sigVert_mem hu) (sigVert_mem hw) ((sigVert_eq_iff hu hw).not.2 huw),
      cSigma_isClique (sigVert_mem hv) (sigVert_mem hw) ((sigVert_eq_iff hv hw).not.2 hvw)⟩
  refine isType1782_of_clabel_eq h (d := sigVert (u + v + w)) ?_
  rw [clabel_mul_sigVert hu hv hw, clabel_sigVert hs]

end CFSG.Monster.B.GSide
