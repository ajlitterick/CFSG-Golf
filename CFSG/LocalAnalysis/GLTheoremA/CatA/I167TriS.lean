module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167TriSLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167TriLab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167TriJCard
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144OutD4Two
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144OutTD4Two
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144Card
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup LieSemisimpleCent LieOrderBridge)
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind FieldKind)
open CFSG.StandardType (GGLabelRigidInput)

set_option linter.unusedSectionVars false


theorem out167_D4two_false (hB : LieOrderBridge) {S : Type} [Group S] [Finite S]
    (hcen : Subgroup.center S = ⊥)
    (hlab : HasLabel S (fun l : GLALabel => l = (⟨.D, 4, 1⟩ : GLALabel))) {β : MulAut S}
    (hβ3 : β ^ 3 = 1) (hnin : ¬ InnDiagKind S (⟨.D, 4, 1⟩ : GLALabel) β)
    (hnfld : ¬ FieldKind S (⟨.D, 4, 1⟩ : GLALabel) β) {Jb : Subgroup S}
    (hJ : GLAPComponent 3 (fixSubgroup β) Jb) (hcat : Type167Grp 3 (PSimple 3 Jb)) : False := by
  have h1 := K144.card_fix_le_D4two hcen hlab hβ3 hnin hnfld
  have h2 := K144.card_pSimple_le_fix hJ
  have h3 := card_gt_of_type167 hB hcat
  omega

theorem out167_TD4two_false (hB : LieOrderBridge) {S : Type} [Group S] [Finite S]
    (hcen : Subgroup.center S = ⊥) {β : MulAut S} (hβ3 : β ^ 3 = 1)
    (hfld : FieldKind S (⟨.triD4, 0, 1⟩ : GLALabel) β) {Jb : Subgroup S}
    (hJ : GLAPComponent 3 (fixSubgroup β) Jb) (hcat : Type167Grp 3 (PSimple 3 Jb)) : False := by
  have h1 := K144.card_fix_le_TD4two hcen hβ3 hfld
  have h2 := K144.card_pSimple_le_fix hJ
  have h3 := card_gt_of_type167 hB hcat
  omega

theorem out167_D4_false (hRig : GGLabelRigidInput) (hLSC : LieSemisimpleCent)
    (hB : LieOrderBridge) {S : Type} [Group S] [Finite S] (hcen : Subgroup.center S = ⊥)
    {labK : GLALabel} (hlab : HasLabel S (fun l : GLALabel => l = labK)) (htag : labK.tag = .D)
    (hrk : labK.rank = 4) {β : MulAut S} (hβ3 : β ^ 3 = 1) (hnin : ¬ InnDiagKind S labK β)
    (hnfld : ¬ FieldKind S labK β) {Jb : Subgroup S} (hJ : GLAPComponent 3 (fixSubgroup β) Jb)
    (hcat : Type167Grp 3 (PSimple 3 Jb)) : False := by
  obtain ⟨t, r, m⟩ := labK
  simp only at htag hrk
  subst htag hrk
  by_cases hβ1 : β = 1
  · subst hβ1
    have h2 := canon167_of_trivial hRig hcen hlab hJ hcat
    simp [canonLabel, Type167Canon] at h2
  · by_cases hn : 2 ≤ m
    · obtain ⟨labJ, hlabJ, hc⟩ := exists_label_component_167 hLSC hcen hlab hn hβ3 hβ1 hJ hcat
      exact not_type167Canon_of_triJLabel
        (triOuterD4_label hRig hcen hn hlab hβ3 hnin hnfld hlabJ hJ) hc
    · have hn1 : m = 1 := by
        have := (CanonSubcomp.lambda2_of_hasLabel hlab).1
        simp only at this
        omega
      subst hn1
      exact out167_D4two_false hB hcen hlab hβ3 hnin hnfld hJ hcat

theorem out167_triD4_false (hRig : GGLabelRigidInput) (hLSC : LieSemisimpleCent)
    (hB : LieOrderBridge) {S : Type} [Group S] [Finite S] (hcen : Subgroup.center S = ⊥)
    {labK : GLALabel} (hlab : HasLabel S (fun l : GLALabel => l = labK))
    (htag : labK.tag = .triD4) {β : MulAut S} (hβ3 : β ^ 3 = 1) (hfld : FieldKind S labK β)
    {Jb : Subgroup S} (hJ : GLAPComponent 3 (fixSubgroup β) Jb)
    (hcat : Type167Grp 3 (PSimple 3 Jb)) : False := by
  by_cases hβ1 : β = 1
  · subst hβ1
    have h2 := canon167_of_trivial hRig hcen hlab hJ hcat
    obtain ⟨t, r, m⟩ := labK
    simp only at htag
    subst htag
    simp [canonLabel, Type167Canon] at h2
  · by_cases hn : 2 ≤ labK.n
    · obtain ⟨labJ, hlabJ, hc⟩ := exists_label_component_167 hLSC hcen hlab hn hβ3 hβ1 hJ hcat
      exact not_type167Canon_of_triJLabel
        (triFieldTD4_label hRig hcen htag hn hfld hβ3 hlabJ hJ) hc
    · have hlam := CanonSubcomp.lambda2_of_hasLabel hlab
      obtain ⟨t, r, m⟩ := labK
      simp only at htag hn
      subst htag
      have hr : r = 0 := hlam.2
      have hm : m = 1 := by
        have := hlam.1
        simp only at this
        omega
      subst hr hm
      exact out167_TD4two_false hB hcen hβ3 hfld hJ hcat

end CFSG.LocalAnalysis.GLTheoremA.I167

end
