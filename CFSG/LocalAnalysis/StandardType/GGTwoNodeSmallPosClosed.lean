module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosFactsC
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosWeyl
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallVerifyT
public import Certificates.Data.CFSGNative.TwoNodeSmall.CheckPos
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallVerifyK

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem verifyPos_elim {Q : SPt}
    [Fact Q.pt.p.Prime] {w : PWitness} (h : verifyPos Q w = true) {C : Prop}
    (hF : Q.pt.AlphaFixed → C) (hS : ¬ Q.pt.WF → C) (hT : (∃ g ∈ Q.pt.group, IsTransv g) → C)
    (hC : Q.pt.CycleAt Q.s → C) (hO : Q.pt.bound < Nat.card Q.pt.group → C)
    (hW : CFSG.StandardType.ZS.LinWeyl Q.pt.p Q.pt.group → C) : C := by
  cases w with
  | fixed => exact hF (verifyF_sound h)
  | self_ => exact hS (verifyS_sound h)
  | transv t =>
    simp only [verifyPos, Bool.and_eq_true] at h
    exact hT (verifyT_sound (wfCheck_sound h.1) h.2)
  | cycle c =>
    simp only [verifyPos, Bool.and_eq_true] at h
    exact hC (verifyC_sound (wfCheck_sound h.1) h.2)
  | order o =>
    simp only [verifyPos, Bool.and_eq_true] at h
    exact hO (verifyO_sound (wfCheck_sound h.1) h.2)
  | weyl c =>
    simp only [verifyPos, Bool.and_eq_true] at h
    exact hW (verifyWPos_sound (wfCheck_sound h.1) h.2)


theorem verifyExcl_elim {Q : SPt} [Fact Q.pt.p.Prime] {w : PWitness} (h : verifyExcl Q w = true) {C : Prop}
    (hF : Q.pt.AlphaFixed → C) (hS : ¬ Q.pt.WF → C) (hT : (∃ g ∈ Q.pt.group, IsTransv g) → C)
    (hC : Q.pt.CycleAt Q.s → C) : C := by
  cases w with
  | fixed => exact hF (verifyF_sound h)
  | self_ => exact hS (verifyS_sound h)
  | transv t =>
    simp only [verifyExcl, verifyPos, Bool.and_eq_true] at h
    exact hT (verifyT_sound (wfCheck_sound h.1) h.2)
  | cycle c =>
    simp only [verifyExcl, verifyPos, Bool.and_eq_true] at h
    exact hC (verifyC_sound (wfCheck_sound h.1) h.2)
  | order o => simp [verifyExcl] at h
  | weyl c => simp [verifyExcl] at h


@[expose] def SPt.ClosedPosB (Q : SPt) [Fact Q.pt.p.Prime] : Prop :=
  Q.pt.AlphaFixed ∨ ¬ Q.pt.WF ∨ (∃ g ∈ Q.pt.group, IsTransv g) ∨ Q.pt.CycleAt Q.s ∨
    Q.pt.bound < Nat.card Q.pt.group ∨ CFSG.StandardType.ZS.LinWeyl Q.pt.p Q.pt.group

@[expose] def SPt.ClosedExcl (Q : SPt) [Fact Q.pt.p.Prime] : Prop :=
  Q.pt.AlphaFixed ∨ ¬ Q.pt.WF ∨ (∃ g ∈ Q.pt.group, IsTransv g) ∨ Q.pt.CycleAt Q.s


end CFSG.TwoNodeSmall
