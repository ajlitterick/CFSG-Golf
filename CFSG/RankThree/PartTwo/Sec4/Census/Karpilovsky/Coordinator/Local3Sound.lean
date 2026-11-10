module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3Check
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.Blueprint
open scoped Matrix

section Push


end Push

section Spec

variable {M V : Type} [Inhabited M] {O : Ops M V} {p d : Nat} (Sp : OpsSpec O p d)
  (S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p)))

include Sp


end Spec

section Words

variable {M V : Type} [Inhabited M] {O : Ops M V} {p d : Nat} (Sp : OpsSpec O p d)
  {G : Type*} [Group G] (φ : G →* Matrix (Fin d) (Fin d) (ZMod p))

include Sp


end Words

section Orbit

variable {M V : Type} [Inhabited M] [Inhabited V] {O : Ops M V}

theorem strictInc_nodup {l : List Nat} (h : strictInc l = true) : l.Nodup := by
  have hc : List.IsChain (· < ·) l := by
    induction l with
    | nil => exact List.isChain_nil
    | cons a l ih =>
      cases l with
      | nil => exact List.isChain_singleton a
      | cons b l =>
        simp only [strictInc, Bool.and_eq_true, decide_eq_true_eq] at h
        exact List.IsChain.cons_cons h.1 (ih h.2)
  exact (List.isChain_iff_pairwise.1 hc).imp (fun h => h.ne)


end Orbit

section Main


end Main

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
