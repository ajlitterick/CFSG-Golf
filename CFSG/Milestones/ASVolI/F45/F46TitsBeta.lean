module

public import CFSG.Milestones.ASVolI.F45.F46TitsTransfer
public import CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F45.F46TitsHyp

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.F7
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

section Dihedral

variable {X V : Type*} [Group X] [MulAction X V] {Γ : SimpleGraph V} [GraphAction X Γ]


end Dihedral

section Conj

variable {G : Type*} [Group G]


end Conj

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]

structure burnsideF46_Data (c : α.Completion Y) (Qx Ql : Subgroup c.G0) : Prop where
  hyp : TitsHyp c 6
  qOne : α.qOne = 4
  qTwo : α.qTwo = 2
  qn : QNormalized Qx Ql
  qx_le : Qx ≤ stv c c.xv
  ql_le : Ql ≤ stv c c.lv
  fix_x : ∀ w, c.graph.Adj c.xv w → Qx ≤ stv c w
  fix_l : ∀ w, c.graph.Adj c.lv w → Ql ≤ stv c w
  compl_l : ∀ q ∈ GPath.nbPaths c.graph c.lv 8,
    IsComplementIn q.stabPath Ql (stv c c.lv ⊓ stv c (q 1))
  idx_x : ∀ q ∈ GPath.nbPaths c.graph c.xv 8, (q.stabPath : Subgroup c.G0) ⊓ Qx = ⊥ ∧
    (Qx ⊔ q.stabPath).relIndex (stv c c.xv ⊓ stv c (q 1)) = 2
  card_x : ∀ q ∈ GPath.nbPaths c.graph c.xv 8, Nat.card (q.stabPath : Subgroup c.G0) = 2
  nontriv_x : ∀ q ∈ GPath.nbPaths c.graph c.xv 8,
    ∃ t ∈ (q.stabPath : Subgroup c.G0), ∃ w, c.graph.Adj c.xv w ∧ t • w ≠ w
  aff : ∃ lab : ZMod 5 → c.Γ, AffLab c.G0 c.graph c.xv lab
  two_orb : burnsideF46_TwoOrb c c.lv 8

namespace burnsideF46_Data

variable {c : α.Completion Y} {Qx Ql : Subgroup c.G0} (D : burnsideF46_Data c Qx Ql)

include D

theorem hval : ∀ v a b : c.Γ, ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b := burnsideF46_hval D.hyp


end burnsideF46_Data

end CFSG.ASVolI
