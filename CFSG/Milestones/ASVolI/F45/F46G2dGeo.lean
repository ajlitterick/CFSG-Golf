module

public import CFSG.Milestones.ASVolI.F45.TitsLoc
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoFacts46
public import CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.F7
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]

@[expose] def burnsideF46_g2d_TwoOrb (c : α.Completion Y) (u : c.Γ) (n : ℕ) : Prop :=
  ∃ q₁ ∈ GPath.nbPaths c.graph u n, ∃ q₂ ∈ GPath.nbPaths c.graph u n,
    GPath.nbPaths c.graph u n = pathOrbit (stv c u) q₁ ∪ pathOrbit (stv c u) q₂ ∧
    Disjoint (pathOrbit (stv c u) q₁) (pathOrbit (stv c u) q₂) ∧
    Nat.card ↥(pathOrbit (stv c u) q₁) = Nat.card ↥(pathOrbit (stv c u) q₂)

section Smul

variable {c : α.Completion Y}


end Smul

structure burnsideF46_g2d_Data (c : α.Completion Y) (Qx Ql : Subgroup c.G0) : Prop where
  faithful : c.IsFaithful
  qOne : α.qOne = 2
  qTwo : α.qTwo = 2
  transX : c.PathTrans c.xv 6
  transL : c.PathTrans c.lv 5
  qn : QNormalized Qx Ql
  qx_le : Qx ≤ stv c c.xv
  ql_le : Ql ≤ stv c c.lv
  fix_x : ∀ w, c.graph.Adj c.xv w → Qx ≤ stv c w
  fix_l : ∀ w, c.graph.Adj c.lv w → Ql ≤ stv c w
  compl_l : ∀ q ∈ GPath.nbPaths c.graph c.lv 6,
    IsComplementIn q.stabPath Ql (stv c c.lv ⊓ stv c (q 1))
  idx_x : ∀ q ∈ GPath.nbPaths c.graph c.xv 6, (q.stabPath : Subgroup c.G0) ⊓ Qx = ⊥ ∧
    (Qx ⊔ q.stabPath).relIndex (stv c c.xv ⊓ stv c (q 1)) = 2
  card_x : ∀ q ∈ GPath.nbPaths c.graph c.xv 6, Nat.card (q.stabPath : Subgroup c.G0) = 1
  invol_x : ∀ g ∈ stv c c.xv, g * g = 1 → ∀ w, c.graph.Adj c.xv w → g • w = w
  two_orb : burnsideF46_g2d_TwoOrb c c.lv 6

namespace burnsideF46_g2d_Data

variable {c : α.Completion Y} {Qx Ql : Subgroup c.G0} (D : burnsideF46_g2d_Data c Qx Ql)

include D

theorem hval : ∀ v a b : c.Γ, ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b :=
  burnsideF4a_hval D.faithful (by rw [D.qOne]) (by rw [D.qTwo])


end burnsideF46_g2d_Data

end CFSG.ASVolI
