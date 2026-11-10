module

public import CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Quasithin.Recognition.F4Main
public import CFSG.Quasithin.Recognition.F4Index

public section

namespace CFSG.ASVolI

open CFSG.Open


open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in


open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in


open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in


open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in


open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in


open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in

section TransCompPort

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] (c : α.Completion Y)

structure burnsideF4b_TC (m : ℕ) : Prop where
  faithful : c.IsFaithful
  thick1 : 2 ≤ α.qOne
  thick2 : 2 ≤ α.qTwo
  trans : ∀ a : c.Γ, c.PathTrans a (m + 1)
  hm : 1 ≤ m

namespace burnsideF4b_TC

variable {c} {m : ℕ} (T : burnsideF4b_TC c m)

include T

theorem hval : ∀ v a b : c.Γ, ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b :=
  CFSG.ASVolI.ChF.burnsideF4a_hval T.faithful T.thick1 T.thick2

theorem f35 {a : c.Γ} {p : GPath c.graph (m + 1)} (hp : p ∈ GPath.nbPaths c.graph a (m + 1)) :
    GPath.F35Conclusion c.graph c.G0 a m p :=
  GPath.lemma_F35 T.hval (T.trans a) (CosetGeom.connected rfl)
    (fun _ _ h => CosetGeom.vtype_ne_of_adj h) T.hm hp


end burnsideF4b_TC


namespace burnsideF4b_TC


end burnsideF4b_TC

end TransCompPort

section QGroup

open CFSG.Quasithin CFSG.Quasithin.F7 CFSG.ASVolI.ChF


end QGroup

section QCompletion

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Quasithin.F7 CFSG.ASVolI.ChF


end QCompletion

section ComplementGeneral

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Quasithin.F7


end ComplementGeneral

section IndexFormula

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Quasithin.F7


end IndexFormula

section Eight

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Quasithin.F7


end Eight

section ComplPath

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Quasithin.F7


end ComplPath

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.Quasithin.F7 in

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.Quasithin.F7 in

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in


end CFSG.ASVolI
