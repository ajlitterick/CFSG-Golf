module

public import CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Quasithin.Recognition.F4Apart
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigFinal
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnGlue
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5Rec
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2F48Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qF48Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctRGD2
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Rec

public section

namespace CFSG.ASVolI

open CFSG.Open


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
structure burnsideF48_TC {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] (c : α.Completion Y)
    (m : ℕ) : Prop where
  faithful : c.IsFaithful
  thick1 : 2 ≤ α.qOne
  thick2 : 2 ≤ α.qTwo
  trans : ∀ a : c.Γ, c.PathTrans a (m + 1)
  hm : 1 ≤ m

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_TC.hval {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y}
    {m : ℕ} (T : burnsideF48_TC c m) : ∀ v a b : c.Γ, ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b :=
  CFSG.ASVolI.ChF.burnsideF4a_hval T.faithful T.thick1 T.thick2


open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in

open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in


open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in


open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in


open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg CFSG.LieType.BorelTits Matrix
  CFSG.Quasithin.H13.F431.Un in

open CFSG.Blueprint CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.BN
  CFSG.Quasithin.H13.F431.D4q.F48 CFSG.Quasithin.H13.F48Rig CFSG.Quasithin.H13.F431.F48Rig
  CFSG.QuasithinUnique CFSG.LieType.Universal.Unitary CFSG.GH74.BNPair CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.Quasithin.H13.F431.Un in

open CFSG.Blueprint CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.BN
  CFSG.Quasithin.H13.F431.D4q.F48 CFSG.Quasithin.H13.F48Rig CFSG.Quasithin.H13.F431.F48Rig
  CFSG.QuasithinUnique CFSG.Open CFSG.LieType.Universal.Unitary CFSG.Quasithin.H13.F431.Un in


section G2


end G2

section D4


end D4

section F4


end F4


section


end


end CFSG.ASVolI
