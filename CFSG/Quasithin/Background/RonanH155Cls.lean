module

public import CFSG.Quasithin.Background.RonanH155Chain
public import CFSG.Quasithin.Background.RonanH154Hyp
public import CFSG.Quasithin.Background.HMathieuPred
public import CFSG.Quasithin.Background.RonanH143ConjA
public import CFSG.Quasithin.Background.RonanH155Gen

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH155

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin.H.ModChk CFSG.QuasithinUnique.Setup.X1
  CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163 CFSG.Quasithin.RonanH154


@[expose] def WitOK (l : List PG2) (w : List (PG2 × ℕ)) : Prop :=
  (∀ p ∈ w, p.1 ∈ subprods l ∧ p.1 ≠ 1 ∧ p.2 < 2 ^ 10 ∧ actP2 p.1 p.2 = p.2) ∧
    nodupB (combos (w.map Prod.snd)) 0 = true

instance (l : List PG2) (w : List (PG2 × ℕ)) : Decidable (WitOK l w) := by
  unfold WitOK
  infer_instance


@[expose] def Alt4Prop (l : List PG2) (w : List (PG2 × ℕ)) : Prop :=
  (fixMasks 10 actP2 l).length = 2 ^ 3 ∧ WitOK l w ∧ w.length = 9 ∧
    ((subprods l).filter (fun s => koL155.contains s)).Nodup ∧
    ((subprods l).filter (fun s => koL155.contains s)).length = 2 ^ 3

instance (l : List PG2) (w : List (PG2 × ℕ)) : Decidable (Alt4Prop l w) := by
  unfold Alt4Prop
  infer_instance


@[expose] def Alt2bProp (l : List PG2) (w : List (PG2 × ℕ)) : Prop :=
  (fixMasks 10 actP2 l).length = 2 ^ 2 ∧ WitOK l w ∧ w.length = 10

instance (l : List PG2) (w : List (PG2 × ℕ)) : Decidable (Alt2bProp l w) := by
  unfold Alt2bProp
  infer_instance


end CFSG.Quasithin.RonanH155
