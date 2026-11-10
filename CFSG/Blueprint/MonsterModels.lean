module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Monster.Generated.Data
public import CFSG.Monster.Griess.AutFinite
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.Blueprint.NativeSporadic

inductive MonsterModel where
  | gmat
  | griess
  | y443Derived
  | tauCeti
  deriving DecidableEq

@[expose] def MonsterModel.Carrier : MonsterModel → Type
  | .gmat => CFSG.Monster.Generated.Gmat
  | .griess => CFSG.Monster.Griess.AutO
  | .y443Derived => M
  | .tauCeti => TauCeti.SporadicName.M.Group

noncomputable instance MonsterModel.carrierGroup (m : MonsterModel) : Group m.Carrier := by
  cases m <;> dsimp [MonsterModel.Carrier] <;> infer_instance

@[expose] def selectCarrier (m : MonsterModel) : TauCeti.SporadicName → Type
  | .M => m.Carrier
  | s => Carrier s

noncomputable instance selectCarrierGroup (m : MonsterModel) (s : TauCeti.SporadicName) :
    Group (selectCarrier m s) := by
  cases s <;> dsimp [selectCarrier] <;> infer_instance


end CFSG.Blueprint.NativeSporadic
