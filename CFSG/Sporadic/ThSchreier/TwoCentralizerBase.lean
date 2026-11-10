
module

public meta import CFSG.Sporadic.ThSchreier.OrbitCheck819Base
public meta import CFSG.Sporadic.Th.Max3.PacketBase
public import CFSG.Sporadic.ThSchreier.TwoCentralizerInputs
public meta import CFSG.Sporadic.ThSchreier.WordsBase
public meta import CFSG.Sporadic.ThSchreier.LocalDataBase

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

@[expose] def tupleLetters {G : Type*} [Group G] (u : List G) (l : ℤ) : G :=
  if 0 < l then u.getD (l.toNat - 1) 1 else (u.getD ((-l).toNat - 1) 1)⁻¹

@[expose] def InvOK (R : Array V4) : Prop :=
  eqRows (mulRows R (invRows R)) idRows = true ∧ (invRows R).size = 248 ∧
    ∀ r ∈ invRows R, r.wf = true

theorem kWord_letters : ∀ l ∈ kWord, l = 1 ∨ l = 2 := by decide

theorem foldl_twoRowsStep_prefix (ws : List (List ℤ)) (Rs : List (Array V4)) :
    ∃ T, ws.foldl twoRowsStep Rs = Rs ++ T := by
  induction ws generalizing Rs with
  | nil => exact ⟨[], by simp⟩
  | cons w ws ih =>
    obtain ⟨T, hT⟩ := ih (twoRowsStep Rs w)
    exact ⟨_ :: T, by rw [List.foldl_cons, hT, twoRowsStep, List.append_assoc]; rfl⟩

end CFSG.Sporadic.ThSchreier
