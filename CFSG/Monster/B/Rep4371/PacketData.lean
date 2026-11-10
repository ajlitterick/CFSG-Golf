module

public import CFSG.Monster.B.Rep4371.Records
public import CFSG.Monster.B.Rep4371.RawOrder
public import CFSG.Monster.B.Rep4371.PacketShape
public import CFSG.Monster.B.Co2.Data
public import CFSG.Monster.B.Rep4371.KeyActXi

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.Griess CFSG.Monster.ScalarKernel CFSG.Monster.B.Rep4371

@[expose] def packetNum (k t u : ℕ) : ℤ :=
  ((Native.packetRows[k]!)[t]!).foldl (fun s e => if e.1 = u then s + e.2 else s) 0

@[expose] def packetQ (k : Fin 48) (t u : Fin 4371) : ℚ := (packetNum k t u : ℚ) / 8


@[expose] def GR : Matrix (Fin 4371) (Fin 4371) ℚ :=
  Matrix.diagonal fun t => if (t : ℕ) = 0 then 2 else if (t : ℕ) ≤ 22 then 4 else 2

@[expose] noncomputable def recPerm (i : Fin 24) : AutPerm := wordPerm (Co2.genRecord i).word

@[expose] noncomputable def recCode (i : Fin 24) : C := frameSum (Co2.genRecord i).word

@[expose] noncomputable def hPair (i : Fin 24) : Pvis :=
  match (Co2.genRecord i).kind with
  | .pairStabilizer => permPair (recPerm i)
  | .codeSign => ⟨(YU ⟨recCode i, 0⟩, gO (recCode i)), YU_gO_mem_Pvis ⟨recCode i, 0⟩⟩
  | .xiSign => xiSignPair

@[expose] noncomputable def hElt (i : Fin 24) : SpaceB ≃ₗ[ℚ] SpaceB := thetaEquiv (hPair i)

theorem hElt_mem_Gvis (i : Fin 24) : hElt i ∈ Gvis := ⟨hPair i, rfl⟩

theorem genRecord_kind (i : Fin 24) :
    (Co2.genRecord i).kind = if (i : ℕ) < 12 then .pairStabilizer
      else if (i : ℕ) < 23 then .codeSign else .xiSign := by
  revert i
  decide +kernel

theorem repPerm_recPerm : ∀ i : Fin 24, (i : ℕ) < 12 →
    RepPerm (recPerm i : Equiv.Perm (Fin 24)) Model.recPerms[(i : ℕ)]! := by
  unfold RepPerm recPerm
  decide +kernel

theorem genRecord_word_codeSign : ∀ i : Fin 24, 12 ≤ (i : ℕ) → (i : ℕ) < 23 →
    (∀ k ∈ (Co2.genRecord i).word, k.toNat - 3 < 12) ∧
      Model.frameCode (Co2.genRecord i).word =
        [3, 5, 9, 17, 33, 64, 129, 256, 512, 1024, 2048][(i : ℕ) - 12]! := by
  decide +kernel

theorem recCode_eq {i : Fin 24} (h1 : 12 ≤ (i : ℕ)) (h2 : (i : ℕ) < 23) :
    recCode i = toC ([3, 5, 9, 17, 33, 64, 129, 256, 512, 1024, 2048][(i : ℕ) - 12]!) := by
  rw [recCode, frameSum_eq _ (genRecord_word_codeSign i h1 h2).1,
    (genRecord_word_codeSign i h1 h2).2]

theorem genRecord_word_xi : (Co2.genRecord 23).word = [0, 3] := by decide +kernel

theorem hPair_of_lt_twelve {i : Fin 24} (h : (i : ℕ) < 12) : hPair i = permPair (recPerm i) := by
  rw [hPair, genRecord_kind, ite_eq_left h]

theorem hPair_of_codeSign {i : Fin 24} (h1 : 12 ≤ (i : ℕ)) (h2 : (i : ℕ) < 23) :
    hPair i = ⟨(YU ⟨recCode i, 0⟩, gO (recCode i)), YU_gO_mem_Pvis ⟨recCode i, 0⟩⟩ := by
  rw [hPair, genRecord_kind, ite_eq_right (by omega), ite_eq_left h2]

theorem hPair_xi : hPair 23 = xiSignPair := by
  rw [hPair, genRecord_kind]
  rfl


end CFSG.Monster.B
