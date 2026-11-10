
module


public import CFSG.Sporadic.ThSchreier.Row
public import CFSG.Sporadic.Th.ChainBase1
public import CFSG.Sporadic.Th.Max3.PacketBase1
public import CFSG.Sporadic.Th.Max3.AllConjBase1
public meta import CFSG.Sporadic.ThSchreier.Text
public import CFSG.Sporadic.Th.Max3.AllConjInputs
public import CFSG.Sporadic.Th.Max3.InvolutionsBase1
public import CFSG.Sporadic.Th.Max3.InvolutionsInputs
public import CFSG.Sporadic.Th.Max3.QuotientBase1
public import CFSG.Sporadic.Th.Max3.QuotientInputs

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

@[expose] noncomputable def localX : J := Packet.run localProgram 1

@[expose] noncomputable def localY : J := Packet.run localProgram 2

@[expose] noncomputable def localH : Subgroup J := Subgroup.closure {localX, localY}

theorem localX_eq_word : localX = ((a * b) ^ 8)⁻¹ * a * (a * b) ^ 8 := by
  simp [localX, Packet.run, localProgram, Packet.Instr.exec, Packet.initRegs]

theorem localY_eq_word : localY =
    ((a * b * (a * b * (a * b * b)) * (a * b)) *
      ((a * b) * ((a * b * (a * b * (a * b * b)) * (a * b)) * (a * b * b)))) ^ 5 := by
  simp [localY, Packet.run, localProgram, Packet.Instr.exec, Packet.initRegs]

theorem localX_eq : localX = xJ := by
  rw [localX_eq_word, xJ]
  simp only [wordG, xWord, pairLetters, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, pow_succ, pow_zero, one_mul, mul_inv_rev, mul_one]
  norm_num
  group

theorem localY_eq : localY = yJ := by
  rw [localY_eq_word, yJ]
  simp only [wordG, yWord, pairLetters, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, pow_succ, pow_zero, one_mul, mul_one]
  norm_num
  group

theorem localH_eq : localH = H := by
  rw [localH, localX_eq, localY_eq]
  rfl


end CFSG.Sporadic.ThSchreier
