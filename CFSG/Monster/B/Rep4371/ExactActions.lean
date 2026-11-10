module

public import CFSG.Monster.B.Rep4371.RBasis
public import CFSG.Monster.B.Rep4371.ExactRow
public import CFSG.Monster.B.Rep4371.PacketGen
public import CFSG.Monster.B.Rep4371.Glue
public import CFSG.Monster.B.Rep4371.Chi
public import CFSG.Monster.B.Gen.HRecords

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.Griess CFSG.Monster.Generated CFSG.Monster.B.Rep4371
  CFSG.Monster.B.Short Matrix

@[expose] noncomputable def Rbasis :
    Module.Basis (Fin 4371) ℚ Vst := RbasisOf octDataOK_true

theorem coe_Rbasis
    (t : Fin 4371) : (Rbasis t : SpaceB) = Rraw t := coe_RbasisOf _ t


theorem row_lt_of_shape {row : Array (ℕ × ℤ)} (h : Native.packetRowShapeOK row = true) :
    ∀ e ∈ row.toList, e.1 < 4371 := by
  intro e he
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 he
  have ht' : t < row.size := by simpa using ht
  simp only [Native.packetRowShapeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  have := (h.2 t ht').1
  rw [getElem!_pos row t ht'] at this
  rw [Array.getElem_toList]
  simpa using this

theorem packetRows_shape
    {i : ℕ} (hi : i < 48) {k : ℕ} (hk : k < 4371) :
    ∀ e ∈ ((Native.packetRows[i]!)[k]!).toList, e.1 < 4371 := by
  have h := packetShapeOK_eq_true
  simp only [Native.packetShapeOK, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h
  obtain ⟨hs, hg⟩ := h
  have hi' : i < Native.packetRows.size := by omega
  obtain ⟨hgs, hrows⟩ := hg i hi'
  have hk' : k < (Native.packetRows[i]).size := by omega
  rw [getElem!_pos Native.packetRows i hi']
  rw [getElem!_pos (Native.packetRows[i]) k hk']
  exact row_lt_of_shape (hrows k hk')

theorem packetNum_eq (i k u : ℕ) :
    packetNum i k u = rowNum ((Native.packetRows[i]!)[k]!).toList u := by
  rw [packetNum, ← Array.foldl_toList, foldl_eq_rowNum, zero_add]

theorem rowSum_packet {i : ℕ} (hi : i < 48) {t : ℕ} (ht : t < 4371) :
    (((Native.packetRows[i]!)[t]!).toList.map fun e => ((e.2 : ℚ) / 8) • Rraw e.1).sum =
      ∑ u : Fin 4371, packetQ ⟨i, hi⟩ ⟨t, ht⟩ u • Rraw u := by
  rw [sum_row_eq_sum_fin Rraw _ (packetRows_shape hi ht)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [packetQ, packetNum_eq]

theorem hw_recPerms : ∀ j < 12,
    ((Model.recPerms[j]!)[0]! = 0 ∧ (Model.recPerms[j]!)[1]! = 1) ∨
      ((Model.recPerms[j]!)[0]! = 1 ∧ (Model.recPerms[j]!)[1]! = 0) := by
  decide

theorem ha_signCodes : ∀ j < 11,
    (Model.wordN Rep4371.Native.signCodes[j]!).testBit 0 =
      (Model.wordN Rep4371.Native.signCodes[j]!).testBit 1 := by
  decide

theorem signCodes_eq : ∀ j < 11,
    Rep4371.Native.signCodes[j]! = [3, 5, 9, 17, 33, 64, 129, 256, 512, 1024, 2048][j]! := by
  decide

theorem hPair_codeSign_eq {i : Fin 24} (h1 : 12 ≤ (i : ℕ)) (h2 : (i : ℕ) < 23) :
    hPair i = signPair Rep4371.Native.signCodes[(i : ℕ) - 12]! := by
  rw [hPair_of_codeSign h1 h2]
  have hc := recCode_eq h1 h2
  rw [← signCodes_eq _ (by omega)] at hc
  apply Subtype.ext
  show (YU ⟨recCode i, 0⟩, gO (recCode i)) =
    (YU ⟨toC Rep4371.Native.signCodes[(i : ℕ) - 12]!, 0⟩, gO (toC Rep4371.Native.signCodes[(i : ℕ) - 12]!))
  rw [hc]

theorem packetGen_keyVec {k : ℕ} (hk : k < 47) (κ : Model.Key) (hκ : KeyValid κ) :
    (packetGen ⟨k, by omega⟩ : SpaceB ≃ₗ[ℚ] SpaceB) (keyVec κ) = interp 64 (genActM k κ) := by
  rcases Nat.lt_or_ge k 23 with h23 | h23
  · rw [coe_packetGen_pauli (k := ⟨k, by omega⟩) h23, genActM, ite_eq_left h23]
    exact keyAct_pauli_sound _ κ
  have e : (⟨k, by omega⟩ : Fin 48) = ⟨23 + ((⟨k - 23, by omega⟩ : Fin 24) : ℕ), by simp; omega⟩ :=
    Fin.ext (by simp; omega)
  rw [e, coe_packetGen_h, hElt]
  rcases Nat.lt_or_ge k 35 with h35 | h35
  · rw [hPair_of_lt_twelve (by simp; omega), permPair, genActM, ite_eq_right (by omega),
      ite_eq_left h35]
    exact keyAct_perm_sound _ (repPerm_recPerm ⟨k - 23, by omega⟩ (by simp; omega))
      (hw_recPerms (k - 23) (by omega)) κ hκ
  rcases Nat.lt_or_ge k 46 with h46 | h46
  · rw [hPair_codeSign_eq (by simp; omega) (by simp; omega), genActM, ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left h46]
    have hidx : k - 23 - 12 = k - 35 := by omega
    simp only [hidx]
    exact keyAct_sign_sound _ (ha_signCodes (k - 35) (by omega)) κ hκ
  · have hk46 : k = 46 := by omega
    subst hk46
    rw [show (⟨46 - 23, by omega⟩ : Fin 24) = 23 from rfl, hPair_xi, genActM,
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    exact keyAct_xi_sound κ hκ

theorem packetGen_Rraw
    (k : Fin 48) (t : Fin 4371) :
    (packetGen k : SpaceB ≃ₗ[ℚ] SpaceB) (Rraw t) = ∑ u : Fin 4371, packetQ k t u • Rraw u := by
  obtain ⟨k, hk⟩ := k
  obtain ⟨t, ht⟩ := t
  rcases Nat.lt_or_ge k 47 with hk47 | hk47
  · rw [← rowSum_packet hk ht]
    exact act_Rraw_of_rowOK (genActM k) (packetGen ⟨k, hk⟩ : SpaceB ≃ₗ[ℚ] SpaceB).toLinearMap
      (fun κ hκ => packetGen_keyVec hk47 κ hκ) (rowOK_packet hk47 ht)
  · have hk' : k = 47 := by omega
    subst hk'
    have htau : (packetGen ⟨47, hk⟩ : SpaceB ≃ₗ[ℚ] SpaceB) = tauB := coe_packetGen_tau
    rw [htau, tauB_Rraw octDataOK_true octSignOK_true ht, ← packetRows_tau ht, rowVec,
      rowSum_packet hk ht]


theorem chi_packetElt_apply
    (k : Fin 48) (t : Fin 4371) :
    (chi (packetElt k) : Vst →ₗ[ℚ] Vst) (Rbasis t) = ∑ u, packetQ k t u • Rbasis u := by
  apply Subtype.ext
  rw [LinearEquiv.coe_coe, packetElt, coe_chi_kappa_apply, coe_Rbasis, packetGen_Rraw,
    Submodule.coe_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Submodule.coe_smul, coe_Rbasis]


end CFSG.Monster.B
