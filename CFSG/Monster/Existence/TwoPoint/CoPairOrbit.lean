module

public import CFSG.Monster.Existence.Co2Bridge
public import Certificates.Data.CFSGNative.MonsterAxis.CoPair

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence.CoPair

open CFSG.Monster CFSG.Monster.SpinLattice CFSG.Monster.VisCert CFSG.Monster.VisQuot
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.Existence.Co2Bridge
  CFSG.Monster.Existence.CoPair.Native

theorem native_actGo_eq (rows : Array ℕ) (v : ℕ) :
    ∀ n acc, VisCert.Native.actGo rows v n acc = VisCert.actGo rows v n acc
  | 0, _ => rfl
  | n + 1, acc => by rw [VisCert.Native.actGo, VisCert.actGo, native_actGo_eq rows v n]

theorem native_actRows_eq (rows : Array ℕ) (v : ℕ) :
    VisCert.Native.actRows rows v = VisCert.actRows rows v :=
  native_actGo_eq rows v 24 0

theorem kOp_alphaK_dec
    {l : ℕ} (hl : l < 24) (v : ℕ) :
    kOp (alphaK l).1 (dec v) = dec (VisCert.Native.actRows (letterRows l) v) := by
  have h : alphaK l = ⟨alpha ⟨l, hl⟩, alpha_mem_Kv _⟩ := by simp [alphaK, hl]
  rw [h]
  show kOp (alpha ⟨l, hl⟩) (dec v) = _
  rw [kOp_alpha_dec, native_actRows_eq]
  rfl

theorem kOp_wordK_dec
    (w : List ℕ) (hw : ∀ l ∈ w, l < 24) (v : ℕ) :
    kOp (wordK w).1 (dec v) = dec (actLetters w v) := by
  induction w generalizing v with
  | nil =>
    rw [wordK, List.map_nil, List.prod_nil]
    exact LinearMap.congr_fun kOp_one (dec v)
  | cons l w ih =>
    have hl : l < 24 := hw l List.mem_cons_self
    rw [wordK, List.map_cons, List.prod_cons, Subgroup.coe_mul, kOp_mul]
    change kOp (wordK w).1 (kOp (alphaK l).1 (dec v)) = _
    rw [kOp_alphaK_dec hl, ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))]
    rfl

theorem xWordN_eq : xWordN = xWord := rfl

theorem yWordN_eq : yWordN = yWord := rfl

theorem kOp_xK_dec
    (v : ℕ) : kOp xK.1 (dec v) = dec (actLetters xWordN v) := by
  rw [xK, kOp_wordK_dec xWord xWord_lt, xWordN_eq]

theorem kOp_yK_dec
    (v : ℕ) : kOp yK.1 (dec v) = dec (actLetters yWordN v) := by
  rw [yK, kOp_wordK_dec yWord yWord_lt, yWordN_eq]

@[expose] def xyK : List ℕ → Kstab v0
  | [] => 1
  | g :: w => (if g = 0 then xK else yK) * xyK w

theorem kOp_xyK_dec
    (w : List ℕ) (v : ℕ) : kOp (xyK w).1 (dec v) = dec (actXY w v) := by
  induction w generalizing v with
  | nil =>
    rw [xyK]
    exact LinearMap.congr_fun kOp_one (dec v)
  | cons g w ih =>
    rw [xyK, Subgroup.coe_mul, kOp_mul]
    change kOp (xyK w).1 (kOp (if g = 0 then xK else yK).1 (dec v)) = _
    by_cases hg : g = 0
    · rw [ite_eq_left hg, kOp_xK_dec, ih]
      simp [actXY, hg]
    · rw [ite_eq_right hg, kOp_yK_dec, ih]
      simp [actXY, hg]

@[expose, instance_reducible] def kvLeft : MulAction (Kstab v0) L2 where
  smul k x := kOp ((k⁻¹ : Kstab v0) : OLq) x
  one_smul x := by
    change kOp (((1 : Kstab v0)⁻¹ : Kstab v0) : OLq) x = x
    rw [inv_one]
    exact LinearMap.congr_fun kOp_one x
  mul_smul k k' x := by
    change kOp (((k * k')⁻¹ : Kstab v0) : OLq) x =
      kOp ((k⁻¹ : Kstab v0) : OLq) (kOp ((k'⁻¹ : Kstab v0) : OLq) x)
    rw [mul_inv_rev, Subgroup.coe_mul, kOp_mul]
    rfl

attribute [local instance] kvLeft

theorem kvLeft_smul (k : Kstab v0) (x : L2) : k • x = kOp ((k⁻¹ : Kstab v0) : OLq) x := rfl

theorem kvLeft_inv_smul (k : Kstab v0) (x : L2) : k⁻¹ • x = kOp (k : OLq) x := by
  rw [kvLeft_smul, inv_inv]

theorem kOp_inv_kOp (k : OLq) (x : L2) : kOp k⁻¹ (kOp k x) = x := by
  have h := LinearMap.congr_fun (kOp_mul k k⁻¹) x
  rw [mul_inv_cancel, kOp_one] at h
  exact h.symm


@[expose] def kvStab (x : L2) : Subgroup (Kstab v0) where
  carrier := {k | kOp (k : OLq) x = x}
  one_mem' := LinearMap.congr_fun kOp_one x
  mul_mem' {k k'} hk hk' := by
    change kOp ((k * k' : Kstab v0) : OLq) x = x
    rw [Subgroup.coe_mul, kOp_mul]
    change kOp (k' : OLq) (kOp (k : OLq) x) = x
    rw [show kOp (k : OLq) x = x from hk]
    exact hk'
  inv_mem' {k} hk := by
    change kOp (((k⁻¹ : Kstab v0)) : OLq) x = x
    have h : kOp (k : OLq) x = x := hk
    conv_lhs => rw [← h]
    exact kOp_inv_kOp (k : OLq) x

theorem mem_kvStab {x : L2} {k : Kstab v0} : k ∈ kvStab x ↔ kOp (k : OLq) x = x := Iff.rfl

theorem stabilizer_kvLeft (x : L2) : MulAction.stabilizer (Kstab v0) x = kvStab x := by
  ext k
  rw [MulAction.mem_stabilizer_iff, kvLeft_smul]
  show k⁻¹ ∈ kvStab x ↔ k ∈ kvStab x
  exact inv_mem_iff (H := kvStab x) (x := k)

theorem index_kvStab
    (x : L2) : (kvStab x).index = (MulAction.orbit (Kstab v0) x).ncard := by
  rw [← stabilizer_kvLeft]
  exact MulAction.index_stabilizer (Kstab v0) x

theorem ncard_orbit_mul
    (x : L2) :
    (MulAction.orbit (Kstab v0) x).ncard * Nat.card (kvStab x) = 42305421312000 := by
  rw [← index_kvStab, Subgroup.index_mul_card, natCard_Kv]

@[expose] def kvStabEquivInf (x : L2) : kvStab x ≃* ↥(Kstab v0 ⊓ Kstab x) where
  toFun k := ⟨(k.1 : OLq), k.1.2, k.2⟩
  invFun k := ⟨⟨k.1, k.2.1⟩, k.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem natCard_inf_of_orbit
    {x : L2} {N : ℕ} (h : (MulAction.orbit (Kstab v0) x).ncard = N) :
    N * Nat.card ↥(Kstab v0 ⊓ Kstab x) = 42305421312000 := by
  rw [← h, ← Nat.card_congr (kvStabEquivInf x).toEquiv, ncard_orbit_mul]

theorem genXY_zero (v : ℕ) : genXY 0 v = actLetters xWordN v := by
  simp [genXY, actXY]

theorem genXY_one (v : ℕ) : genXY 1 v = actLetters yWordN v := by
  simp [genXY, actXY]

theorem dec_genXY_zero
    (v : ℕ) : dec (genXY 0 v) = xK⁻¹ • dec v := by
  rw [genXY_zero, kvLeft_inv_smul, kOp_xK_dec]

theorem dec_genXY_one
    (v : ℕ) : dec (genXY 1 v) = yK⁻¹ • dec v := by
  rw [genXY_one, kvLeft_inv_smul, kOp_yK_dec]


end CFSG.Monster.Existence.CoPair
