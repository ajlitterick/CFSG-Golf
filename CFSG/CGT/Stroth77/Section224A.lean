module

public import CFSG.CGT.Stroth77.Stroth2Mho

public section

namespace CFSG.CGT.Stroth77

open CFSG.GroupTheory.HuppertProduct

variable {G : Type} [Group G] [Finite G] {X : StrothAmbient G}

theorem card_four_torsion_zmod_two_pow (n : ℕ) (hn : 2 ≤ n) :
    Nat.card {z : ZMod (2 ^ n) // (4 : ℤ) • z = 0} = 4 := by
  have hN : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show 4 = 2 ^ 2 by norm_num, ← pow_add, show 2 + (n - 2) = n by omega]
  have hpos : 0 < 2 ^ (n - 2) := pow_pos (by norm_num) _
  have hmul4 : ∀ z : ZMod (2 ^ n), (4 : ℤ) • z = 0 → 2 ^ (n - 2) ∣ z.val := by
    intro z hz
    have hz' : ((4 * z.val : ℕ) : ZMod (2 ^ n)) = 0 := by
      rw [zsmul_eq_mul] at hz
      simpa [Nat.cast_mul, ZMod.natCast_zmod_val, Int.cast_ofNat] using hz
    have hdiv : 2 ^ n ∣ 4 * z.val := (ZMod.natCast_eq_zero_iff _ _).mp hz'
    have h4dvd : 4 * 2 ^ (n - 2) ∣ 4 * z.val := by
      rw [← hN]
      exact hdiv
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 4)).mp h4dvd
  let e : {z : ZMod (2 ^ n) // (4 : ℤ) • z = 0} ≃ Fin 4 :=
    { toFun := fun z =>
        ⟨z.1.val / 2 ^ (n - 2), by
          have hMdiv := hmul4 z.1 z.2
          have hlt : 2 ^ (n - 2) * (z.1.val / 2 ^ (n - 2)) < 2 ^ (n - 2) * 4 := by
            rw [Nat.mul_div_cancel' hMdiv, mul_comm (2 ^ (n - 2)) 4, ← hN]
            exact ZMod.val_lt z.1
          exact Nat.lt_of_mul_lt_mul_left hlt⟩
      invFun := fun t =>
        ⟨((2 ^ (n - 2) * t.val : ℕ) : ZMod (2 ^ n)), by
          have h4 : ((4 * (2 ^ (n - 2) * t.val) : ℕ) : ZMod (2 ^ n)) = 0 := by
            rw [ZMod.natCast_eq_zero_iff, hN]
            exact ⟨t.val, by ring⟩
          rw [zsmul_eq_mul]
          simpa [Nat.cast_mul, Int.cast_ofNat] using h4⟩
      left_inv := fun z => by
        apply Subtype.ext
        apply ZMod.val_injective (2 ^ n)
        rw [← ZMod.natCast_zmod_val z.1]
        rw [ZMod.val_cast_of_lt (by
          rw [Nat.mul_div_cancel' (hmul4 z.1 z.2)]
          exact ZMod.val_lt z.1), ZMod.val_cast_of_lt (ZMod.val_lt z.1)]
        exact Nat.mul_div_cancel' (hmul4 z.1 z.2)
      right_inv := fun t => by
        apply Fin.ext
        change ((2 ^ (n - 2) * t.val : ℕ) : ZMod (2 ^ n)).val / 2 ^ (n - 2) = t.val
        have hlt : 2 ^ (n - 2) * t.val < 2 ^ n := by
          have h := Nat.mul_lt_mul_of_pos_left t.isLt hpos
          rwa [mul_comm (2 ^ (n - 2)) 4, ← hN] at h
        rw [ZMod.val_cast_of_lt hlt]
        exact Nat.mul_div_cancel_left t.val hpos }
  simpa using Nat.card_congr e

theorem card_omegaIn_two_of_two_le_k (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i) :
    Nat.card (omegaIn 2 Z.D) = 64 := by
  rw [card_omegaIn_two_eq Z.dataD.e, card_four_torsion_torus, Fin.prod_univ_three,
    card_four_torsion_zmod_two_pow (Z.τ.k 0) (hk 0),
    card_four_torsion_zmod_two_pow (Z.τ.k 1) (hk 1),
    card_four_torsion_zmod_two_pow (Z.τ.k 2) (hk 2)]
  norm_num

theorem A_index_two_omegaIn_two (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i) :
    (X.A.subgroupOf (omegaIn 2 Z.D)).index = 2 := by
  have hcardΩ : Nat.card (omegaIn 2 Z.D) = 64 := card_omegaIn_two_of_two_le_k Z hk
  have hcardA : Nat.card (X.A.subgroupOf (omegaIn 2 Z.D)) = 32 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (A_le_omegaIn_two Z)).toEquiv).trans
      X.card_A
  rw [Subgroup.index_eq_card_div, hcardA, hcardΩ]

theorem torus_exists_two_zsmul_eq_of_two_zsmul_eq_zero {k : Fin 3 → ℕ}
    (hk : ∀ i, 2 ≤ k i) {v : Torus k} (hv : (2 : ℤ) • v = 0) :
    ∃ w : Torus k, (2 : ℤ) • w = v := by
  obtain ⟨V, hV⟩ : ∃ V : Fin 3 → ℤ, v = Torus.ofInt k V := by
    choose V hV using fun i => ZMod.intCast_surjective (v i)
    exact ⟨V, funext fun i => by simpa [Torus.ofInt_apply] using (hV i).symm⟩
  have hEven : ∀ i, Even (V i) := by
    intro i
    have hdiv : ((2 ^ k i : ℕ) : ℤ) ∣ 2 * V i := by
      have hi : ((2 * V i : ℤ) : ZMod (2 ^ k i)) = 0 := by
        have h := congrFun (hV ▸ hv) i
        simpa only [Torus.ofInt_apply, Pi.smul_apply, Pi.zero_apply, zsmul_eq_mul,
          Int.cast_ofNat, Int.cast_mul, Int.cast_natCast] using h
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * V i) (2 ^ k i)).mp hi
    have h4 : (4 : ℤ) ∣ ((2 ^ k i : ℕ) : ℤ) := by
      have h := pow_dvd_pow (2 : ℕ) (hk i)
      exact_mod_cast h
    obtain ⟨t, ht⟩ := h4.trans hdiv
    exact even_iff_two_dvd.mpr ⟨t, by omega⟩
  obtain ⟨w, hw⟩ := (Torus.exists_two_zsmul_eq_iff
    (fun i => le_trans (by norm_num : 1 ≤ 2) (hk i)) V).mpr hEven
  exact ⟨w, by rw [hV]; exact hw⟩

theorem exists_sq_eq_of_mem_omegaIn_one (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i)
    {y : G} (hy : y ∈ omegaIn 1 Z.D) :
    ∃ x : G, x ∈ omegaIn 2 Z.D ∧ x * x = y := by
  have hcomm : ∀ a ∈ Z.D, ∀ b ∈ Z.D, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val
      (Z.dataD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hyD, hy2⟩ := (mem_omegaIn_iff_of_comm hcomm).mp hy
  have hy2' : y ^ 2 = 1 := by simpa using hy2
  set v : Torus Z.τ.k := Z.dataD.e (Additive.ofMul ⟨y, hyD⟩) with hv
  have hv2 : (2 : ℤ) • v = 0 := by
    calc (2 : ℤ) • v
        = Z.dataD.e ((2 : ℤ) • Additive.ofMul (⟨y, hyD⟩ : Z.D)) := by
          rw [hv, map_zsmul]
      _ = Z.dataD.e (Additive.ofMul ((⟨y, hyD⟩ : Z.D) ^ 2)) := by
          rw [ofMul_pow]
          norm_num
      _ = Z.dataD.e (Additive.ofMul (1 : Z.D)) := by
          rw [show (⟨y, hyD⟩ : Z.D) ^ 2 = 1 from Subtype.ext hy2']
      _ = 0 := by simp
  obtain ⟨w, hw⟩ := torus_exists_two_zsmul_eq_of_two_zsmul_eq_zero hk hv2
  set x : Z.D := Additive.toMul (Z.dataD.e.symm w) with hx
  have hxw : Additive.ofMul x = Z.dataD.e.symm w := by
    rw [hx]
    simp
  have hx2' : x * x = ⟨y, hyD⟩ := by
    apply Additive.ofMul.injective
    apply Z.dataD.e.injective
    have h1 : Z.dataD.e (Additive.ofMul (x * x)) = w + w := by
      rw [ofMul_mul, map_add, hxw]
      simp
    rw [h1]
    show w + w = v
    rw [← hw, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, natCast_zsmul, two_nsmul]
  have hx2 : (x : G) * (x : G) = y := by
    simpa using congrArg Subtype.val hx2'
  have hy2D : (⟨y, hyD⟩ : Z.D) ^ 2 = 1 := Subtype.ext hy2'
  have hx4D : (x : Z.D) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_two x, hx2', hy2D]
  have hx4 : (x : G) ^ 4 = 1 := by
    simpa using congrArg Subtype.val hx4D
  refine ⟨(x : G), ?_, hx2⟩
  exact mem_omegaIn_of_pow_eq_one (i := 2) x.2 (by simpa using hx4)


theorem omegaIn_one_le_of_index_two (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i)
    (h2 : (X.A.subgroupOf (omegaIn 2 Z.D)).index = 2) :
    omegaIn 1 Z.D ≤ X.A := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := exists_sq_eq_of_mem_omegaIn_one Z hk hy
  subst hxy
  have hmem : (⟨x, hx⟩ : omegaIn 2 Z.D) * ⟨x, hx⟩ ∈
      X.A.subgroupOf (omegaIn 2 Z.D) :=
    Subgroup.mul_self_mem_of_index_two h2 ⟨x, hx⟩
  exact Subgroup.mem_subgroupOf.mp hmem

theorem omegaIn_one_le_A (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i) :
    omegaIn 1 Z.D ≤ X.A :=
  omegaIn_one_le_of_index_two Z hk (A_index_two_omegaIn_two Z hk)


theorem mem_mho_iff_exists_pow_of_comm {S : Subgroup G}
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {n : ℕ} {x : G} :
    x ∈ mho S n ↔ ∃ d ∈ S, d ^ n = x := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => simpa [eq_comm] using hy
    | one => exact ⟨1, S.one_mem, one_pow n⟩
    | mul a b _ _ ha hb =>
        obtain ⟨da, hda, rfl⟩ := ha
        obtain ⟨db, hdb, rfl⟩ := hb
        have hc : Commute da db := hcomm da hda db hdb
        exact ⟨da * db, S.mul_mem hda hdb, by rw [hc.mul_pow n]⟩
    | inv a _ ha =>
        obtain ⟨da, hda, rfl⟩ := ha
        exact ⟨da⁻¹, S.inv_mem hda, by rw [inv_pow]⟩
  · rintro ⟨d, hd, rfl⟩
    exact pow_mem_mho hd


namespace StrothWeakTypeData

variable {S : Type*} [Group S] {B : Subgroup S} {τ : StrothTypeIndex}

theorem e_c (D : StrothWeakTypeData B τ) :
    D.e (Additive.ofMul D.c) = Torus.c := by
  rw [c, ofMul_toMul, AddEquiv.apply_symm_apply]

theorem e_a (D : StrothWeakTypeData B τ) :
    D.e (Additive.ofMul D.a) = Torus.a := by
  rw [a, ofMul_toMul, AddEquiv.apply_symm_apply]

theorem e_b (D : StrothWeakTypeData B τ) :
    D.e (Additive.ofMul D.b) = Torus.b := by
  rw [b, ofMul_toMul, AddEquiv.apply_symm_apply]

theorem e_pow (D : StrothWeakTypeData B τ) (x : B) (n : ℕ) :
    D.e (Additive.ofMul (x ^ n)) = n • D.e (Additive.ofMul x) := by
  rw [ofMul_pow, map_nsmul]

theorem orderOf_c (D : StrothWeakTypeData B τ) : orderOf D.c = 2 ^ τ.m := by
  rw [c, ← addOrderOf_ofMul_eq_orderOf, ofMul_toMul, AddEquiv.addOrderOf_eq, addOrderOf_c]
  rfl

theorem orderOf_a (D : StrothWeakTypeData B τ) : orderOf D.a = 2 ^ τ.n := by
  rw [a, ← addOrderOf_ofMul_eq_orderOf, ofMul_toMul, AddEquiv.addOrderOf_eq, addOrderOf_a]
  rfl

theorem orderOf_b (D : StrothWeakTypeData B τ) : orderOf D.b = 2 ^ τ.n := by
  rw [b, ← addOrderOf_ofMul_eq_orderOf, ofMul_toMul, AddEquiv.addOrderOf_eq, addOrderOf_b,
    StrothTypeIndex.k_two]

theorem exists_zpow_c_a_b (D : StrothWeakTypeData B τ) (x : B) :
    ∃ i j l : ℤ, x = D.c ^ i * D.a ^ j * D.b ^ l := by
  let y : Torus τ.k := D.e (Additive.ofMul x)
  choose z hz using fun i : Fin 3 => ZMod.intCast_surjective (y i)
  have hy : y = z 0 • gen τ.k 0 + z 1 • gen τ.k 1 + z 2 • gen τ.k 2 := by
    funext i
    fin_cases i <;>
      simp [gen, Pi.single_eq_same, Pi.single_eq_of_ne, hz, Pi.add_apply, Pi.smul_apply]
  refine ⟨z 0, z 1, z 2, ?_⟩
  apply Additive.ofMul.injective
  apply D.e.injective
  rw [show D.e (Additive.ofMul x) = y from rfl, hy]
  simp only [ofMul_mul, ofMul_zpow, map_add, map_zsmul]
  rw [D.e_c, D.e_a, D.e_b]

theorem closure_c_a_b_of_zpow (D : StrothWeakTypeData B τ) :
    Subgroup.closure ({(D.c : S), (D.a : S), (D.b : S)} : Set S) = B := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [D.c.2, D.a.2, D.b.2]
  · intro x hx
    obtain ⟨i, j, l, h⟩ := D.exists_zpow_c_a_b ⟨x, hx⟩
    have hx' : x = (D.c : S) ^ i * (D.a : S) ^ j * (D.b : S) ^ l := by
      simpa using congrArg Subtype.val h
    rw [hx']
    let cl : Subgroup S := Subgroup.closure ({(D.c : S), (D.a : S), (D.b : S)} : Set S)
    have hc : (D.c : S) ∈ cl := Subgroup.subset_closure (by simp)
    have ha : (D.a : S) ∈ cl := Subgroup.subset_closure (by simp)
    have hb : (D.b : S) ∈ cl := Subgroup.subset_closure (by simp)
    exact cl.mul_mem (cl.mul_mem (cl.zpow_mem hc i) (cl.zpow_mem ha j)) (cl.zpow_mem hb l)

end StrothWeakTypeData


end CFSG.CGT.Stroth77
