module

public import CFSG.Perm.ChainByOrder
public import CFSG.Certificates.Kernel.RouteP.TabComplete
public import Certificates.Certificate7802

public section

namespace CFSG.ASVolI

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm
  CFSG.Perm.Native

attribute [local irreducible] burnsideF48d_KeysHex burnsideF48d_TabsHex burnsideF48d_GensHex
  burnsideF48d_PhiHex burnsideF48d_limbs burnsideF48d_colTab

instance burnsideF48d_finite_X : Finite ↥burnsideF48d_X := Subgroup.instFiniteSubtypeMem _

section Chains

abbrev burnsideF48d_lv0 : Fin 26572 × Finset (Fin 17) × ℕ := (0, ∅, 0)

@[expose] noncomputable def burnsideF48d_lvH (C : List (Fin 26572 × Finset (Fin 17) × ℕ))
    (i : ℕ) : Subgroup ↥burnsideF48d_X :=
  Subgroup.closure (burnsideF48d_L '' ↑(C.getD i burnsideF48d_lv0).2.1)

variable {C : List (Fin 26572 × Finset (Fin 17) × ℕ)}

theorem burnsideF48d_getD_lv {i : ℕ} (hi : i < C.length) : C.getD i burnsideF48d_lv0 = C[i] := by
  simp [hi]

theorem burnsideF48d_lvH_length : burnsideF48d_lvH C C.length = ⊥ := by
  simp [burnsideF48d_lvH, List.getD_eq_default]

@[expose] def burnsideF48d_ChainNested (C : List (Fin 26572 × Finset (Fin 17) × ℕ)) : Prop :=
  ∀ i < C.length - 1, (C.getD (i + 1) burnsideF48d_lv0).2.1 ⊆ (C.getD i burnsideF48d_lv0).2.1

theorem burnsideF48d_lvH_le (hC : burnsideF48d_ChainBound C) (hsub : burnsideF48d_ChainNested C)
    {i : ℕ} (hi : i < C.length) :
    burnsideF48d_lvH C (i + 1) ≤
      burnsideF48d_lvH C i ⊓ MulAction.stabilizer ↥burnsideF48d_X C[i].1 := by
  by_cases h : i + 1 < C.length
  · rw [burnsideF48d_lvH, Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    refine ⟨Subgroup.subset_closure ⟨j, hsub i (by omega) hj, rfl⟩, ?_⟩
    change burnsideF48d_L j ∈ MulAction.stabilizer ↥burnsideF48d_X C[i].1
    rw [MulAction.mem_stabilizer_iff]
    have hj' : j ∈ C[i + 1].2.1 := by
      have := hj
      rwa [Finset.mem_coe, burnsideF48d_getD_lv h] at this
    exact (hC (i + 1) h).1 j hj' i (Nat.lt_succ_self i)
  · rw [show i + 1 = C.length by omega, burnsideF48d_lvH_length]
    exact bot_le

theorem burnsideF48d_lvH_card (hC : burnsideF48d_ChainBound C) (hsub : burnsideF48d_ChainNested C)
    {i : ℕ} (hi : i < C.length) :
    C[i].2.2 * Nat.card (burnsideF48d_lvH C (i + 1)) ≤ Nat.card (burnsideF48d_lvH C i) := by
  rw [card_eq_orbit_mul_inf (burnsideF48d_lvH C i) C[i].1, Nat.card_coe_set_eq]
  refine Nat.mul_le_mul ?_ (Subgroup.card_le_of_le (burnsideF48d_lvH_le hC hsub hi))
  have e : burnsideF48d_lvH C i = Subgroup.closure (burnsideF48d_L '' ↑C[i].2.1) := by
    rw [burnsideF48d_lvH, burnsideF48d_getD_lv hi]
  rw [e]
  exact (hC i hi).2

theorem burnsideF48d_lvH_prod_le (hC : burnsideF48d_ChainBound C)
    (hsub : burnsideF48d_ChainNested C) : ∀ j ≤ C.length,
    ∏ l ∈ Finset.Ico j C.length, (C.getD l burnsideF48d_lv0).2.2 ≤
      Nat.card (burnsideF48d_lvH C j) := by
  suffices h : ∀ d j, j + d = C.length → ∏ l ∈ Finset.Ico j C.length,
      (C.getD l burnsideF48d_lv0).2.2 ≤ Nat.card (burnsideF48d_lvH C j) from
    fun j hj => h (C.length - j) j (by omega)
  intro d
  induction d with
  | zero =>
    intro j hj
    rw [show j = C.length by omega, Finset.Ico_self, Finset.prod_empty]
    exact Nat.card_pos
  | succ d ih =>
    intro j hj
    have hjm : j < C.length := by omega
    rw [Finset.prod_eq_prod_Ico_succ_bot hjm, burnsideF48d_getD_lv hjm]
    exact (Nat.mul_le_mul_left _ (ih (j + 1) (by omega))).trans
      (burnsideF48d_lvH_card hC hsub hjm)

theorem burnsideF48d_lvH_tight (hC : burnsideF48d_ChainBound C) (hsub : burnsideF48d_ChainNested C)
    (hN : Nat.card ↥burnsideF48d_X ≤
      ∏ l ∈ Finset.range C.length, (C.getD l burnsideF48d_lv0).2.2) :
    (∀ j ≤ C.length, Nat.card (burnsideF48d_lvH C j) =
      ∏ l ∈ Finset.Ico j C.length, (C.getD l burnsideF48d_lv0).2.2) ∧
    ∀ i (hi : i < C.length), burnsideF48d_lvH C (i + 1) =
      burnsideF48d_lvH C i ⊓ MulAction.stabilizer ↥burnsideF48d_X C[i].1 := by
  set s : ℕ → ℕ := fun l => (C.getD l burnsideF48d_lv0).2.2 with hs
  set a : ℕ → ℕ := fun j => Nat.card (burnsideF48d_lvH C j) with ha
  have hstep : ∀ i < C.length, s i * a (i + 1) ≤ a i := fun i hi => by
    have := burnsideF48d_lvH_card hC hsub hi
    rwa [← burnsideF48d_getD_lv hi] at this
  have hN0 : ∏ l ∈ Finset.range C.length, s l ≠ 0 :=
    Nat.pos_iff_ne_zero.1 (lt_of_lt_of_le Nat.card_pos hN)
  have hspos : ∀ l < C.length, 0 < s l := fun l hl =>
    Nat.pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.1 hN0 l (Finset.mem_range.2 hl))
  have hup : ∀ j ≤ C.length, a j * ∏ l ∈ Finset.range j, s l ≤ a 0 := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [Finset.prod_range_succ]
      calc a (j + 1) * ((∏ l ∈ Finset.range j, s l) * s j)
          = (s j * a (j + 1)) * ∏ l ∈ Finset.range j, s l := by ring
        _ ≤ a j * ∏ l ∈ Finset.range j, s l := Nat.mul_le_mul_right _ (hstep j (by omega))
        _ ≤ a 0 := ih (by omega)
  have ha0 : a 0 ≤ ∏ l ∈ Finset.range C.length, s l :=
    (Subgroup.card_le_card_group _).trans hN
  have heq : ∀ j ≤ C.length, a j = ∏ l ∈ Finset.Ico j C.length, s l := by
    intro j hj
    refine le_antisymm ?_ (burnsideF48d_lvH_prod_le hC hsub j hj)
    have hP : 0 < ∏ l ∈ Finset.range j, s l :=
      Finset.prod_pos fun l hl => hspos l (by simp at hl; omega)
    rw [← Finset.prod_range_mul_prod_Ico s hj] at ha0
    have := (hup j hj).trans ha0
    rw [mul_comm (a j)] at this
    exact Nat.le_of_mul_le_mul_left this hP
  refine ⟨heq, fun i hi => ?_⟩
  have hle := burnsideF48d_lvH_le hC hsub hi
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hc := card_eq_orbit_mul_inf (burnsideF48d_lvH C i) C[i].1
  rw [Nat.card_coe_set_eq] at hc
  have ho : s i ≤ (MulAction.orbit ↥(burnsideF48d_lvH C i) C[i].1).ncard := by
    have h0 := (hC i hi).2
    have e : burnsideF48d_lvH C i = Subgroup.closure (burnsideF48d_L '' ↑C[i].2.1) := by
      rw [burnsideF48d_lvH, burnsideF48d_getD_lv hi]
    rw [e]
    change (C.getD i burnsideF48d_lv0).2.2 ≤ _
    rw [burnsideF48d_getD_lv hi]
    exact h0
  have hai : a i = s i * a (i + 1) := by
    rw [heq i hi.le, heq (i + 1) hi, Finset.prod_eq_prod_Ico_succ_bot hi]
  have h1 : s i * Nat.card ↥(burnsideF48d_lvH C i ⊓
      MulAction.stabilizer ↥burnsideF48d_X C[i].1) ≤ s i * a (i + 1) := by
    rw [← hai]
    exact (Nat.mul_le_mul_right _ ho).trans hc.ge
  exact Nat.le_of_mul_le_mul_left h1 (hspos i hi)

end Chains


section Reps


abbrev burnsideF48d_F : Type := GaloisField 3 3

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem burnsideF48d_card_F : Nat.card burnsideF48d_F = 27 := by
  rw [GaloisField.card 3 3 (by norm_num)]
  norm_num

noncomputable abbrev burnsideF48d_σF : burnsideF48d_F →+* burnsideF48d_F := frobenius burnsideF48d_F 3

theorem burnsideF48d_σF_apply (c : burnsideF48d_F) : burnsideF48d_σF c = c ^ 3 := frobenius_def 3 c

noncomputable def burnsideF48d_ωF : burnsideF48d_F := by
  haveI : Fintype burnsideF48d_F := Fintype.ofFinite _
  exact Classical.choose (burnsideF48d_exists_omega (K := burnsideF48d_F)
    (by rw [← Nat.card_eq_fintype_card, burnsideF48d_card_F]))

theorem burnsideF48d_ωF_spec : burnsideF48d_ωF ^ 3 = burnsideF48d_ωF + 1 := by
  haveI : Fintype burnsideF48d_F := Fintype.ofFinite _
  exact Classical.choose_spec (burnsideF48d_exists_omega (K := burnsideF48d_F)
    (by rw [← Nat.card_eq_fintype_card, burnsideF48d_card_F]))


theorem burnsideF48d_card_X_le' : Nat.card ↥burnsideF48d_X ≤ 20560831566912 :=
  burnsideF48d_card_X_le burnsideF48d_σF burnsideF48d_ωF burnsideF48d_card_F burnsideF48d_σF_apply
    burnsideF48d_ωF_spec


end Reps

section ChainX

theorem burnsideF48d_chain_cert :
    burnsideF48d_ChainBound burnsideF48d_chainXL ∧ burnsideF48d_ChainBound burnsideF48d_chainBL :=
  Certificates.certificate7802

theorem burnsideF48d_nestedX : burnsideF48d_ChainNested burnsideF48d_chainXL := by
  unfold burnsideF48d_ChainNested
  decide +kernel

theorem burnsideF48d_nestedB : burnsideF48d_ChainNested burnsideF48d_chainBL := by
  unfold burnsideF48d_ChainNested
  decide +kernel

theorem burnsideF48d_tightX :
    (∀ j ≤ 8, Nat.card (burnsideF48d_lvH burnsideF48d_chainXL j) =
      ∏ l ∈ Finset.Ico j 8, (burnsideF48d_chainXL.getD l burnsideF48d_lv0).2.2) ∧
    ∀ i (hi : i < burnsideF48d_chainXL.length), burnsideF48d_lvH burnsideF48d_chainXL (i + 1) =
      burnsideF48d_lvH burnsideF48d_chainXL i ⊓
        MulAction.stabilizer ↥burnsideF48d_X burnsideF48d_chainXL[i].1 :=
  burnsideF48d_lvH_tight burnsideF48d_chain_cert.1 burnsideF48d_nestedX
    (burnsideF48d_card_X_le'.trans (by decide +kernel))

theorem burnsideF48d_card_X : Nat.card ↥burnsideF48d_X = 20560831566912 := by
  refine le_antisymm burnsideF48d_card_X_le' ?_
  have h := burnsideF48d_lvH_prod_le burnsideF48d_chain_cert.1 burnsideF48d_nestedX 0
    (Nat.zero_le _)
  have e : ∏ l ∈ Finset.Ico 0 burnsideF48d_chainXL.length,
      (burnsideF48d_chainXL.getD l burnsideF48d_lv0).2.2 = 20560831566912 := by
    decide +kernel
  rw [e] at h
  exact h.trans (Subgroup.card_le_card_group _)

theorem burnsideF48d_lvX_zero : burnsideF48d_lvH burnsideF48d_chainXL 0 = ⊤ := by
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [burnsideF48d_tightX.1 0 (by norm_num), burnsideF48d_card_X]
  decide +kernel

theorem burnsideF48d_mem_lvX : ∀ i ≤ 8, ∀ g : ↥burnsideF48d_X,
    g ∈ burnsideF48d_lvH burnsideF48d_chainXL i ↔
      ∀ t < i, (g : Equiv.Perm (Fin 26572)) (burnsideF48d_chainXL.getD t burnsideF48d_lv0).1 =
        (burnsideF48d_chainXL.getD t burnsideF48d_lv0).1 := by
  intro i
  induction i with
  | zero =>
    intro _ g
    rw [burnsideF48d_lvX_zero]
    simp
  | succ i ih =>
    intro hi g
    have hi8 : i < burnsideF48d_chainXL.length := by
      change i < 8
      omega
    rw [burnsideF48d_tightX.2 i hi8, Subgroup.mem_inf, ih (by omega), MulAction.mem_stabilizer_iff,
      ← burnsideF48d_getD_lv hi8]
    constructor
    · rintro ⟨h, hg⟩ t ht
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · exact h t ht
      · exact hg
    · intro h
      exact ⟨fun t ht => h t (by omega), h i (by omega)⟩

theorem burnsideF48d_mem_P1 (z : ↥burnsideF48d_X) :
    z ∈ burnsideF48d_P1 ↔ (z : Equiv.Perm (Fin 26572)) 0 = 0 := by
  have hS : ∀ j : Fin 17, j ∈ (burnsideF48d_chainXL.getD 1 burnsideF48d_lv0).2.1 ↔ j ≠ 1 := by
    decide +kernel
  have e : burnsideF48d_lvH burnsideF48d_chainXL 1 = burnsideF48d_P1 := by
    unfold burnsideF48d_lvH burnsideF48d_P1
    congr 2
    ext j
    exact hS j
  rw [← e, burnsideF48d_mem_lvX 1 (by norm_num)]
  constructor
  · intro h
    exact h 0 (by norm_num)
  · intro h t ht
    obtain rfl : t = 0 := by omega
    exact h


theorem burnsideF48d_base (z : ↥burnsideF48d_X)
    (h : ∀ p ∈ burnsideF48d_baseF, (z : Equiv.Perm (Fin 26572)) p = p) : z = 1 := by
  have h1 : ∀ t < 8, (burnsideF48d_chainXL.getD t burnsideF48d_lv0).1 ∈ burnsideF48d_baseF := by
    decide +kernel
  have hmem := (burnsideF48d_mem_lvX 8 le_rfl z).2 fun t ht => h _ (h1 t ht)
  rw [show (8 : ℕ) = burnsideF48d_chainXL.length from rfl, burnsideF48d_lvH_length] at hmem
  exact hmem


theorem burnsideF48d_trans (p : Fin 26572) :
    ∃ z : ↥burnsideF48d_X, (z : Equiv.Perm (Fin 26572)) 0 = p := by
  have h := (burnsideF48d_chain_cert.1 0 (by decide)).2
  have huniv : MulAction.orbit ↥(Subgroup.closure (burnsideF48d_L '' ↑burnsideF48d_chainXL[0].2.1))
      burnsideF48d_chainXL[0].1 = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact h
  have hp : p ∈ MulAction.orbit ↥(Subgroup.closure (burnsideF48d_L '' ↑burnsideF48d_chainXL[0].2.1))
      burnsideF48d_chainXL[0].1 := by
    rw [huniv]
    exact Set.mem_univ p
  obtain ⟨g, hg⟩ := hp
  exact ⟨(g : ↥burnsideF48d_X), hg⟩

end ChainX

section Equiv


end Equiv

end CFSG.ASVolI
