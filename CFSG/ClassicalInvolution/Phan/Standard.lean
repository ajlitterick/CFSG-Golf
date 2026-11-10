module

public import CFSG.ClassicalInvolution.Phan.Residues

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.Monster.B.Geometry

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

variable (K p f) in
@[expose] noncomputable def standardU (n : ℕ) (i : Fin n) : Subgroup (Su K p f (n + 1)) :=
  (blockEmb2 K p f n i).range

variable (K p f) in
@[expose] noncomputable def standardW (n : ℕ) (i j : Fin n) : Subgroup (Su K p f (n + 1)) :=
  standardU K p f n i ⊔ standardU K p f n j

variable (K p f) in
@[expose] noncomputable def standardFamily (n : ℕ) : PhanFamily K p f (Su K p f (n + 1)) n where
  ι i := blockEmb2 K p f n i
  θ i := if h : (i : ℕ) + 1 < n then blockEmb3 K p f n i h else 1
  left i h := by
    rw [dite_eq_left h]
    exact blockEmb3_comp_embSUid_two n i h
  right i h := by
    rw [dite_eq_left h]
    exact blockEmb3_comp_embSUid_zero n i h
  comm i j hij A B := blockEmb2_comm n i j hij A B


omit [Fact p.Prime] [CharP K p] in
theorem three_le_pow_of_card (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) : 3 ≤ p ^ f := by
  have := one_lt_pow_of_card hK
  omega

theorem torus_le_iSup_blockEmb2 (n : ℕ) :
    torus (unitaryInvolution K p f) (n + 1) ≤ ⨆ i : Fin n, (blockEmb2 K p f n i).range := by
  set H : Subgroup (Su K p f (n + 1)) := ⨆ i : Fin n, (blockEmb2 K p f n i).range with hH
  intro t ht
  obtain ⟨s, hs⟩ := (torusEquiv (unitaryInvolution K p f) n).surjective ⟨t, ht⟩
  have key : ∀ S : Finset (Fin n),
      ((torusEquiv (unitaryInvolution K p f) n (∏ k ∈ S, Pi.mulSingle k (s k)) :
        torus (unitaryInvolution K p f) (n + 1)) : Su K p f (n + 1)) ∈ H := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, map_one]
      exact H.one_mem
    | insert k S hk ih =>
      rw [Finset.prod_insert hk, map_mul, Subgroup.coe_mul]
      refine H.mul_mem ?_ ih
      rw [coe_torusEquiv_mulSingle]
      exact Subgroup.mem_iSup_of_mem k ⟨_, rfl⟩
  have := key Finset.univ
  rw [Finset.univ_prod_mulSingle, hs] at this
  exact this

theorem iSup_range_blockEmb2 (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) (n : ℕ) :
    ⨆ i : Fin n, (blockEmb2 K p f n i).range = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨γ, hγ, hend⟩ := frameSystem_connected (isUnitaryInvolution_unitaryInvolution hK) hK
    (three_le_pow_of_card hK hq) (stdFrame (unitaryInvolution K p f) (n + 1))
    (x • stdFrame (unitaryInvolution K p f) (n + 1))
  have hx : x ∈ parabolic K p f n Set.univ :=
    (mem_parabolic_iff hK Set.univ x).2 ⟨γ, hγ, fun _ _ => Set.mem_univ _, hend⟩
  rw [parabolic_def] at hx
  exact sup_le (torus_le_iSup_blockEmb2 n)
    (iSup₂_le fun j _ => le_iSup (fun i : Fin n => (blockEmb2 K p f n i).range) j) hx

theorem B12_sup_B23 (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) :
    B12 K p f ⊔ B23 K p f = ⊤ := by
  rw [eq_top_iff, ← iSup_range_blockEmb2 hK hq 2]
  refine iSup_le fun i => ?_
  fin_cases i
  · change (blockEmb K p f 3 2 0 (by omega)).range ≤ _
    rw [B12, embSUid_two_eq_blockEmb]
    exact le_sup_left
  · change (blockEmb K p f 3 2 1 (by omega)).range ≤ _
    rw [B23, embSUid_zero_eq_blockEmb]
    exact le_sup_right

theorem map_B12_blockEmb3 (n : ℕ) (i : Fin n) (h : (i : ℕ) + 1 < n) :
    (B12 K p f).map (blockEmb3 K p f n i h) = (blockEmb2 K p f n i).range := by
  rw [B12, ← MonoidHom.range_comp, blockEmb3_comp_embSUid_two]

theorem map_B23_blockEmb3 (n : ℕ) (i : Fin n) (h : (i : ℕ) + 1 < n) :
    (B23 K p f).map (blockEmb3 K p f n i h) = (blockEmb2 K p f n ⟨i + 1, h⟩).range := by
  rw [B23, ← MonoidHom.range_comp, blockEmb3_comp_embSUid_zero]

theorem range_blockEmb3 (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) (n : ℕ) (i : Fin n)
    (h : (i : ℕ) + 1 < n) :
    (blockEmb3 K p f n i h).range =
      (blockEmb2 K p f n i).range ⊔ (blockEmb2 K p f n ⟨i + 1, h⟩).range := by
  rw [MonoidHom.range_eq_map, ← B12_sup_B23 hK hq, Subgroup.map_sup, map_B12_blockEmb3,
    map_B23_blockEmb3]


theorem weakPhanA_standard (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) (n : ℕ) :
    WeakPhanA K p f n (standardU K p f n) (standardW K p f n) where
  iso i := ⟨MonoidHom.ofInjective (blockEmb2_injective n i)⟩
  join _ _ _ := rfl
  comm i j hij := by
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    exact blockEmb2_comm n i j hij A B
  pair i j hj := by
    have h : (i : ℕ) + 1 < n := by have := j.isLt; omega
    obtain rfl : j = ⟨i + 1, h⟩ := Fin.ext hj
    have hc : ∀ H : Subgroup (Su K p f 3), H.map (MulAut.conj (1 : Su K p f 3)⁻¹).toMonoidHom = H :=
      fun H => by ext x; simp
    refine ⟨blockEmb3 K p f n i h, 1, range_blockEmb3 hK hq n i h, ?_, Or.inl ⟨?_, ?_⟩⟩
    · rw [(MonoidHom.ker_eq_bot_iff _).mpr (blockEmb3_injective n i h)]
      exact bot_le
    · rw [hc, map_B12_blockEmb3]
      rfl
    · rw [hc, map_B23_blockEmb3]
      rfl
  gen := iSup_range_blockEmb2 hK hq n

theorem sup_range_blockEmb2_three (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) :
    (blockEmb2 K p f 3 0).range ⊔ (blockEmb2 K p f 3 1).range ⊔ (blockEmb2 K p f 3 2).range =
      ⊤ := by
  rw [eq_top_iff, ← iSup_range_blockEmb2 hK hq 3]
  refine iSup_le fun l => ?_
  fin_cases l
  · exact le_sup_of_le_left (le_sup_of_le_left le_rfl)
  · exact le_sup_of_le_left (le_sup_of_le_right le_rfl)
  · exact le_sup_of_le_right le_rfl


end CFSG.ClassicalInvolution.Phan
