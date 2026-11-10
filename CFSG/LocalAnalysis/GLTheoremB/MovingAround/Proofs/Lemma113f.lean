module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113c

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)
open scoped Pointwise

namespace Lemma113f

variable {G : Type} [Group G] [Finite G]

theorem comm_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {x y : G}
    (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x :=
  congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem card_mul_le_card_inf_mul {A B R : Subgroup G} (hA : A ≤ R) (hB : B ≤ R) :
    Nat.card A * Nat.card B ≤ Nat.card (A ⊓ B : Subgroup G) * Nat.card R := by
  have h1 : (A ⊓ B).relIndex R ≤ A.relIndex R * B.relIndex R := Subgroup.relIndex_inf_le
  have hA' : A.relIndex R * Nat.card A = Nat.card R := by
    have := Subgroup.relIndex_mul_card (H := A) (K := R)
    rwa [inf_eq_left.2 hA] at this
  have hB' : B.relIndex R * Nat.card B = Nat.card R := by
    have := Subgroup.relIndex_mul_card (H := B) (K := R)
    rwa [inf_eq_left.2 hB] at this
  have hAB' : (A ⊓ B).relIndex R * Nat.card (A ⊓ B : Subgroup G) = Nat.card R := by
    have := Subgroup.relIndex_mul_card (H := A ⊓ B) (K := R)
    rwa [inf_eq_left.2 (inf_le_left.trans hA)] at this
  set i := A.relIndex R
  set j := B.relIndex R
  set k := (A ⊓ B).relIndex R
  set a := Nat.card A
  set b := Nat.card B
  set c := Nat.card (A ⊓ B : Subgroup G)
  set n := Nat.card R
  have hn : 0 < n := Nat.card_pos
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, zero_mul] at hAB'
      omega
    · exact h0
  have key : k * (a * b) ≤ k * (c * n) := by
    calc k * (a * b) ≤ (i * j) * (a * b) := Nat.mul_le_mul_right _ h1
      _ = (i * a) * (j * b) := by ring
      _ = n * n := by rw [hA', hB']
      _ = (k * c) * n := by rw [hAB']
      _ = k * (c * n) := by ring
  exact Nat.le_of_mul_le_mul_left key hkpos


theorem zmod3_pow_three_pow (y : ZMod 3) (m : ℕ) : y ^ (3 ^ m) = y := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_mul, ih]
    exact ZMod.pow_card y

theorem mul_comm_of_normalizer_zpowers_three_pow {e x : G} (he3 : e ^ 3 = 1) (he1 : e ≠ 1)
    (hx : x ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    {m : ℕ} (hm : x ^ (3 ^ m) = 1) : x * e = e * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf e = 3 := orderOf_eq_prime he3 he1
  obtain ⟨k, hk⟩ : ∃ k : ℤ, e ^ k = x * e * x⁻¹ :=
    Subgroup.mem_zpowers_iff.1 ((Subgroup.mem_normalizer_iff.1 hx e).1 (Subgroup.mem_zpowers e))
  have hc : ∀ j : ℤ, x * e ^ j * x⁻¹ = (x * e * x⁻¹) ^ j := fun j => by
    have := map_zpow (MulAut.conj x) e j
    simpa [MulAut.conj_apply] using this
  have hpow : ∀ n : ℕ, x ^ n * e * (x ^ n)⁻¹ = e ^ (k ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : x ^ (n + 1) * e * (x ^ (n + 1))⁻¹ = x * (x ^ n * e * (x ^ n)⁻¹) * x⁻¹ := by
        rw [pow_succ']
        group
      rw [h1, ih, hc, ← hk, ← zpow_mul]
      congr 1
      rw [pow_succ']
  have hfix : e ^ (k ^ (3 ^ m)) = e := by
    have := hpow (3 ^ m)
    rw [hm] at this
    simpa using this.symm
  have hzp : e ^ (k ^ (3 ^ m) - 1) = 1 := by
    rw [zpow_sub, zpow_one, hfix, mul_inv_cancel]
  have hdvd1 : (3 : ℤ) ∣ k ^ (3 ^ m) - 1 := by
    have h := (orderOf_dvd_iff_zpow_eq_one (x := e)).2 hzp
    rw [hord] at h
    exact_mod_cast h
  have hk1 : (k : ZMod 3) = 1 := by
    have h0 : (((k ^ (3 ^ m) - 1 : ℤ)) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (by exact_mod_cast hdvd1)
    push_cast at h0
    rw [sub_eq_zero] at h0
    rw [zmod3_pow_three_pow] at h0
    exact h0
  have hdvd2 : (3 : ℤ) ∣ k - 1 := by
    have h0 : (((k - 1 : ℤ)) : ZMod 3) = 0 := by
      push_cast
      rw [hk1, sub_self]
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 h0
  have hek : e ^ (k - 1) = 1 :=
    (orderOf_dvd_iff_zpow_eq_one (x := e)).1 (by rw [hord]; exact_mod_cast hdvd2)
  have hek' : e ^ k = e := by
    have : k = (k - 1) + 1 := by ring
    rw [this, zpow_add, hek, one_mul, zpow_one]
  have hxe : x * e * x⁻¹ = e := by rw [← hk, hek']
  calc x * e = (x * e * x⁻¹) * x := by group
    _ = e * x := by rw [hxe]

theorem exists_sylow_three_eight_of_index {E Q : Subgroup G} {e : G}
    (he3 : e ^ 3 = 1) (he1 : e ≠ 1)
    (hQN : Q ≤ Subgroup.normalizer (E : Set G))
    (hQC : IsSylowIn 3 (Subgroup.centralizer ({e} : Set G)) Q)
    (hQcard : Nat.card Q = 3 ^ 5)
    (hidx : Nat.card ↥(Subgroup.normalizer (E : Set G)) =
      27 * Nat.card ↥(Subgroup.normalizer (E : Set G) ⊓
        Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))) :
    ∃ R : Subgroup G, IsSylowIn 3 (Subgroup.normalizer (E : Set G)) R ∧ Q ≤ R ∧
      Nat.card R = 3 ^ 8 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup G := Subgroup.normalizer (E : Set G) with hN
  set S : Subgroup G := N ⊓ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)
    with hS
  set T : Subgroup G := N ⊓ Subgroup.centralizer ({e} : Set G) with hT
  have hQ0 : Q ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hQcard
    norm_num at hQcard
  have hQT : Q ≤ T := le_inf hQN hQC.1
  have hTS : T ≤ S := inf_le_inf_left _ (Lemma113b.centralizer_le_normalizer_zpowers' e)
  have hQT_syl : IsSylowIn 3 T Q :=
    ⟨hQT, hQC.2.1, fun R' hR'T hR'p hQR' => hQC.2.2 R' (hR'T.trans inf_le_right) hR'p hQR'⟩
  have hS3 : ∀ R' : Subgroup G, R' ≤ S → IsPGroup 3 ↥R' → R' ≤ T := by
    intro R' hR'S hR'p x hx
    obtain ⟨m, hm⟩ := hR'p ⟨x, hx⟩
    have hm' : x ^ (3 ^ m) = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hxS : x ∈ S := hR'S hx
    refine ⟨(Subgroup.mem_inf.1 hxS).1, Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)⟩
    rw [Set.mem_singleton_iff.1 hh]
    exact (mul_comm_of_normalizer_zpowers_three_pow he3 he1 (Subgroup.mem_inf.1 hxS).2 hm').symm
  have hQS : IsSylowIn 3 S Q :=
    ⟨hQT.trans hTS, hQC.2.1, fun R' hR'S hR'p hQR' =>
      hQT_syl.2.2 R' (hS3 R' hR'S hR'p) hR'p hQR'⟩
  obtain ⟨k1, hk1, hk1'⟩ := Lemma113c.isSylowIn_card_index hQS hQ0
  obtain ⟨R, hRsyl, hQR⟩ := Lemma113b.exists_sylowIn_above' hQN hQC.2.1
  have hR0 : R ≠ ⊥ := by
    intro h
    apply hQ0
    rw [h] at hQR
    exact le_bot_iff.1 hQR
  obtain ⟨k2, hk2, hk2'⟩ := Lemma113c.isSylowIn_card_index hRsyl hR0
  have hN_eq : Nat.card N = 3 ^ 8 * k1 := by
    rw [hidx, hk1, hQcard]
    ring
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 3)).1 hRsyl.2.1
  have hj8 : j = 8 := by
    have h : 3 ^ j * k2 = 3 ^ 8 * k1 := by
      rw [← hj, ← hk2, hN_eq]
    exact Lemma113c.pow_three_eq_of_mul h hk2' hk1'
  exact ⟨R, hRsyl, hQR, by rw [hj, hj8]⟩

theorem mem_centBar_iff {p : ℕ} {X L : Subgroup G} {g : G} :
    g ∈ centBar p X L ↔ g ∈ X ∧ ∃ h : g ∈ Subgroup.normalizer (L : Set G),
      barAut p L ⟨g, h⟩ = 1 := by
  unfold centBar
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨n, hn, hng⟩, hX⟩
    subst hng
    exact ⟨hX, n.2, MonoidHom.mem_ker.1 hn⟩
  · rintro ⟨hX, h, hb⟩
    exact ⟨⟨⟨g, h⟩, MonoidHom.mem_ker.2 hb, rfl⟩, hX⟩


theorem le_normalizer_of_eq_thompsonJ {E Q : Subgroup G} (hEJ : E = thompsonJ 3 Q) :
    Q ≤ Subgroup.normalizer (E : Set G) := by
  intro q hq
  have hqn : q ∈ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer hq
  apply mem_normalizer_of_GLBConj_eq
  rw [hEJ]
  exact GLBConj_thompsonJ_eq (p := 3) hqn


end Lemma113f

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
