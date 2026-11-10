module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.NodeTab
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.DigitConds
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.SmallCheck

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem

section NodeBound


variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]
  {s : Fin τ.rank}

theorem odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ⟨2 ^ m - 1, by rw [pow_succ]; have := Nat.one_le_two_pow (n := m); omega⟩

include hw in
theorem node_dim_big [Module.Finite k V] (T : NodeTab τ s) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) (hJ : ∀ s', s' ≠ s → s' ∈ J) (hs : s ∉ J)
    {J' : Finset ℕ} (hJ' : ∀ i ∈ J', i < n) (h2 : 2 ≤ J'.card)
    (hgood : ∑ i ∈ J', 2 ^ i < 2 ^ n - 1 →
      3 ≤ Nat.gcd (∑ i ∈ J', 2 ^ i) (2 ^ n - 1) ∨ (J'.card ≤ 3 ∧ 6 ≤ n))
    (hvec : ∀ b ∈ J', ∃ e ∈ orbitSpan (ρ.comp (rankOne τ K s)) y, e ≠ 0 ∧
      e ∈ wtE ρ (((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) • omegaF τ s - (2 : ℤ) ^ b • alphaF τ s)) :
    T.A * T.B ≤ Module.finrank k V := by
  classical
  obtain ⟨b, hb⟩ : J'.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨e, he, he0, hew⟩ := hvec b hb
  set a : ℕ := ∑ i ∈ J', 2 ^ i with ha
  have hbn : b < n := hJ' b hb
  have hn2 : 2 ≤ n := by
    by_contra hcon
    have hsub : J' ⊆ Finset.range n := fun i hi => Finset.mem_range.2 (hJ' i hi)
    have := Finset.card_le_card hsub
    simp at this
    omega
  have hMod : Odd (2 ^ n - 1) := odd_two_pow_sub_one hn
  have haM' : a ≤ 2 ^ n - 1 := sum_two_pow_le J' hJ'
  have ha0 : 0 < a := lt_of_le_of_lt (Nat.zero_le _) (pair_le_sum h2 hb)
  by_cases haM : a = 2 ^ n - 1
  ·
    rw [haM] at hew
    exact node_dim_R2 (hw := hw) T.wW T.uW hρ ht hs hK hn2 b T.fam_hU T.fam_hU2 T.v0F T.fam_hv0
      T.fam_hdist T.fam_hβinj T.fam_hβ he he0 hew
  · have haM2 : a < 2 ^ n - 1 := by omega
    have hA0 : ¬ (((2 ^ n - 1 : ℕ) : ℤ) ∣ (a : ℤ)) := by
      intro h
      have := Int.le_of_dvd (by exact_mod_cast ha0) h
      have h' : 2 ^ n - 1 ≤ a := by exact_mod_cast this
      omega
    refine node_dim_of_sep (hw := hw) T.wW T.uW hρ hK a b T.fam_hU he0 hew ?_
    intro p q hcong
    have hcong' : ∀ i, (((2 ^ n - 1 : ℕ) : ℤ)) ∣ ((a : ℤ) * famX τ s T.wW T.uW p.1 p.2 i -
        2 ^ b * famB τ s T.wW p.1 i) - ((a : ℤ) * famX τ s T.wW T.uW q.1 q.2 i -
        2 ^ b * famB τ s T.wW q.1 i) := by
      intro i
      simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hcong i
    have hinjP : ∀ p q : Fin T.A × Fin T.B, famX τ s T.wW T.uW p.1 p.2 = famX τ s T.wW T.uW q.1 q.2 →
        famB τ s T.wW p.1 = famB τ s T.wW q.1 → p = q := by
      intro p q h1 h2
      obtain ⟨e1, e2⟩ := T.fam_hinj p.1 q.1 p.2 q.2 h1 h2
      exact Prod.ext e1 e2
    by_cases h3 : 3 ≤ Nat.gcd a (2 ^ n - 1)
    · exact class_sep_gcd (fun p : Fin T.A × Fin T.B => famX τ s T.wW T.uW p.1 p.2)
        (fun p => famB τ s T.wW p.1) (2 ^ n - 1) a b hMod h3
        (fun p q h => T.fam_hβ p.1 q.1 h) (fun p q h => T.fam_hX p.1 q.1 p.2 q.2 h) hinjP hA0 p q
        hcong'
    · have hcard3 : J'.card ≤ 3 := by
        rcases hgood haM2 with h | h
        · exact absurd h h3
        · exact h.1
      have hgcd1 : Nat.gcd a (2 ^ n - 1) = 1 := by
        have hodd : Odd (Nat.gcd a (2 ^ n - 1)) := Odd.of_dvd_nat hMod (Nat.gcd_dvd_right _ _)
        have hpos : 0 < Nat.gcd a (2 ^ n - 1) := Nat.gcd_pos_of_pos_left _ ha0
        rcases hodd with ⟨m, hm⟩
        omega
      have hn6 : 6 ≤ n := by
        rcases hgood haM2 with h | h
        · exact absurd h h3
        · exact h.2
      have hbig : 32 < 2 ^ n - 1 := by
        have : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn6
        omega
      have hD3 := digit_D3 (J' := J') (n := n) (by omega)
      obtain ⟨c0, c1, c2, c3, c4, c5, c6⟩ := digit_conds hn2 hJ' hb h2 haM2 hD3
      exact class_sep_unit (fun p : Fin T.A × Fin T.B => famX τ s T.wW T.uW p.1 p.2)
        (fun p => famB τ s T.wW p.1) (2 ^ n - 1) a b hMod hbig hgcd1
        (fun p i => T.fam_bdX p.1 p.2 i) (fun p i => T.fam_bdβ p.1 i)
        (fun p q h => T.fam_hβ p.1 q.1 h) (fun p q h => T.fam_hX p.1 q.1 p.2 q.2 h) hinjP
        c0 c1 c2 c3 c4 c5 c6 p q hcong'


include hw in
theorem node_copies [Module.Finite k V] (T : NodeTab τ s) {ρ : Representation k (adjointGroup τ K) V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) (hs : s ∉ J) :
    T.B * Module.finrank k (orbitSpan (ρ.comp (rankOne τ K s)) y) ≤ Module.finrank k V := by
  let u' : Fin T.B → WeylGroup τ := fun j => (coxeterSystem τ).wordProd (T.uW j)
  have hu : ∀ j, u' j • (Pi.single s 1 : Fin τ.rank → ℤ) = Pi.single s 1 := by
    intro j; rw [wordProd_smul', T.fam_hU2 j]
  have hli : LinearIndependent k (fun j => ρ (nWC τ K (u' j)) y) := by
    refine linearIndependent_translates_of_isChevType hρ ht hs T.fam_hv0 u' ?_
    intro j j' hjj h
    apply T.fam_hdist j j' hjj
    have := h
    simp only [u', wordProd_smul'] at this
    exact this
  exact copies_finrank_orbit hρ ht u' hu hli


end NodeBound

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
