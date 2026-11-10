module

public import CFSG.LocalAnalysis.StandardType.GGDRootOrbit
public import CFSG.LocalAnalysis.StandardType.GGLatticeWitness

public section

namespace CFSG.StandardType

private def lwd_root0 : ℕ → ℤ := fun i => if i = 0 then 1 else 0

private theorem lwd_GGDRoot_root0 {m : ℕ} (hm : 5 ≤ m) : GGDRoot m lwd_root0 := by
  refine ⟨0, 1, by omega, by omega, by omega, 1, -1, Or.inl rfl, Or.inr rfl, ?_⟩
  intro k
  unfold ggDeps lwd_root0
  split_ifs <;> omega

private theorem lwd_getD_range_map (f : ℕ → ℤ) {m i : ℕ} (hi : i < m) :
    ((List.range m).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

private theorem lwd_dvd_foldl_gcd {p : ℕ} (init : ℕ) (hp : p ∣ init) (l : List ℕ)
    (h : ∀ x ∈ l, p ∣ x) : p ∣ l.foldl Nat.gcd init := by
  induction l generalizing init with
  | nil => simpa using hp
  | cons a t ih =>
    rw [List.foldl_cons]
    exact ih (Nat.gcd init a) (Nat.dvd_gcd hp (h a (by simp)))
      (fun x hx => h x (by simp [hx]))

private theorem lwd_dvd_ggLWminors {p : ℕ} {u v : List ℤ}
    (h : ∀ i j, i < u.length → j < u.length →
      (p : ℤ) ∣ (u.getD i 0 * v.getD j 0 - u.getD j 0 * v.getD i 0)) :
    p ∣ ggLWminors u v := by
  rw [ggLWminors]
  refine lwd_dvd_foldl_gcd 0 (by simp) _ ?_
  intro x hx
  rw [List.mem_flatMap] at hx
  obtain ⟨i, hi, hx⟩ := hx
  rw [List.mem_filterMap] at hx
  obtain ⟨j, hj, hx⟩ := hx
  rw [List.mem_range] at hi hj
  by_cases hij : i < j
  · rw [if_pos hij] at hx
    have hx' : x = (u.getD i 0 * v.getD j 0 - u.getD j 0 * v.getD i 0).natAbs :=
      (Option.some.inj hx).symm
    rw [hx']
    exact (Int.natCast_dvd).mp (h i j hi hj)
  · rw [if_neg hij] at hx
    exact absurd hx (by simp)

private theorem lwd_prime_not_dvd_twelve {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : ¬ p ∣ 12 := by
  intro h
  have hp12 : p ∣ 2 * (2 * 3) := by norm_num; exact h
  rcases hp.dvd_mul.mp hp12 with h2 | h23
  · have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    omega
  · rcases hp.dvd_mul.mp h23 with h2 | h3
    · have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
      omega
    · have : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3
      omega

theorem ggD_nonprop {n b₀ : ℕ} (hb₀ : 5 ≤ b₀) (hn : b₀ ≤ n) {w : ℕ → ℤ}
    (hw : ∀ i < n - b₀, w i = 0)
    (hblock : ∀ u ∈ ggDRootList b₀,
      12 % ggLWminors ((List.range b₀).map fun i => w (n - b₀ + i)) u = 0)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {v : ℕ → ℤ} (hv : GGDRoot n v) (t : ZMod p) :
    ¬ ∀ i < n, ((w i : ℤ) : ZMod p) = t * ((v i : ℤ) : ZMod p) := by
  intro hprop
  haveI : Fact p.Prime := ⟨hp⟩
  have hn5 : 5 ≤ n := le_trans hb₀ hn
  have hp12 : p ∣ 12 := by
    by_cases ht : t = 0
    · have hwp : ∀ i < n, (p : ℤ) ∣ w i := by
        intro i hi
        have h := hprop i hi
        rw [ht, zero_mul] at h
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd (w i) p).mp h
      have hmem : (List.range b₀).map lwd_root0 ∈ ggDRootList b₀ :=
        ggDRoot_mem_ggDRootList (by omega) (lwd_GGDRoot_root0 hb₀)
      have hblk := hblock _ hmem
      refine dvd_trans ?_ (Nat.dvd_of_mod_eq_zero hblk)
      apply lwd_dvd_ggLWminors
      intro i j hi hj
      have hi' : i < b₀ := by simpa using hi
      have hj' : j < b₀ := by simpa using hj
      rw [lwd_getD_range_map (f := fun i => w (n - b₀ + i)) hi',
        lwd_getD_range_map (f := fun i => w (n - b₀ + i)) hj']
      exact dvd_sub (dvd_mul_of_dvd_left (hwp (n - b₀ + i) (by omega)) _)
        (dvd_mul_of_dvd_left (hwp (n - b₀ + j) (by omega)) _)
    · have hv0 : ∀ i < n - b₀, v i = 0 := by
        intro i hi
        have h := hprop i (by omega)
        rw [hw i hi] at h
        simp only [Int.cast_zero] at h
        have hz : ((v i : ℤ) : ZMod p) = 0 := by
          have h' : t * ((v i : ℤ) : ZMod p) = 0 := h.symm
          rcases mul_eq_zero.mp h' with h0 | h0
          · exact absurd h0 ht
          · exact h0
        have hdvd : (p : ℤ) ∣ v i := (ZMod.intCast_zmod_eq_zero_iff_dvd (v i) p).mp hz
        have hle : |v i| ≤ (2 : ℤ) := ggDRoot_abs_le hn5 hv (by omega)
        by_contra hne
        have hz2 : (v i).natAbs ≤ 2 := by
          have h1 : v i ≤ 2 := (abs_le.mp hle).2
          have h2 : -2 ≤ v i := (abs_le.mp hle).1
          rcases Int.eq_nat_or_neg (v i) with ⟨k, hk | hk⟩
          · rw [hk]; simp only [Int.natAbs_natCast]; omega
          · rw [hk]; rw [Int.natAbs_neg, Int.natAbs_natCast]; omega
        have hdvd' : p ∣ (v i).natAbs := (Int.natCast_dvd).mp hdvd
        have hpos : 0 < (v i).natAbs := Int.natAbs_pos.mpr hne
        have : p ≤ (v i).natAbs := Nat.le_of_dvd hpos hdvd'
        omega
      have htail := ggDRoot_tail (n := n) (m := n - b₀) (by omega) hv hv0
      have hb_eq : n - (n - b₀) = b₀ := by omega
      rw [hb_eq] at htail
      have hmem : (List.range b₀).map (fun i => v (n - b₀ + i)) ∈ ggDRootList b₀ :=
        ggDRoot_mem_ggDRootList (by omega) htail
      have hblk := hblock _ hmem
      refine dvd_trans ?_ (Nat.dvd_of_mod_eq_zero hblk)
      apply lwd_dvd_ggLWminors
      intro i j hi hj
      have hi' : i < b₀ := by simpa using hi
      have hj' : j < b₀ := by simpa using hj
      rw [lwd_getD_range_map (f := fun i => w (n - b₀ + i)) hi',
        lwd_getD_range_map (f := fun i => w (n - b₀ + i)) hj',
        lwd_getD_range_map (f := fun i => v (n - b₀ + i)) hi',
        lwd_getD_range_map (f := fun i => v (n - b₀ + i)) hj']
      have hz : (((w (n - b₀ + i) * v (n - b₀ + j)
          - w (n - b₀ + j) * v (n - b₀ + i)) : ℤ) : ZMod p) = 0 := by
        have hi2 := hprop (n - b₀ + i) (by omega)
        have hj2 := hprop (n - b₀ + j) (by omega)
        push_cast
        rw [hi2, hj2]
        ring
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz
  exact lwd_prime_not_dvd_twelve hp h5 hp12

@[expose] def lwd_shift {n b₀ : ℕ} (hn : b₀ ≤ n) : Option (Fin b₀) → Option (Fin n)
  | none => none
  | some i => some ⟨n - b₀ + i, by have := i.isLt; omega⟩

private theorem lwd_shift_inj {n b₀ : ℕ} (hn : b₀ ≤ n) :
    Function.Injective (lwd_shift hn) := by
  intro x y h
  rcases x with _ | x <;> rcases y with _ | y
  · rfl
  · simp only [lwd_shift] at h
    exact absurd h (by simp)
  · simp only [lwd_shift] at h
    exact absurd h (by simp)
  · simp only [lwd_shift, Option.some.injEq] at h
    have hv : (n - b₀ + x : ℕ) = n - b₀ + y := congrArg Fin.val h
    have hx : (x : ℕ) = y := by omega
    exact congrArg some (Fin.ext hx)

@[expose] def lwd_single {n b₀ : ℕ} (hn : b₀ ≤ n) (j : Option (Fin b₀)) :
    Option (Fin n) → ℤ :=
  Pi.single (lwd_shift hn j) (1 : ℤ)

@[expose] def lwd_extend {n b₀ : ℕ} (hn : b₀ ≤ n) (m : Option (Fin b₀) → ℤ) :
    Option (Fin n) → ℤ :=
  ∑ j, m j • lwd_single hn j

theorem lwd_extend_shift {n b₀ : ℕ} (hn : b₀ ≤ n) (m : Option (Fin b₀) → ℤ)
    (x : Option (Fin b₀)) : lwd_extend hn m (lwd_shift hn x) = m x := by
  unfold lwd_extend lwd_single
  rw [Finset.sum_apply, Fintype.sum_eq_single x]
  · rw [Pi.smul_apply, smul_eq_mul, Pi.single_apply, if_pos rfl, mul_one]
  · intro j hj
    rw [Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      if_neg (fun h => hj (lwd_shift_inj hn h).symm), mul_zero]

theorem lwd_extend_single {n b₀ : ℕ} (hn : b₀ ≤ n) (x : Option (Fin b₀)) :
    lwd_extend hn (Pi.single x 1) = lwd_single hn x := by
  unfold lwd_extend lwd_single
  rw [Fintype.sum_eq_single x]
  · rw [Pi.single_eq_same, one_smul]
  · intro j hj
    rw [Pi.single_eq_of_ne hj, zero_smul]


theorem lwd_extend_sub_smul {n b₀ : ℕ} (hn : b₀ ≤ n) (m m' : Option (Fin b₀) → ℤ)
    (r : ℤ) : lwd_extend hn (m - r • m') = lwd_extend hn m - r • lwd_extend hn m' := by
  unfold lwd_extend
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul, mul_smul]

theorem lwd_dot_extend {n b₀ : ℕ} (hn : b₀ ≤ n)
    {Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ}
    {Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ}
    (hX : ∀ i j, Xn (lwd_shift hn i) (lwd_shift hn j) = Xb i j)
    (m : Option (Fin b₀) → ℤ) (i : Option (Fin b₀)) :
    (∑ y, Xn (lwd_shift hn i) y * lwd_extend hn m y) = ∑ j, Xb i j * m j := by
  have hstep : ∀ y, lwd_extend hn m y = ∑ j, m j * lwd_single hn j y := by
    intro y
    unfold lwd_extend
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Pi.smul_apply, smul_eq_mul]
  calc ∑ y, Xn (lwd_shift hn i) y * lwd_extend hn m y
      = ∑ y, ∑ j, Xn (lwd_shift hn i) y * (m j * lwd_single hn j y) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [hstep y, Finset.mul_sum]
    _ = ∑ j, ∑ y, Xn (lwd_shift hn i) y * (m j * lwd_single hn j y) :=
          Finset.sum_comm
    _ = ∑ j, m j * Xn (lwd_shift hn i) (lwd_shift hn j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [show (∑ y, Xn (lwd_shift hn i) y * (m j * lwd_single hn j y))
              = m j * ∑ y, Xn (lwd_shift hn i) y * lwd_single hn j y by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y _
                ring]
          rw [show (∑ y, Xn (lwd_shift hn i) y * lwd_single hn j y)
              = Xn (lwd_shift hn i) (lwd_shift hn j) by
                unfold lwd_single
                rw [Fintype.sum_eq_single (lwd_shift hn j)
                  (fun y hy => by rw [Pi.single_eq_of_ne hy, mul_zero])]
                rw [Pi.single_eq_same, mul_one]]
    _ = ∑ j, Xb i j * m j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hX i j]
          ring

theorem lwd_dot_extendR {n b₀ : ℕ} (hn : b₀ ≤ n)
    {Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ}
    {Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ}
    (hX : ∀ i j, Xn (lwd_shift hn i) (lwd_shift hn j) = Xb i j)
    (m : Option (Fin b₀) → ℤ) (i : Option (Fin b₀)) :
    (∑ y, lwd_extend hn m y * Xn y (lwd_shift hn i)) = ∑ j, m j * Xb j i := by
  have hstep : ∀ y, lwd_extend hn m y = ∑ j, m j * lwd_single hn j y := by
    intro y
    unfold lwd_extend
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Pi.smul_apply, smul_eq_mul]
  calc ∑ y, lwd_extend hn m y * Xn y (lwd_shift hn i)
      = ∑ y, ∑ j, m j * lwd_single hn j y * Xn y (lwd_shift hn i) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [hstep y, Finset.sum_mul]
    _ = ∑ j, ∑ y, m j * lwd_single hn j y * Xn y (lwd_shift hn i) :=
          Finset.sum_comm
    _ = ∑ j, m j * Xn (lwd_shift hn j) (lwd_shift hn i) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [show (∑ y, m j * lwd_single hn j y * Xn y (lwd_shift hn i))
              = m j * ∑ y, lwd_single hn j y * Xn y (lwd_shift hn i) by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y _
                ring]
          rw [show (∑ y, lwd_single hn j y * Xn y (lwd_shift hn i))
              = Xn (lwd_shift hn j) (lwd_shift hn i) by
                unfold lwd_single
                rw [Fintype.sum_eq_single (lwd_shift hn j)
                  (fun y hy => by rw [Pi.single_eq_of_ne hy, zero_mul])]
                rw [Pi.single_eq_same, one_mul]]
    _ = ∑ j, m j * Xb j i := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hX j i]

private theorem lwd_sRefl_extend {n b₀ : ℕ} (hn : b₀ ≤ n)
    {Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ}
    {Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ}
    (hX : ∀ i j, Xn (lwd_shift hn i) (lwd_shift hn j) = Xb i j)
    (j : Option (Fin b₀)) (m : Option (Fin b₀) → ℤ) :
    ggSRefl Xn (lwd_shift hn j) (lwd_extend hn m) = lwd_extend hn (ggSRefl Xb j m) := by
  rw [show ggSRefl Xn (lwd_shift hn j) (lwd_extend hn m)
      = lwd_extend hn m - (∑ y, Xn (lwd_shift hn j) y * lwd_extend hn m y) •
          lwd_single hn j from rfl]
  rw [lwd_dot_extend hn hX m j]
  rw [show ggSRefl Xb j m = m - (∑ i, Xb j i * m i) • Pi.single j (1:ℤ) from rfl]
  rw [lwd_extend_sub_smul, lwd_extend_single]

private theorem lwd_sReflR_extend {n b₀ : ℕ} (hn : b₀ ≤ n)
    {Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ}
    {Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ}
    (hX : ∀ i j, Xn (lwd_shift hn i) (lwd_shift hn j) = Xb i j)
    (j : Option (Fin b₀)) (m : Option (Fin b₀) → ℤ) :
    ggSReflR Xn (lwd_shift hn j) (lwd_extend hn m) = lwd_extend hn (ggSReflR Xb j m) := by
  rw [show ggSReflR Xn (lwd_shift hn j) (lwd_extend hn m)
      = lwd_extend hn m - (∑ y, lwd_extend hn m y * Xn y (lwd_shift hn j)) •
          lwd_single hn j from rfl]
  rw [lwd_dot_extendR hn hX m j]
  rw [show ggSReflR Xb j m = m - (∑ i, m i * Xb i j) • Pi.single j (1:ℤ) from rfl]
  rw [lwd_extend_sub_smul, lwd_extend_single]

theorem lwd_sWord_extend {n b₀ : ℕ} (hn : b₀ ≤ n)
    {Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ}
    {Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ}
    (hX : ∀ i j, Xn (lwd_shift hn i) (lwd_shift hn j) = Xb i j)
    (ψ : List (Option (Fin b₀))) (m : Option (Fin b₀) → ℤ) :
    ggSWord Xn (ψ.map (lwd_shift hn)) (lwd_extend hn m)
      = lwd_extend hn (ggSWord Xb ψ m) := by
  induction ψ generalizing m with
  | nil => rw [List.map_nil]; rfl
  | cons j ψ ih =>
    rw [List.map_cons, ggSWord, ggSWord, ih, lwd_sRefl_extend hn hX]

theorem lwd_sWordR_extend {n b₀ : ℕ} (hn : b₀ ≤ n)
    {Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ}
    {Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ}
    (hX : ∀ i j, Xn (lwd_shift hn i) (lwd_shift hn j) = Xb i j)
    (ψ : List (Option (Fin b₀))) (m : Option (Fin b₀) → ℤ) :
    ggSWordR Xn (ψ.map (lwd_shift hn)) (lwd_extend hn m)
      = lwd_extend hn (ggSWordR Xb ψ m) := by
  induction ψ generalizing m with
  | nil => rw [List.map_nil]; rfl
  | cons j ψ ih =>
    rw [List.map_cons, ggSWordR, ggSWordR, ih, lwd_sReflR_extend hn hX]

private theorem lwd_D_sub {n b₀ : ℕ} (hb : 3 ≤ b₀) (hn : b₀ ≤ n) {i j : Fin b₀} :
    CartanMatrix.D n ⟨n - b₀ + i, by omega⟩ ⟨n - b₀ + j, by omega⟩ =
      CartanMatrix.D b₀ i j := by
  have hi : (i : ℕ) < b₀ := i.isLt
  have hj : (j : ℕ) < b₀ := j.isLt
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem lwd_attach_sub {n b₀ : ℕ} (hb : 4 ≤ b₀) (hn : b₀ ≤ n)
    (kb : Fin b₀) {k : Fin n} (hk : k = ⟨n - b₀ + kb, by omega⟩) (i j : Option (Fin b₀)) :
    ggAttachCartan (CartanMatrix.D n) k (lwd_shift hn i) (lwd_shift hn j) =
      ggAttachCartan (CartanMatrix.D b₀) kb i j := by
  rcases i with _ | i <;> rcases j with _ | j
  · rfl
  · simp only [lwd_shift, ggAttachCartan_none_some]
    rw [hk]
    by_cases h : j = kb
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (by
        intro hh
        exact h (Fin.ext (by
          have h' : n - b₀ + (j : ℕ) = n - b₀ + (kb : ℕ) := congrArg Fin.val hh
          omega)))]
  · simp only [lwd_shift, ggAttachCartan_some_none]
    rw [hk]
    by_cases h : i = kb
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (by
        intro hh
        exact h (Fin.ext (by
          have h' : n - b₀ + (i : ℕ) = n - b₀ + (kb : ℕ) := congrArg Fin.val hh
          omega)))]
  · simp only [lwd_shift, ggAttachCartan_some_some]
    exact lwd_D_sub (by omega) hn

theorem lwd_extend_eq_zero_of_not_mem {n b₀ : ℕ} (hn : b₀ ≤ n)
    (m : Option (Fin b₀) → ℤ) {y : Option (Fin n)}
    (hy : y ∉ Set.range (lwd_shift hn)) : lwd_extend hn m y = 0 := by
  unfold lwd_extend lwd_single
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  rw [Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    if_neg (fun h => hy ⟨j, h.symm⟩), mul_zero]

theorem lwd_not_mem_shift {n b₀ : ℕ} (hn : b₀ ≤ n) {i : ℕ} (hi : i < n - b₀) :
    (some ⟨i, by omega⟩ : Option (Fin n)) ∉ Set.range (lwd_shift hn) := by
  rintro ⟨x, hx⟩
  rcases x with _ | x
  · simp only [lwd_shift] at hx
    exact absurd hx (by simp)
  · simp only [lwd_shift, Option.some.injEq] at hx
    have hix : i = n - b₀ + x := (congrArg Fin.val hx).symm
    have := x.isLt
    omega


@[expose] def lwd_psig5 : List (Option (Fin 5)) :=
  [some ⟨2, by decide⟩, some ⟨4, by decide⟩, some ⟨1, by decide⟩, some ⟨2, by decide⟩, none,
    some ⟨3, by decide⟩, some ⟨2, by decide⟩, some ⟨1, by decide⟩]

@[expose] def lwd_gb5 : Option (Fin 5) → ℤ
  | none => 1
  | some i => ![1, 2, 4, 1, 2] i

theorem lwd_gb5_eq :
    ggSWord (ggAttachCartan (CartanMatrix.D 5) ⟨2, by decide⟩) lwd_psig5
      (Pi.single (some ⟨0, by decide⟩) 1) = lwd_gb5 := by
  funext i
  rcases i with _ | i
  · decide +kernel
  · fin_cases i <;> decide +kernel

theorem lwd_gRb5_eq :
    ggSWordR (ggAttachCartan (CartanMatrix.D 5) ⟨2, by decide⟩) lwd_psig5
      (Pi.single (some ⟨0, by decide⟩) 1) = lwd_gb5 := by
  funext i
  rcases i with _ | i
  · decide +kernel
  · fin_cases i <;> decide +kernel

theorem lwd_gb5_none : lwd_gb5 none = 1 := rfl

theorem lwd_hP1_5 :
    (∑ j, ggAttachCartan (CartanMatrix.D 5) ⟨2, by decide⟩ none j * lwd_gb5 j) = -2 := by
  decide +kernel

theorem lwd_hP2_5 :
    (∑ j, lwd_gb5 j * ggAttachCartan (CartanMatrix.D 5) ⟨2, by decide⟩ j none) = -2 := by
  decide +kernel


@[expose] def lwd_psig8 : List (Option (Fin 8)) :=
  [some ⟨7, by decide⟩, some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨4, by decide⟩,
    some ⟨5, by decide⟩, some ⟨7, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩,
    some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨2, by decide⟩, some ⟨3, by decide⟩,
    some ⟨4, by decide⟩, some ⟨5, by decide⟩, some ⟨7, by decide⟩, none,
    some ⟨1, by decide⟩, some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩,
    some ⟨5, by decide⟩, some ⟨7, by decide⟩, some ⟨6, by decide⟩, some ⟨5, by decide⟩,
    some ⟨4, by decide⟩, some ⟨3, by decide⟩, some ⟨2, by decide⟩, some ⟨1, by decide⟩]

@[expose] def lwd_gb8 : Option (Fin 8) → ℤ
  | none => 1
  | some i => ![1, 2, 3, 4, 5, 6, 3, 4] i

theorem lwd_gb8_eq :
    ggSWord (ggAttachCartan (CartanMatrix.D 8) ⟨7, by decide⟩) lwd_psig8
      (Pi.single (some ⟨0, by decide⟩) 1) = lwd_gb8 := by
  funext i
  rcases i with _ | i
  · decide +kernel
  · fin_cases i <;> decide +kernel

theorem lwd_gRb8_eq :
    ggSWordR (ggAttachCartan (CartanMatrix.D 8) ⟨7, by decide⟩) lwd_psig8
      (Pi.single (some ⟨0, by decide⟩) 1) = lwd_gb8 := by
  funext i
  rcases i with _ | i
  · decide +kernel
  · fin_cases i <;> decide +kernel

theorem lwd_gb8_none : lwd_gb8 none = 1 := rfl

theorem lwd_hP1_8 :
    (∑ j, ggAttachCartan (CartanMatrix.D 8) ⟨7, by decide⟩ none j * lwd_gb8 j) = -2 := by
  decide +kernel

theorem lwd_hP2_8 :
    (∑ j, lwd_gb8 j * ggAttachCartan (CartanMatrix.D 8) ⟨7, by decide⟩ j none) = -2 := by
  decide +kernel


@[expose] def lwd_psig8a : List (Option (Fin 8)) :=
  [some ⟨6, by decide⟩, some ⟨5, by decide⟩, some ⟨7, by decide⟩, some ⟨4, by decide⟩,
    some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩,
    some ⟨5, by decide⟩, some ⟨7, by decide⟩, some ⟨2, by decide⟩, some ⟨3, by decide⟩,
    some ⟨4, by decide⟩, some ⟨5, by decide⟩, some ⟨6, by decide⟩, none,
    some ⟨1, by decide⟩, some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩,
    some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩, some ⟨5, by decide⟩,
    some ⟨4, by decide⟩, some ⟨3, by decide⟩, some ⟨2, by decide⟩, some ⟨1, by decide⟩]

@[expose] def lwd_gb8a : Option (Fin 8) → ℤ
  | none => 1
  | some i => ![1, 2, 3, 4, 5, 6, 4, 3] i

theorem lwd_gb8a_eq :
    ggSWord (ggAttachCartan (CartanMatrix.D 8) ⟨6, by decide⟩) lwd_psig8a
      (Pi.single (some ⟨0, by decide⟩) 1) = lwd_gb8a := by
  funext i
  rcases i with _ | i
  · decide +kernel
  · fin_cases i <;> decide +kernel

theorem lwd_gRb8a_eq :
    ggSWordR (ggAttachCartan (CartanMatrix.D 8) ⟨6, by decide⟩) lwd_psig8a
      (Pi.single (some ⟨0, by decide⟩) 1) = lwd_gb8a := by
  funext i
  rcases i with _ | i
  · decide +kernel
  · fin_cases i <;> decide +kernel

theorem lwd_gb8a_none : lwd_gb8a none = 1 := rfl

theorem lwd_hP1_8a :
    (∑ j, ggAttachCartan (CartanMatrix.D 8) ⟨6, by decide⟩ none j * lwd_gb8a j) = -2 := by
  decide +kernel

theorem lwd_hP2_8a :
    (∑ j, lwd_gb8a j * ggAttachCartan (CartanMatrix.D 8) ⟨6, by decide⟩ j none) = -2 := by
  decide +kernel


end CFSG.StandardType
