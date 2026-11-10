module

public import CFSG.Quasithin.Background.B3Named
public import CFSG.Quasithin.Background.B3Sign
public import CFSG.Quasithin.Background.B3Class

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ}

@[expose] def Dc (n : ℕ) : List Tab := AmL n (n / 2)

@[expose] def DLc (n : ℕ) : List Tab := (Dc n).filter isEvenT

@[expose] def regB (n : ℕ) (K : List Tab) : Bool :=
  (List.range n).all (fun j => K.any (fun t => t.getD 0 0 == j))


@[expose] def isE8T (n : ℕ) (K : List Tab) : Bool :=
  n == 8 && K.length == 8 && K.all isEvenT && regB n K


@[expose] def chkNamed (n : ℕ) : Bool :=
  (List.range (n / 2)).all (fun i => chkGen n (gensAm n (i + 1)) && memD (Dl n) (AmL n (i + 1))) &&
  chkGen n (gensAm n (n / 2)) && chkGen n (gensA0 n) && memD (Dl n) (A0L n) &&
  subOK n (DLc n) && memD (Dl n) (DLc n) && memD (Dl n) (Dc n) &&
  (Dc n).all (fun t => (Tl n).contains t)


@[expose] def Hset (n : ℕ) : Set (Subgroup (Gp n)) :=
  {B | ∃ γ : Gp n, ∃ H : Subgroup (Gp n), H ≤ Dsub n ∧ Nat.card (Dsub n) = 2 * Nat.card H ∧
    H ≠ Dsub n ⊓ alternatingGroup (Fin n) ∧ B = cj γ H}

@[expose] def Rset (n : ℕ) : Set (Subgroup (Gp n)) :=
  {A | A ≤ alternatingGroup (Fin n) ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a * a = 1) ∧
    Nat.card A = 8 ∧ ∀ i j : Fin n, ∃! a : Gp n, a ∈ A ∧ a i = j}

theorem chkNamed_spec (h : chkNamed n = true) :
    (∀ i < n / 2, chkGen n (gensAm n (i + 1)) = true ∧ memD (Dl n) (AmL n (i + 1)) = true) ∧
    chkGen n (gensAm n (n / 2)) = true ∧ chkGen n (gensA0 n) = true ∧
    memD (Dl n) (A0L n) = true ∧ subOK n (DLc n) = true ∧ memD (Dl n) (DLc n) = true ∧
    memD (Dl n) (Dc n) = true ∧ (∀ t ∈ Dc n, t ∈ Tl n) := by
  simp only [chkNamed, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨fun i hi => by simpa using h1 i hi, h2, h3, h4, h5, h6, h7, h8⟩


theorem Dsub_eq (hg : chkGen n (gensAm n (n / 2)) = true) : Dsub n = subOf n (Dc n) := by
  unfold Dsub Dc
  exact closure_eq_of_chkGen hg

theorem subOK_Dc (hg : chkGen n (gensAm n (n / 2)) = true) : subOK n (Dc n) = true := by
  simp only [chkGen, Bool.and_eq_true] at hg
  exact hg.1.1

theorem subOf_eq_of_iff {L L' : List Tab} (hL : subOK n L = true) (hL' : subOK n L' = true)
    (h : ∀ t, t ∈ L ↔ t ∈ L') : subOf n L = subOf n L' := by
  ext x
  rw [mem_subOf hL, mem_subOf hL', h]


theorem Rset_cj {A : Subgroup (Gp n)} (hA : A ∈ Rset n) (γ : Gp n) : cj γ A ∈ Rset n := by
  obtain ⟨hL, hcomm, hsq, hcard, hreg⟩ := hA
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [mem_cj] at hx
    have h1 := hL hx
    rw [Equiv.Perm.mem_alternatingGroup] at h1 ⊢
    have hs : Equiv.Perm.sign (γ⁻¹ * x * γ) = Equiv.Perm.sign x := by
      rw [map_mul, map_mul, Equiv.Perm.sign_inv, mul_comm (Equiv.Perm.sign γ) (Equiv.Perm.sign x),
        mul_assoc, Int.units_mul_self, mul_one]
    rw [← hs]
    exact h1
  · intro a ha b hb
    rw [mem_cj] at ha hb
    have h1 := congrArg (fun x => γ * x * γ⁻¹) (hcomm _ ha _ hb)
    simpa [mul_assoc] using h1
  · intro a ha
    rw [mem_cj] at ha
    have h1 := congrArg (fun x => γ * x * γ⁻¹) (hsq _ ha)
    simpa [mul_assoc] using h1
  · unfold cj
    rw [Subgroup.card_map_of_injective (MulAut.conj γ).injective]
    exact hcard
  · intro i j
    obtain ⟨a', ⟨ha'A, ha'ij⟩, huniq⟩ := hreg (γ⁻¹ i) (γ⁻¹ j)
    refine ⟨γ * a' * γ⁻¹, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_cj]
      simpa [mul_assoc] using ha'A
    · calc (γ * a' * γ⁻¹) i = γ (a' (γ⁻¹ i)) := rfl
        _ = γ (γ⁻¹ j) := by rw [ha'ij]
        _ = j := by simp
    · rintro b ⟨hbA, hbij⟩
      rw [mem_cj] at hbA
      have h1 : γ⁻¹ * b * γ = a' := by
        apply huniq
        refine ⟨hbA, ?_⟩
        simp [Equiv.Perm.mul_apply, hbij]
      rw [← h1]
      simp [mul_assoc]

theorem isE8T_mem_Rset {C : List Tab} (hCok : subOK n C = true)
    (hcomm : ∀ a ∈ C, ∀ b ∈ C, mulT a b = mulT b a) (hsq : ∀ a ∈ C, mulT a a = idT n)
    (h : isE8T n C = true) : subOf n C ∈ Rset n := by
  classical
  simp only [isE8T, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hn8, hlen⟩, heven⟩, hreg⟩ := h
  subst hn8
  refine ⟨?_, subOf_comm hCok hcomm, subOf_sq hCok hsq, ?_, ?_⟩
  · intro x hx
    rw [mem_subOf hCok] at hx
    rw [mem_alternatingGroup_iff]
    exact heven _ hx
  · rw [card_subOf hCok, hlen]
  · have horb : ∀ j : Fin 8, ∃ a ∈ subOf 8 C, a 0 = j := by
      intro j
      simp only [regB, List.all_eq_true, List.mem_range, List.any_eq_true, beq_iff_eq] at hreg
      obtain ⟨t, ht, htj⟩ := hreg j j.isLt
      obtain ⟨a, rfl⟩ := exists_tab_eq ((subOK_spec hCok).1 t ht)
      refine ⟨a, (mem_subOf hCok).2 ht, ?_⟩
      apply Fin.ext
      have := getD_tab a 0
      simp only [Fin.val_zero] at this
      rw [← this]
      exact htj
    have htrans : ∀ i j : Fin 8, ∃ a ∈ subOf 8 C, a i = j := by
      intro i j
      obtain ⟨ai, hai, haii⟩ := horb i
      obtain ⟨aj, haj, hajj⟩ := horb j
      refine ⟨aj * ai⁻¹, (subOf 8 C).mul_mem haj ((subOf 8 C).inv_mem hai), ?_⟩
      have h1 : ai⁻¹ i = 0 := by rw [← haii]; simp
      simp [Equiv.Perm.mul_apply, h1, hajj]
    intro i j
    have hbij : Function.Bijective (fun a : subOf 8 C => (a : Gp 8) i) := by
      rw [Fintype.bijective_iff_surjective_and_card]
      refine ⟨?_, ?_⟩
      · intro j
        obtain ⟨a, ha, haj⟩ := htrans i j
        exact ⟨⟨a, ha⟩, haj⟩
      · rw [← Nat.card_eq_fintype_card, card_subOf hCok, hlen, Fintype.card_fin]
    obtain ⟨⟨a, ha⟩, haj, huniq⟩ := hbij.existsUnique j
    exact ⟨a, ⟨ha, haj⟩, fun b hb => congrArg Subtype.val (huniq ⟨b, hb.1⟩ hb.2)⟩

theorem isE8T_of_mem_Rset {C : List Tab} (hCok : subOK n C = true) (hn : n = 8)
    {K : Subgroup (Gp n)} (hK : K ∈ Rset n) (hKC : ∀ x : Gp n, x ∈ K ↔ tab x ∈ C) :
    isE8T n C = true := by
  obtain ⟨hL, -, -, hcard, hreg⟩ := hK
  have hKeq : K = subOf n C := subOf_eq hCok hKC
  simp only [isE8T, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨⟨hn, ?_⟩, ?_⟩, ?_⟩
  · rw [← card_subOf hCok, ← hKeq]
    exact hcard
  · intro t ht
    obtain ⟨x, rfl⟩ := exists_tab_eq ((subOK_spec hCok).1 t ht)
    rw [← mem_alternatingGroup_iff]
    exact hL ((hKC x).2 ht)
  · simp only [regB, List.all_eq_true, List.mem_range, List.any_eq_true, beq_iff_eq]
    intro j hj
    subst hn
    obtain ⟨a, ⟨haK, haj⟩, -⟩ := hreg 0 ⟨j, hj⟩
    refine ⟨tab a, (hKC a).1 haK, ?_⟩
    have := getD_tab a 0
    simp only [Fin.val_zero] at this
    rw [this, haj]


end CFSG.Quasithin.B3
