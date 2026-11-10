module

public import CFSG.Quasithin.Background.B3Off

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ}

theorem cj_mul (a b : Gp n) (A : Subgroup (Gp n)) : cj (a * b) A = cj a (cj b A) := by
  ext x
  simp only [mem_cj]
  simp [mul_assoc]

@[expose] def conjT (g : Tab) (A : List Tab) : List Tab := A.map (cjT g)

theorem cjT_tab (γ y : Gp n) : cjT (tab γ) (tab y) = tab (γ * y * γ⁻¹) := by
  unfold cjT
  rw [← tab_mul, ← tab_inv, ← tab_mul]

theorem cj_subOf_eq {L K : List Tab} (hL : subOK n L = true) (hK : subOK n K = true) {g : Tab}
    (hg : isTab n g = true) (h : seteqT (conjT g L) K = true) :
    ∃ γ : Gp n, cj γ (subOf n L) = subOf n K := by
  obtain ⟨γ, rfl⟩ := exists_tab_eq hg
  refine ⟨γ, ?_⟩
  simp only [seteqT, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, conjT,
    List.mem_map] at h
  obtain ⟨h1, h2⟩ := h
  ext x
  rw [mem_cj, mem_subOf hL, mem_subOf hK]
  constructor
  · intro hx
    have := h1 (cjT (tab γ) (tab (γ⁻¹ * x * γ))) ⟨_, hx, rfl⟩
    rw [cjT_tab] at this
    simpa [mul_assoc] using this
  · intro hx
    obtain ⟨l, hl, hlx⟩ := h2 _ hx
    obtain ⟨y, rfl⟩ := exists_tab_eq ((subOK_spec hL).1 l hl)
    rw [cjT_tab] at hlx
    have h3 := tab_injective hlx
    rw [← h3]
    simpa [mul_assoc] using hl


theorem isPGroup_of_sq {A : Subgroup (Gp n)} (h : ∀ a ∈ A, a * a = 1) : IsPGroup 2 A := by
  intro x
  refine ⟨1, ?_⟩
  have := h x x.2
  apply Subtype.ext
  simpa [pow_two] using this

theorem cj_inv_cj (g : Gp n) (A : Subgroup (Gp n)) : cj g⁻¹ (cj g A) = A := by
  have := cj_cj_inv g⁻¹ A
  simpa using this

theorem classification (hn : 5 ≤ n) (k : Mod) {D reps : List (List Tab)} {S : Sylow 2 (Gp n)}
    (hS : (S : Subgroup (Gp n)) = subOf n (Tl n)) (hT : subOK n (Tl n) = true)
    (hD : chkEA n (Tl n) D = true)
    (hreps : ∀ L ∈ reps, L ∈ D ∧ offOK n k D L = true)
    (hcover : ∀ K ∈ D, offOK n k D K = true →
      ∃ L ∈ reps, ∃ g, isTab n g = true ∧ seteqT (conjT g L) K = true) :
    ∀ A : Subgroup (Gp n), IsOffG n k A ↔ ∃ L ∈ reps, ∃ γ : Gp n, A = cj γ (subOf n L) := by
  intro A
  obtain ⟨-, hmem, -⟩ := chkEA_spec hD
  constructor
  · intro hA
    have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
      intro a ha b hb
      have h1 := hA.2.2.1.1 (Mod.act n k a) (Subgroup.mem_map_of_mem _ ha) (Mod.act n k b)
        (Subgroup.mem_map_of_mem _ hb)
      apply act_injective hn k
      simpa [map_mul] using h1
    have hsq : ∀ a ∈ A, a * a = 1 := by
      intro a ha
      have h1 := hA.2.2.1.2 (Mod.act n k a) (Subgroup.mem_map_of_mem _ ha)
      apply act_injective hn k
      rw [map_mul, map_one]
      simpa [pow_two] using h1
    obtain ⟨γ, hγ⟩ := exists_conj_le_sylow S A (isPGroup_of_sq hsq)
    have hKcomm : ∀ a ∈ cj γ A, ∀ b ∈ cj γ A, a * b = b * a := by
      intro a ha b hb
      rw [mem_cj] at ha hb
      have h1 := congrArg (fun x => γ * x * γ⁻¹) (hcomm _ ha _ hb)
      simpa [mul_assoc] using h1
    have hKsq : ∀ a ∈ cj γ A, a * a = 1 := by
      intro a ha
      rw [mem_cj] at ha
      have h1 := congrArg (fun x => γ * x * γ⁻¹) (hsq _ ha)
      simpa [mul_assoc] using h1
    have hKoff : IsOffG n k (cj γ A) := hA.cj γ
    obtain ⟨C, hC, hCok, hKC⟩ := exists_mem_D hT hD (cj γ A)
      (fun x hx => by
        have := hγ hx
        rw [hS] at this
        exact (mem_subOf hT).1 this) hKcomm hKsq
    have hKeq : cj γ A = subOf n C := subOf_eq hCok hKC
    have hoff : offOK n k D C = true :=
      (isOffG_iff_offOK hn k hT hD hC).1 (by rw [← hKeq]; exact hKoff)
    obtain ⟨L, hL, g, hg, hseteq⟩ := hcover C hC hoff
    obtain ⟨δ, hδ⟩ := cj_subOf_eq (hmem L (hreps L hL).1).1 hCok hg hseteq
    refine ⟨L, hL, γ⁻¹ * δ, ?_⟩
    rw [cj_mul, hδ, ← hKeq, cj_inv_cj]
  · rintro ⟨L, hL, γ, rfl⟩
    exact ((isOffG_iff_offOK hn k hT hD (hreps L hL).1).2 (hreps L hL).2).cj γ


@[expose] def mkDF (n : ℕ) (k : Mod) (D : List (List Tab)) : List (List Tab × ℕ) :=
  D.map (fun B => (B, Fval n k B))

@[expose] def offP (DF : List (List Tab × ℕ)) (p : List Tab × ℕ) : Bool :=
  !(p.1.length == 1) && DF.all (fun q => !(q.1.all (fun t => p.1.contains t)) || decide (q.2 ≤ p.2))

theorem offP_mkDF (n : ℕ) (k : Mod) (D : List (List Tab)) (A : List Tab) :
    offP (mkDF n k D) (A, Fval n k A) = offOK n k D A := by
  simp [offP, mkDF, offOK, List.all_map, Function.comp_def]


end CFSG.Quasithin.B3
