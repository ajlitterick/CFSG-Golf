
module

public import CFSG.Sporadic.Co1.Module.InvFam

@[expose] public section

namespace CFSG.Sporadic.Co1.Module

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative Matrix

theorem exists_co1_wordMat
    (w : List Bool) : ∃ g : NativeSporadic.Co1, matHom g = wordMat w := by
  induction w with
  | nil => exact ⟨1, by simp [wordMat]⟩
  | cons b w ih =>
    obtain ⟨g, hg⟩ := ih
    cases b
    · obtain ⟨a, ha⟩ := exists_co1_matB
      refine ⟨a * g, ?_⟩
      have h1 : matHom a = matB := ha
      rw [map_mul, h1, hg]
      simp [wordMat, letterMat]
    · obtain ⟨a, ha⟩ := exists_co1_matA
      refine ⟨a * g, ?_⟩
      have h1 : matHom a = matA := ha
      rw [map_mul, h1, hg]
      simp [wordMat, letterMat]

theorem exists_gen_family (w₁ w₂ : List Bool) :
    ∃ kk : ℕ → NativeSporadic.Co1,
      ∀ l < (#[wordRows w₁, wordRows w₂] : Array (Array ℕ)).size,
        matHom (kk l) = rowsMatrix 24 (#[wordRows w₁, wordRows w₂] : Array (Array ℕ))[l]! := by
  obtain ⟨k₁, h₁⟩ := exists_co1_wordMat w₁
  obtain ⟨k₂, h₂⟩ := exists_co1_wordMat w₂
  refine ⟨fun l => if l = 0 then k₁ else k₂, fun l hl => ?_⟩
  have hl2 : l < 2 := hl
  interval_cases l
  · simpa [rowsMatrix_wordRows] using h₁
  · simpa [rowsMatrix_wordRows] using h₂

theorem exists_rep (G : Array (Array ℕ)) (kk : ℕ → NativeSporadic.Co1)
    (hk : ∀ l < G.size, matHom (kk l) = rowsMatrix 24 G[l]!) (w : List ℕ)
    (hw : ∀ l ∈ w, l < G.size) (e : ℕ) :
    ∃ s : NativeSporadic.Co1, matHom s = rowsMatrix 24 (powRows 24 (genWordRows G w) e) := by
  refine ⟨(w.map kk).prod ^ e, ?_⟩
  rw [rowsMatrix_powRows, rowsMatrix_genWordRows, map_pow, map_list_prod, List.map_map]
  congr 2
  exact List.map_congr_left fun l hl => hk l (hw l hl)

theorem repOK_facts {G Gi : Array (Array ℕ)} {S : Array ℕ} {c : ℕ}
    (h : repOK G Gi S c = true) :
    G.size = 2 ∧ Gi.size = 2 ∧ orderIs S 2 = true ∧ isFixedN (transposeRows 24 S) c = true ∧
      ∀ l < 2, mulRows 24 G[l]! Gi[l]! = idRows 24 ∧
        isFixedN (transposeRows 24 G[l]!) c = true := by
  simp only [repOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem countsOK_facts {S : Array ℕ} {a b : ℕ} (h : countsOK S a b = true) :
    {v : Vec24 | rowsMatrix 24 S *ᵥ v = v}.ncard = a ∧
      {v : Vec24 | rowsMatrix 24 S *ᵥ v = v ∧ q₀ v = 1}.ncard = b := by
  simp only [countsOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨by rw [ncard_fix, h.1], by rw [ncard_fixQ, h.2]⟩

theorem witOK_facts
    {w : List Bool} {S T : Array ℕ} {n : ℕ} (hn : 0 < n)
    (h : witOK w S T n = true) {s t : NativeSporadic.Co1} (hs : matHom s = rowsMatrix 24 S)
    (ht : matHom t = rowsMatrix 24 T) :
    ∃ g : NativeSporadic.Co1, orderOf (g * s * g⁻¹ * t) = n := by
  simp only [witOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hinv, hord⟩ := h
  obtain ⟨g, hg⟩ := exists_co1_wordMat w
  have hg' : matHom g = rowsMatrix 24 (wordRows w) := hg.trans (rowsMatrix_wordRows w).symm
  have hgi : matHom g⁻¹ = rowsMatrix 24 (invRows (wordRows w)) := by
    apply matHom_inv_eq
    rw [hg', ← rowsMatrix_mulRows, hinv, rowsMatrix_idRows]
  refine ⟨g, orderOf_eq_of_orderIs (M := mulRows 24 (mulRows 24 (mulRows 24 (wordRows w) S)
    (invRows (wordRows w))) T) ?_ hn hord⟩
  rw [map_mul, map_mul, map_mul, hg', hs, hgi, ht, rowsMatrix_mulRows, rowsMatrix_mulRows,
    rowsMatrix_mulRows]


theorem family_bound_set {v : Vec24} {s : NativeSporadic.Co1}
    (hsv : co1Act s v = v) {n : ℕ} {f : ℕ → NativeSporadic.Co1}
    (hfinj : ∀ i < n, ∀ j < n, f i = f j → i = j) (hf : ∀ i < n, InvFam.IsConjBy v s (f i))
    {N F : ℕ} (hN : (Set.range fun g : NativeSporadic.Co1 => co1Act g v).ncard = N)
    (hF : {w ∈ Set.range (fun g : NativeSporadic.Co1 => co1Act g v) | co1Act s w = w}.ncard ≤ F) :
    Nat.card (Subgroup.centralizer ({s} : Set NativeSporadic.Co1)) * n * N ≤
      Nat.card NativeSporadic.Co1 * F :=
  card_centralizer_bound hN hsv f hfinj hf hF


@[expose] def RepFacts (sA sB sC : NativeSporadic.Co1) : Prop :=
  orderOf sA = 2 ∧ orderOf sB = 2 ∧ orderOf sC = 2 ∧
  {v : Vec24 | co1Act sA v = v}.ncard = 2 ^ 16 ∧
  {v : Vec24 | co1Act sB v = v}.ncard = 2 ^ 12 ∧
  {v : Vec24 | co1Act sC v = v}.ncard = 2 ^ 12 ∧
  {v : Vec24 | co1Act sA v = v ∧ q₀ v = 1}.ncard = 30720 ∧
  {v : Vec24 | co1Act sB v = v ∧ q₀ v = 1}.ncard = 0 ∧
  {v : Vec24 | co1Act sC v = v ∧ q₀ v = 1}.ncard = 2048 ∧
  Nat.card (Subgroup.centralizer ({sA} : Set NativeSporadic.Co1)) ≤ 2 ^ 21 * 3 ^ 5 * 5 ^ 2 * 7 ∧
  Nat.card (Subgroup.centralizer ({sB} : Set NativeSporadic.Co1)) * 2 ^ 12 <
    2 ^ 37 * 3 ^ 5 * 5 ^ 2 * 7 ∧
  Nat.card (Subgroup.centralizer ({sC} : Set NativeSporadic.Co1)) * 2 ^ 12 <
    2 ^ 37 * 3 ^ 5 * 5 ^ 2 * 7 ∧
  (∃ g : NativeSporadic.Co1, orderOf (g * sA * g⁻¹ * sA) = 3) ∧
  (∃ g : NativeSporadic.Co1, orderOf (g * sA * g⁻¹ * sB) = 10) ∧
  (∃ g : NativeSporadic.Co1, orderOf (g * sA * g⁻¹ * sC) = 12)

end CFSG.Sporadic.Co1.Module
