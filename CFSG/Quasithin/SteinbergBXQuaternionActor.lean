module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderGroup

public section

namespace CFSG.Quasithin.SteinbergBX

open Subgroup CFSG CFSG.QuasithinUnique.Setup.Offender Module Matrix

namespace QuaternionActor

@[expose] def slA (q : ℕ) : SpecialLinearGroup (Fin 2) (ZMod q) :=
  ⟨!![0, 1; -1, 0], by rw [Matrix.det_fin_two_of]; ring⟩

@[expose] def slB : (q : ℕ) → SpecialLinearGroup (Fin 2) (ZMod q)
  | 3 => ⟨!![1, 1; 1, -1], by rw [Matrix.det_fin_two_of]; decide⟩
  | 5 => ⟨!![2, 0; 0, 3], by rw [Matrix.det_fin_two_of]; decide⟩
  | _ => 1

@[expose] def quatEval {G : Type*} [Monoid G] (x y : G) : QuaternionGroup 2 → G
  | .a i => x ^ i.val
  | .xa i => y * x ^ i.val

theorem quatEval_mul (q : ℕ) (hq : q = 3 ∨ q = 5) (g h : QuaternionGroup 2) :
    quatEval (slA q) (slB q) (g * h) = quatEval (slA q) (slB q) g * quatEval (slA q) (slB q) h := by
  rcases hq with rfl | rfl <;> revert g h <;> decide


@[expose] def quatHom (q : ℕ) (hq : q = 3 ∨ q = 5) :
    QuaternionGroup 2 →* SpecialLinearGroup (Fin 2) (ZMod q) :=
  MonoidHom.mk' (quatEval (slA q) (slB q)) (quatEval_mul q hq)


theorem det_entries {R : Type*} [CommRing R] (g : SpecialLinearGroup (Fin 2) R) :
    g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
  have h := g.2
  rwa [Matrix.det_fin_two] at h

theorem mul_entry {R : Type*} [CommRing R] (g h : SpecialLinearGroup (Fin 2) R) (i j : Fin 2) :
    (g * h).1 i j = g.1 i 0 * h.1 0 j + g.1 i 1 * h.1 1 j := by
  change (g.1 * h.1) i j = _
  rw [Matrix.mul_apply, Fin.sum_univ_two]

theorem eq_of_entries {R : Type*} [CommRing R] {g h : SpecialLinearGroup (Fin 2) R}
    (h00 : g.1 0 0 = h.1 0 0) (h01 : g.1 0 1 = h.1 0 1) (h10 : g.1 1 0 = h.1 1 0)
    (h11 : g.1 1 1 = h.1 1 1) : g = h := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> assumption


theorem quatHom_three_sq (i : QuaternionGroup 2) :
    quatHom 3 (Or.inl rfl) i * quatHom 3 (Or.inl rfl) i = 1 ∨
      quatHom 3 (Or.inl rfl) i * quatHom 3 (Or.inl rfl) i = -1 := by
  revert i
  decide

theorem mem_range_quatHom_three_entries : ∀ w x y z : ZMod 3, w * z - x * y = 1 →
    ((w * w + x * y = 1 ∧ w * x + x * z = 0 ∧ y * w + z * y = 0 ∧ y * x + z * z = 1) ∨
      (w * w + x * y = -1 ∧ w * x + x * z = 0 ∧ y * w + z * y = 0 ∧ y * x + z * z = -1)) →
    ∃ i : QuaternionGroup 2, (quatHom 3 (Or.inl rfl) i).1 0 0 = w ∧
      (quatHom 3 (Or.inl rfl) i).1 0 1 = x ∧ (quatHom 3 (Or.inl rfl) i).1 1 0 = y ∧
      (quatHom 3 (Or.inl rfl) i).1 1 1 = z := by
  decide

theorem mem_range_quatHom_three (g : SpecialLinearGroup (Fin 2) (ZMod 3))
    (hg : g * g = 1 ∨ g * g = -1) : g ∈ (quatHom 3 (Or.inl rfl)).range := by
  have hentries : (g.1 0 0 * g.1 0 0 + g.1 0 1 * g.1 1 0 = 1 ∧
      g.1 0 0 * g.1 0 1 + g.1 0 1 * g.1 1 1 = 0 ∧ g.1 1 0 * g.1 0 0 + g.1 1 1 * g.1 1 0 = 0 ∧
      g.1 1 0 * g.1 0 1 + g.1 1 1 * g.1 1 1 = 1) ∨
      (g.1 0 0 * g.1 0 0 + g.1 0 1 * g.1 1 0 = -1 ∧
      g.1 0 0 * g.1 0 1 + g.1 0 1 * g.1 1 1 = 0 ∧ g.1 1 0 * g.1 0 0 + g.1 1 1 * g.1 1 0 = 0 ∧
      g.1 1 0 * g.1 0 1 + g.1 1 1 * g.1 1 1 = -1) := by
    rcases hg with hg | hg
    · left
      have h1 : ∀ i j : Fin 2, (g * g).1 i j = (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) i j :=
        fun i j => by rw [hg]; rfl
      refine ⟨?_, ?_, ?_, ?_⟩ <;> [have h2 := h1 0 0; have h2 := h1 0 1; have h2 := h1 1 0;
        have h2 := h1 1 1] <;> rw [mul_entry] at h2 <;> rw [h2] <;> rfl
    · right
      have h1 : ∀ i j : Fin 2, (g * g).1 i j = (-1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) i j :=
        fun i j => by rw [hg]; rfl
      refine ⟨?_, ?_, ?_, ?_⟩ <;> [have h2 := h1 0 0; have h2 := h1 0 1; have h2 := h1 1 0;
        have h2 := h1 1 1] <;> rw [mul_entry] at h2 <;> rw [h2] <;> rfl
  obtain ⟨i, h00, h01, h10, h11⟩ :=
    mem_range_quatHom_three_entries _ _ _ _ (det_entries g) hentries
  exact ⟨i, eq_of_entries h00 h01 h10 h11⟩

instance quatHom_three_range_normal : (quatHom 3 (Or.inl rfl)).range.Normal := by
  constructor
  rintro _ ⟨i, rfl⟩ g
  apply mem_range_quatHom_three
  have hc : ∀ x : SpecialLinearGroup (Fin 2) (ZMod 3), (-1 : SpecialLinearGroup (Fin 2) (ZMod 3)) *
      x = x * -1 := fun x => by rw [neg_one_mul, mul_neg_one]
  rcases quatHom_three_sq i with h | h
  · left
    calc g * quatHom 3 _ i * g⁻¹ * (g * quatHom 3 _ i * g⁻¹) =
        g * (quatHom 3 _ i * quatHom 3 _ i) * g⁻¹ := by group
      _ = 1 := by rw [h, mul_one, mul_inv_cancel]
  · right
    calc g * quatHom 3 _ i * g⁻¹ * (g * quatHom 3 _ i * g⁻¹) =
        g * (quatHom 3 _ i * quatHom 3 _ i) * g⁻¹ := by group
      _ = -1 := by rw [h, ← hc, mul_assoc, mul_inv_cancel, mul_one]


end QuaternionActor

end CFSG.Quasithin.SteinbergBX
