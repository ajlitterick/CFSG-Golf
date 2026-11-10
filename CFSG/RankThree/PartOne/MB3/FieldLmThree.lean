module

public import CFSG.RankThree.PartOne.S11c.SuFiveFixed
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.RankThree.PartOne.MB3

open Matrix Module CFSG.RankThree.PartOne.KFSU5

variable {F : Type} [Field F] [Finite F]


omit [Finite F] in
theorem exists_eigenvector_of_invariant {M : Matrix (Fin 3) (Fin 3) F}
    {W : Submodule F (Fin 3 → F)} (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤)
    (hinv : ∀ w ∈ W, M *ᵥ w ∈ W) : ∃ x : Fin 3 → F, x ≠ 0 ∧ ∃ μ : F, M *ᵥ x = μ • x := by
  classical
  have hfin : finrank F (Fin 3 → F) = 3 := Module.finrank_fin_fun F
  have hlt : finrank F W < 3 := by
    have := Submodule.finrank_lt hW1
    rwa [hfin] at this
  have hpos : 0 < finrank F W := by
    rcases Nat.eq_zero_or_pos (finrank F W) with h | h
    · exact absurd (Submodule.finrank_eq_zero.mp h) hW0
    · exact h
  rcases (by omega : finrank F W = 1 ∨ finrank F W = 2) with h1 | h2
  ·
    obtain ⟨w, hw0, hgen⟩ := finrank_eq_one_iff'.mp h1
    obtain ⟨c, hc⟩ := hgen ⟨M *ᵥ (w : Fin 3 → F), hinv w w.2⟩
    refine ⟨(w : Fin 3 → F), fun h => hw0 (Subtype.ext h), c, ?_⟩
    exact (congrArg Subtype.val hc).symm
  ·
    obtain ⟨u, hu⟩ : ∃ u : Fin 3 → F, u ∉ W := by
      by_contra hcon
      push Not at hcon
      exact hW1 (eq_top_iff.mpr fun x _ => hcon x)
    have hspan : finrank F (Submodule.span F {u}) = 1 :=
      finrank_span_singleton (fun h => hu (h ▸ W.zero_mem))
    have hinf : W ⊓ Submodule.span F {u} = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxW, hxu⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxu
      by_cases hc : c = 0
      · simp [hc]
      · exact absurd (by simpa [smul_smul, hc] using W.smul_mem c⁻¹ hxW) hu
    have hsup : W ⊔ Submodule.span F {u} = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span F {u})
      rw [hinf, finrank_bot, hspan, h2] at this
      rw [hfin]
      omega
    have hMu : M *ᵥ u ∈ W ⊔ Submodule.span F {u} := by rw [hsup]; trivial
    obtain ⟨w₀, hw₀, y, hy, hMuy⟩ := Submodule.mem_sup.mp hMu
    obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hy
    let f : (Fin 3 → F) →ₗ[F] (Fin 3 → F) := Matrix.toLin' M - μ • LinearMap.id
    have hrange : ∀ x, f x ∈ W := by
      intro x
      have hx : x ∈ W ⊔ Submodule.span F {u} := by rw [hsup]; trivial
      obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have hfx : f (w + c • u) = (M *ᵥ w - μ • w) + c • w₀ := by
        simp only [f, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
          Matrix.toLin'_apply, Matrix.mulVec_add, Matrix.mulVec_smul, ← hMuy]
        module
      rw [hfx]
      exact W.add_mem (W.sub_mem (hinv w hw) (W.smul_mem μ hw)) (W.smul_mem c hw₀)
    have hker : LinearMap.ker f ≠ ⊥ := by
      intro hbot
      have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hbot
      have hsurj := LinearMap.injective_iff_surjective.mp hinj
      obtain ⟨x, hx⟩ := hsurj u
      exact hu (hx ▸ hrange x)
    obtain ⟨x, hxk, hx0⟩ := (Submodule.ne_bot_iff _).mp hker
    refine ⟨x, hx0, μ, ?_⟩
    have : f x = 0 := hxk
    simpa [f, sub_eq_zero, Matrix.toLin'_apply] using this

theorem eigenvalue_eq_one (hF : Nat.card F = 2 ^ 7) {g : GL (Fin 3) F} (hg7 : g ^ 7 = 1)
    {v : Fin 3 → F} (hv : v ≠ 0) {μ : F}
    (hgv : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = μ • v) : μ = 1 := by
  classical
  have := Fintype.ofFinite F
  have hpow : ∀ k : ℕ, (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hgv, Matrix.mulVec_smul, ih, smul_smul, pow_succ]
      rw [mul_comm]
  have h7 := hpow 7
  have hg7' : (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 7) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hg7, Units.val_one]
  rw [hg7', Matrix.one_mulVec] at h7
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hμ7 : μ ^ 7 = 1 := by
    have := congrFun h7 i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact (mul_left_eq_self₀.mp this.symm).resolve_right hi
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hμ7
  have h127 : μ ^ 127 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one μ hμ0
    rwa [← Nat.card_eq_fintype_card, hF] at this
  have := pow_gcd_eq_one.mpr ⟨hμ7, h127⟩
  rwa [show Nat.gcd 7 127 = 1 by norm_num, pow_one] at this


end CFSG.RankThree.PartOne.MB3
