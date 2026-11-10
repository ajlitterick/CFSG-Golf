
module

public import CFSG.GF2Type.Smith1979.GammaU.ViolationDefs
public import CFSG.GF2Type.Smith1979.GammaU.StepABase

public section

namespace CFSG.GF2Type.Smith1979.GammaU.Viol

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

@[expose] def GenSet (gs : List (Array ℕ)) : Set (V12 ≃ₗ[ZMod 2] V12) :=
  {l | ∃ r ∈ gs, ∀ x, l x = linOfRows r x}

@[expose] def genGrp (gs : List (Array ℕ)) : Subgroup (V12 ≃ₗ[ZMod 2] V12) :=
  Subgroup.closure (GenSet gs)

@[expose] def InFrame (Lc : List (Array ℕ)) (u : V12 ≃ₗ[ZMod 2] V12) (r : Array ℕ) : Prop :=
  ∃ r' ∈ Lc, ∀ x, u⁻¹ (linOfRows r (u x)) = linOfRows r' x

@[expose] def F4Indep (x y : V12) : Prop := x ≠ 0 ∧ ∀ a b : ZMod 2, y ≠ a • x + b • theta0 x

@[expose] def F2Indep3 (x y w : V12) : Prop :=
  ∀ a b c : ZMod 2, a • x + b • y + c • w = 0 → a = 0 ∧ b = 0 ∧ c = 0

@[expose] def Violation (N : Subgroup (V12 ≃ₗ[ZMod 2] V12)) (Lc H : List (Array ℕ)) : Prop :=
  (∃ h ∈ N, h (vecOf a0) = vecOf a0 ∧
      ∃ r ∈ Lc, ¬ ∃ r' ∈ Lc, ∀ x, h (linOfRows r (h⁻¹ x)) = linOfRows r' x) ∨
    (∃ r ∈ Lc, (∀ x, linOfRows r (theta0 x) = theta0 (linOfRows r x)) ∧ r ∉ H ∧
      ∃ u₁ ∈ N, ∃ u₂ ∈ N, InFrame Lc u₁ r ∧ InFrame Lc u₂ r ∧
        F4Indep (u₁ (vecOf a0)) (u₂ (vecOf a0))) ∨
    (∃ r ∈ Lc, (∀ x, linOfRows r (theta0 x) = theta0 (theta0 (linOfRows r x))) ∧
      ∃ u₁ ∈ N, ∃ u₂ ∈ N, ∃ u₃ ∈ N, InFrame Lc u₁ r ∧ InFrame Lc u₂ r ∧ InFrame Lc u₃ r ∧
        F2Indep3 (u₁ (vecOf a0)) (u₂ (vecOf a0)) (u₃ (vecOf a0)))

theorem okRows_spec {r : Array ℕ} (h : okRows r = true) : r.size = 12 ∧ ∀ x ∈ r, x < 4096 := by
  simp only [okRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at h
  exact ⟨h.1, fun x hx => by simpa using h.2 x hx⟩


theorem size_mulR (g h : Array ℕ) : (mulR g h).size = h.size := by
  simp [mulR]

theorem lt_of_mem_mulR {g h : Array ℕ} (hg : ∀ x ∈ g, x < 4096) : ∀ x ∈ mulR g h, x < 4096 := by
  intro x hx
  simp only [mulR, Array.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact appN_lt hg y

theorem okRows_mulR {g h : Array ℕ} (hg : okRows g = true) (hh : okRows h = true) :
    okRows (mulR g h) = true := by
  have hg' := okRows_spec hg
  have hh' := okRows_spec hh
  simp only [okRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', decide_eq_true_eq]
  exact ⟨by rw [size_mulR, hh'.1], fun x hx => lt_of_mem_mulR hg'.2 x hx⟩

@[expose] noncomputable def eqvOf (g gi : Array ℕ) (h1 : mulR g gi = idR) (h2 : mulR gi g = idR) :
    V12 ≃ₗ[ZMod 2] V12 :=
  LinearEquiv.ofLinear (linOfRows g) (linOfRows gi)
    (LinearMap.ext fun x => by
      change linOfRows g (linOfRows gi x) = x
      rw [← linOfRows_mulR, h1, linOfRows_idR])
    (LinearMap.ext fun x => by
      change linOfRows gi (linOfRows g x) = x
      rw [← linOfRows_mulR, h2, linOfRows_idR])

theorem eqvOf_apply (g gi : Array ℕ) (h1 : mulR g gi = idR) (h2 : mulR gi g = idR) (x : V12) :
    eqvOf g gi h1 h2 x = linOfRows g x := rfl

theorem eqvOf_inv_apply (g gi : Array ℕ) (h1 : mulR g gi = idR) (h2 : mulR gi g = idR)
    (x : V12) : (eqvOf g gi h1 h2)⁻¹ x = linOfRows gi x := rfl


@[expose] def GensOK (gs : List (Array ℕ)) : Prop :=
  ∀ g ∈ gs, okRows g = true ∧ okRows (invR g) = true ∧ mulR g (invR g) = idR ∧
    mulR (invR g) g = idR

theorem gen_mem {gs : List (Array ℕ)} (hgs : GensOK gs) {g : Array ℕ} (hg : g ∈ gs) :
    eqvOf g (invR g) (hgs g hg).2.2.1 (hgs g hg).2.2.2 ∈ genGrp gs :=
  Subgroup.subset_closure ⟨g, hg, fun _ => rfl⟩


theorem f4Indep_spec {x y : ℕ} (hx : x < 4096) (hy : y < 4096) (h : f4Indep x y = true) :
    F4Indep (vecOf x) (vecOf y) := by
  simp only [f4Indep, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨hx0, hy0⟩, hyx⟩, hyt⟩, hyxt⟩ := h
  have htx := theta0N_lt hx
  refine ⟨fun h0 => hx0 ((vecOf_eq_zero hx).1 h0), fun a b hab => ?_⟩
  have ha : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rw [← vecOf_theta0N hx] at hab
  rcases ha a with rfl | rfl <;> rcases ha b with rfl | rfl
  · simp only [zero_smul, add_zero] at hab
    exact hy0 ((vecOf_eq_zero hy).1 hab)
  · simp only [zero_smul, one_smul, zero_add] at hab
    exact hyt (vecOf_inj hy htx hab)
  · simp only [zero_smul, one_smul, add_zero] at hab
    exact hyx (vecOf_inj hy hx hab)
  · simp only [one_smul] at hab
    rw [← vecOf_xor] at hab
    exact hyxt (vecOf_inj hy (xor_lt hx htx) hab)

theorem eq_of_add_eq_zero {x y : V12} (h : x + y = 0) : x = y := by
  have := congrArg (· + y) h
  simp only [add_assoc, zero_add] at this
  rwa [show y + y = 0 from funext fun j => by
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize y j = c
    revert c
    decide, add_zero] at this

theorem f2Indep3_spec {x y w : ℕ} (hx : x < 4096) (hy : y < 4096) (hw : w < 4096)
    (h : f2Indep3 x y w = true) : F2Indep3 (vecOf x) (vecOf y) (vecOf w) := by
  simp only [f2Indep3, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hx0, hy0⟩, hyx⟩, hw0⟩, hwx⟩, hwy⟩, hwxy⟩ := h
  have ha : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  intro a b c habc
  have nz : ∀ {n}, n < 4096 → n ≠ 0 → vecOf n ≠ 0 := fun hn hn0 h0 => hn0 ((vecOf_eq_zero hn).1 h0)
  rcases ha a with rfl | rfl <;> rcases ha b with rfl | rfl <;> rcases ha c with rfl | rfl <;>
    simp only [zero_smul, one_smul, add_zero, zero_add, true_and, and_true] at habc ⊢
  · exact (nz hw hw0 habc).elim
  · exact (nz hy hy0 habc).elim
  · exact (hwy (vecOf_inj hw hy (eq_of_add_eq_zero habc).symm)).elim
  · exact (nz hx hx0 habc).elim
  · exact (hwx (vecOf_inj hw hx (eq_of_add_eq_zero habc).symm)).elim
  · exact (hyx (vecOf_inj hy hx (eq_of_add_eq_zero habc).symm)).elim
  · rw [← vecOf_xor] at habc
    exact (hwxy (vecOf_inj hw (xor_lt hx hy) (eq_of_add_eq_zero habc).symm)).elim


end CFSG.GF2Type.Smith1979.GammaU.Viol
