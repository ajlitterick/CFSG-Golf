module

public import CFSG.Quasithin.AppendixH.H12.ModelCore

public section

namespace CFSG.Quasithin.AppendixH.H12.Model

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H12Cert
  CFSG.Quasithin.H13.MatNCert CFSG.Open
open CFSG.ASVolI.ChH (IsConjPt cenIn ptStab)

@[expose] def maskOf (l : List ℕ) : ℕ := l.foldl (fun m v => m ||| (1 <<< v)) 0

private theorem testBit_foldl_mask (l : List ℕ) (m c : ℕ) :
    (l.foldl (fun m v => m ||| (1 <<< v)) m).testBit c =
      (m.testBit c || decide (c ∈ l)) := by
  induction l generalizing m with
  | nil => simp
  | cons v l ih =>
    rw [List.foldl_cons, ih (m ||| (1 <<< v))]
    rw [show decide (c ∈ v :: l) = (decide (v = c) || decide (c ∈ l)) from by
      rw [← Bool.decide_or]
      exact decide_eq_decide.mpr (by
        rw [List.mem_cons]
        constructor
        · rintro (h | h)
          · exact Or.inl h.symm
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl h.symm
          · exact Or.inr h)]
    simp only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_assoc]

theorem testBit_maskOf (l : List ℕ) (c : ℕ) : (maskOf l).testBit c = decide (c ∈ l) := by
  rw [maskOf, testBit_foldl_mask, Nat.zero_testBit, Bool.false_or]

theorem mem_iff_of_maskOf_eq {l l' : List ℕ} (h : maskOf l = maskOf l') (c : ℕ) :
    c ∈ l ↔ c ∈ l' := by
  have h1 : (maskOf l).testBit c = (maskOf l').testBit c := by rw [h]
  rw [testBit_maskOf, testBit_maskOf] at h1
  exact decide_eq_decide.mp h1


@[expose] def closedAux (m : ℕ) (vs : List ℕ) : Bool :=
  vs.all fun c =>
    m.testBit (mvN (gG.getD 0 one12) c) && m.testBit (mvN (gG.getD 1 one12) c)

@[expose] def closedCheck (vs : List ℕ) : Bool := closedAux (maskOf vs) vs

theorem closed_of_closedCheck {vs : List ℕ} (h : closedCheck vs = true) {g : Γ12} (hg : g ∈ G0)
    {c : ℕ} (hc : c ∈ vs) : gmv g c ∈ vs := by
  have hall : ∀ c ∈ vs, (maskOf vs).testBit (mvN (gG.getD 0 one12) c) &&
      (maskOf vs).testBit (mvN (gG.getD 1 one12) c) = true :=
    List.all_eq_true.mp h
  refine closed_of_gen (S := fun c => c ∈ vs) ?_ hg hc
  intro i hi c hc
  have hc' := hall c hc
  rw [Bool.and_eq_true] at hc'
  interval_cases i
  · have h0 := hc'.1
    rw [testBit_maskOf] at h0
    exact of_decide_eq_true h0
  · have h1 := hc'.2
    rw [testBit_maskOf] at h1
    exact of_decide_eq_true h1

theorem closed_of_gen_act {α : Type*} (act : Γ12 → α → α) (hone : ∀ x, act 1 x = x)
    (hmul : ∀ g h x, act (g * h) x = act g (act h x)) (S : α → Prop)
    (h : ∀ i < 2, ∀ x, S x → S (act (gU i) x)) {g : Γ12} (hg : g ∈ G0) {x : α} (hx : S x) :
    S (act g x) := by
  refine G_induction (p := fun g => ∀ y, S y → S (act g y)) ?_ ?_ hg x hx
  · intro y hy
    rwa [hone]
  · intro i hi y hy z hz
    rw [hmul]
    exact h i hi (act y z) (hy z hz)

theorem gmv_zero (g : Γ12) : gmv g 0 = 0 := by
  simp only [gmv, mvN_zero]

theorem gmv_eq_zero_iff (g : Γ12) {c : ℕ} (hc : c < 4096) : gmv g c = 0 ↔ c = 0 := by
  constructor
  · intro h
    have h2 : gmv g c = gmv g 0 := by rw [h, gmv_zero]
    refine dc_inj hc (by norm_num) ?_
    apply (glHom g).injective
    rw [glHom_dc, glHom_dc]
    exact congrArg dc h2
  · rintro rfl
    exact gmv_zero g


end CFSG.Quasithin.AppendixH.H12.Model
