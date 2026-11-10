module

public import Certificates.Kernel.Sporadic.RelSeg
public import CFSG.Sporadic.Bridge.Common

public section

namespace CertificateChecks.KernelHomG

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.RelSeg CFSG.Sporadic.Bridge

variable {d : Nat} {K : Type} [CommRing K]

structure LayoutSound (Q : Nat → Prop) (Mt : Nat → Matrix (Fin d) (Fin d) K)
    (mul : Nat → Nat → Nat) (vld : Nat → Bool) (ONE : Nat) : Prop where
  mul_sound : ∀ A B, Q A → Q B → Q (mul A B) ∧ Mt (mul A B) = Mt A * Mt B
  one_q : Q ONE
  one_mt : Mt ONE = 1
  vld_q : ∀ X, vld X = true → Q X

@[expose] def rootSetG (Mt : Nat → Matrix (Fin d) (Fin d) K) (Lg : Nat) (RB : Nat → Nat) :
    Set (Matrix (Fin d) (Fin d) K) :=
  {M | ∃ g, 0 < g ∧ g ≤ 2 * Lg ∧ M = Mt (RB g)}

@[expose] def RegsInG (Q : Nat → Prop) (Mt : Nat → Matrix (Fin d) (Fin d) K) (Lg : Nat)
    (RB : Nat → Nat) (s : Nat) : Prop :=
  ∀ r, 0 < r → r < s → Q (RB r) ∧ Mt (RB r) ∈ Submonoid.closure (rootSetG Mt Lg RB)

theorem strictN_eqG (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl


theorem rec_andG {f : Nat → Bool} : ∀ m,
    Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) m = true →
      ∀ g < m, f g = true
  | 0, _, g, hg => absurd hg (Nat.not_lt_zero g)
  | m + 1, h, g, hg => by
    have h' : andB (Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) m)
        (f m) = true := h
    obtain ⟨h1, h2⟩ := (andB_iff _ _).1 h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | rfl
    · exact rec_andG m h1 g hg
    · exact h2


variable {Q : Nat → Prop} {Mt : Nat → Matrix (Fin d) (Fin d) K} {mul : Nat → Nat → Nat}
  {vld : Nat → Bool} {ONE : Nat}


theorem letM_q {Lg : Nat} {RB : Nat → Nat} (hs : LayoutSound Q Mt mul vld ONE)
    (hroot : rootsOK RB vld 1 (Lg + 1) = true) (hinv : invsOK RB mul vld Lg ONE = true)
    {x : Nat × Bool} (hx : x.1 < Lg) : Q (letM RB Lg x) := by
  obtain ⟨g, s⟩ := x
  cases s
  · have h := rec_andG (f := fun g => andB (vld (RB (Nat.add (Nat.succ Lg) g)))
      (Nat.beq (mul (RB (Nat.succ g)) (RB (Nat.add (Nat.succ Lg) g))) ONE)) Lg hinv g hx
    exact hs.vld_q _ ((andB_iff _ _).1 h).1
  · have h := rec_andG (f := fun i => Bool.rec (motive := fun _ => Bool) true
      (vld (RB i)) (Nat.ble 1 i)) (Lg + 1) hroot (g + 1) (by simp at hx; omega)
    have hb1 : Nat.ble 1 (g + 1) = true := Nat.ble_eq.mpr (by omega)
    rw [hb1] at h
    exact hs.vld_q _ h

theorem pair_of_invsG {Lg : Nat} {RB : Nat → Nat} (hs : LayoutSound Q Mt mul vld ONE)
    (hroot : rootsOK RB vld 1 (Lg + 1) = true) (hinv : invsOK RB mul vld Lg ONE = true) :
    ∀ g < Lg, Mt (RB (g + 1)) * Mt (RB (Lg + 1 + g)) = 1 := by
  intro g hg
  have h := rec_andG (f := fun g => andB (vld (RB (Nat.add (Nat.succ Lg) g)))
    (Nat.beq (mul (RB (Nat.succ g)) (RB (Nat.add (Nat.succ Lg) g))) ONE)) Lg hinv g hg
  obtain ⟨h1, h2⟩ := (andB_iff _ _).1 h
  have hr : Q (RB (g + 1)) := letM_q hs hroot hinv (x := (g, true)) hg
  have h1' : vld (RB (Lg + 1 + g)) = true := h1
  have h2' : mul (RB (g + 1)) (RB (Lg + 1 + g)) = ONE := Nat.eq_of_beq_eq_true h2
  have e := (hs.mul_sound (RB (g + 1)) (RB (Lg + 1 + g)) hr (hs.vld_q _ h1')).2
  rw [← e, h2', hs.one_mt]


@[expose] noncomputable def flipG (x : Nat × Bool) : Nat × Bool :=
  Prod.rec (motive := fun _ => Nat × Bool) (fun g s => (g, notB s)) x


theorem prod_invG {R : Type*} [Monoid R] {f : Nat × Bool → R} :
    ∀ u : List (Nat × Bool), (∀ x ∈ u, f (flipG x) * f x = 1) →
      ((u.map flipG).reverse.map f).prod * (u.map f).prod = 1
  | [], _ => by simp
  | x :: u, h => by
    have ih := prod_invG u (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x (by simp)
    simp only [List.map_cons, List.reverse_cons, List.map_append, List.prod_append, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    rw [mul_assoc, ← mul_assoc (f (flipG x)), hx, one_mul, ih]


end CertificateChecks.KernelHomG

end
