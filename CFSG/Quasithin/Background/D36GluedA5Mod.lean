module

public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.Quasithin.A5Mod

variable {M : Type} [CommGroup M]

@[expose] def fixSub (φ : MulAut M) : Subgroup M where
  carrier := {x | φ x = x}
  one_mem' := map_one φ
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

theorem mem_fixSub {φ : MulAut M} {x : M} : x ∈ fixSub φ ↔ φ x = x := Iff.rfl


theorem pow_mem_of_invariant {φ : MulAut M} {S : Subgroup M} (hS : ∀ x ∈ S, φ x ∈ S) (n : ℕ) :
    ∀ x ∈ S, (φ ^ n) x ∈ S := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    have : (φ ^ (n + 1)) x = (φ ^ n) (φ x) := by
      rw [pow_succ, MulAut.mul_apply]
    rw [this]
    exact ih _ (hS x hx)

theorem card_fixedPoints_modEq' {α : Type} [Finite α] (p : ℕ) [Fact p.Prime]
    (σ : Equiv.Perm α) (hσ : σ ^ p = 1) :
    Nat.card α ≡ Nat.card {x // σ x = x} [MOD p] := by
  classical
  haveI := Fintype.ofFinite α
  have h := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) (σ := σ) (by rwa [pow_one])
  have e : (σ.supportᶜ : Finset α).card = Nat.card {x // σ x = x} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp
  rw [e] at h
  rw [Nat.card_eq_fintype_card]
  exact h.symm

theorem card_fix_modEq [Finite M] (p : ℕ) [hp : Fact p.Prime] (φ : MulAut M) (hφ : φ ^ p = 1)
    (S : Subgroup M) (hS : ∀ x ∈ S, φ x ∈ S) :
    Nat.card S ≡ Nat.card ↥(S ⊓ fixSub φ) [MOD p] := by
  have hinvφ : φ⁻¹ = φ ^ (p - 1) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ' φ (p - 1), Nat.sub_add_cancel hp.out.one_lt.le, hφ]
  have hinv : ∀ x ∈ S, φ⁻¹ x ∈ S := by
    intro x hx
    rw [hinvφ]
    exact pow_mem_of_invariant hS _ x hx
  let σ : Equiv.Perm S :=
    { toFun := fun x => ⟨φ x, hS x x.2⟩
      invFun := fun x => ⟨φ⁻¹ x, hinv x x.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  have hσn : ∀ n : ℕ, ∀ x : S, ((σ ^ n) x : M) = (φ ^ n) (x : M) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, MulAut.mul_apply]
      rfl
  have hσp : σ ^ p = 1 := by
    ext x
    rw [hσn, hφ]
    simp
  have h := card_fixedPoints_modEq' p σ hσp
  have e : Nat.card {x : S // σ x = x} = Nat.card ↥(S ⊓ fixSub φ) := by
    refine Nat.card_congr ⟨fun x => ⟨(x.1 : M), x.1.2, ?_⟩, fun x => ⟨⟨(x : M), x.2.1⟩, ?_⟩, ?_, ?_⟩
    · have := congrArg (fun y : S => (y : M)) x.2
      exact this
    · exact Subtype.ext x.2.2
    · intro x; rfl
    · intro x; rfl
  rw [e] at h
  exact h


section Hom


end Hom

end CFSG.Quasithin.A5Mod
