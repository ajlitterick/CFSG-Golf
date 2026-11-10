module

public import CFSG.ClassicalInvolution.Balance.BootstrapTripleBridge
public import CFSG.ClassicalInvolution.Balance.BootstrapAlphaDelta
public import CFSG.ClassicalInvolution.Balance.BootstrapExact
public import CFSG.ClassicalInvolution.Balance.BootstrapP1

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace ExactTriple

variable {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}

theorem card_eq_four (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hd : z₁ * z₂ = z₃) :
    Nat.card T.group = 4 := by
  classical
  rw [T.group_eq_closure_pair hd]
  have c : z₂ * z₁ = z₁ * z₂ := T.comm₁₂'.symm
  have s1 := T.sq₁
  have s2 := T.sq₂
  have s1' : ∀ b, z₁ * (z₁ * b) = b := fun b => by rw [← mul_assoc, s1, one_mul]
  have c' : ∀ b, z₂ * (z₁ * b) = z₁ * (z₂ * b) := fun b => by rw [← mul_assoc, c, mul_assoc]
  have i1 : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right s1
  have i2 : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right s2
  have key : ∀ x (hx : x ∈ Subgroup.closure ({z₁, z₂} : Set G)),
      x = 1 ∨ x = z₁ ∨ x = z₂ ∨ x = z₁ * z₂ := by
    intro x hx
    refine Subgroup.closure_induction
      (p := fun x _ => x = 1 ∨ x = z₁ ∨ x = z₂ ∨ x = z₁ * z₂) ?_ ?_ ?_ ?_ hx
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy <;> subst hy <;> simp
    · simp
    · rintro a b - - (ha | ha | ha | ha) (hb | hb | hb | hb) <;> subst ha <;> subst hb <;>
        simp [mul_assoc, s1, s2, s1', c, c']
    · rintro a - (ha | ha | ha | ha) <;> subst ha <;> simp [i1, i2, c]
  have hsub : (Subgroup.closure ({z₁, z₂} : Set G) : Set G) ⊆
      ({1, z₁, z₂, z₁ * z₂} : Finset G) := by
    intro x hx
    simpa only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] using key x hx
  have hle : Nat.card (Subgroup.closure ({z₁, z₂} : Set G)) ≤ 4 := by
    calc Nat.card (Subgroup.closure ({z₁, z₂} : Set G))
        = Nat.card ((Subgroup.closure ({z₁, z₂} : Set G) : Set G)) := rfl
      _ ≤ Nat.card (({1, z₁, z₂, z₁ * z₂} : Finset G) : Set G) :=
        Nat.card_mono (Set.toFinite _) hsub
      _ = Finset.card ({1, z₁, z₂, z₁ * z₂} : Finset G) := Nat.card_eq_finsetCard _
      _ ≤ 4 := by
        refine (Finset.card_insert_le _ _).trans ?_
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        simp
  set A₁ : Subgroup G := Subgroup.closure ({z₁} : Set G) with hA₁
  set A₂ : Subgroup G := Subgroup.closure ({z₁, z₂} : Set G) with hA₂
  have h1 : (⊥ : Subgroup G) < A₁ := by
    refine lt_of_le_of_ne bot_le fun hh => T.ne_one₁ ?_
    have : z₁ ∈ A₁ := Subgroup.subset_closure rfl
    rwa [← hh, Subgroup.mem_bot] at this
  have h2 : A₁ < A₂ := by
    refine lt_of_le_of_ne (Subgroup.closure_mono (by simp)) fun hh => ?_
    have : z₂ ∈ A₂ := Subgroup.subset_closure (by simp)
    rw [← hh] at this
    exact T.not_mem_closure_single this
  have c1 := two_mul_card_le_of_lt' h1
  have c2 := two_mul_card_le_of_lt' h2
  have hbot : Nat.card (⊥ : Subgroup G) = 1 := Subgroup.card_bot
  omega


end ExactTriple


end CFSG.ClassicalInvolution.Balance.Bootstrap
