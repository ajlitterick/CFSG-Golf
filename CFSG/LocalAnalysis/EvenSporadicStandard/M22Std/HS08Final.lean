module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Orbit
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup
open scoped Classical

variable {G : Type*} [Group G] [Fintype G]

structure FinalData (E N : Subgroup G) (t : G) (F1 F2 F3 : Finset G) : Prop where
  card_E : Nat.card E = 64
  sq : ∀ x ∈ E, x * x = 1
  comm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x
  t_mem : t ∈ E
  t_ne : t ≠ 1
  E_le : E ≤ N
  norm : ∀ n ∈ N, ∀ x ∈ E, n * x * n⁻¹ ∈ E
  cent : ∀ n ∈ N, (∀ x ∈ E, n * x = x * n) → n ∈ E
  card_N0 : Nat.card ↥(N ⊓ centralizer ({t} : Set G)) = 7680
  mem_F : ∀ x, (x ∈ F1 ∨ x ∈ F2 ∨ x ∈ F3) ↔ (x ∈ E ∧ x ≠ 1 ∧ x ≠ t)
  disj12 : Disjoint F1 F2
  disj13 : Disjoint F1 F3
  disj23 : Disjoint F2 F3
  card1 : F1.card = 30
  card2 : F2.card = 12
  card3 : F3.card = 20
  tmul1 : ∀ x ∈ F1, t * x ∈ F1
  tmul2 : ∀ x ∈ F2, t * x ∈ F2
  tmul3 : ∀ x ∈ F3, t * x ∈ F3
  trans1 : ∀ x ∈ F1, ∀ y ∈ F1,
    ∃ n ∈ N, n * t = t * n ∧ (n * x * n⁻¹ = y ∨ n * x * n⁻¹ = t * y)
  trans2 : ∀ x ∈ F2, ∀ y ∈ F2,
    ∃ n ∈ N, n * t = t * n ∧ (n * x * n⁻¹ = y ∨ n * x * n⁻¹ = t * y)
  trans3 : ∀ x ∈ F3, ∀ y ∈ F3,
    ∃ n ∈ N, n * t = t * n ∧ (n * x * n⁻¹ = y ∨ n * x * n⁻¹ = t * y)
  fix2 : ∀ n ∈ N, n * t = t * n → (∀ x ∈ F2, n * x * n⁻¹ = x) → n ∈ E
  odd1 : ∃ z ∈ F1, Odd (conjOrb N z).card ∧ Odd (conjOrb N (t * z)).card
  nonfixed : ∃ n ∈ N, n * t * n⁻¹ ≠ t
  outer : ∀ n ∈ N, n * t * n⁻¹ ≠ t → n * t * n⁻¹ ∈ F2 ∨ n * t * n⁻¹ ∈ F3


namespace FinalData

variable {E N : Subgroup G} {t : G} {F1 F2 F3 : Finset G} (h : FinalData E N t F1 F2 F3)
include h

theorem t_sq : t * t = 1 := h.sq t h.t_mem


end FinalData


end CFSG.EvenSporadicStandard.M22Std
