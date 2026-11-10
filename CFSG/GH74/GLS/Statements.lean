module

public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.GH74.GLS.Pattern

public section

namespace CFSG.GH74.GLS

open Subgroup Blueprint Assembly.LowTwoRank
open scoped commutatorElement

theorem pRank_two_eq_twoRank (G : Type) [Group G] [Finite G] :
    pRank 2 G = CFSG.Open.twoRank G :=
  CFSG.SectionRank.pRank_eq_open_pRank_top 2 G

theorem InB2.inT2 {K : Type} [Group K] (h : InB2 K) : InT2 K := h.1

@[expose] def C23List (G : Type) [Group G] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
    ((5 ≤ p ^ f ∧ LieModel G .PSL 2 p f) ∨
      LieModel G .PSL 3 p f ∨ LieModel G .PSU 3 p f ∨
      (3 < p ^ f ∧ (LieModel G .PSp 2 p f ∨ LieModel G .G2 0 p f)) ∨
      LieModel G .trialityD4 0 p f ∨
      (3 < p ^ f ∧ ((p ^ f % 8 ≠ 1 ∧ LieModel G .PSL 4 p f) ∨
        (p ^ f % 8 ≠ 7 ∧ LieModel G .PSU 4 p f))))) ∨
    (∃ f : ℕ, LieModel G .twistedG2 0 3 f) ∨
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨ Nonempty (G ≃* alternatingGroup (Fin 9)) ∨
    Nonempty (G ≃* alternatingGroup (Fin 10)) ∨ Nonempty (G ≃* alternatingGroup (Fin 11)) ∨
    NativeSporadic.IsSporadic G .M11 ∨ LieModel G .PSU 3 2 2 ∨
    NativeSporadic.IsSporadic G .M12 ∨ NativeSporadic.IsSporadic G .J1 ∨
    NativeSporadic.IsSporadic G .McL ∨ NativeSporadic.IsSporadic G .Ly ∨
    NativeSporadic.IsSporadic G .ONan

@[expose] def C2StarList (G : Type) [Group G] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
    ((3 < p ^ f ∧ (LieModel G .PSL 2 p f ∨ LieModel G .PSp 2 p f ∨ LieModel G .G2 0 p f)) ∨
      LieModel G .PSL 3 p f ∨ LieModel G .PSU 3 p f ∨
      LieModel G .trialityD4 0 p f ∨
      (3 < p ^ f ∧ ((p ^ f % 8 ≠ 1 ∧ LieModel G .PSL 4 p f) ∨
        (p ^ f % 8 ≠ 7 ∧ LieModel G .PSU 4 p f))))) ∨
    (∃ f : ℕ, LieModel G .twistedG2 0 3 f) ∨
    LieModel G .PSU 3 2 2 ∨ Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    NativeSporadic.IsSporadic G .M11 ∨
    NativeSporadic.IsSporadic G .M12 ∨ NativeSporadic.IsSporadic G .J1 ∨
    NativeSporadic.IsSporadic G .McL ∨ NativeSporadic.IsSporadic G .Ly ∨
    NativeSporadic.IsSporadic G .ONan


@[expose] def S_C23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → IsSpecialOddType G → C23List G


@[expose] def S_C2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → IsLB2Type G →
    ¬ HasTwoUniquenessSubgroup G →
      C23List G ∧ ¬ LieModel G .PSU 3 2 2 ∧ ¬ NativeSporadic.IsSporadic G .J1 ∧
        ¬ Nonempty (G ≃* alternatingGroup (Fin 5)) ∧ ¬ Nonempty (G ≃* alternatingGroup (Fin 9)) ∧
        ¬ Nonempty (G ≃* alternatingGroup (Fin 10)) ∧ ¬ Nonempty (G ≃* alternatingGroup (Fin 11))


@[expose] def S_C3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → IsLT2oType G →
    ¬ IsRestrictedEvenType G →
      Nonempty (G ≃* alternatingGroup (Fin 9)) ∨ Nonempty (G ≃* alternatingGroup (Fin 10)) ∨
        Nonempty (G ≃* alternatingGroup (Fin 11))


end CFSG.GH74.GLS
