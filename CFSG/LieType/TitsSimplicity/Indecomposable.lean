module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Matrix.Basic

public section

namespace CFSG.LieType.TitsSimplicity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def IsIndecomposable (A : Matrix ι ι ℤ) : Prop :=
  ¬ ∃ I J : Finset ι, I.Nonempty ∧ J.Nonempty ∧ Disjoint I J ∧ I ∪ J = Finset.univ ∧
    ∀ i ∈ I, ∀ j ∈ J, A i j = 0

theorem isIndecomposable_iff {A : Matrix ι ι ℤ} :
    IsIndecomposable A ↔
      ∀ S : Finset ι, (∀ i ∈ S, ∀ j ∉ S, A i j = 0) → S = ∅ ∨ S = Finset.univ := by
  constructor
  · intro h S hS
    by_contra hne
    rw [not_or] at hne
    refine h ⟨S, Sᶜ, Finset.nonempty_iff_ne_empty.2 hne.1, ?_, disjoint_compl_right,
      Finset.union_compl S, fun i hi j hj => hS i hi j (Finset.mem_compl.1 hj)⟩
    rw [Finset.nonempty_iff_ne_empty, Ne, Finset.compl_eq_empty_iff]
    exact hne.2
  · rintro h ⟨I, J, hI, hJ, hIJ, hU, h0⟩
    have hJI : ∀ j, j ∈ J ↔ j ∉ I := fun j =>
      ⟨fun hj hi => Finset.disjoint_left.1 hIJ hi hj, fun hi => by
        have := Finset.mem_univ j
        rw [← hU, Finset.mem_union] at this
        exact this.resolve_left hi⟩
    rcases h I fun i hi j hj => h0 i hi j ((hJI j).2 hj) with rfl | rfl
    · exact Finset.not_nonempty_empty hI
    · obtain ⟨j, hj⟩ := hJ
      exact (hJI j).1 hj (Finset.mem_univ j)

instance (A : Matrix ι ι ℤ) : Decidable (IsIndecomposable A) :=
  have : DecidablePred fun S : Finset ι =>
      (∀ i ∈ S, ∀ j ∉ S, A i j = 0) → S = ∅ ∨ S = Finset.univ := fun S =>
    have : DecidablePred fun i => ∀ j ∉ S, A i j = 0 := fun _ => inferInstance
    inferInstance
  decidable_of_iff _ isIndecomposable_iff.symm

@[expose] def dynkinGraph (A : Matrix ι ι ℤ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ A i j ≠ 0 ∧ A j i ≠ 0
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩


end CFSG.LieType.TitsSimplicity
