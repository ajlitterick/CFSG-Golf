module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Algebra.Semigroup
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Separation.Lemmas
public import CFSG.LocalAnalysis.ZStar.BrauerPrincipal
public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG

namespace ZStar.BrauerBlockLift

open ZStar.Helpers ZStar.BrauerProjection
  ZStar.BrauerPrincipal

universe u

variable {G : Type u} [Group G] [Fintype G]

noncomputable local instance subgroupFintype (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H


@[expose] noncomputable def ambientClassCoeff (w : G)
    (r : GroupAlgebraTwo (involutionCentralizer w))
    (C : ConjClasses G) : ZMod 2 := by
  classical
  exact if h : ∃ a : involutionCentralizer w,
      ConjClasses.mk (a : G) = C then
    r.coeff (Classical.choose h)
  else 0


@[expose] noncomputable def ambientExtension (w : G)
    (r : GroupAlgebraTwo (involutionCentralizer w)) : GroupAlgebraTwo G :=
  ∑ g : G,
    MonoidAlgebra.single g (ambientClassCoeff w r (ConjClasses.mk g))

@[simp]
theorem ambientExtension_coeff (w : G)
    (r : GroupAlgebraTwo (involutionCentralizer w)) (g : G) :
    (ambientExtension w r).coeff g =
      ambientClassCoeff w r (ConjClasses.mk g) := by
  classical
  simp [ambientExtension, Finsupp.finsetSum_apply, Finsupp.single_apply]


theorem isGroupCentral_pow (e : GroupAlgebraTwo G)
    (he : IsGroupCentral G e) (n : ℕ) :
    IsGroupCentral G (e ^ n) := by
  induction n with
  | zero => simpa using isGroupCentral_one G
  | succ n ih =>
      simpa only [pow_succ] using ih.mul G he

theorem brauerProjection_pow (w : G) (hw2 : w * w = 1)
    (e : GroupAlgebraTwo G) (he : IsGroupCentral G e) (n : ℕ) :
    brauerProjection w (e ^ n) = (brauerProjection w e) ^ n := by
  induction n with
  | zero =>
      ext a
      rw [pow_zero, brauerProjection_coeff, pow_zero]
      by_cases ha : a = 1
      · subst a
        simp
      · have hcoe : (a : G) ≠ 1 := by
          intro h
          apply ha
          exact Subtype.ext h
        simp [MonoidAlgebra.one_def, ha, hcoe]
  | succ n ih =>
      rw [pow_succ, brauerProjection_mul w hw2]
      · rw [ih, pow_succ]
      · exact conjInvariantBy_of_isGroupCentral w (e ^ n)
          (isGroupCentral_pow e he n)
      · exact conjInvariantBy_of_isGroupCentral w e he

theorem exists_positive_idempotent_power
    {M : Type*} [Monoid M] [Finite M] (a : M) :
    ∃ n : ℕ, n ≠ 0 ∧ a ^ n * a ^ n = a ^ n := by
  let : TopologicalSpace M := ⊥
  let : DiscreteTopology M := ⟨rfl⟩
  let s : Set M := Set.range (fun n : ℕ => a ^ (n + 1))
  have hsne : s.Nonempty := ⟨a ^ (0 + 1), ⟨0, rfl⟩⟩
  have hscompact : IsCompact s := Set.toFinite s |>.isCompact
  have hsclosed : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ s := by
    rintro x ⟨m, rfl⟩ y ⟨n, rfl⟩
    refine ⟨m + n + 1, ?_⟩
    calc
      a ^ (m + n + 1 + 1) = a ^ ((m + 1) + (n + 1)) := by
        congr 1
        omega
      _ = a ^ (m + 1) * a ^ (n + 1) := pow_add a (m + 1) (n + 1)
  obtain ⟨b, hb, hbidem⟩ :=
    exists_idempotent_in_compact_subsemigroup
      (fun _ => continuous_of_discreteTopology) s hsne hscompact hsclosed
  obtain ⟨n, rfl⟩ := hb
  exact ⟨n + 1, by omega, hbidem⟩


end ZStar.BrauerBlockLift

end CFSG
