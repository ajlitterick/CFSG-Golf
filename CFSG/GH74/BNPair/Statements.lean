module

public import CFSG.GH74.BNPair.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

public section

namespace CFSG.GH74.BNPair

universe u

open scoped Pointwise

section Prop302

variable {X : Type*} [Group X]

structure Proposition302 (B N : Subgroup X) [(cartan B N).Normal] (S : Finset (WeylGroup B N)) :
    Prop where
  iUnion_dc : (⋃ w : WeylGroup B N, dc B N w) = Set.univ
  pairwiseDisjoint_dc : Pairwise (Function.onFun Disjoint (dc B N))
  parabolic_subgroup : ∀ J : Finset (WeylGroup B N), J ⊆ S →
    ∃ P : Subgroup X, (P : Set X) = parabolicSet B N (J : Set (WeylGroup B N)) ∧ B ≤ P ∧
      Subgroup.normalizer (P : Set X) = P
  parabolic_le_iff : ∀ J K : Finset (WeylGroup B N), J ⊆ S → K ⊆ S →
    (parabolic B N (J : Set (WeylGroup B N)) ≤ parabolic B N (K : Set (WeylGroup B N)) ↔ J ⊆ K)
  exists_parabolic : ∀ P : Subgroup X, B ≤ P →
    ∃ J : Finset (WeylGroup B N), J ⊆ S ∧ P = parabolic B N (J : Set (WeylGroup B N))
  parabolic_empty : parabolic B N ((∅ : Finset (WeylGroup B N)) : Set (WeylGroup B N)) = B
  parabolic_univ : parabolic B N (S : Set (WeylGroup B N)) = ⊤
  refined : ∀ n m : N, (n : WeylGroup B N) ∈ S →
    wordLength (S : Set (WeylGroup B N)) ((n : WeylGroup B N) * (m : WeylGroup B N)) >
        wordLength (S : Set (WeylGroup B N)) (m : WeylGroup B N) →
      ({(n : X)} : Set X) * (B : Set X) * {(m : X)} ⊆
        dc B N ((n : WeylGroup B N) * (m : WeylGroup B N))

@[expose] def Prop30_2 : Prop :=
  ∀ (X : Type u) [Group X] (B N : Subgroup X) [(cartan B N).Normal] (S : Finset (WeylGroup B N)),
    IsTitsSystem B N S → Proposition302 B N S

end Prop302

section Building

@[expose] def Eq30_3 : Prop :=
  ∀ (X : Type u) [Group X] (n : ℕ) (D : RankTwoSystem X n), D.Xplus.Normal


@[expose] def Lemma30_8 : Prop :=
  ∀ (X : Type u) [Group X] (n : ℕ) (D : RankTwoSystem X n), ∀ j : ℕ, j ≤ n →
    ∀ l l' : List D.Vertex, IsGLSPath D.graph l → IsGLSPath D.graph l' → l.length = j + 1 →
      l'.length = j + 1 → (∀ a b : D.Vertex, l.head? = some a → l'.head? = some b →
        (D.IsTypeOne a ↔ D.IsTypeOne b)) → ∃ g : X, l.map (D.action g) = l'

@[expose] def Lemma30_9 : Prop :=
  ∀ (X : Type u) [Group X] (n : ℕ) (D : RankTwoSystem X n),
    ∃ π₁ π₂ : List D.Vertex,
      IsGLSPath D.graph π₁ ∧ IsGLSPath D.graph π₂ ∧ π₁.length = n + 1 ∧ π₂.length = n + 1 ∧
      (∃ a : D.Vertex, π₁.head? = some a ∧ D.IsTypeOne a) ∧
      (∃ a : D.Vertex, π₂.head? = some a ∧ D.IsTypeTwo a) ∧
      (∀ x ∈ D.root n, ∀ v ∈ interiorVertices π₂, ∀ w : D.Vertex, D.graph.Adj v w →
        D.action x w = w) ∧
      (∀ l l' : List D.Vertex, IsGLSPath D.graph l → IsGLSPath D.graph l' → l.length = n + 2 →
        l'.length = n + 2 → π₂ <+: l → π₂ <+: l' → ∃ x ∈ D.root n, l.map (D.action x) = l') ∧
      (∀ x ∈ D.root 1, ∀ v ∈ interiorVertices π₁, ∀ w : D.Vertex, D.graph.Adj v w →
        D.action x w = w) ∧
      (∀ l l' : List D.Vertex, IsGLSPath D.graph l → IsGLSPath D.graph l' → l.length = n + 2 →
        l'.length = n + 2 → π₁ <+: l → π₁ <+: l' → ∃ x ∈ D.root 1, l.map (D.action x) = l')


@[expose] def Theorem30_4 : Prop :=
  ∀ (X X' : Type u) [Group X] [Group X'] (n : ℕ) (D : RankTwoSystem X n) (D' : RankTwoSystem X' n)
    (φ : D.U ≃* D'.U),
    (∀ i : ℤ, 1 ≤ i → i ≤ n → ∀ x : D.U, (x : X) ∈ D.root i ↔ ((φ x : D'.U) : X') ∈ D'.root i) →
      Nonempty (D.Xplus ≃* D'.Xplus)

end Building

end CFSG.GH74.BNPair
