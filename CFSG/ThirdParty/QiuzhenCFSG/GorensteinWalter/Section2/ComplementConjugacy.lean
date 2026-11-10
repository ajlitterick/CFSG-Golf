module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.I.theorem_18_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.Algebra.Group.Pointwise.Set.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Schur–Zassenhaus complement conjugacy support

The complement-conjugacy machinery used by Statement 1.1 (Thompson lemma,
Bender [1] p. 164) and its T1 invariant-coset-lifting step (KS 8.2.1).

The unrestricted theorem `complements_conjugate_of_coprime` (Gorenstein
6.2.4 / KS 6.2.1) wraps the axiom-free validation oracle
`BenderSuzuki.External.huppert_I_18_3_complements_conjugate` (Huppert I.18.3,
itself the classical minimal-normal proof closed by Feit–Thompson on the odd
side).  The classical-route helpers from the sz-conjugacy verdict
(`map_complement_quotient`, `quotient_coprime_of_coprime`,
`map_mk'_map_conj_eq`, `lift_conj_eq_of_map_eq`, `complements_of_M_inside_join`)
are NOT needed: the oracle route avoids the solvable-normal/solvable-quotient
induction entirely.  `exists_mem_normal_conjugator` (the ambient-to-`N`
adjustment) is proved locally and is the piece that upgrades the oracle's
ambient conjugator to the normal-complement conjugator used by the
semidirect-product argument of T1.  `invariant_right_coset_has_fixed_representative_of_pgroup`
is the KS 8.2.1 invariant-coset-lifting lemma in the p-group-operator case
(the case used by Statement 1.1, where the operator is the `p`-group `P`):
the invariant coset `U·g` carries a fixed representative, by the p-group
fixed-point theorem on the invariant set `U·g` (order coprime to `p`).
-/


open scoped Pointwise

namespace CFSG.GorensteinWalter

namespace SchurZassenhaus

/-- Any ambient conjugator can be adjusted into the normal complement `N`. -/
public theorem exists_mem_normal_conjugator
    {G : Type*} [Group G] [Finite G]
    {N H K : Subgroup G} [N.Normal]
    (hH : N.IsComplement' H)
    {g : G} (hg : K = H.map (MulAut.conj g).toMonoidHom) :
    ∃ n : N, K = H.map (MulAut.conj (n : G)).toMonoidHom := by
  have hgmem : g ∈ (N : Set G) * (H : Set G) := by
    have : g ∈ (N ⊔ H : Subgroup G) := by
      rw [hH.sup_eq_top]
      trivial
    change g ∈ (↑(N ⊔ H) : Set G) at this
    rwa [Subgroup.normal_mul N H] at this
  rcases (Set.mem_mul.mp hgmem) with ⟨n, hn, h, hh, hnmh⟩
  refine ⟨⟨n, hn⟩, ?_⟩
  rw [hg, ← hnmh]
  exact map_conj_mul_right_eq_of_mem_normalizer n ⟨h, Subgroup.le_normalizer hh⟩

/-- Schur–Zassenhaus complement conjugacy: all complements of a normal Hall
subgroup are conjugate (Gorenstein 6.2.4 / KS 6.2.1, unrestricted via
Feit–Thompson). -/
public theorem complements_conjugate_of_coprime
    {G : Type*} [Group G] [Finite G]
    (N H K : Subgroup G) :
    N.Normal → N.IsComplement' H → N.IsComplement' K →
      Nat.Coprime (Nat.card N) N.index →
      ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom := by
  intro hN hH hK hcop
  let : N.Normal := hN
  have hcopQ : Nat.Coprime (Nat.card N) (Nat.card (G ⧸ N)) := by
    simpa [Subgroup.index_eq_card] using hcop
  exact BenderSuzuki.External.huppert_I_18_3_complements_conjugate N H K hcopQ hH hK

/-- The stronger form: the conjugator can be chosen inside the normal
complement `N`. -/
public theorem exists_mem_normal_conjugator_of_coprime
    {G : Type*} [Group G] [Finite G]
    (N H K : Subgroup G) :
    N.Normal → N.IsComplement' H → N.IsComplement' K →
      Nat.Coprime (Nat.card N) N.index →
      ∃ n : N, K = H.map (MulAut.conj (n : G)).toMonoidHom := by
  intro hN hH hK hcop
  let : N.Normal := hN
  rcases (complements_conjugate_of_coprime N H K hN hH hK hcop) with ⟨g, hg⟩
  exact exists_mem_normal_conjugator hH hg


-- p-group special case of T1 (KS 8.2.1): the invariant coset U·g contains a
-- fixed representative.

-- the coset condition gives g * φ a g⁻¹ ∈ U

-- sub-goal 2: the U-copy is normal in AU
-- the action of A on U, restricted from the action on G


-- the compatibility: the restricted action commutes with the inclusion

-- the embedding of U ⋊ A into S


-- the normal form: the left coordinate of every AU element lies in U

-- every element of AU is inl u · inr a with u ∈ U (the decomposition)


-- the U-copy and the A-copy are disjoint in S


-- the complement structure in ↥AU: the U-copy and the A-copy

-- the U-copy is contained in AU

-- the A-copy is contained in AU

-- AU is the join of the U-copy and the A-copy

-- the image of `H.subgroupOf K` under the inclusion of K is H (when H ≤ K)
private lemma map_subtype_subgroupOf {G : Type*} [Group G] (H K : Subgroup G) (hHK : H ≤ K) :
    (H.subgroupOf K).map K.subtype = H := by
  apply le_antisymm
  · intro x hx
    rcases (Subgroup.mem_map.mp hx) with ⟨y, hy, hyx⟩
    rw [← hyx]
    exact Subgroup.mem_subgroupOf.mp hy
  · intro x hx
    rw [Subgroup.mem_map]
    exact ⟨⟨x, hHK hx⟩, by
      rw [Subgroup.mem_subgroupOf]
      exact hx, rfl⟩

-- sub-goal 5: the index of the U-copy in AU is |A|, via the right projection

-- the cardinality of the U-copy inside AU is |U|

-- sub-goal 4b: the conjugated A-copy is a complement of the U-copy in AU

-- a conjugate of the A-copy equal to the A-copy means the conjugating element is fixed

-- sub-goal 6 + assembly: T1 in the general coprime case (KS 8.2.1 via
-- Schur–Zassenhaus complement conjugacy in the semidirect-product subgroup AU)

/-! ## Coprime-action and p-group commutator consequences -/

/-- The two coprime-action identities used repeatedly in the Thompson lemma.
This is the operator-action form of KS 8.2.7; ambient subgroup commutators are
obtained with the bridges in `FeitThompson.SubgroupConj`. -/
public theorem coprime_action_decomposition
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    [MulDistribMulAction A B]
    (hsolv : IsSolvable B) (hcop : Nat.Coprime (Nat.card A) (Nat.card B)) :
    fixedPointSubgroup A B ⊔ commutatorAction (A := A) (G := B) = ⊤ ∧
      commutatorAction₂ (A := A) (G := B) = commutatorAction (A := A) (G := B) := by
  exact ⟨fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
      (G := B) (A := A) hsolv hcop,
    commutatorAction₂_eq_commutatorAction_of_solvable_coprime
      (G := B) (A := A) hsolv hcop⟩

/-- KS 8.1.4(b), in the ambient-subgroup form used by the Thompson lemma:
if two `p`-subgroups normalize as indicated and `B` is nontrivial, then
commutation with `P` cannot generate all of `B`. -/
public theorem commutator_lt_of_pGroups
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (B P : Subgroup G) (hBp : IsPGroup p B) (hPp : IsPGroup p P)
    (hPB : P ≤ Subgroup.normalizer (B : Set G)) (hBne : B ≠ ⊥) :
    ⁅B, P⁆ < B := by
  have hle : ⁅B, P⁆ ≤ B :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hPB
  refine lt_of_le_of_ne hle ?_
  intro heq
  let S : Subgroup G := B ⊔ P
  have hBnormS : (B.subgroupOf S).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (H := B) (K := S) le_sup_left).2
    exact sup_le Subgroup.le_normalizer hPB
  let : (B.subgroupOf S).Normal := hBnormS
  have hBPp : IsPGroup p S :=
    IsPGroup.to_sup_of_normal_left' hBp hPp hPB
  have hnil : Group.IsNilpotent ↑S :=
    IsPGroup.isNilpotent (p := p) hBPp
  obtain ⟨n, hn⟩ :=
    (Subgroup.nilpotent_iff_lowerCentralSeries (G := ↑S)).mp hnil
  have hB_le_lcs :
      ∀ n : ℕ, B.subgroupOf S ≤
        (⊤ : Subgroup ↑S).lowerCentralSeries n := by
    intro n
    induction n with
    | zero => simp [Subgroup.lowerCentralSeries_zero]
    | succ n ih =>
        rw [Subgroup.lowerCentralSeries_succ]
        have hcomm_sub :
            ⁅B.subgroupOf S, P.subgroupOf S⁆ = B.subgroupOf S := by
          apply (Subgroup.map_subtype_inj (H := S)).mp
          calc
            (⁅B.subgroupOf S, P.subgroupOf S⁆).map S.subtype = B := by
              rw [Subgroup.map_commutator,
                Subgroup.map_subgroupOf_eq_of_le le_sup_left,
                Subgroup.map_subgroupOf_eq_of_le le_sup_right, heq]
            _ = (B.subgroupOf S).map S.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le le_sup_left).symm
        rw [← hcomm_sub]
        exact Subgroup.commutator_mono ih le_top
  have hBsub_bot : B.subgroupOf S = ⊥ := by
    apply bot_unique
    exact (hB_le_lcs n).trans_eq hn
  apply hBne
  calc
    B = (B.subgroupOf S).map S.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le le_sup_left).symm
    _ = ⊥ := by rw [hBsub_bot]; simp

end SchurZassenhaus

end CFSG.GorensteinWalter
