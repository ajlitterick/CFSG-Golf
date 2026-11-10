module

public import CFSG.ClassicalInvolution.Q3.Q3DStand

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7E

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Disc3

section Stmt


theorem ih8T_mono {p f : ℕ} [Fact p.Prime] {m n : ℕ} (hmn : m ≤ n) (h : IH8T p f n) :
    IH8T p f m where
  thm2 := fun hp hq G _ _ hG => h.thm2 hp hq G (hG.trans_le hmn)
  thm4 := fun hp hq G _ _ hG => h.thm4 hp hq G (hG.trans_le hmn)
  thm5 := fun hp hq G _ _ hG => h.thm5 hp hq G (hG.trans_le hmn)
  thm6 := fun hp hq G _ _ _ hG => h.thm6 hp hq G (hG.trans_le hmn)
  thm7 := fun hp hq G _ _ _ hG => h.thm7 hp hq G (hG.trans_le hmn)
  thm8 := fun hp hq G _ _ _ hG => h.thm8 hp hq G (hG.trans_le hmn)
  muTable := fun hp hq G _ _ _ hG => h.muTable hp hq G (hG.trans_le hmn)
  thm3 := ⟨fun hp hq G _ _ hG => h.thm3.1 hp hq G (hG.trans_le hmn),
    fun hp hq G _ _ hG => h.thm3.2 hp hq G (hG.trans_le hmn)⟩

structure EStand3 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R W : Subgroup G) : Prop where
  hyp : HypOmegaModU (.sl2 3 1) Ω
  below : CITBelowT (.sl2 3 1) (Nat.card G)
  ih : IH8T 3 1 (Nat.card G)
  mem : K ∈ Ω
  aEmpty : AEmpty Ω K
  twin : ∃ K' ∈ twinSet Ω K, K' ≠ K ∧ ∃ R' ∈ RSet Ω, R' ≤ K' ∧ R' ≤ (S : Subgroup G)
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hW : W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W

@[expose] def ThmEBelow3 (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n →
    ∀ (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G) (R W H : Subgroup G),
      EStand3 Ω K S R W → EHyp Ω K W H → H = ⊤

structure MinCex3 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R W H : Subgroup G) : Prop where
  stand : EStand3 Ω K S R W
  hyp : EHyp Ω K W H
  proper : H ≠ ⊤
  minimal : ThmEBelow3 (Nat.card G)

@[expose] def ThmEWithSylow3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), EStand3 Ω K S R W → EHyp Ω K W H → H = ⊤

@[expose] def MinCexFalse3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex3 Ω K S R W H → False

theorem thmEWithSylow3_of_minCexFalse (h : MinCexFalse3) : ThmEWithSylow3 := by
  have key : ∀ n, ThmEBelow3 n := by
    intro n
    induction n with
    | zero =>
      intro G _ _ hG
      exact absurd hG (by omega)
    | succ n ih =>
      intro G _ _ hG Ω K S R W H hst hH
      by_cases hn : Nat.card G < n
      · exact ih G hn Ω K S R W H hst hH
      · have hGn : Nat.card G = n := by omega
        by_contra hne
        exact h G Ω K S R W H ⟨hst, hH, hne, hGn ▸ ih⟩
  intro G _ _ Ω K S R W H hst hH
  exact key (Nat.card G + 1) G (Nat.lt_succ_self _) Ω K S R W H hst hH


end Stmt

end CFSG.ClassicalInvolution.Q3.Q3T7E
