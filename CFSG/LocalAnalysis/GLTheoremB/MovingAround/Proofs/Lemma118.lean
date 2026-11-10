module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma104c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input31

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

section Principle

variable {G : Type} [Group G] [Finite G]

theorem ddKey_fst_le {p : ℕ} {E A E' A' : Subgroup G} (h : ddKey p E' A' ≤ ddKey p E A) :
    CFSG.Open.pRank p (E' ⊓ A') ≤ CFSG.Open.pRank p (E ⊓ A) := by
  unfold ddKey at h
  rcases Prod.Lex.toLex_le_toLex.1 h with h1 | ⟨h1, -⟩
  · exact le_of_lt h1
  · exact le_of_eq h1

theorem rank_ge_of_card' {p : ℕ} [hp : Fact p.Prime] {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian p E)
    {k : ℕ} (hk : p ^ k ≤ Nat.card E) : k ≤ CFSG.Open.pRank p E := by
  obtain ⟨r, hr⟩ := (isPGroup_of_isElemAbelian' hE).exists_card_eq
  rw [hr] at hk
  have hkr : k ≤ r := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hk
  exact hkr.trans (CFSG.SectionRank.le_pRank hp.out.one_lt le_rfl hE hr)

theorem normalizer_le_glbCore' {p : ℕ} {Q P : Subgroup G} (hQP : Q ≤ P)
    (hQ : 2 ≤ CFSG.Open.pRank p Q) : Subgroup.normalizer (Q : Set G) ≤ GLBCore p 2 P := by
  unfold GLBCore
  exact le_sSup ⟨Q, hQP, hQ, rfl⟩

theorem ddKey_snd_le {p : ℕ} {E A E' A' : Subgroup G} (h : ddKey p E' A' ≤ ddKey p E A)
    (h1 : CFSG.Open.pRank p (E' ⊓ A') = CFSG.Open.pRank p (E ⊓ A)) :
    min (CFSG.Open.pRank p E') (CFSG.Open.pRank p A') ≤
      min (CFSG.Open.pRank p E) (CFSG.Open.pRank p A) := by
  unfold ddKey at h
  rcases Prod.Lex.toLex_le_toLex.1 h with h2 | ⟨-, h3⟩
  · omega
  · rcases Prod.Lex.toLex_le_toLex.1 h3 with h4 | ⟨h4, -⟩
    · exact le_of_lt h4
    · exact le_of_eq h4

theorem le_M_of_rank_two {p : ℕ} {M F H : Subgroup G} (hF : inD p M F) (hH : IsSCp p ⊤ H)
    (h2 : 2 ≤ CFSG.Open.pRank p (F ⊓ H)) : H ≤ M := by
  have hHC : H ≤ Subgroup.centralizer ((F ⊓ H : Subgroup G) : Set G) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact elemAbelian_comm hH.2.1 (Subgroup.mem_inf.1 hx).2 hh
  exact hHC.trans ((Subgroup.centralizer_le_normalizer _).trans
    ((normalizer_le_glbCore' inf_le_left h2).trans hF.2.clause_d))

theorem inD_of_bigger_key {p : ℕ} [hp : Fact p.Prime] {M E A : Subgroup G} (hEA : IsDDpStar p M E A)
    {F H : Subgroup G} (hF : inD p M F) (hH : IsSCp p ⊤ H) (h2 : 2 ≤ CFSG.Open.pRank p (F ⊓ H))
    (h3 : 3 ≤ CFSG.Open.pRank p H) (hbig : ¬ ddKey p F H ≤ ddKey p E A) : inD p M H := by
  have hHM := le_M_of_rank_two hF hH h2
  have hHmax : IsSCp p M H := ⟨hHM, hH.2.1, fun E' _ hE' hHE' => hH.2.2 E' le_top hE' hHE'⟩
  refine ⟨⟨hHmax, h3⟩, ?_⟩
  by_contra hnot
  exact hbig (hEA.2 F H ⟨hF, ⟨⟨hHmax, h3⟩, hnot⟩, h2⟩)

theorem inD_of_meet {p : ℕ} [hp : Fact p.Prime] {M E A : Subgroup G} (hEA : IsDDpStar p M E A)
    {F H : Subgroup G} (hF : inD p M F) (hH : IsSCp p ⊤ H)
    (hr : CFSG.Open.pRank p (E ⊓ A) + 1 ≤ CFSG.Open.pRank p (F ⊓ H)) : inD p M H := by
  have hk2 : 2 ≤ CFSG.Open.pRank p (E ⊓ A) := hEA.1.2.2
  refine inD_of_bigger_key hEA hF hH (by omega) ?_ ?_
  · exact (by omega : 3 ≤ CFSG.Open.pRank p (F ⊓ H)).trans
      (CFSG.SectionRank.pRank_mono hp.out.one_lt inf_le_right)
  · intro hle
    have := ddKey_fst_le hle
    omega

theorem propagate_commute {p : ℕ} [hp : Fact p.Prime] {M E A : Subgroup G} (hEA : IsDDpStar p M E A)
    {X Z : Subgroup G} (hX : CFSG.Open.IsElemAbelian p X)
    (hXr : CFSG.Open.pRank p (E ⊓ A) + 1 ≤ CFSG.Open.pRank p X)
    (hZ : CFSG.Open.IsElemAbelian p Z) (hcomm : X ≤ Subgroup.centralizer (Z : Set G))
    (hZP : ∀ H : Subgroup G, IsSCp p ⊤ H → Z ≤ H → inD p M H) :
    ∀ H : Subgroup G, IsSCp p ⊤ H → X ≤ H → inD p M H := by
  intro H hH hXH
  have hS : CFSG.Open.IsElemAbelian p (X ⊔ Z) := isElemAbelian_sup_of_commute hX hZ hcomm
  obtain ⟨H', hH'S, hSH'⟩ := c104_exists_isSCp_top hS
  have hH'D : inD p M H' := hZP H' hH'S (le_trans le_sup_right hSH')
  refine inD_of_meet hEA hH'D hH ?_
  have hXle : X ≤ H' ⊓ H := le_inf (le_trans le_sup_left hSH') hXH
  exact hXr.trans (CFSG.SectionRank.pRank_mono hp.out.one_lt hXle)

theorem propagate_chain {p : ℕ} [hp : Fact p.Prime] {M E A : Subgroup G} (hEA : IsDDpStar p M E A)
    {X Y : Subgroup G} (hXY : IsKConnectedIn p (CFSG.Open.pRank p (E ⊓ A) + 1) ⊤ X Y)
    (hYP : ∀ H : Subgroup G, IsSCp p ⊤ H → Y ≤ H → inD p M H) :
    ∀ H : Subgroup G, IsSCp p ⊤ H → X ≤ H → inD p M H := by
  obtain ⟨-, hXab, hXcard, -, hYab, -, hcases⟩ := hXY
  have hXr : CFSG.Open.pRank p (E ⊓ A) + 1 ≤ CFSG.Open.pRank p X :=
    rank_ge_of_card' hXab hXcard
  rcases hcases with hXY' | ⟨U, V, hU, hV, hXU, hrtg, hVY⟩
  · exact propagate_commute hEA hXab hXr hYab hXY' hYP
  · have hVr : CFSG.Open.pRank p (E ⊓ A) + 1 ≤ CFSG.Open.pRank p V :=
      rank_ge_of_card' hV.2.1 hV.2.2.ge
    have hVP : ∀ H : Subgroup G, IsSCp p ⊤ H → V ≤ H → inD p M H :=
      propagate_commute hEA hV.2.1 hVr hYab hVY hYP
    have hall : ∀ W : Subgroup G,
        Relation.ReflTransGen (IsKConnStep p (CFSG.Open.pRank p (E ⊓ A) + 1) ⊤) W V →
          ∀ H : Subgroup G, IsSCp p ⊤ H → W ≤ H → inD p M H := by
      intro W hW
      induction hW using Relation.ReflTransGen.head_induction_on with
      | refl => exact hVP
      | @head W' W'' hstep _ ih =>
        exact propagate_commute hEA hstep.1.2.1
          (rank_ge_of_card' hstep.1.2.1 hstep.1.2.2.ge) hstep.2.1.2.1 hstep.2.2 ih
    have hUP := hall U hrtg
    exact propagate_commute hEA hXab hXr hU.2.1 hXU hUP

theorem base_of_le {p : ℕ} [hp : Fact p.Prime] {M E A : Subgroup G} (hEA : IsDDpStar p M E A)
    {F Y : Subgroup G} (hF : inD p M F) (hYF : Y ≤ F)
    (hYr : CFSG.Open.pRank p (E ⊓ A) + 1 ≤ CFSG.Open.pRank p Y) :
    ∀ H : Subgroup G, IsSCp p ⊤ H → Y ≤ H → inD p M H := by
  intro H hH hYH
  refine inD_of_meet hEA hF hH ?_
  exact hYr.trans (CFSG.SectionRank.pRank_mono hp.out.one_lt (le_inf hYF hYH))

theorem chain_min_step {p : ℕ} [hp : Fact p.Prime] {M E A : Subgroup G} (hEA : IsDDpStar p M E A)
    (hr2 : CFSG.Open.pRank p (E ⊓ A) = 2) (hA3 : CFSG.Open.pRank p A ≤ 3)
    {C C' : Subgroup G} (hC : CFSG.Open.IsElemAbelian p C) (hC4 : 4 ≤ CFSG.Open.pRank p C)
    (hC'4 : 4 ≤ CFSG.Open.pRank p C') (hCC' : 2 ≤ CFSG.Open.pRank p (C ⊓ C'))
    (hCP : ∀ H : Subgroup G, IsSCp p ⊤ H → C ≤ H → inD p M H) :
    ∀ H : Subgroup G, IsSCp p ⊤ H → C' ≤ H → inD p M H := by
  intro H hH hC'H
  obtain ⟨HC, hHC, hCHC⟩ := c104_exists_isSCp_top hC
  have hHCD : inD p M HC := hCP HC hHC hCHC
  have hsub : C ⊓ C' ≤ HC ⊓ H := le_inf (inf_le_left.trans hCHC) (inf_le_right.trans hC'H)
  have h2 : 2 ≤ CFSG.Open.pRank p (HC ⊓ H) :=
    hCC'.trans (CFSG.SectionRank.pRank_mono hp.out.one_lt hsub)
  have hrC' : CFSG.Open.pRank p C' ≤ CFSG.Open.pRank p H :=
    CFSG.SectionRank.pRank_mono hp.out.one_lt hC'H
  have hrC : CFSG.Open.pRank p C ≤ CFSG.Open.pRank p HC :=
    CFSG.SectionRank.pRank_mono hp.out.one_lt hCHC
  have h3 : 3 ≤ CFSG.Open.pRank p H := by omega
  refine inD_of_bigger_key hEA hHCD hH h2 h3 ?_
  intro hle
  have hfst := ddKey_fst_le hle
  have heq : CFSG.Open.pRank p (HC ⊓ H) = CFSG.Open.pRank p (E ⊓ A) := by omega
  have hsnd := ddKey_snd_le hle heq
  have hmin : 4 ≤ min (CFSG.Open.pRank p HC) (CFSG.Open.pRank p H) :=
    le_min (by omega) (by omega)
  have hA : min (CFSG.Open.pRank p E) (CFSG.Open.pRank p A) ≤ 3 :=
    (min_le_right _ _).trans hA3
  omega

theorem succ_le_pow_pred {p r : ℕ} (hp : 3 ≤ p) (hr : 2 ≤ r) : r + 1 ≤ p ^ (r - 1) := by
  have key : ∀ s : ℕ, s + 3 ≤ 3 ^ (s + 1) := by
    intro s
    induction s with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; omega
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  have h3 : 3 ^ (s + 1) ≤ p ^ (s + 1) := Nat.pow_le_pow_left hp _
  have := key s
  rw [show s + 2 - 1 = s + 1 by omega]
  omega

theorem exists_elemAb_sub_of_rank {p : ℕ} [hp : Fact p.Prime] {Q : Subgroup G}
    (hQ : CFSG.Open.IsElemAbelian p Q) {s : ℕ} (hs : s ≤ CFSG.Open.pRank p Q) :
    ∃ X : Subgroup G, X ≤ Q ∧ CFSG.Open.IsElemAbelian p X ∧ Nat.card X = p ^ s := by
  obtain ⟨E0, hE0Q, hE0ab, hE0card⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt Q
  obtain ⟨X, hXE0, hXab, hXcard⟩ :=
    exists_le_isElemAbelian_card hE0ab (n := s) (by rw [hE0card]; exact pow_dvd_pow p hs)
  exact ⟨X, hXE0.trans hE0Q, hXab, hXcard⟩

theorem kconn_mono {p k : ℕ} {R A B : Subgroup G} (h : IsKConnectedIn p k R A B) :
    IsKConnectedIn p k ⊤ A B := by
  obtain ⟨-, hAab, hAc, -, hBab, hBc, hcases⟩ := h
  refine ⟨le_top, hAab, hAc, le_top, hBab, hBc, ?_⟩
  rcases hcases with hc | ⟨U, V, hU, hV, hAU, hrtg, hVB⟩
  · exact Or.inl hc
  · refine Or.inr ⟨U, V, ⟨le_top, hU.2.1, hU.2.2⟩, ⟨le_top, hV.2.1, hV.2.2⟩, hAU, ?_, hVB⟩
    have hstep : ∀ x y : Subgroup G, IsKConnStep p k R x y → IsKConnStep p k ⊤ x y :=
      fun x y hxy => ⟨⟨le_top, hxy.1.2.1, hxy.1.2.2⟩, ⟨le_top, hxy.2.1.2.1, hxy.2.1.2.2⟩, hxy.2.2⟩
    have key : ∀ x y : Subgroup G, Relation.ReflTransGen (IsKConnStep p k R) x y →
        Relation.ReflTransGen (IsKConnStep p k ⊤) x y := by
      intro x y hxy
      induction hxy with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih => exact ih.tail (hstep _ _ hbc)
    exact key U V hrtg

end Principle

section Anchor

variable {G : Type} [Group G] [Finite G]


theorem glbCore_mono {p : ℕ} [Finite G] {Q P : Subgroup G} (h : Q ≤ P) :
    GLBCore p 2 Q ≤ GLBCore p 2 P := by
  unfold GLBCore
  refine sSup_le fun N hN => ?_
  obtain ⟨Q', hQ'Q, hr, rfl⟩ := hN
  exact le_sSup ⟨Q', hQ'Q.trans h, hr, rfl⟩


end Anchor

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
