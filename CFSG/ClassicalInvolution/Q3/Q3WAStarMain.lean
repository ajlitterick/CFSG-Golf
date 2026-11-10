module

public import CFSG.ClassicalInvolution.Q3.Generation
public import CFSG.ClassicalInvolution.Q3.Q3WAStar
public import CFSG.ClassicalInvolution.Q3.Q3WAM11Comp

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.RouteD.NonClassical (Linked NCEdge)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

section Facts


@[expose] def ModelConnFactNe3 : Prop :=
  ∀ (t : StatedLieTag) (n : ℕ), IsFundTag t → StatedLieAdmissible t n 3 1 → t ≠ .G2 →
    t ≠ .trialityD4 →
    ∀ R ∈ ModelFund 3 t n 1, ∀ R₁ ∈ ModelFund 3 t n 1, ∀ R₂ ∈ ModelFund 3 t n 1,
      R₁ ≠ R₂ → Commutes R R₁ → Commutes R R₂ → ¬ Commutes R₁ R₂ →
        CommFamilyConnected (ModelFund 3 t n 1)

@[expose] def ModelStarFact3 : Prop :=
  ∀ (t : StatedLieTag) (n : ℕ), IsFundTag t → StatedLieAdmissible t n 3 1 → t ≠ .G2 →
    t ≠ .trialityD4 →
    ∀ R ∈ ModelFund 3 t n 1, ∀ R₁ ∈ ModelFund 3 t n 1, ∀ R₂ ∈ ModelFund 3 t n 1,
      ∀ R_q ∈ ModelFund 3 t n 1, Commutes R R₁ → Commutes R R₂ → Commutes R₁ R₂ →
      ¬ LinkedIn (ModelFund 3 t n 1) R R₁ R₂ → ¬ Commutes R_q R → ¬ Commutes R_q R₁ →
      ¬ Commutes R_q R₂ →
        ∃ R_β ∈ ModelFund 3 t n 1, ∃ R₁' ∈ ModelFund 3 t n 1, ∃ R₂' ∈ ModelFund 3 t n 1,
          LinkedIn (ModelFund 3 t n 1) R R₁ R₁' ∧ LinkedIn (ModelFund 3 t n 1) R R₂ R₂' ∧
          (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R R_β) ∧
          (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁' R_β) ∧
          (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₂' R_β)


end Facts

section Lift


variable {G : Type} [Group G] [Finite G] {ι : Type} {Ω : Set (Subgroup G)} {x : G}

theorem members_chain_of_commConnected3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {i : ι}
    (hsc : ∀ R ∈ (D.kind i).fund, ∀ R' ∈ (D.kind i).fund, ∃ g, R' = conjSub g R)
    (hk : PowCop3 (D.kind i)) (hcc : CommFamilyConnected (D.kind i).fund) :
    ∀ A ∈ compMembers3 Ω x D i, ∀ B ∈ compMembers3 Ω x D i, Relation.ReflTransGen
      (fun U V : Subgroup G => U ∈ compMembers3 Ω x D i ∧ V ∈ compMembers3 Ω x D i ∧
        Commutes U V) A B := by
  intro A hA B hB
  obtain ⟨R_A, hRA⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hA
  obtain ⟨R_B, hRB⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hB
  have key : ∀ X, Relation.ReflTransGen
      (fun U V : Subgroup (D.kind i).G => U ∈ (D.kind i).fund ∧ V ∈ (D.kind i).fund ∧
        Commutes U V) R_A X →
      ∃ N, Corr3 Ω x D i N X ∧ Relation.ReflTransGen
        (fun U V : Subgroup G => U ∈ compMembers3 Ω x D i ∧ V ∈ compMembers3 Ω x D i ∧
          Commutes U V) A N := by
    intro X hX
    induction hX with
    | refl => exact ⟨A, hRA, Relation.ReflTransGen.refl⟩
    | @tail U V _ huv ih =>
      obtain ⟨N, hN, hlink⟩ := ih
      obtain ⟨N', hN'⟩ := exists_corr_right3 hΩ D hsc huv.2.1
      have hNm : N ∈ compMembers3 Ω x D i := ⟨hN.1, hN.2.2 ▸ Subgroup.map_le_range _ _⟩
      have hN'm : N' ∈ compMembers3 Ω x D i := ⟨hN'.1, hN'.2.2 ▸ Subgroup.map_le_range _ _⟩
      exact ⟨N', hN', hlink.tail ⟨hNm, hN'm,
        (corr_commutes3 hΩ hex hP1 hO3 hk hN hN').mpr huv.2.2⟩⟩
  obtain ⟨N, hN, hlink⟩ := key R_B (hcc R_A hRA.2.1 R_B hRB.2.1)
  have : N = B := corr_unique_right3 hΩ hex hP1 hO3 hN hRB
  rwa [this] at hlink

theorem linked_of_linkedIn3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {i : ι}
    (hsc : ∀ R ∈ (D.kind i).fund, ∀ R' ∈ (D.kind i).fund, ∃ g, R' = conjSub g R)
    (hk : PowCop3 (D.kind i)) {K N N' : Subgroup G} {R_K R_N R_N' : Subgroup (D.kind i).G}
    {z : G} (hz : z ∈ K) (hK : Corr3 Ω x D i K R_K) (hN : Corr3 Ω x D i N R_N)
    (hN' : Corr3 Ω x D i N' R_N') (hlink : LinkedIn (D.kind i).fund R_K R_N R_N') :
    Linked Ω z N N' := by
  have key : ∀ X, LinkedIn (D.kind i).fund R_K R_N X →
      ∃ M, Corr3 Ω x D i M X ∧ Linked Ω z N M := by
    intro X hX
    induction hX with
    | refl => exact ⟨N, hN, Relation.ReflTransGen.refl⟩
    | @tail U V _ huv ih =>
      obtain ⟨M, hM, hlinkM⟩ := ih
      obtain ⟨M', hM'⟩ := exists_corr_right3 hΩ D hsc huv.2.1
      have hMK : Commutes M K := (corr_commutes3 hΩ hex hP1 hO3 hk hM hK).mpr huv.2.2.1
      have hM'K : Commutes M' K := (corr_commutes3 hΩ hex hP1 hO3 hk hM' hK).mpr huv.2.2.2.1
      have hMz : M ∈ centralizingMembers Ω {z} :=
        mem_centralizingMembers_of_commutes hM.1.1 hz hMK
      have hM'z : M' ∈ centralizingMembers Ω {z} :=
        mem_centralizingMembers_of_commutes hM'.1.1 hz hM'K
      have hnc : ¬ Commutes M M' := fun hc =>
        huv.2.2.2.2 ((corr_commutes3 hΩ hex hP1 hO3 hk hM hM').mp hc)
      exact ⟨M', hM', hlinkM.trans (Linked.single ⟨hMz, hM'z, hnc⟩)⟩
  obtain ⟨M, hM, hlinkM⟩ := key R_N' hlink
  have : M = N' := corr_unique_right3 hΩ hex hP1 hO3 hM hN'
  rwa [this] at hlinkM

end Lift

section Main


@[expose] def MultiStar3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z → LocalOddThreeFree3 (conjClass3 K) z →
      ∀ {ι : Type} (D : LieSystemData3 ι (locQuot (conjClass3 K) z) (locFamily (conjClass3 K) z)),
        (∃ i j : ι, i ≠ j ∧ ¬ IsA1Comp3 D i ∧ ¬ IsA1Comp3 D j) →
          ∃ (i₁ i₂ : ι) (a₁ a₂ β : Subgroup G), i₁ ≠ i₂ ∧ ¬ IsA1Comp3 D i₁ ∧
            ¬ IsA1Comp3 D i₂ ∧ a₁ ∈ compMembers3 (conjClass3 K) z D i₁ ∧
            a₂ ∈ compMembers3 (conjClass3 K) z D i₂ ∧ β ∈ conjClass3 K ∧
            (∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) ∧
            (∃ W, LinearBlockStandardPair (GaloisField 3 1) W a₁ β) ∧
            (∃ W, LinearBlockStandardPair (GaloisField 3 1) W a₂ β)

theorem local_conj3 {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} (hc : LocCtx3 K z)
    {c : Subgroup G} (hcΩ : c ∈ conjClass3 K) {y : G} (hyc : IsClassicalMember3 c y) :
    LocalOddCentral (conjClass3 K) {y} ∧ LocalOddThreeFree3 (conjClass3 K) y := by
  obtain ⟨g, hg⟩ := single_class3 K c hcΩ
  have hcl : IsClassicalMember3 c (g * z * g⁻¹) := by
    rw [hg]
    exact hc.hz.conj g
  have hyeq : g * z * g⁻¹ = y := involution_unique3 hcl hyc
  rw [← hyeq]
  exact ⟨Gaps.localOddCentral_conj hc.hΩ.conjInvariant g z hc.hP1,
    localOddThreeFree3_conj hc.hΩ.conjInvariant g z hc.hO3⟩


end Main

end CFSG.ClassicalInvolution.Q3.Q3W
