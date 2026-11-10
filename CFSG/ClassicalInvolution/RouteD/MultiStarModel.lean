module

public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectBridge
public import CFSG.ClassicalInvolution.RouteD.MultiD4
public import CFSG.ClassicalInvolution.RouteD.MultiStarWeak

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.NonClassical
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

section Chains

variable {X : Type*} [Group X]

@[expose] def CommFamilyConnected (F : Set (Subgroup X)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, Relation.ReflTransGen
    (fun U V : Subgroup X => U ∈ F ∧ V ∈ F ∧ Commutes U V) A B

@[expose] def LinkedIn (F : Set (Subgroup X)) (R : Subgroup X) : Subgroup X → Subgroup X → Prop :=
  Relation.ReflTransGen
    (fun U V : Subgroup X => U ∈ F ∧ V ∈ F ∧ Commutes U R ∧ Commutes V R ∧ ¬ Commutes U V)


theorem commFamilyConnected_of_stable {M : Type} [Group M] [Finite M] {F : Set (Subgroup M)}
    (hF : ∀ A ∈ F, ∀ g : M, conjSub g A ∈ F) (htrans : ∀ A ∈ F, ∀ B ∈ F, ∃ g : M, B = conjSub g A)
    {X : Set M} (hX : Subgroup.closure X = ⊤) {R₀ : Subgroup M} (hR₀ : R₀ ∈ F)
    (hx : ∀ x ∈ X, conjSub x R₀ = R₀ ∨ ∃ R' ∈ F, Commutes R₀ R' ∧ conjSub x R' = R') :
    CommFamilyConnected F := by
  let r : Subgroup M → Subgroup M → Prop := fun U V => U ∈ F ∧ V ∈ F ∧ Commutes U V
  let D : Set (Subgroup M) := {R | Relation.ReflTransGen r R₀ R}
  have hDF : ∀ R ∈ D, R ∈ F := by
    intro R hR
    have hR' : Relation.ReflTransGen r R₀ R := hR
    induction hR' with
    | refl => exact hR₀
    | tail _ hbc _ => exact hbc.2.1
  have hstab : ∀ x ∈ X, ∀ R ∈ D, conjSub x R ∈ D := by
    intro x hxX R hR
    have h0 : conjSub x R₀ ∈ D := by
      rcases hx x hxX with hfix | ⟨R', hR'F, hcomm, hnorm⟩
      · rw [hfix]
        exact Relation.ReflTransGen.refl
      · have h1 : Relation.ReflTransGen r R₀ R' :=
          Relation.ReflTransGen.single ⟨hR₀, hR'F, hcomm⟩
        have h2 : Commutes (conjSub x R₀) R' := by
          have := (commutes_conjSub_iff x).mpr hcomm
          rwa [hnorm] at this
        exact h1.tail ⟨hR'F, hF R₀ hR₀ x, Gaps.commutes_symm h2⟩
    have hR' : Relation.ReflTransGen r R₀ R := hR
    induction hR' with
    | refl => exact h0
    | @tail b c hb hbc ih =>
      have hbD : b ∈ D := hb
      exact (ih hbD).tail ⟨hF b (hDF b hbD) x, hF c hbc.2.1 x,
        (commutes_conjSub_iff x).mpr hbc.2.2⟩
  have hinv : ∀ g : M, (∀ R ∈ D, conjSub g R ∈ D) → ∀ R ∈ D, conjSub g⁻¹ R ∈ D := by
    intro g hg R hR
    have hbij := (Set.Finite.injOn_iff_bijOn_of_mapsTo (Set.toFinite D)
      (fun A hA => hg A hA)).mp (fun A _ B _ h => conjSub_injective g h)
    obtain ⟨R'', hR'', hR''eq⟩ := hbij.surjOn hR
    rw [← hR''eq, conjSub_inv_conjSub]
    exact hR''
  have hall : ∀ g : M, ∀ R ∈ D, conjSub g R ∈ D := by
    intro g R hR
    have hg : g ∈ Subgroup.closure X := by rw [hX]; exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction generalizing R with
    | mem x hxX => exact hstab x hxX R hR
    | one => rw [conjSub_one]; exact hR
    | mul a b _ _ ha hb =>
      rw [conjSub_mul]
      exact ha _ (hb R hR)
    | inv a _ ha =>
      exact hinv a (fun R' hR' => ha R' hR') R hR
  have hFD : ∀ B ∈ F, B ∈ D := by
    intro B hB
    obtain ⟨g, hg⟩ := htrans R₀ hR₀ B hB
    rw [hg]
    exact hall g R₀ Relation.ReflTransGen.refl
  intro A hA B hB
  have h1 : Relation.ReflTransGen r R₀ A := hFD A hA
  have h2 : Relation.ReflTransGen r R₀ B := hFD B hB
  have hsymm : ∀ {U V : Subgroup M}, Relation.ReflTransGen r U V → Relation.ReflTransGen r V U := by
    intro U V h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, Gaps.commutes_symm hbc.2.2⟩ ih
  exact (hsymm h1).trans h2

end Chains

section Lift

variable [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem members_chain_of_commConnected (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    {i : Fin D.card}
    (hsc : FundamentalSingleClass (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    (hperf : Gaps.FundPerfect (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    (hcc : CommFamilyConnected (Gaps.compFund D i)) :
    ∀ A ∈ Gaps.compMembers Ω x D i, ∀ B ∈ Gaps.compMembers Ω x D i, Relation.ReflTransGen
      (fun U V : Subgroup G => U ∈ Gaps.compMembers Ω x D i ∧ V ∈ Gaps.compMembers Ω x D i ∧
        Commutes U V) A B := by
  intro A hA B hB
  obtain ⟨R_A, hRA⟩ := Gaps.exists_corr_left hΩ hex D hA
  obtain ⟨R_B, hRB⟩ := Gaps.exists_corr_left hΩ hex D hB
  have key : ∀ X, Relation.ReflTransGen
      (fun U V : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K =>
        U ∈ Gaps.compFund D i ∧ V ∈ Gaps.compFund D i ∧ Commutes U V) R_A X →
      ∃ N, Gaps.Corr Ω x D i N X ∧ Relation.ReflTransGen
        (fun U V : Subgroup G => U ∈ Gaps.compMembers Ω x D i ∧
          V ∈ Gaps.compMembers Ω x D i ∧ Commutes U V) A N := by
    intro X hX
    induction hX with
    | refl => exact ⟨A, hRA, Relation.ReflTransGen.refl⟩
    | @tail U V _ huv ih =>
      obtain ⟨N, hN, hlink⟩ := ih
      obtain ⟨N', hN'⟩ := Gaps.exists_corr_right hΩ D hsc huv.2.1
      have hNm : N ∈ Gaps.compMembers Ω x D i := ⟨hN.1, hN.2.2 ▸ Subgroup.map_le_range _ _⟩
      have hN'm : N' ∈ Gaps.compMembers Ω x D i := ⟨hN'.1, hN'.2.2 ▸ Subgroup.map_le_range _ _⟩
      exact ⟨N', hN', hlink.tail ⟨hNm, hN'm,
        (Gaps.corr_commutes hΩ hP1 hperf hN hN').mpr huv.2.2⟩⟩
  obtain ⟨N, hN, hlink⟩ := key R_B (hcc R_A hRA.2.1 R_B hRB.2.1)
  have : N = B := Gaps.corr_unique_right hΩ hP1 hN hRB
  rwa [this] at hlink

theorem linked_of_linkedIn (hΩ : InClass p f Ω) (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {i : Fin D.card}
    (hsc : FundamentalSingleClass (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    (hperf : Gaps.FundPerfect (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    {K N N' : Subgroup G} {R_K R_N R_N' : Subgroup
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K} {z : G} (hz : z ∈ K)
    (hK : Gaps.Corr Ω x D i K R_K) (hN : Gaps.Corr Ω x D i N R_N)
    (hN' : Gaps.Corr Ω x D i N' R_N') (hlink : LinkedIn (Gaps.compFund D i) R_K R_N R_N') :
    Linked Ω z N N' := by
  have key : ∀ X, LinkedIn (Gaps.compFund D i) R_K R_N X →
      ∃ M, Gaps.Corr Ω x D i M X ∧ Linked Ω z N M := by
    intro X hX
    induction hX with
    | refl => exact ⟨N, hN, Relation.ReflTransGen.refl⟩
    | @tail U V _ huv ih =>
      obtain ⟨M, hM, hlinkM⟩ := ih
      obtain ⟨M', hM'⟩ := Gaps.exists_corr_right hΩ D hsc huv.2.1
      have hMK : Commutes M K := (Gaps.corr_commutes hΩ hP1 hperf hM hK).mpr huv.2.2.1
      have hM'K : Commutes M' K := (Gaps.corr_commutes hΩ hP1 hperf hM' hK).mpr huv.2.2.2.1
      have hMz : M ∈ centralizingMembers Ω {z} :=
        mem_centralizingMembers_of_commutes hM.1.1 hz hMK
      have hM'z : M' ∈ centralizingMembers Ω {z} :=
        mem_centralizingMembers_of_commutes hM'.1.1 hz hM'K
      have hnc : ¬ Commutes M M' := fun hc =>
        huv.2.2.2.2 ((Gaps.corr_commutes hΩ hP1 hperf hM hM').mp hc)
      exact ⟨M', hM', hlinkM.trans (Linked.single ⟨hMz, hM'z, hnc⟩)⟩
  obtain ⟨M, hM, hlinkM⟩ := key R_N' hlink
  have : M = N' := Gaps.corr_unique_right hΩ hP1 hM hN'
  rwa [this] at hlinkM

end Lift


section Nbhd

theorem exists_nc_pair_of_block {Ω : Set (Subgroup G)} {y : G} {A : Subgroup G}
    (h : ∃ B ∈ ncBlock Ω y A, B ≠ A) :
    ∃ b₁ ∈ ncBlock Ω y A, ∃ b₂ ∈ ncBlock Ω y A, b₁ ≠ b₂ ∧ ¬ Commutes b₁ b₂ := by
  obtain ⟨B, hB, hne⟩ := h
  have hB' : Linked Ω y A B := hB
  have key : ∀ C, Linked Ω y A C → C = A ∨ ∃ b₁ b₂, Linked Ω y A b₁ ∧ Linked Ω y A b₂ ∧
      b₁ ≠ b₂ ∧ ¬ Commutes b₁ b₂ := by
    intro C hC
    induction hC with
    | refl => exact Or.inl rfl
    | @tail b c hab hbc ih =>
      by_cases hbc' : b = c
      · subst hbc'
        exact ih
      · exact Or.inr ⟨b, c, hab, hab.tail hbc, hbc', hbc.2.2⟩
  rcases key B hB' with h | ⟨b₁, b₂, h₁, h₂, hne', hnc⟩
  · exact (hne h).elim
  · exact ⟨b₁, h₁, b₂, h₂, hne', hnc⟩

end Nbhd


section MaxBlock

variable [Finite G] [IsSimpleGroup G]


end MaxBlock


section Reduction

abbrev ModelFund (p : ℕ) [Fact p.Prime] (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ) :
    Set (Subgroup (modelUniv t n p e Fact.out).K) :=
  fundamentalSubgroups t (modelUniv t n p e Fact.out).D


@[expose] def ModelStarFact (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ), IsFundTag t →
    StatedLieAdmissible t n p e → p ≠ 2 → 5 ≤ p ^ e → t ≠ .G2 → t ≠ .trialityD4 →
    ∀ R ∈ ModelFund p t n e, ∀ R₁ ∈ ModelFund p t n e, ∀ R₂ ∈ ModelFund p t n e,
      ∀ R_q ∈ ModelFund p t n e, Commutes R R₁ → Commutes R R₂ → Commutes R₁ R₂ →
      ¬ LinkedIn (ModelFund p t n e) R R₁ R₂ → ¬ Commutes R_q R → ¬ Commutes R_q R₁ →
      ¬ Commutes R_q R₂ →
        ∃ R_β ∈ ModelFund p t n e, ∃ R₁' ∈ ModelFund p t n e, ∃ R₂' ∈ ModelFund p t n e,
          LinkedIn (ModelFund p t n e) R R₁ R₁' ∧ LinkedIn (ModelFund p t n e) R R₂ R₂' ∧
          (∃ W, LinearBlockStandardPair (GaloisField p e) W R R_β) ∧
          (∃ W, LinearBlockStandardPair (GaloisField p e) W R₁' R_β) ∧
          (∃ W, LinearBlockStandardPair (GaloisField p e) W R₂' R_β)

@[expose] def NoG2D4 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      ∀ (L : Subgroup G) (w : G), L ∈ conjClass K → IsClassicalMember p f L w →
        ∀ D : LieSystemData p f (locQuot (conjClass K) w) (locFamily (conjClass K) w),
          ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4

theorem linearBlockStandardPair_congr_field {X : Type} [Group X] {e e' : ℕ} (hee : e = e')
    {W U V : Subgroup X} (h : LinearBlockStandardPair (GaloisField p e) W U V) :
    LinearBlockStandardPair (GaloisField p e') W U V := by
  subst hee
  exact h


end Reduction

end CFSG.ClassicalInvolution.RouteD
