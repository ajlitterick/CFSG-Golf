module

public import CFSG.ClassicalInvolution.Balance.BootstrapAuditLink
public import CFSG.ClassicalInvolution.Balance.BootstrapSplit
import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure MemberFamily (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (A : Subgroup G) (𝒦 : Set (Subgroup G)) : Prop where
  elem : IsElemAbelian 2 A
  card : Nat.card A = 8
  subset : 𝒦 ⊆ Ω
  nonempty : 𝒦.Nonempty
  involution : ∀ K ∈ 𝒦, ∃ z ∈ A, IsClassicalMember p f K z ∧
    K ≤ Subgroup.centralizer (A : Set G)
  generate : A = Subgroup.closure {z | ∃ K ∈ 𝒦, IsClassicalMember p f K z}

namespace MemberFamily

variable {A : Subgroup G} {𝒦 : Set (Subgroup G)}

omit [Finite G] in
theorem mem_of_isClassicalMember (hM : MemberFamily p f Ω A 𝒦) {K : Subgroup G} {z : G}
    (hK : K ∈ 𝒦) (hz : IsClassicalMember p f K z) : z ∈ A :=
  hM.generate ▸ Subgroup.subset_closure ⟨K, hK, hz⟩

end MemberFamily

section Balance

variable {A : Subgroup G} {𝒦 : Set (Subgroup G)}

omit [Finite G] in
theorem oddQuotMk_centralizes_of_memberFamily (hM : MemberFamily p f Ω A 𝒦) {a : G} (ha : a ∈ A)
    {L : Subgroup (OddQuot a)} (hL : OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) {g : G} (hg : g ∈ A)
    (hgC : g ∈ Subgroup.centralizer ({a} : Set G)) (y : OddQuot a) (hy : y ∈ L) :
    oddQuotMk a ⟨g, hgC⟩ * y = y * oddQuotMk a ⟨g, hgC⟩ := by
  have hcom : ∀ {x y : G}, x ∈ A → y ∈ A → x * y = y * x := fun hx hy =>
    congrArg Subtype.val (hM.elem.1.is_comm.comm (⟨_, hx⟩ : A) ⟨_, hy⟩)
  have hcen : ∀ {K : Subgroup G}, K ≤ Subgroup.centralizer (A : Set G) →
      K ≤ Subgroup.centralizer ({a} : Set G) := fun hK =>
    hK.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hmem : ∀ {z : G}, z ∈ A → z ∈ Subgroup.centralizer ({a} : Set G) := fun hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcom hz ha)
  let Q : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    (Subgroup.centralizer ((L : Subgroup (OddQuot a)) : Set (OddQuot a))).comap (oddQuotMk a)
  have hsub : A ≤ Q.map (Subgroup.centralizer ({a} : Set G)).subtype := by
    have hAle : Subgroup.closure {z | ∃ K ∈ 𝒦, IsClassicalMember p f K z} ≤
        Q.map (Subgroup.centralizer ({a} : Set G)).subtype := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro z ⟨K, hK, hz⟩
      have hzA : z ∈ A := hM.mem_of_isClassicalMember hK hz
      refine ⟨⟨z, hmem hzA⟩, ?_, rfl⟩
      show oddQuotMk a _ ∈ Subgroup.centralizer ((L : Subgroup (OddQuot a)) : Set (OddQuot a))
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨-, -, -, hKA⟩ := hM.involution K hK
      exact (oddQuotMk_centralizes_of_isCentralInvolution (hM.subset hK) (hcen hKA)
        hz.isCentralInvolution (hmem hzA) hL y hy).symm
    rwa [← hM.generate] at hAle
  obtain ⟨q, hq, hqg⟩ := hsub hg
  have hqe : q = ⟨g, hgC⟩ := Subtype.ext hqg
  subst hqe
  exact (Subgroup.mem_centralizer_iff.mp hq y hy).symm

theorem exists_mem_ne_one_centralizes_of_memberFamily (hM : MemberFamily p f Ω A 𝒦) {a : G}
    (ha : a ∈ A) {F₀ : Subgroup G} (hF₀ : F₀ ≤ A) (h4 : Nat.card F₀ = 4)
    {L : Subgroup (OddQuot a)} (hL : OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) :
    ∃ g ∈ modOdd a F₀, g ≠ 1 ∧ ∀ y ∈ L, g * y = y * g := by
  obtain ⟨g, hgF, hg1⟩ := exists_ne_one_of_card_eq_two_pow (n := 2) (by norm_num) (by omega)
  have hgA : g ∈ A := hF₀ hgF
  have hgC : g ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hM.elem.1.is_comm.comm (⟨g, hgA⟩ : A) ⟨a, ha⟩))
  refine ⟨oddQuotMk a ⟨g, hgC⟩, oddQuotMk_mem_modOdd hgF hgC, ?_, fun y hy =>
    oddQuotMk_centralizes_of_memberFamily hM ha hL hgA hgC y hy⟩
  intro h
  have hsq : (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨g, hgC⟩ = 1 :=
    Subtype.ext (by rw [← pow_two]; exact hM.elem.2 g hgA)
  exact hg1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))

theorem twoBalancedWrt_of_memberFamily_of_layers (hM : MemberFamily p f Ω A 𝒦)
    (hloc : ∀ a ∈ A, a ≠ 1 → ComponentLayersAt Ω A a) : TwoBalancedWrt A := by
  have hA := hM.elem
  refine twoBalancedWrt_of_quotient_deltaCore_eq_bot hA.1 ?_
  intro a ha ha1 F₀ hF₀
  obtain ⟨hF₀E, hF₀card⟩ := hF₀
  have h4 : Nat.card F₀ = 4 := by rw [hF₀card]; norm_num
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hA.1.is_comm.comm (⟨g, hF₀E hg⟩ : A) ⟨a, ha⟩)
  have hF2 : ∀ g ∈ F₀, g * g = 1 := fun g hg => by
    rw [← pow_two]
    exact hA.2 g (hF₀E hg)
  have hF2bar : ∀ g ∈ modOdd a F₀, g * g = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ F₀ := hx
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (hF2 _ hx')
    rw [this, map_one]
  show deltaCore (modOdd a F₀) = ⊥
  refine deltaCore_eq_bot_of_oddCentralizerFree (pPrimeCore_oddQuot_eq_bot a)
    (by rw [card_modOdd_of_exponent_two hFC hF2, h4]) hF2bar ?_
  intro L hL hFn hfaith
  rcases hloc a ha ha1 L hL with h | h | hfree
  · obtain ⟨g, hg, hg1, hgc⟩ :=
      exists_mem_ne_one_centralizes_of_memberFamily hM ha hF₀E h4 (Or.inl h)
    exact absurd hgc (hfaith g hg hg1)
  · obtain ⟨g, hg, hg1, hgc⟩ :=
      exists_mem_ne_one_centralizes_of_memberFamily hM ha hF₀E h4 (Or.inr h)
    exact absurd hgc (hfaith g hg hg1)
  · exact hfree F₀ hF₀E h4 hFn hfaith

end Balance

section Stage2

variable {A : Subgroup G} {𝒦 : Set (Subgroup G)}

theorem weakBalanced_of_memberFamily [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) (hM : MemberFamily p f Ω A 𝒦) :
    WeakBalanced A :=
  weakBalanced_of_members hnab hp2 hq h0 hA1 hΩ hIH hM.elem hM.generate (by
    rintro z ⟨K, hK, hz⟩
    obtain ⟨-, -, -, hKA⟩ := hM.involution K hK
    exact ⟨K, hM.subset hK, hz, hKA⟩)

theorem generation_of_memberFamily_of_closure (hΩ : InClass p f Ω)
    (hM : MemberFamily p f Ω A 𝒦) (hconn : OmegaConnected Ω)
    (hgenModO : ∀ a ∈ A, IsFrameInvolution p f 𝒦 a → CentralizerGenerationModOTwo Ω A a)
    (hlink : ∀ a ∈ A, IsFrameInvolution p f 𝒦 a → InvolutionLink p f Ω A 𝒦 a) :
    (⨆ F ∈ signalizerFunctorEk 2 2 A, Subgroup.centralizer (F : Set G)) = ⊤ :=
  rankTwoSpan_eq_top hΩ
    { elem := hM.elem
      card := hM.card.ge
      subset := hM.subset
      nonempty := hM.nonempty
      involution := fun K hK => by
        obtain ⟨z, hzA, hz, -⟩ := hM.involution K hK
        exact ⟨z, hzA, hz⟩
      generation := hgenModO
      link := hlink } hconn


end Stage2

end CFSG.ClassicalInvolution.Balance.Bootstrap
