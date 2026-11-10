module

public import CFSG.ClassicalInvolution.Q3.Generation
public import CFSG.ClassicalInvolution.Q3.LieDecomposition
public import CFSG.ClassicalInvolution.Balance.BootstrapClosure
public import CFSG.ClassicalInvolution.Balance.BootstrapTriple

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Defs

variable {G : Type} [Group G]

structure FrameSideTwo3 (Ω : Set (Subgroup G)) (A : Subgroup G) (S : Set (Subgroup G)) :
    Prop where
  elem : IsElemAbelian 2 A
  card : 8 ≤ Nat.card A
  subset : S ⊆ Ω
  nonempty : S.Nonempty
  involution : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember3 K z
  generation : ∀ a ∈ A, IsFrameInvolution3 S a → CentralizerGenerationModOTwo Ω A a
  link : ∀ a ∈ A, IsFrameInvolution3 S a → InvolutionLink3 Ω A S a

@[expose] def omegaStarTwo3 (Ω : Set (Subgroup G)) (A : Subgroup G) (S : Set (Subgroup G)) :
    Set (Subgroup G) :=
  {L | L ∈ Ω ∧ ∃ h ∈ rankTwoSpan A, ∃ K ∈ S, ∃ z ∈ A,
    IsClassicalMember3 K z ∧ IsClassicalMember3 L (h * z * h⁻¹)}

end Defs

section Closure

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}
  {S : Set (Subgroup G)}

theorem le_rankTwoSpan_of_mem_omegaStarTwo3 (hΩ : InClass3 Ω) (hF : FrameSideTwo3 Ω A S)
    {L : Subgroup G} (hLs : L ∈ omegaStarTwo3 Ω A S) : L ≤ rankTwoSpan A := by
  obtain ⟨hLΩ, h, hh, K, hK, a, haA, hKa, hLa⟩ := hLs
  have hconj := hΩ.conjInvariant
  have hLa' := isClassicalMember3_conj_inv hLa
  have hmem : conjSub h⁻¹ L ∈ centralizingMembers Ω {a} :=
    ⟨hconj _ _ hLΩ, isSubnormal_le hLa'.subnormal⟩
  have hY : conjSub h⁻¹ L ≤ rankTwoSpan A :=
    (le_centralizingLayer hmem).trans (centralizingLayer_le_rankTwoSpan hconj hF.elem hF.card haA
      (hF.generation a haA ⟨K, hK, hKa⟩))
  intro x hx
  have h1 : h⁻¹ * x * h ∈ conjSub h⁻¹ L := by
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using hx
  have h2 := hY h1
  have h3 : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
  rw [h3]
  exact mul_mem (mul_mem hh h2) (inv_mem hh)

theorem mem_omegaStarTwo3_of_commutes (hΩ : InClass3 Ω) (hF : FrameSideTwo3 Ω A S)
    {L L' : Subgroup G} (hLs : L ∈ omegaStarTwo3 Ω A S) (hL' : L' ∈ Ω) (hc : Commutes L L') :
    L' ∈ omegaStarTwo3 Ω A S := by
  obtain ⟨hLΩ, h₀, hh₀, K, hKS, a, haA, hKa, hLa⟩ := hLs
  have hconj := hΩ.conjInvariant
  have hLa' := isClassicalMember3_conj_inv hLa
  have hc' : Commutes (conjSub h₀⁻¹ L) (conjSub h₀⁻¹ L') := hc.conjSub h₀⁻¹
  set M := conjSub h₀⁻¹ L' with hM
  have hMΩ : M ∈ Ω := hconj _ _ hL'
  have hMa : M ≤ Subgroup.centralizer ({a} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc' a hLa'.mem x hx).symm
  have hMmem : M ∈ centralizingMembers Ω {a} := ⟨hMΩ, hMa⟩
  obtain ⟨z₀, hz₀⟩ := hΩ.classical M hMΩ
  obtain ⟨K', hK'S, z', hz'A, hK'z', h₁, hh₁Y, hz₀h₁⟩ :=
    hF.link a haA ⟨K, hKS, hKa⟩ M hMmem z₀ hz₀
  have hYH := centralizingLayer_le_rankTwoSpan hconj hF.elem hF.card haA
    (hF.generation a haA ⟨K, hKS, hKa⟩)
  have hz₀' : IsClassicalMember3 M (h₁ * z' * h₁⁻¹) := by rwa [← hz₀h₁]
  have hL'z : IsClassicalMember3 L' (h₀ * (h₁ * z' * h₁⁻¹) * h₀⁻¹) := by
    have := hz₀'.conj h₀
    rwa [hM, conjSub_conjSub_inv] at this
  refine ⟨hL', h₀ * h₁, mul_mem hh₀ (hYH hh₁Y), K', hK'S, z', hz'A, hK'z', ?_⟩
  have e : h₀ * h₁ * z' * (h₀ * h₁)⁻¹ = h₀ * (h₁ * z' * h₁⁻¹) * h₀⁻¹ := by group
  rwa [e]

theorem mem_omegaStarTwo3_of_omegaConnected (hΩ : InClass3 Ω) (hF : FrameSideTwo3 Ω A S)
    (hconn : OmegaConnected Ω) {L : Subgroup G} (hLΩ : L ∈ Ω) : L ∈ omegaStarTwo3 Ω A S := by
  obtain ⟨K₀, hK₀⟩ := hF.nonempty
  obtain ⟨z, hzA, hz⟩ := hF.involution K₀ hK₀
  have hK₀s : K₀ ∈ omegaStarTwo3 Ω A S :=
    ⟨hF.subset hK₀, 1, one_mem _, K₀, hK₀, z, hzA, hz, by simpa using hz⟩
  have key : ∀ L', Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Commutes M N) K₀ L' →
      L' ∈ omegaStarTwo3 Ω A S := by
    intro L' hpath
    induction hpath with
    | refl => exact hK₀s
    | tail _ hbc ih => exact mem_omegaStarTwo3_of_commutes hΩ hF ih hbc.1 hbc.2
  exact key L (hconn K₀ (hF.subset hK₀) L hLΩ)

theorem rankTwoSpan_eq_top3 (hΩ : InClass3 Ω) (hF : FrameSideTwo3 Ω A S)
    (hconn : OmegaConnected Ω) : rankTwoSpan A = ⊤ := by
  refine top_unique ?_
  rw [← hΩ.generated]
  exact iSup₂_le fun _ hLΩ => le_rankTwoSpan_of_mem_omegaStarTwo3 hΩ hF
    (mem_omegaStarTwo3_of_omegaConnected hΩ hF hconn hLΩ)

end Closure

section Family

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


end Family

section Link

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}
  {S : Set (Subgroup G)}

omit [Finite G] in
theorem range_inf_range_le_center3 {ι X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) {i j : ι} (h : i ≠ j) :
    (D.hom i).range ⊓ (D.hom j).range ≤ Subgroup.center X := by
  rintro x ⟨hxi, hxj⟩
  have key : ∀ k, (D.hom k).range ≤ Subgroup.centralizer ({x} : Set X) := by
    intro k y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨u, rfl⟩ := hy
    by_cases hki : k = i
    · subst hki
      obtain ⟨v, hv⟩ := hxj
      rw [← hv]
      exact D.commute k j h u v
    · obtain ⟨v, hv⟩ := hxi
      rw [← hv]
      exact D.commute k i hki u v
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ (⨆ k, (D.hom k).range : Subgroup X) := by rw [D.generate]; trivial
  exact Subgroup.mem_centralizer_singleton_iff.mp ((iSup_le key) hg)

omit [Finite G] in
theorem exists_conj_modOddIn_of_fund3 {a : G} {ι : Type}
    (D : LieSystemData3 ι (LocalQuot Ω a) (localFamily Ω a)) {M K : Subgroup G} {i : ι}
    {R R' : Subgroup (D.kind i).G}
    (hMR : modOddIn (centralizingLayer Ω {a}) M = R.map (D.hom i))
    (hKR' : modOddIn (centralizingLayer Ω {a}) K = R'.map (D.hom i)) (g : (D.kind i).G)
    (hg : R' = conjSub g R) :
    ∃ w ∈ centralizingLayer Ω {a}, modOddIn (centralizingLayer Ω {a}) K =
      modOddIn (centralizingLayer Ω {a}) (conjSub w M) := by
  set Y := centralizingLayer Ω {a} with hY
  obtain ⟨wT, hwT⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥Y) (D.hom i g)
  refine ⟨(wT : G), wT.2, ?_⟩
  calc modOddIn Y K = R'.map (D.hom i) := hKR'
    _ = (conjSub g R).map (D.hom i) := by rw [hg]
    _ = conjSub (D.hom i g) (R.map (D.hom i)) := (conjSub_map _ _ _).symm
    _ = conjSub (D.hom i g) (modOddIn Y M) := by rw [← hMR]
    _ = conjSub (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) wT) (modOddIn Y M) := by
        rw [hwT]
    _ = (conjSub wT (M.subgroupOf Y)).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) :=
        conjSub_map _ _ _
    _ = ((conjSub (wT : G) M).subgroupOf Y).map
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) := by
        rw [conjSub_subgroupOf]
    _ = modOddIn Y (conjSub (wT : G) M) := rfl

@[expose] def LieCovers3 (Ω : Set (Subgroup G)) (S : Set (Subgroup G)) (a : G) : Prop :=
  ∀ (ι : Type) (D : LieSystemData3 ι (LocalQuot Ω a) (localFamily Ω a)) (i : ι),
    ∃ K ∈ S, K ≤ Subgroup.centralizer ({a} : Set G) ∧
      modOddIn (centralizingLayer Ω {a}) K ≤ (D.hom i).range


end Link

end CFSG.ClassicalInvolution.Q3
