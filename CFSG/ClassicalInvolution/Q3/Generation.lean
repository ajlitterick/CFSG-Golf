module

public import CFSG.ClassicalInvolution.Q3.Induction
public import CFSG.ClassicalInvolution.Q3.Frame
public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureFrame

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.ClassicalInvolution.Balance (oddCoreIn odd_card_oddCoreIn oddCoreIn_le conj_mem_oddCoreIn
  FusionGenerated)
open scoped MatrixGroups

section Members

variable {Y : Type} [Group Y]

theorem IsClassicalMember3.exists_chart {L : Subgroup Y} {z : Y} (h : IsClassicalMember3 L z) :
    ∃ φ : ↥L →* SL(2, ZMod 3), IsChart3 L φ := by
  obtain ⟨e⟩ := h.nonempty_equiv
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore ↥L)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem involution_unique3 [Finite Y] {L : Subgroup Y} {z z' : Y} (h : IsClassicalMember3 L z)
    (h' : IsClassicalMember3 L z') : z = z' := by
  obtain ⟨φ, hφ⟩ := h.exists_chart
  exact hφ.eq_of_central h.isCentralInvolution h'.isCentralInvolution

theorem mul_mem_oddCoreIn_of_modOddIn_eq3 [Finite Y] {X K K' : Subgroup Y} {z z' : Y}
    (hK : IsClassicalMember3 K z) (hK' : IsClassicalMember3 K' z') (hKX : K ≤ X) (hK'X : K' ≤ X)
    (h : modOddIn X K = modOddIn X K') : z * z' ∈ oddCoreIn X := by
  have h1 := (hK.subgroupOf hKX).map_oddQuotient
  have h2 := (hK'.subgroupOf hK'X).map_oddQuotient
  unfold modOddIn at h
  rw [← h] at h2
  have h3 := involution_unique3 h1 h2
  have h4 := QuotientGroup.eq.mp h3
  refine ⟨_, h4, ?_⟩
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right hK.isCentralInvolution.sq
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hz]

end Members

section Defs

variable {G : Type} [Group G]

@[expose] def CompData.SingleClass (c : CompData) : Prop :=
  ∀ R ∈ c.fund, ∀ R' ∈ c.fund, ∃ g : c.G, R' = conjSub g R

@[expose] def SingleClassComponents3 {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) : Prop :=
  ∀ i, (D.kind i).SingleClass

structure LocalHypotheses3 (Ω : Set (Subgroup G)) (A : Subgroup G) : Prop where
  inClass : InClass3 Ω
  noncentral : ∀ a ∈ A, a ≠ 1 → a ∉ Subgroup.center G
  lie : LocalLieSystems3 Ω
  single : ∀ a ∈ A, a ≠ 1 → ∀ (ι : Type) (D : LieSystemData3 ι (LocalQuot Ω a) (localFamily Ω a)),
    SingleClassComponents3 D

@[expose] def IsFrameInvolution3 (S : Set (Subgroup G)) (a : G) : Prop :=
  ∃ K ∈ S, IsClassicalMember3 K a

@[expose] def InvolutionLink3 (Ω : Set (Subgroup G)) (A : Subgroup G) (S : Set (Subgroup G))
    (a : G) : Prop :=
  ∀ M ∈ centralizingMembers Ω {a}, ∀ z : G, IsClassicalMember3 M z →
    ∃ K ∈ S, ∃ z' ∈ A, IsClassicalMember3 K z' ∧
      ∃ h ∈ centralizingLayer Ω {a}, z = h * z' * h⁻¹

structure FrameSide3 (Ω : Set (Subgroup G)) (A : Subgroup G) (S : Set (Subgroup G)) : Prop where
  elem : IsElemAbelian 2 A
  card : 16 ≤ Nat.card A
  subset : S ⊆ Ω
  nonempty : S.Nonempty
  involution : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember3 K z
  generation : ∀ a ∈ A, IsFrameInvolution3 S a → CentralizerGenerationModO Ω A a
  link : ∀ a ∈ A, IsFrameInvolution3 S a → InvolutionLink3 Ω A S a


end Defs

section Link

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}
  {S : Set (Subgroup G)}

omit [Finite G] in
theorem exists_conj_modOddIn3 {a : G} {ι : Type}
    (D : LieSystemData3 ι (LocalQuot Ω a) (localFamily Ω a)) (hD : SingleClassComponents3 D)
    {M K : Subgroup G} (hM : M ∈ centralizingMembers Ω {a}) (hK : K ∈ centralizingMembers Ω {a})
    (hnc : ∃ x ∈ M, ∃ y ∈ K, x * y * x⁻¹ * y⁻¹ ∉ oddCoreIn (centralizingLayer Ω {a})) :
    ∃ w ∈ centralizingLayer Ω {a}, modOddIn (centralizingLayer Ω {a}) K =
      modOddIn (centralizingLayer Ω {a}) (conjSub w M) := by
  set Y := centralizingLayer Ω {a} with hY
  have hMY : M ≤ Y := le_centralizingLayer hM
  have hKY : K ≤ Y := le_centralizingLayer hK
  have hMfam : modOddIn Y M ∈ localFamily Ω a := ⟨M.subgroupOf Y, ⟨M, hM, hMY, rfl⟩, rfl⟩
  have hKfam : modOddIn Y K ∈ localFamily Ω a := ⟨K.subgroupOf Y, ⟨K, hK, hKY, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := D.fundamental _ hMfam
  obtain ⟨j, R', hR', hKR'⟩ := D.fundamental _ hKfam
  have hij : i = j := by
    by_contra hne
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    have hxY : x ∈ Y := hMY hx
    have hyY : y ∈ Y := hKY hy
    have hx' : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨x, hxY⟩ ∈ modOddIn Y M :=
      ⟨⟨x, hxY⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hy' : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨y, hyY⟩ ∈ modOddIn Y K :=
      ⟨⟨y, hyY⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    rw [hMR] at hx'
    rw [hKR'] at hy'
    obtain ⟨r, -, hr⟩ := hx'
    obtain ⟨r', -, hr'⟩ := hy'
    have hcomm := D.commute i j hne r r'
    rw [hr, hr'] at hcomm
    exact hxy ((mk_comm_eq_iff hxY hyY).mp hcomm)
  subst hij
  obtain ⟨g, hg⟩ := hD i R hR R' hR'
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

theorem involutionLink_of_lie3 (hL : LocalHypotheses3 Ω A) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1)
    (hS : S ⊆ Ω) (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember3 K z)
    (hcover : FrameCoversModO Ω S a) : InvolutionLink3 Ω A S a := by
  intro M hMmem z hz
  have hΩ := hL.inClass.conjInvariant
  obtain ⟨K', hK'S, hK'a, hnc⟩ := hcover M hMmem
  have hK'mem : K' ∈ centralizingMembers Ω {a} := ⟨hS hK'S, hK'a⟩
  obtain ⟨ι, -, ⟨D⟩⟩ := hL.lie {a} (fun h => hL.noncentral a haA ha1 (h rfl))
  obtain ⟨w, hwY, hmod⟩ := exists_conj_modOddIn3 D (hL.single a haA ha1 ι D) hMmem hK'mem hnc
  obtain ⟨z', hz'A, hK'z'⟩ := hinv K' hK'S
  have hK'' : IsClassicalMember3 (conjSub w M) (w * z * w⁻¹) := hz.conj w
  have hwC : w ∈ Subgroup.centralizer ({a} : Set G) := centralizingLayer_le_centralizer Ω {a} hwY
  have hK''Y : conjSub w M ≤ centralizingLayer Ω {a} :=
    le_centralizingLayer (conjSub_mem_centralizingMembers hΩ hwC hMmem)
  have hU := mul_mem_oddCoreIn_of_modOddIn_eq3 hK'z' hK'' (le_centralizingLayer hK'mem)
    hK''Y hmod
  obtain ⟨o, ho, hoz⟩ := exists_conj_of_mul_mem hK''.isCentralInvolution.sq
    hK'z'.isCentralInvolution.sq (odd_card_oddCoreIn _) hU
  have hoY : o ∈ centralizingLayer Ω {a} := oddCoreIn_le _ ho
  refine ⟨K', hK'S, z', hz'A, hK'z', w⁻¹ * o⁻¹, mul_mem (inv_mem hwY) (inv_mem hoY), ?_⟩
  rw [hoz]
  group

theorem FrameSide3.of_cover (hL : LocalHypotheses3 Ω A) (hA : IsElemAbelian 2 A)
    (h16 : 16 ≤ Nat.card A) (hS : S ⊆ Ω) (hne : S.Nonempty)
    (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember3 K z)
    (hgen : ∀ a ∈ A, IsFrameInvolution3 S a → CentralizerGenerationModO Ω A a)
    (hcover : ∀ a ∈ A, IsFrameInvolution3 S a → FrameCoversModO Ω S a) :
    FrameSide3 Ω A S where
  elem := hA
  card := h16
  subset := hS
  nonempty := hne
  involution := hinv
  generation := hgen
  link := fun a ha hfa => by
    obtain ⟨K, hKS, hK⟩ := hfa
    exact involutionLink_of_lie3 hL ha hK.ne_one hS hinv (hcover a ha ⟨K, hKS, hK⟩)

end Link

section Step

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}
  {S : Set (Subgroup G)}

omit [Finite G] in
theorem isClassicalMember3_conj_inv {L : Subgroup G} {z h : G}
    (hL : IsClassicalMember3 L (h * z * h⁻¹)) : IsClassicalMember3 (conjSub h⁻¹ L) z := by
  have := hL.conj h⁻¹
  have e : h⁻¹ * (h * z * h⁻¹) * h⁻¹⁻¹ = z := by group
  rwa [e] at this


end Step

section Frame


end Frame

section Weak


end Weak

end CFSG.ClassicalInvolution.Q3
