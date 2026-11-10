module

public import CFSG.ClassicalInvolution.Reduction
public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentInteraction
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open

section OmegaAt

variable {G : Type*} [Group G]

@[expose] def omegaAt (J : Subgroup G) (z a : G) : Set (Subgroup G) :=
  {A | ∃ g : G, A = J.map (MulAut.conj g⁻¹).toMonoidHom ∧ g⁻¹ * z * g = a}


private theorem map_conj_one (J : Subgroup G) : J.map (MulAut.conj 1).toMonoidHom = J :=
  map_conj_eq_iff_mem_normalizer.mpr (Subgroup.one_mem _)

private theorem map_map_conj_eq (J : Subgroup G) (a b : G) :
    (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      J.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  show b * (a * x * a⁻¹) * b⁻¹ = b * a * x * (b * a)⁻¹
  group


theorem self_mem_omegaAt (J : Subgroup G) (z : G) : J ∈ omegaAt J z z :=
  ⟨1, by rw [inv_one, map_conj_one], by rw [inv_one, one_mul, mul_one]⟩

theorem omegaAt_eq_orbit {J : Subgroup G} {z a : G} {A₀ : Subgroup G} (hA₀ : A₀ ∈ omegaAt J z a) :
    omegaAt J z a =
      {A | ∃ c ∈ Subgroup.centralizer ({a} : Set G), A = A₀.map (MulAut.conj c).toMonoidHom} := by
  obtain ⟨g₀, rfl, hg₀⟩ := hA₀
  ext A
  constructor
  · rintro ⟨g, rfl, hg⟩
    refine ⟨g⁻¹ * g₀, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have e1 : g⁻¹ * g₀ * h = g⁻¹ * z * g₀ := by rw [← hg₀]; group
      have e2 : h * (g⁻¹ * g₀) = g⁻¹ * z * g₀ := by rw [← hg]; group
      exact e2.trans e1.symm
    · rw [map_map_conj_eq, mul_inv_cancel_right]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨g₀ * c⁻¹, ?_, ?_⟩
    · rw [map_map_conj_eq, mul_inv_rev, inv_inv]
    · have hca : a * c = c * a := Subgroup.mem_centralizer_iff.mp hc a rfl
      calc (g₀ * c⁻¹)⁻¹ * z * (g₀ * c⁻¹) = c * (g₀⁻¹ * z * g₀) * c⁻¹ := by group
        _ = c * a * c⁻¹ := by rw [hg₀]
        _ = a := by rw [← hca]; group


theorem omegaAt_self_eq_map_conj (J : Subgroup G) (z : G) :
    omegaAt J z z =
      {A | ∃ c ∈ Subgroup.centralizer ({z} : Set G), A = J.map (MulAut.conj c).toMonoidHom} :=
  omegaAt_eq_orbit (self_mem_omegaAt J z)

theorem map_conj_mem_omegaAt_self {J : Subgroup G} {z c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    J.map (MulAut.conj c).toMonoidHom ∈ omegaAt J z z := by
  rw [omegaAt_self_eq_map_conj]
  exact ⟨c, hc, rfl⟩

theorem mem_of_mem_omegaAt {J : Subgroup G} {z a : G} (hzJ : z ∈ J) {A : Subgroup G}
    (hA : A ∈ omegaAt J z a) : a ∈ A := by
  obtain ⟨g, rfl, rfl⟩ := hA
  refine mem_map_conj_iff.mpr ?_
  have h : (g⁻¹)⁻¹ * (g⁻¹ * z * g) * g⁻¹ = z := by group
  rw [h]
  exact hzJ

theorem le_centralizer_of_mem_omegaAt {J : Subgroup G} {z a : G}
    (hJ : J ≤ Subgroup.centralizer ({z} : Set G)) {A : Subgroup G} (hA : A ∈ omegaAt J z a) :
    A ≤ Subgroup.centralizer ({a} : Set G) := by
  obtain ⟨g, rfl, rfl⟩ := hA
  have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hJ
  rwa [map_conj_centralizer_singleton, inv_inv] at this


end OmegaAt

section Involutions

variable {G : Type*} [Group G] {J : Subgroup G} {z : G}


end Involutions

section Subnormal

variable {G : Type*} [Group G] {J : Subgroup G} {z : G}


end Subnormal

section TightlyEmbedded

variable {G : Type*} [Group G] {J : Subgroup G} {z : G}


variable [Finite G]


end TightlyEmbedded

section Hypotheses

variable {G : Type*} [Group G] [Finite G] {J : Subgroup G} {z : G}


end Hypotheses

section Twins

open CFSG.ComponentClassification

variable {G : Type*} [Group G]

private theorem isSubnormal_subgroupOf_top {J X : Subgroup G} (h : IsSubnormal J X) :
    IsSubnormal (J.subgroupOf X) ⊤ := by
  have key : ∀ {H K : Subgroup G}, IsSubnormal H K →
      IsSubnormal (H.subgroupOf X) (K.subgroupOf X) := by
    intro H K h
    induction h with
    | refl => exact IsSubnormal.refl _
    | @step H M K hHM hN _ ih =>
      have hle : H.subgroupOf X ≤ M.subgroupOf X := fun x hx => hHM hx
      refine IsSubnormal.step hle ?_ ih
      rw [Subgroup.normal_subgroupOf_iff hle]
      intro x y hx hy
      exact (Subgroup.normal_subgroupOf_iff hHM).mp hN x y hx hy
  simpa using key h

private theorem isQuasisimple_map_conj {J : Subgroup G} (hJ : IsQuasisimple J) (g : G) :
    IsQuasisimple (J.map (MulAut.conj g).toMonoidHom) :=
  Components.quasisimple_of_equiv
    (J.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm hJ

private theorem subgroupOf_ne_of_ne {X A B : Subgroup G} (hAX : A ≤ X) (hBX : B ≤ X)
    (hne : A ≠ B) : A.subgroupOf X ≠ B.subgroupOf X := fun h => hne (by
  have := congrArg (Subgroup.map X.subtype) h
  simpa only [Subgroup.map_subgroupOf_eq_of_le hAX, Subgroup.map_subgroupOf_eq_of_le hBX] using
    this)

theorem commute_of_isSubnormal_of_isQuasisimple [Finite G] {X A B : Subgroup G}
    (hA : IsSubnormal A X) (hB : IsSubnormal B X) (hAq : IsQuasisimple A)
    (hBq : IsQuasisimple B) (hne : A ≠ B) : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := by
  have hAX := isSubnormal_le hA
  have hBX := isSubnormal_le hB
  have hcomp : ∀ {C : Subgroup G}, C ≤ X → IsSubnormal C X → IsQuasisimple C →
      IsComponentOf (C.subgroupOf X) ⊤ := fun hCX hC hq =>
    ⟨le_top, isSubnormal_subgroupOf_top hC,
      Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hCX) hq⟩
  have hcomm := LocalComponents.commute_of_ne (A.subgroupOf X) (B.subgroupOf X)
    (hcomp hAX hA hAq) (hcomp hBX hB hBq) (subgroupOf_ne_of_ne hAX hBX hne)
  intro x hx y hy
  have hx' : (⟨x, hAX hx⟩ : X) ∈ A.subgroupOf X := hx
  have := Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx') (⟨y, hBX hy⟩ : X) hy
  exact (congrArg Subtype.val this).symm


variable {J : Subgroup G} {z : G}


end Twins

section TwoComponentTwins

open CFSG.ComponentClassification

variable {G : Type*} [Group G] [Finite G]

theorem isTwoComponent_subgroupOf_map_iff {G' : Type*} [Group G'] [Finite G'] (φ : G ≃* G')
    (X A : Subgroup G) :
    TwoComponents.IsTwoComponent ((A.map φ.toMonoidHom).subgroupOf (X.map φ.toMonoidHom)) ↔
      TwoComponents.IsTwoComponent (A.subgroupOf X) := by
  rw [← TwoComponentTransport.equiv_iff (φ.subgroupMap X) (A.subgroupOf X)]
  have hmap : (A.subgroupOf X).map (φ.subgroupMap X).toMonoidHom =
      (A.map φ.toMonoidHom).subgroupOf (X.map φ.toMonoidHom) := by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨⟨x, hxX⟩, hxA, hxy⟩
      exact ⟨x, hxA, congrArg Subtype.val hxy⟩
    · rintro ⟨a, haA, rfl⟩
      obtain ⟨x, hxX, hx⟩ := hy
      obtain rfl := φ.injective hx
      exact ⟨⟨x, hxX⟩, haA, rfl⟩
  rw [hmap]
  exact Iff.rfl

variable {J : Subgroup G} {z : G}

theorem isTwoComponent_of_mem_omegaAt
    (hJ : TwoComponents.IsTwoComponent (J.subgroupOf (Subgroup.centralizer ({z} : Set G))))
    {A : Subgroup G} {a : G} (hA : A ∈ omegaAt J z a) :
    TwoComponents.IsTwoComponent (A.subgroupOf (Subgroup.centralizer ({a} : Set G))) := by
  obtain ⟨g, rfl, rfl⟩ := hA
  have h := (isTwoComponent_subgroupOf_map_iff (MulAut.conj g⁻¹)
    (Subgroup.centralizer ({z} : Set G)) J).mpr hJ
  rwa [map_conj_centralizer_singleton, inv_inv] at h

omit [Finite G] in
private theorem map_oddCore_subgroupOf {X A : Subgroup G} (hAX : A ≤ X) :
    ((componentClassificationOddCore (A.subgroupOf X)).map (A.subgroupOf X).subtype).map
        X.subtype = (classicalInvolutionOddCore A).map A.subtype := by
  rw [show classicalInvolutionOddCore A = componentClassificationOddCore A from rfl,
    ← OddCore.equiv_invariant (Subgroup.subgroupOfEquivOfLe hAX), Subgroup.map_map,
    Subgroup.map_map]
  rfl

theorem twoComponents_interaction {X A B : Subgroup G} (hAX : A ≤ X) (hBX : B ≤ X)
    (hA : TwoComponents.IsTwoComponent (A.subgroupOf X))
    (hB : TwoComponents.IsTwoComponent (B.subgroupOf X)) (hne : A ≠ B) :
    B ≤ Subgroup.normalizer (A : Set G) ∧ A ≤ Subgroup.normalizer (B : Set G) ∧
      ⁅A, B⁆ ≤ (classicalInvolutionOddCore A).map A.subtype ⊓
        (classicalInvolutionOddCore B).map B.subtype ∧
      ⁅A, B⁆ ≤ (classicalInvolutionOddCore X).map X.subtype := by
  obtain ⟨h1, h2, h3⟩ := TwoComponentInteraction.mutual_normalization_core_commutation _ _ hA hB
    (subgroupOf_ne_of_ne hAX hBX hne)
  have hmap : ⁅A, B⁆ = (⁅A.subgroupOf X, B.subgroupOf X⁆).map X.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hAX,
      Subgroup.map_subgroupOf_eq_of_le hBX]
  have hcore : ((componentClassificationOddCore (A.subgroupOf X)).map
      (A.subgroupOf X).subtype).map X.subtype ≤ (classicalInvolutionOddCore X).map X.subtype := by
    refine Subgroup.map_mono ?_
    rw [OddCore.subnormal_intersection _ hA.1, Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (Subgroup.map_mono (f := X.subtype) h1).trans
      (Subgroup.le_normalizer_map (H := A.subgroupOf X) X.subtype)
    rwa [Subgroup.map_subgroupOf_eq_of_le hBX, Subgroup.map_subgroupOf_eq_of_le hAX] at this
  · have := (Subgroup.map_mono (f := X.subtype) h2).trans
      (Subgroup.le_normalizer_map (H := B.subgroupOf X) X.subtype)
    rwa [Subgroup.map_subgroupOf_eq_of_le hAX, Subgroup.map_subgroupOf_eq_of_le hBX] at this
  · rw [hmap, ← map_oddCore_subgroupOf hAX, ← map_oddCore_subgroupOf hBX]
    exact (Subgroup.map_mono h3).trans (Subgroup.map_inf_le _ _ _)
  · rw [hmap]
    exact (Subgroup.map_mono (h3.trans inf_le_left)).trans hcore

theorem twins_of_isTwoComponent (hJle : J ≤ Subgroup.centralizer ({z} : Set G))
    (hJ : TwoComponents.IsTwoComponent (J.subgroupOf (Subgroup.centralizer ({z} : Set G))))
    {A B : Subgroup G} {a : G} (hA : A ∈ omegaAt J z a) (hB : B ∈ omegaAt J z a) (hne : A ≠ B) :
    B ≤ Subgroup.normalizer (A : Set G) ∧ A ≤ Subgroup.normalizer (B : Set G) ∧
      ⁅A, B⁆ ≤ (classicalInvolutionOddCore A).map A.subtype ⊓
        (classicalInvolutionOddCore B).map B.subtype ∧
      ⁅A, B⁆ ≤ (classicalInvolutionOddCore (Subgroup.centralizer ({a} : Set G))).map
        (Subgroup.centralizer ({a} : Set G)).subtype :=
  twoComponents_interaction (le_centralizer_of_mem_omegaAt hJle hA)
    (le_centralizer_of_mem_omegaAt hJle hB) (isTwoComponent_of_mem_omegaAt hJ hA)
    (isTwoComponent_of_mem_omegaAt hJ hB) hne

theorem twins_self_of_isTwoComponent (hJle : J ≤ Subgroup.centralizer ({z} : Set G))
    (hJ : TwoComponents.IsTwoComponent (J.subgroupOf (Subgroup.centralizer ({z} : Set G))))
    {A : Subgroup G} (hA : A ∈ omegaAt J z z) (hne : A ≠ J) :
    A ≤ Subgroup.normalizer (J : Set G) ∧ J ≤ Subgroup.normalizer (A : Set G) ∧
      ⁅J, A⁆ ≤ (classicalInvolutionOddCore J).map J.subtype ⊓
        (classicalInvolutionOddCore A).map A.subtype ∧
      ⁅J, A⁆ ≤ (classicalInvolutionOddCore (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype :=
  twins_of_isTwoComponent hJle hJ (self_mem_omegaAt J z) hA hne.symm

theorem isTwoComponent_subgroupOf_of_perfect {J X : Subgroup G} (hJX : IsSubnormal J X)
    (hperf : commutator J = ⊤) (hq : IsQuasisimple (J ⧸ classicalInvolutionOddCore J)) :
    TwoComponents.IsTwoComponent (J.subgroupOf X) := by
  refine (TwoComponentTransport.subgroupOf_iff J X (isSubnormal_le hJX)).mpr ⟨?_, ?_, hq⟩
  · exact Components.mathlib_subnormal_of_chain (isSubnormal_subgroupOf_top hJX)
      Subgroup.IsSubnormal.top
  · have : Group.IsPerfect J := ⟨hperf⟩
    have : (TwoResidual.subgroup J).Characteristic := TwoResidual.characteristic J
    have hodd : Odd (Nat.card (J ⧸ TwoResidual.subgroup J)) := by
      rw [← Subgroup.index_eq_card]
      exact TwoResidual.odd_index J
    have : Group.IsSolvable (J ⧸ TwoResidual.subgroup J) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    by_contra hne
    have : Nontrivial (J ⧸ TwoResidual.subgroup J) :=
      not_subsingleton_iff_nontrivial.mp fun h => hne (QuotientGroup.subsingleton_iff.mp h)
    exact Group.IsPerfect.not_isSolvable (J ⧸ TwoResidual.subgroup J) inferInstance

theorem twins_of_perfect (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (hperf : commutator J = ⊤) (hq : IsQuasisimple (J ⧸ classicalInvolutionOddCore J))
    {A B : Subgroup G} {a : G} (hA : A ∈ omegaAt J z a) (hB : B ∈ omegaAt J z a) (hne : A ≠ B) :
    B ≤ Subgroup.normalizer (A : Set G) ∧ A ≤ Subgroup.normalizer (B : Set G) ∧
      ⁅A, B⁆ ≤ (classicalInvolutionOddCore A).map A.subtype ⊓
        (classicalInvolutionOddCore B).map B.subtype ∧
      ⁅A, B⁆ ≤ (classicalInvolutionOddCore (Subgroup.centralizer ({a} : Set G))).map
        (Subgroup.centralizer ({a} : Set G)).subtype :=
  twins_of_isTwoComponent (isSubnormal_le hJ) (isTwoComponent_subgroupOf_of_perfect hJ hperf hq)
    hA hB hne

theorem twins_self_of_perfect (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (hperf : commutator J = ⊤) (hq : IsQuasisimple (J ⧸ classicalInvolutionOddCore J))
    {A : Subgroup G} (hA : A ∈ omegaAt J z z) (hne : A ≠ J) :
    A ≤ Subgroup.normalizer (J : Set G) ∧ J ≤ Subgroup.normalizer (A : Set G) ∧
      ⁅J, A⁆ ≤ (classicalInvolutionOddCore J).map J.subtype ⊓
        (classicalInvolutionOddCore A).map A.subtype ∧
      ⁅J, A⁆ ≤ (classicalInvolutionOddCore (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype :=
  twins_self_of_isTwoComponent (isSubnormal_le hJ)
    (isTwoComponent_subgroupOf_of_perfect hJ hperf hq) hA hne

end TwoComponentTwins

section Frames

variable {G : Type*} [Group G] {J : Subgroup G} {z : G}

@[expose] def IsFrame (z : G) (J : Subgroup G) (s : Finset G) : Prop :=
  ∃ A : G → Subgroup G, (∀ a ∈ s, orderOf a = 2 ∧ A a ∈ omegaAt J z a) ∧
    ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∀ x ∈ A a, ∀ y ∈ A b, x * y = y * x


theorem IsFrame.mono {s t : Finset G} (h : IsFrame z J t) (hst : s ⊆ t) : IsFrame z J s := by
  obtain ⟨A, hA, hcomm⟩ := h
  exact ⟨A, fun a ha => hA a (hst ha), fun a ha b hb => hcomm a (hst ha) b (hst hb)⟩


theorem IsFrame.orderOf_eq_two {s : Finset G} (h : IsFrame z J s) {a : G} (ha : a ∈ s) :
    orderOf a = 2 := by
  obtain ⟨A, hA, -⟩ := h
  exact (hA a ha).1

theorem IsFrame.commute {s : Finset G} (hzJ : z ∈ J) (h : IsFrame z J s) {a b : G} (ha : a ∈ s)
    (hb : b ∈ s) : a * b = b * a := by
  obtain ⟨A, hA, hcomm⟩ := h
  by_cases hab : a = b
  · rw [hab]
  · exact hcomm a ha b hb hab a (mem_of_mem_omegaAt hzJ (hA a ha).2) b
      (mem_of_mem_omegaAt hzJ (hA b hb).2)


end Frames

end CFSG.ClassicalInvolution
