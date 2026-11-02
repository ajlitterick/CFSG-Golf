module

public import CFSG.Monster.Existence.StdOdd.Defs
public import CFSG.Monster.Existence.BabyTableIVOf
public import CFSG.Monster.Existence.BabyW3Classes
public import CFSG.Monster.B.TwoA.Amalgam.DerivedCoverMain

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence.StdOdd

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.GMS CFSG.Blueprint
  CFSG.LieType.Chevalley.C2E6Std

private theorem eq_one_of_pow_eq_one_of_odd {X : Type*} [Group X] {x : X} {n : ℕ} (hn : Odd n)
    (h1 : x ^ n = 1) (h2 : x ^ 2 = 1) : x = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rwa [pow_succ, pow_mul, h2, one_pow, one_mul] at h1

theorem injective_of_odd_of_sq_eq_one {M K : Type*} [Group M] [Group K]
    (hM : Odd (Nat.card M)) (g : M →* K) (h : ∀ m : M, g m = 1 → m ^ 2 = 1) :
    Function.Injective g := by
  rw [injective_iff_map_eq_one]
  exact fun m hm => eq_one_of_pow_eq_one_of_odd hM pow_card_eq_one' (h m hm)

theorem map_mem_of_index_eq_two {M G : Type*} [Group M] [Group G] {K : Subgroup G}
    (hK : K.index = 2) (hM : Odd (Nat.card M)) (f : M →* G) (m : M) : f m ∈ K := by
  have := Subgroup.normal_of_index_eq_two hK
  set g : M →* G ⧸ K := (QuotientGroup.mk' K).comp f with hg
  have h2 : g m ^ 2 = 1 := by
    have := pow_card_eq_one' (G := G ⧸ K) (x := g m)
    rwa [show Nat.card (G ⧸ K) = 2 from hK] at this
  have h1 : g m ^ Nat.card M = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  exact (QuotientGroup.eq_one_iff _).1 (eq_one_of_pow_eq_one_of_odd hM h1 h2)

theorem exists_injective_of_index_two_of_card_two {E T M : Type*} [Group E] [Group T] [Group M]
    {K Z : Subgroup E} [Z.Normal] (hK : K.index = 2) (hZ : Nat.card Z = 2)
    (e : K ⧸ Z.subgroupOf K ≃* T) (hM : Odd (Nat.card M)) (f : M →* E)
    (hf : Function.Injective f) : ∃ g : M →* T, Function.Injective g := by
  have hmem : ∀ m : M, f m ∈ K := map_mem_of_index_eq_two hK hM f
  set f' : M →* K := f.codRestrict K hmem with hf'
  set g : M →* T := (e.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf K))).comp f' with hg
  refine ⟨g, injective_of_odd_of_sq_eq_one hM g fun m hm => ?_⟩
  have h1 : f' m ∈ Z.subgroupOf K := by
    rw [← QuotientGroup.eq_one_iff]
    exact (MulEquiv.map_eq_one_iff e).1 hm
  have h2 : f m ∈ Z := Subgroup.mem_subgroupOf.1 h1
  have h3 : f m ^ 2 = 1 := by
    have := pow_card_eq_one' (x := (⟨f m, h2⟩ : Z))
    rw [hZ] at this
    exact congrArg Subtype.val this
  exact hf (by rw [map_pow, h3, map_one])

theorem exists_injective_stdGroup_of_injective_Eam
    {M : Type*} [Group M]
    (hM : Odd (Nat.card M)) (f : M →* ↥Eam) (hf : Function.Injective f) :
    ∃ g : M →* ↥stdGroup, Function.Injective g := by
  obtain ⟨hidx, -, -, -, hZ2, ⟨e⟩, -⟩ := short_F4_derived_standard_perfect_cover
  exact exists_injective_of_index_two_of_card_two hidx hZ2 e hM f hf

private theorem nonempty_centralizer_mulEquiv_of_isConj {G : Type*} [Group G] {a b : G}
    (h : IsConj a b) :
    Nonempty (↥(Subgroup.centralizer ({a} : Set G)) ≃* ↥(Subgroup.centralizer ({b} : Set G))) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have e := centralizerMulEquiv (MulAut.conj c) a
  rw [MulAut.conj_apply, hc] at e
  exact ⟨e⟩

private theorem exists_injective_of_le_centralizer {G H : Type*} [Group G] [Group H] {a : G}
    {M : Subgroup G} (hM : M ≤ Subgroup.centralizer ({a} : Set G))
    (e : ↥(Subgroup.centralizer ({a} : Set G)) ≃* H) :
    ∃ f : ↥M →* H, Function.Injective f :=
  ⟨(e : _ →* _).comp (Subgroup.inclusion hM), e.injective.comp (Subgroup.inclusion_injective hM)⟩

theorem nonempty_centralizer_phiB_uBar_mulEquiv_Eam
    (hC : CTIB.CentralizerInput) :
    Nonempty (↥(Subgroup.centralizer ({phiB uBar} : Set NativeSporadic.B)) ≃* ↥Eam) := by
  obtain ⟨Ψ⟩ := CTIB.centralizer_equiv_Eam hC
    (CTIB.isConj_labelS_of_rank orderOf_op_uBar rank_betaS_op_uBar)
  exact ⟨((@centralizerMulEquiv Cbar NativeSporadic.B _ Units.instGroup phiB uBar).symm.trans
    centOpUBarEquiv.symm).trans Ψ⟩

theorem nonempty_centralizer_mulEquiv_Eam_of_babyInv_zero
    (h3 : Nat.card ↥(Subgroup.centralizer ({babyRep 3} : Set NativeSporadic.B)) ≠ babyCentOrder 0)
    {r : NativeSporadic.B} (hr : BabyInv 0 r) :
    Nonempty (↥(Subgroup.centralizer ({r} : Set NativeSporadic.B)) ≃* ↥Eam) := by
  have hconj : IsConj r (phiB uBar) := (isConj_babyRep_one_of_babyInv_zero h3 hr).trans
    (isConj_rep_one_of_rank orderOf_phiB_uBar rank_phiB_uBar_sub_one).symm
  obtain ⟨e₁⟩ := nonempty_centralizer_mulEquiv_of_isConj hconj
  obtain ⟨e₂⟩ := nonempty_centralizer_phiB_uBar_mulEquiv_Eam centralizerInput_B
  exact ⟨e₁.trans e₂⟩

theorem exists_subgroup_stdGroup_card_eq
    (h3 : Nat.card ↥(Subgroup.centralizer ({babyRep 3} : Set NativeSporadic.B)) ≠ babyCentOrder 0)
    {r : NativeSporadic.B} (hr : BabyInv 0 r) {M : Subgroup NativeSporadic.B}
    (hM : M ≤ Subgroup.centralizer ({r} : Set NativeSporadic.B)) (hodd : Odd (Nat.card M)) :
    ∃ N : Subgroup Rgrp, Nat.card N = Nat.card M := by
  obtain ⟨e⟩ := nonempty_centralizer_mulEquiv_Eam_of_babyInv_zero h3 hr
  obtain ⟨f, hf⟩ := exists_injective_of_le_centralizer hM e
  obtain ⟨g, hg⟩ := exists_injective_stdGroup_of_injective_Eam hodd f hf
  exact ⟨g.range, Nat.card_congr (MonoidHom.ofInjective hg).toEquiv.symm⟩

end CFSG.Monster.Existence.StdOdd
