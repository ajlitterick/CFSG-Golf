module

public import CFSG.ClassicalInvolution.Q3.TL3LeafCore
public import CFSG.ClassicalInvolution.Q3.TL3Weak
public import CFSG.ClassicalInvolution.Q3.TL3Main
public import CFSG.ClassicalInvolution.Q3.Q3CLBasic
public import CFSG.ClassicalInvolution.TwoGroupCase.EscapeOdd

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}


theorem TightDatum.nonempty_omegaNbr_of_not_dEdgeless (h : TightDatum R S t)
    (hne : ¬ Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R))) :
    (omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)).Nonempty := by
  have hΩ := h.hypOmegaGen
  simp only [Disconnected.DEdgeless, not_forall] at hne
  obtain ⟨K, hK, J, hJ, hadj⟩ := hne
  have hadj' := not_not.mp hadj
  have hJK : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) K := by
    rcases hadj' with h1 | h1
    · exact h1
    · exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ hK h1
  obtain ⟨g, rfl⟩ := hK
  refine ⟨conjSub g⁻¹ J, ?_⟩
  have := omegaNbr_conj hΩ.conjInvariant hJK g⁻¹
  rwa [conjSub_inv_conjSub] at this

theorem TightDatum.not_dEdgeless_of_escape (h : TightDatum R S t) {T U : Subgroup G} {x : G}
    (hT : IsSylow2Of T
      (Subgroup.normalizer (((S : Subgroup R).map R.subtype : Subgroup G) : Set G)))
    (e : Escape T U x) :
    ¬ Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R)) := by
  classical
  have d : OddByQuat R ((S : Subgroup R).map R.subtype) t :=
    OddByQuat.of_quaternion S h.quat h.mem h.order h.cent h.normal h.twoGroup
  set S0 : Subgroup G := (S : Subgroup R).map R.subtype with hS0
  have huniq := h.isUniqueInvolution_core
  have hΩ := h.hypOmegaGen
  have hS0K0 : S0 ≤ tightCore R := by
    intro s hs
    exact Subgroup.subset_closure ⟨d.S_le hs, d.S_two.to_le (Subgroup.zpowers_le.mpr hs)⟩
  have hSyl : IsSylow2In S0 (tightCore R) :=
    ⟨hS0K0, d.S_two, fun V hVK hV2 hle => d.sylow.2.2 V (hVK.trans (tightCore_le R)) hV2 hle⟩
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hJ : conjSub x (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨x, rfl⟩
  have hne : conjSub x (tightCore R) ≠ tightCore R := by
    intro heq
    have h1 : IsUniqueInvolution (conjSub x (tightCore R)) (x * t * x⁻¹) := huniq.conj x
    rw [heq] at h1
    exact d.t₁_ne hT e (huniq.eq h1).symm
  have hR' : conjSub x S0 ∈ RSet (CoreAssembly.conjClass (tightCore R)) :=
    RSet.conj hΩ.conjInvariant (mem_RSet_of_isSylow2In hK hSyl) x
  have hnbr : conjSub x (tightCore R) ∈
      omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    refine ⟨hJ, hne, conjSub x S0, hR', conjSub_mono hS0K0, fun y hy => ?_⟩
    have hy' : y ∈ conjSubgroup x S0 := mem_conjSubgroup_iff.mpr (mem_conjSub_iff.mp hy)
    have hty : t * y = y * t := d.commute_S_S₁ hT e t h.mem y hy'
    exact h.le_normalizer_core (Subgroup.mem_centralizer_singleton_iff.mpr hty.symm)
  intro hedge
  exact hedge (tightCore R) hK _ hJ (Or.inl hnbr)

theorem TightDatum.not_dEdgeless_of_not_sylow (h : TightDatum R S t) {T : Subgroup G}
    (hT : IsSylow2Of T
      (Subgroup.normalizer (((S : Subgroup R).map R.subtype : Subgroup G) : Set G)))
    (hnot : ¬ IsSylow2Of T ⊤) :
    ¬ Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R)) := by
  obtain ⟨U, hU, hTU⟩ := exists_isSylow2Of_ge hT.2.1 (le_top : T ≤ ⊤)
  obtain ⟨x, e⟩ := exists_escape hnot hU hTU
  exact h.not_dEdgeless_of_escape hT e


@[expose] def GoodThreeElement {Y : Type} [Group Y] (R : Subgroup Y) (t : Y) : Prop :=
  ∃ (x : Y) (k : ℕ), x ∈ Subgroup.centralizer ({t} : Set Y) ∧ x ^ 3 ^ k = 1 ∧
    (∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R) ∧
    ∀ y ∈ Subgroup.centralizer ({t} : Set Y), (∀ r ∈ R, ⁅y, r⁆ ∈ oddCoreImg R) →
      ⁅x, y⁆ ∈ oddCoreImg (Subgroup.centralizer ({t} : Set Y))


section Scaffold

@[expose] def TightHasLift {Y : Type} [Group Y] (R : Subgroup Y) (t : Y) : Prop :=
  ∃ L : Subgroup Y, tightCore R ≤ L ∧ IsClassicalMember3 L t


end Scaffold

end CFSG.ClassicalInvolution.Q3
