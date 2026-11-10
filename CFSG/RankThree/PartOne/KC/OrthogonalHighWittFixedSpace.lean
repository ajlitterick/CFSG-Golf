module

public import CFSG.RankThree.PartOne.KC.OrthogonalLocalComponents
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDickson
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.Classical2 CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

section Helpers

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem dicksonHom_eq_one_of_mem_orthDerived (hQ : Q.polarBilin.Nondegenerate) {g : V ≃ₗ[K] V}
    (hg : g ∈ orthDerived Q) :
    dicksonHom Q hQ ⟨g, orthDerived_le_orthogonalGroup hg⟩ = 1 := by
  have hle : orthDerived Q ≤
      (dicksonHom Q hQ).ker.map (TauCeti.QuadraticMap.orthogonalGroup Q).subtype := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    refine ⟨⁅(⟨a, ha⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup Q)), ⟨b, hb⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  obtain ⟨g', hg', hgg'⟩ := Subgroup.mem_map.mp (hle hg)
  have : g' = ⟨g, orthDerived_le_orthogonalGroup hg⟩ := Subtype.ext hgg'
  rw [← this]
  exact hg'

end Helpers

section Binary

variable {K : Type*} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.commute_fixed_of_mem_orthDerived (hx : OddOrderIsometry Q p x)
    (hp2 : Odd p) (hQ : Q.polarBilin.Nondegenerate) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) (hdim : finrank K (fixedSpace x) = 2)
    {m w₀ : V ≃ₗ[K] V} (hm : m ∈ isometryCentralizer Q x) (hmΩ : m ∈ orthDerived Q)
    (hw : w₀ ∈ supportedBlock Q x (X - 1)) (hwp : w₀ ^ p = 1) : m * w₀ = w₀ * m := by
  have hQW := hx.polarBilin_fixed_nondegenerate
  have hwM : w₀ ∈ isometryCentralizer Q x := supportedBlock_le_isometryCentralizer _ hw
  have h1 : dicksonCentralizer Q x hQ ⟨m, hm⟩ = 1 :=
    dicksonHom_eq_one_of_mem_orthDerived hQ hmΩ
  have h2 := DFunLike.congr_fun (hx.dicksonCentralizer_eq_dicksonFixed hp2 hQ hRep) ⟨m, hm⟩
  rw [h1] at h2
  have hδm : dicksonHom (Q.comp (fixedSpace x).subtype) hQW
      ⟨isometryRestrictFixed Q x ⟨m, hm⟩, isometryRestrictFixed_mem_orthogonalGroup _⟩ = 1 :=
    h2.symm
  have hδw : dicksonHom (Q.comp (fixedSpace x).subtype) hQW
      ⟨isometryRestrictFixed Q x ⟨w₀, hwM⟩, isometryRestrictFixed_mem_orthogonalGroup _⟩ = 1 := by
    refine dicksonHom_eq_one_of_pow_eq_one hQW hp2 ?_
    refine Subtype.ext ?_
    show (isometryRestrictFixed Q x ⟨w₀, hwM⟩) ^ p = 1
    rw [← map_pow]
    have : (⟨w₀, hwM⟩ : ↥(isometryCentralizer Q x)) ^ p = 1 := Subtype.ext hwp
    rw [this, map_one]
  have hcomm := commute_of_dicksonHom_eq_one hQW hdim
    (isometryRestrictFixed_mem_orthogonalGroup ⟨m, hm⟩)
    (isometryRestrictFixed_mem_orthogonalGroup ⟨w₀, hwM⟩) hδm hδw
  have hmc : m ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := (Subgroup.mem_inf.mp hm).2
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_of_isCompl hx.fixed_others.1 v
  have hmr : m r ∈ othersSpace x.toLinearMap (X - 1) := mem_othersSpace_of_apply hmc hr
  have hw1 := (mem_supportedBlock.mp hw).2 r hr
  have hw2 := (mem_supportedBlock.mp hw).2 _ hmr
  have hcu := congrArg (fun φ : fixedSpace x ≃ₗ[K] fixedSpace x => (φ ⟨u, hu⟩ : V)) hcomm
  show m (w₀ (u + r)) = w₀ (m (u + r))
  simp only [map_add, hw1, hw2]
  exact congrArg (· + m r) hcu

end Binary

section PCore

theorem mem_pCoreOf_of_central {G : Type*} [Group G] {p : ℕ} {N : Subgroup G} {w : G}
    (hwN : w ∈ N) (hc : ∀ n ∈ N, w * n = n * w) (hw : w ^ p = 1) :
    w ∈ CFSG.Assembly.pCoreOf p N := by
  refine Subgroup.mem_map.mpr ⟨⟨w, hwN⟩, ?_, rfl⟩
  let P : Subgroup ↥N := Subgroup.zpowers ⟨w, hwN⟩
  have hcomm : ∀ (n : ↥N) (k : ℤ), (⟨w, hwN⟩ : ↥N) ^ k * n = n * (⟨w, hwN⟩ : ↥N) ^ k := by
    intro n k
    have h1 : Commute (⟨w, hwN⟩ : ↥N) n := Subtype.ext (hc n n.2)
    exact (h1.zpow_left k).eq
  have hPn : P.Normal := by
    refine ⟨fun t ht g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    rw [← hcomm g k, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ k
  have hPp : IsPGroup p P := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine Subtype.ext ?_
    show (g : ↥N) ^ p ^ 1 = 1
    rw [pow_one, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    have : (⟨w, hwN⟩ : ↥N) ^ p = 1 := Subtype.ext hw
    rw [this, one_zpow]
  rw [CFSG.pCore_eq_iSup]
  exact Subgroup.mem_iSup_of_mem P (Subgroup.mem_iSup_of_mem hPn
    (Subgroup.mem_iSup_of_mem hPp (Subgroup.mem_zpowers _)))

end PCore

end CFSG.RankThree.PartOne.KCOrthogonal

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal


end CFSG.RankThree.PartOne
