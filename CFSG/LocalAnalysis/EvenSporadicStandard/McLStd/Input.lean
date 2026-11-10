module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Consistency
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction

public section

namespace CFSG.EvenSporadicStandard.McLStd

open Subgroup CFSG CFSG.GH74.GLS CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.GSThmB CFSG.OddStandard.Solomon75

@[expose] def HasIntrinsicAn (G : Type) [Group G] : Prop :=
  ∃ (z : G) (B : Subgroup G) (n : ℕ), orderOf z = 2 ∧ 8 ≤ n ∧ B ≤ centralizer ({z} : Set G) ∧
    IsPComponent 2 (B.subgroupOf (centralizer ({z} : Set G))) ∧ z ∈ B ∧
    Group.IsPerfect (B ⧸ pPrimeCore 2 B) ∧ Nat.card (center (B ⧸ pPrimeCore 2 B)) = 2 ∧
    Nonempty ((B ⧸ pPrimeCore 2 B) ⧸ center (B ⧸ pPrimeCore 2 B) ≃* alternatingGroup (Fin n))

theorem mulEquiv_mcl_or_ly_of_hasIntrinsicAn (hS : Solomon2AnInput) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (h : HasIntrinsicAn G) :
    Nonempty (G ≃* NativeSporadic.McL) ∨ Nonempty (G ≃* NativeSporadic.Ly) := by
  obtain ⟨z, B, n, hz, hn, hBC, hB, hzB, hperf, hcard, hquot⟩ := h
  exact hS G z hz B n hn hBC hB hzB hperf hcard hquot

@[expose] def StdHasIntrinsicAn (s : TauCeti.SporadicName) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → IsSporadic L s →
    HasIntrinsicAn G


variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_inf_eq_map {L : Subgroup G} {u : G} (hu : u ∈ L) :
    centralizer ({u} : Set G) ⊓ L =
      (centralizer ({(⟨u, hu⟩ : L)} : Set ↥L)).map L.subtype := by
  ext g
  simp only [mem_inf, mem_centralizer_singleton_iff, mem_map, coe_subtype]
  constructor
  · rintro ⟨hg, hgL⟩
    refine ⟨⟨g, hgL⟩, ?_, rfl⟩
    exact Subtype.ext (by simpa using hg)
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by simpa using congrArg Subtype.val hx, x.2⟩

omit [Finite G] in
theorem isDoubleCoverOfAlt_inf {L : Subgroup G} {u : G} (hu : u ∈ L) {n : ℕ}
    (hcov : IsDoubleCoverOfAlt ↥(centralizer ({(⟨u, hu⟩ : L)} : Set ↥L)) n) :
    IsDoubleCoverOfAlt ↥(centralizer ({u} : Set G) ⊓ L) n := by
  have hBmap : centralizer ({u} : Set G) ⊓ L =
      (centralizer ({(⟨u, hu⟩ : L)} : Set ↥L)).map L.subtype := centralizer_inf_eq_map hu
  have eB : ↥(centralizer ({(⟨u, hu⟩ : L)} : Set ↥L)) ≃* ↥(centralizer ({u} : Set G) ⊓ L) :=
    (Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hBmap.symm)
  exact Stage12.McLRec.isDoubleCoverOfAlt_congr eB hcov


end CFSG.EvenSporadicStandard.McLStd
