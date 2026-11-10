module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XTabLemmas
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XEnumLemmas
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XAutGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4.XModel

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.HNRecog.Section3

open scoped commutatorElement

@[expose] noncomputable def XP : Subgroup (Equiv.Perm (Fin 1408)) :=
  P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))

theorem mem_XP_iff {g : Equiv.Perm (Fin 1408)} :
    g ∈ XP ↔ g ∈ P1408 ∧ g * elemZ = elemZ * g := by
  rw [XP, mem_inf, mem_centralizer_singleton_iff]


theorem commute_of_mem_closure {Γ : Type*} [Group Γ] {s : Set Γ} {a : Γ}
    (h : ∀ g ∈ s, g * a = a * g) {x : Γ} (hx : x ∈ closure s) : x * a = a * x := by
  have hle : closure s ≤ centralizer ({a} : Set Γ) := by
    rw [closure_le]
    intro y hy
    exact mem_centralizer_singleton_iff.2 (h y hy)
  exact mem_centralizer_singleton_iff.1 (hle hx)

theorem mem_derivedOf_comm {Γ : Type} [Group Γ] {K : Subgroup Γ} {p q : Γ} (hp : p ∈ K)
    (hq : q ∈ K) : p * q * p⁻¹ * q⁻¹ ∈ derivedOf K := by
  refine mem_derivedOf_iff.mpr ⟨K.mul_mem (K.mul_mem (K.mul_mem hp hq) (K.inv_mem hp))
    (K.inv_mem hq), ?_⟩
  have h : ⁅(⟨p, hp⟩ : ↥K), ⟨q, hq⟩⁆ ∈ _root_.commutator ↥K := by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)
  exact h


end CFSG.EvenSporadicStandard.HNRecog.Section4.XModel
