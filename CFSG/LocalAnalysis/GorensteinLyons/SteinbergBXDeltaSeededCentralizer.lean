module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXDeltaFailureWitness
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBMLocalPrimeSetRankFour
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.LocalAnalysis.LargeEvenClassification.Helpers
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open

variable {G : Type*} [Group G]


theorem mem_normalizer_inf_of_mem' {S T : Subgroup G} {g : G} (hS : g ∈ normalizer (S : Set G))
    (hT : g ∈ normalizer (T : Set G)) : g ∈ normalizer ((S ⊓ T : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hS hT ⊢
  intro x
  rw [mem_inf, mem_inf, hS x, hT x]


end CFSG.LocalAnalysis.GorensteinLyons
