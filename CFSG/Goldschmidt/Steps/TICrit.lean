module

import CFSG.Goldschmidt.Steps.Ind
import CFSG.Goldschmidt.Steps.IHConseq
import CFSG.Goldschmidt.Steps.PropHSetup
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.Basic
public import CFSG.LocalAnalysis.ComponentClassification.OddCore

public section

namespace CFSG.Goldschmidt

open CFSG.Open

namespace TICrit

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_fusionIsSylowIn {U X : Subgroup G} (hU : IsPGroup 2 U) (hUX : U ≤ X) :
    ∃ T : Subgroup G, U ≤ T ∧ fusionIsSylowIn 2 T X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := (hU.comap_subtype (K := X)).exists_le_sylow
  refine ⟨(P : Subgroup X).map X.subtype,
    fun u hu => ⟨⟨u, hUX hu⟩, hP (show (⟨u, hUX hu⟩ : X) ∈ U.comap X.subtype from hu), rfl⟩,
    Subgroup.map_subtype_le _, P.isPGroup'.map _, fun Q hQX hQ hPQ => ?_⟩
  have h1 := P.is_maximal' (Q := Q.subgroupOf X) hQ.comap_subtype
    (fun x hx => hPQ ⟨x, hx, rfl⟩)
  refine le_antisymm (fun q hq => ⟨⟨q, hQX hq⟩, ?_, rfl⟩) hPQ
  rw [← h1]
  exact hq

theorem card_centralizer_lt [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {u : G}
    (hu1 : u ≠ 1) : Nat.card (Subgroup.centralizer ({u} : Set G)) < Nat.card G := by
  have hne : Subgroup.centralizer ({u} : Set G) ≠ ⊤ := by
    intro htop
    have hZ : u ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer ({u} : Set G) := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [PropHSetup.center_eq_bot hnab] at hZ
    exact hu1 (Subgroup.mem_bot.mp hZ)
  rw [← Subgroup.card_top (G := G)]
  exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hne)

omit [Finite G] in
theorem normalClosureIn_le_of_le_normalizer {U X : Subgroup G} (hUX : U ≤ X)
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) : normalClosureIn X U ≤ U := by
  have : (U.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUX).mpr hXU
  have h := Subgroup.map_mono (f := X.subtype)
    (Subgroup.normalClosure_le_normal (N := U.subgroupOf X) subset_rfl)
  rw [Subgroup.subgroupOf_map_subtype] at h
  exact h.trans inf_le_left


end TICrit


end CFSG.Goldschmidt
