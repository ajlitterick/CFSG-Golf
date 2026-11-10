module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi22Classes
public import CFSG.Sporadic.FischerOddCore.Fi22AllInv
public import Certificates.Certificate25641
public import Certificates.Certificate25642
public import Certificates.Certificate25643
public import Certificates.Certificate25644
public import Certificates.Certificate25645
public import Certificates.Certificate25646

public section

namespace CFSG.EvenSporadicStandard.HypOne.Fi22

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.ComponentClassification.M12Cover
open CFSG.Sporadic.Schreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977


theorem fourClassesLarge_rows :
    (∀ v ∈ fi22P, orderOf v = 2 → FourClassesLarge ↥(centralizerIn fi22P v)) ∧
      ∀ v ∈ fi22R, orderOf v = 2 → FourClassesLarge ↥(centralizerIn fi22R v) := by
  have hP0 := Certificates.certificate25641
  have hP1 := Certificates.certificate25642
  have hP2 := Certificates.certificate25643
  have hR0 := Certificates.certificate25644
  have hR1 := Certificates.certificate25645
  have hR2 := Certificates.certificate25646
  obtain ⟨-, -, hR3, hR4, hR5⟩ := Certificates.certificate25640
  have fP : ∀ k < 3, FourClassesLarge ↥(centralizerIn fi22P (fi22ExtRep k)) := by
    intro k hk
    interval_cases k
    · exact hP0
    · exact hP1
    · exact hP2
  have fR : ∀ k < 6, FourClassesLarge ↥(centralizerIn fi22R (fi22ExtRep k)) := by
    intro k hk
    interval_cases k
    · exact hR0
    · exact hR1
    · exact hR2
    · exact hR3
    · exact hR4
    · exact hR5
  refine ⟨fourClassesLarge_centralizerIn_of_reps fi22P ((List.range 3).map fi22ExtRep) cover_P
      fun r hr => ?_, fourClassesLarge_centralizerIn_of_reps fi22R ((List.range 6).map fi22ExtRep)
      cover_R fun r hr => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
    exact fP k (List.mem_range.1 hk)
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
    exact fR k (List.mem_range.1 hk)

theorem hypothesisOne_native :
    HypothesisOne NativeSporadic.Fi22 := by
  obtain ⟨hP, hR⟩ := fourClassesLarge_rows
  exact hypothesisOne_of_outTwo fi22PermEquiv center_fi22P fi22_autModel fi22RAut card_fi22R_le
    (fun τ hτ h2 => CTUC_Fi22_all_involution_fixed_subgroups_odd_core_trivial τ hτ h2) hP hR

theorem fi22ExtRep_mem_R
    {k : ℕ} (hk : 3 ≤ k) (hk6 : k < 6) :
    fi22ExtRep k ∈ fi22R := by
  have := (CTUC_Fi22_all_extension_involutions_covered.2.1 (k - 3) (by omega)).1
  rwa [show 3 + (k - 3) = k by omega] at this


theorem hypothesisOne_of_isSporadic
    {Y : Type} [Group Y]
    (h : IsSporadic Y .Fi22) : HypothesisOne Y := by
  obtain ⟨e⟩ := h
  exact CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm hypothesisOne_native


end CFSG.EvenSporadicStandard.HypOne.Fi22
