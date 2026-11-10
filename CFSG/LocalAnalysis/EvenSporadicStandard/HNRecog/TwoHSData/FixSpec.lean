module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WClassSpec
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Iso
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.TwoHS

local notation "𝒞" => CFSG.Sporadic.SmallOddCore.conjClass


theorem p0_gens_spec (hgens : gensOK = true) {p0w : List (List ℕ)}
    (hw : p0w.all wordOK = true)
    (hinv : p0w.all (fun w => invOK 1408 (tabW w) (invT 1408 (tabW w))) = true) :
    ∀ l < (p0Tabs p0w).size, Rep 1408 (p0Tabs p0w)[l]! (tablePerm 1408 (p0Tabs p0w)[l]!) ∧
      Rep 1408 (p0Invs p0w)[l]! (tablePerm 1408 (p0Tabs p0w)[l]!)⁻¹ ∧
        tablePerm 1408 (p0Tabs p0w)[l]! ∈ P1408 := by
  intro l hl
  have hmem : (p0Tabs p0w)[l]! ∈ tabsW p0w := by
    have := getElem!_mem_array hl
    simpa [p0Tabs] using this
  obtain ⟨w, hwm, hwl⟩ := List.mem_map.1 hmem
  have hr : Rep 1408 (tabW w) (elemW w) :=
    rep_elemW_of_gensOK hgens (List.all_eq_true.1 hw w hwm)
  have hr' : Rep 1408 (p0Tabs p0w)[l]! (elemW w) := by rw [← hwl]; exact hr
  have htp : tablePerm 1408 (p0Tabs p0w)[l]! = elemW w := tablePerm_eq hr'
  have hinvr : Rep 1408 (invT 1408 (tabW w)) (elemW w)⁻¹ :=
    Rep.inv_of_invOK hr (List.all_eq_true.1 hinv w hwm)
  have hInvEntry : (p0Invs p0w)[l]! = invT 1408 (tabW w) := by
    rw [p0Invs, getElem!_pos _ l (by simpa [p0Tabs] using hl), Array.getElem_map,
      ← getElem!_pos (p0Tabs p0w) l hl, hwl]
  refine ⟨by rw [htp]; exact hr', by rw [htp, hInvEntry]; exact hinvr, by
    rw [htp]; exact elemW_mem w⟩

theorem rep_conjTab (hgens : gensOK = true) {c : List ℕ} (hc : wordOK c = true)
    (hinv : invOK 1408 (tabW c) (invT 1408 (tabW c)) = true) {tx : Table}
    {x : Equiv.Perm (Fin 1408)} (hx : Rep 1408 tx x) :
    Rep 1408 (conjTab c tx) (elemW c * x * (elemW c)⁻¹) := by
  have hr := rep_elemW_of_gensOK hgens hc
  exact rep_conjT hr (Rep.inv_of_invOK hr hinv) hx


end CFSG.EvenSporadicStandard.HNRecog
