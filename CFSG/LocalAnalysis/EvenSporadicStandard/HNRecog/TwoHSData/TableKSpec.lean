module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableKCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableISpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem elemW_nil : elemW [] = 1 := by
  simp only [elemW, TwoHS.wordVal, List.map_nil, List.prod_nil]

theorem elemW_flatten_replicate (e : ℕ) (w : List ℕ) :
    elemW (List.replicate e w).flatten = elemW w ^ e := by
  induction e with
  | zero => simp [elemW_nil]
  | succ e ih => rw [List.replicate_succ, List.flatten_cons, elemW_append, ih, pow_succ']

theorem elemW_getD_mem (gs : List (List ℕ)) (i : ℕ) :
    elemW (gs.getD i []) ∈ closure (elemW '' {w | w ∈ gs}) := by
  by_cases h : i < gs.length
  · rw [List.getD_eq_getElem _ _ h]
    exact subset_closure ⟨_, List.getElem_mem h, rfl⟩
  · rw [List.getD_eq_default _ _ (by omega), elemW_nil]
    exact one_mem _

theorem elemW_specWord_mem (gs : List (List ℕ)) (spec : List (ℕ × ℕ)) :
    elemW (specWord gs spec) ∈ closure (elemW '' {w | w ∈ gs}) := by
  induction spec with
  | nil => simp [specWord, elemW_nil]
  | cons p ps ih =>
    have e : specWord gs (p :: ps) =
        (List.replicate p.2 (gs.getD (p.1 - 1) [])).flatten ++ specWord gs ps := by
      simp [specWord, List.flatMap_cons]
    rw [e, elemW_append, elemW_flatten_replicate]
    exact mul_mem (pow_mem (elemW_getD_mem gs (p.1 - 1)) _) ih

theorem closure_specWords_le (gs : List (List ℕ)) (specs : List (List (ℕ × ℕ))) :
    closure (elemW '' {w | w ∈ specs.map (specWord gs)}) ≤ closure (elemW '' {w | w ∈ gs}) := by
  rw [closure_le]
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨spec, -, rfl⟩ := List.mem_map.1 hw
  exact elemW_specWord_mem gs spec


end CFSG.EvenSporadicStandard.HNRecog
