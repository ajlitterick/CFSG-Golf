module

public import CFSG.LocalAnalysis.StandardType.GGK1ADefs
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.LieType.SemisimpleCentralizers.OrderThree.CenterQuot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CoverSU3
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyStatements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LieType.SemisimpleCentralizers.Held CFSG.LieType.SemisimpleCentralizers.HeldLang
open CFSG.LieType.SemisimpleCentralizers.OrderThree
  (nonempty_quotientCenter_equiv_statedProj_statedSU)
open CFSG.Quasithin.Background.Harris.OrdinaryProofs (card_statedSU_three_two_of_card_four)


private theorem ggK1Ak_blockA_arith {nf r d : ℕ} (hnf : 1 ≤ nf) (hr : 1 ≤ r)
    (hd : d = 1 ∨ d = 2) (hqs : (ggMultBlockA r nf d).qs = true) :
    nf ∣ (ggMultBlockA r nf d).lab.n ∧ LargeEvenInLambda2 (ggMultBlockA r nf d).lab := by
  rcases hd with rfl | rfl
  · have hP : r ≠ 1 ∨ nf ≠ 1 := by simpa [ggMultBlockA] using hqs
    rw [ggMultBlockA]
    rw [if_pos (rfl : (1 : ℕ) = 1)]
    constructor
    · exact dvd_rfl
    · simp only [LargeEvenInLambda2]
      refine ⟨hnf, hr, ?_⟩
      intro hr1
      rcases hP with h | h
      · exact absurd hr1 h
      · omega
  · by_cases h2 : 2 ≤ r
    · have hP : r ≠ 2 ∨ nf ≠ 1 := by simpa [ggMultBlockA, h2] using hqs
      rw [ggMultBlockA]
      rw [if_neg (by decide : ¬ (2 : ℕ) = 1), if_pos h2]
      constructor
      · exact dvd_rfl
      · simp only [LargeEvenInLambda2]
        refine ⟨hnf, h2, ?_⟩
        intro hr2
        rcases hP with h | h
        · exact absurd hr2 h
        · omega
    · have hr1 : r = 1 := by omega
      have hP : nf ≠ 1 := by simpa [ggMultBlockA, h2] using hqs
      rw [ggMultBlockA]
      rw [if_neg (by decide : ¬ (2 : ℕ) = 1), if_neg h2]
      subst hr1
      constructor
      · exact dvd_rfl
      · simp only [LargeEvenInLambda2]
        refine ⟨hnf, le_rfl, ?_⟩
        intro _; omega

private theorem ggK1Ak_A2nf_arith {nf r : ℕ} (hnf : 1 ≤ nf) (hr : 1 ≤ r) :
    nf ∣ (2 * nf) ∧ LargeEvenInLambda2 (⟨.A, r, 2 * nf⟩ : LargeEvenLabel) := by
  constructor
  · exact dvd_mul_left nf 2
  · simp only [LargeEvenInLambda2]
    constructor
    · omega
    · constructor
      · exact hr
      · intro _; omega

private theorem ggK1Ak_orbits_eq_trivial {p nf : ℕ} {tw : Bool} {m : List ℕ}
    (h : (tw = false ∧ ggMultOrd p nf = 1) ∨ (tw = true ∧ ggMultOrd p nf = 2)) :
    (ggMultDatumA p nf (ggMultOrd p nf) tw m).orbits =
      ((List.range p).filter (fun j => decide (2 ≤ m.getD j 0))).map
        (fun j => ggMultBlockA (m.getD j 0 - 1) nf (ggMultOrd p nf)) := by
  simp only [ggMultDatumA, if_pos h]

private theorem ggK1Ak_orbits_eq_nontrivial {p nf : ℕ} {tw : Bool} {m : List ℕ}
    (h : ¬ ((tw = false ∧ ggMultOrd p nf = 1) ∨ (tw = true ∧ ggMultOrd p nf = 2))) :
    (ggMultDatumA p nf (ggMultOrd p nf) tw m).orbits =
      (if 2 ≤ m.headD 0 then
        (if tw = false then
          [⟨⟨.A, m.headD 0 - 1, nf⟩, decide (¬ (m.headD 0 - 1 = 1 ∧ nf = 1))⟩]
         else [ggMultBlockA (m.headD 0 - 1) nf 2])
       else []) ++
      ((List.range ((p - 1) / 2 + 1)).filter (fun j => decide (1 ≤ j ∧ 2 ≤ m.getD j 0))).map
        (fun j => (⟨⟨.A, m.getD j 0 - 1, 2 * nf⟩, true⟩ : GGKacOrbit)) := by
  simp only [ggMultDatumA, if_neg h]


theorem ggK1ACo_orbit_arith {p nf : ℕ} {tw : Bool} {m : List ℕ} (hnf : 1 ≤ nf) {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumA p nf (ggMultOrd p nf) tw m).orbits) (hqs : o.qs = true) :
    nf ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab := by
  classical
  by_cases htriv : (tw = false ∧ ggMultOrd p nf = 1) ∨ (tw = true ∧ ggMultOrd p nf = 2)
  · rw [ggK1Ak_orbits_eq_trivial (p := p) (nf := nf) (tw := tw) (m := m) htriv] at ho
    rw [List.mem_map] at ho
    obtain ⟨j, hj, rfl⟩ := ho
    rw [List.mem_filter] at hj
    obtain ⟨-, hj2⟩ := hj
    have hj2' : 2 ≤ m.getD j 0 := by simpa using hj2
    have hd : ggMultOrd p nf = 1 ∨ ggMultOrd p nf = 2 :=
      htriv.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
    exact ggK1Ak_blockA_arith hnf (by omega) hd (by simpa using hqs)
  · rw [ggK1Ak_orbits_eq_nontrivial (p := p) (nf := nf) (tw := tw) (m := m) htriv] at ho
    rw [List.mem_append] at ho
    rcases ho with ho | ho
    · by_cases h0 : 2 ≤ m.headD 0
      · rw [if_pos h0] at ho
        by_cases htw : tw = false
        · rw [if_pos htw] at ho
          rw [List.mem_singleton] at ho
          rw [ho] at hqs ⊢
          change nf ∣ (ggMultBlockA (m.headD 0 - 1) nf 1).lab.n ∧
            LargeEvenInLambda2 (ggMultBlockA (m.headD 0 - 1) nf 1).lab
          exact ggK1Ak_blockA_arith hnf (by omega) (Or.inl rfl) hqs
        · rw [if_neg htw] at ho
          rw [List.mem_singleton] at ho
          rw [ho] at hqs ⊢
          exact ggK1Ak_blockA_arith hnf (by omega) (Or.inr rfl) hqs
      · rw [if_neg h0] at ho
        simp at ho
    · rw [List.mem_map] at ho
      obtain ⟨j, hj, ho⟩ := ho
      rw [List.mem_filter] at hj
      obtain ⟨-, hj2⟩ := hj
      have hj2' : 2 ≤ m.getD j 0 := (of_decide_eq_true hj2).2
      rw [← ho] at hqs ⊢
      exact ggK1Ak_A2nf_arith hnf (by omega)


end CFSG.StandardType

end
