module

public import CFSG.Quasithin.Recognition.St84.Sec5CaseA
public import CFSG.Quasithin.Recognition.St84.Sec5CaseB
public import CFSG.Quasithin.Recognition.St84.Sec5CaseC
public import CFSG.Quasithin.Recognition.St84.HigmanQuadProof

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s n₀ : ℕ}

namespace Setup

theorem sec5_trichotomy (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    (n₀ = 2 ∧ s = 5 ∧ Y.swap.TreeU42Data) ∨ (s = 7 ∧ Y.TreeD4Data n₀) ∨
      (n₀ = 2 ∧ s = 5 ∧ Y.swap.TreeJ2Data ∧ Y.J2Arc) := by
  obtain ⟨r, -, -, hr⟩ := exists_isMaxRegLen Y H
  by_cases hZ : Y.Zt 0 = ⊥
  · obtain ⟨-, -, -, hcase⟩ := s52_step11 Y H hZ hr
    rcases hcase with ⟨h7, -⟩ | ⟨h5, -⟩
    · exact Or.inr (Or.inl ⟨h7, treeD4_of_caseB Y H hZ h7⟩)
    · obtain ⟨hn, -⟩ := caseC_n Y H hZ h5
      exact Or.inr (Or.inr ⟨hn, h5, treeJ2_of_caseC Y H hZ h5, j2Arc_of_five Y H hZ h5⟩)
  · exact Or.inl (treeU42_of_caseA Y H hZ (higmanQuad n₀))


theorem sec5_two (Y : Setup Γ G) (H : Y.Sec5Hyp s 2) :
    s = 5 ∧ (Y.swap.TreeU42Data ∨ (Y.swap.TreeJ2Data ∧ Y.J2Arc)) := by
  rcases sec5_trichotomy Y H with ⟨-, h5, hU⟩ | ⟨-, hD⟩ | ⟨-, h5, hJ, hJArc⟩
  · exact ⟨h5, Or.inl hU⟩
  · exact hD.false_of_two.elim
  · exact ⟨h5, Or.inr ⟨hJ, hJArc⟩⟩

end Setup

theorem sec5_S3A5_univ_odd (hc : CharTwoStab (V := V) (G := G))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (Y : Setup Γ G) (hY0 : Y.n 0 = 1) (hY1 : Y.n 1 = 2)
    (hGT : Odd (Nat.card Y.GT)) :
    s = 5 ∧ (Y.TreeU42Data ∨ Y.TreeJ2Data) := by
  have H : Y.swap.Sec5Hyp s 2 :=
    ⟨hc, le_rfl, by rw [Setup.swap_n]; simpa using hY1,
      by rw [Setup.swap_n]; simpa using hY0, hs, hodd, h5, by rw [Setup.swap_GT]; exact hGT⟩
  obtain ⟨h5', hU | ⟨hJ, -⟩⟩ := Setup.sec5_two Y.swap H
  · exact ⟨h5', Or.inl (Setup.TreeU42Data.congr (X := Y.swap.swap) (Y := Y)
      (by simp) (by simp) hU)⟩
  · exact ⟨h5', Or.inr (Setup.TreeJ2Data.congr (X := Y.swap.swap) (Y := Y)
      (by simp) (by simp) hJ)⟩


theorem sec5_S3A5_univ (hc : CharTwoStab (V := V) (G := G))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (h6 : ∀ X : Setup Γ G, ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s →
      Even (Nat.card X.GT) → False)
    (Y : Setup Γ G) (hY0 : Y.n 0 = 1) (hY1 : Y.n 1 = 2) :
    s = 5 ∧ (Y.TreeU42Data ∨ Y.TreeJ2Data) := by
  rcases Nat.even_or_odd (Nat.card Y.GT) with hEven | hOdd
  · exfalso
    obtain ⟨o, ho, -⟩ := exists_odd_orbit Y.hyp.isTree Y.hyp.adj_smul
      (fun v x y hx hy => Y.hyp.locTrans hx hy) Y.hyp.edgeTrans Y.hyp.preservesParts hs hodd
    rcases Nat.even_or_odd (Γ.dist o (Y.vert 0)) with hd0 | hd0
    · have hend : Odd (Γ.dist o (Y.vert (s : ℤ))) := Y.odd_dist_vert_of_even o hodd hd0
      have hX : ¬ RightTransitive Γ G (Y.line.arc 0 s).vert 0 s :=
        (ho s le_rfl (Y.line.arc 0 s)).1 (by simpa [Line.arc] using hend)
      exact h6 Y hX hEven
    · have hend : Odd (Γ.dist o (Y.vert ((s : ℤ) + 1))) :=
        Y.odd_dist_vert_succ_of_odd o hodd hd0
      have hX : ¬ RightTransitive Γ G ((Y.shift 1).line.arc 0 s).vert 0 s :=
        (ho s le_rfl ((Y.shift 1).line.arc 0 s)).1
          (by simpa [Line.arc] using hend)
      exact h6 (Y.shift 1) hX (by simpa [Setup.shift_GT] using hEven)
  · exact sec5_S3A5_univ_odd hc hs hodd h5 Y hY0 hY1 hOdd

end CFSG.Quasithin.St84
