module

public import CFSG.ClassicalInvolution.RouteD.ExoticSingleSplit
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleGeom
public import CFSG.ClassicalInvolution.RouteD.GapsToralB

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

@[expose] def OddTwinFixed (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ n, n = 3 → 5 ≤ p ^ f → StatedLieAdmissible .POmegaOdd n p f →
    FundTwinFixed (modelFund p f .POmegaOdd n)

theorem rowSingleOddSmall_of_fixed (h : OddTwinFixed p f) : RowPiece p f ShapeSingleOddSmall := by
  intro a t n hs G _ _ _ _ K z S hshape
  obtain ⟨rfl, rfl, hn34⟩ := hs
  exfalso
  obtain ⟨-, hadm⟩ := admissible_of_localShapeT hshape (by decide)
  have hn : 3 ≤ n := hadm.2.2.1
  have hY := yData_odd hn hadm (by have := S.five; omega)
  have hd := (hshape.nonempty_dictT hY.ne_d4 hY.sc S.inClass (mem_conjClass_self K) S.cls).some
  let c : ETCtx p f .POmegaOdd n (conjClass K) K z :=
    { hp2 := S.odd, hq := S.five, hΩ := S.inClass, hex := S.exact, hK := mem_conjClass_self K,
      hz := S.cls, hP1 := S.p1, d := hd,
      hF := CFSG.ClassicalInvolution.RouteD.oddCoverSL3_of_five_le S.five, hY := hY }
  exact false_of_twin_fixed c (single_class K) hshape (nonempty_fund_odd hn)
    (Gaps.range_le_iSup_fund_odd hn hadm hY.std c.d.ψ) (oddTwinsExist S.odd S.five hadm)
    (oddHubUnique S.odd S.five hadm) (h n hn34 S.five hadm)

end CFSG.ClassicalInvolution.RouteD.Exotic
