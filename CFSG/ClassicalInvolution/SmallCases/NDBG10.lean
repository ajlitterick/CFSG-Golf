module

public import CFSG.ClassicalInvolution.SmallCases.NDBG9Main
public import CFSG.ClassicalInvolution.SmallCases.NDBS1Exo
public import CFSG.ClassicalInvolution.SmallCases.NDBS1Main
import CFSG.ClassicalInvolution.Asc77.AscBSD4
import CFSG.ClassicalInvolution.Asc77.AscBSD10
import CFSG.ClassicalInvolution.Asc77.AscBSE8

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance.Bootstrap

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime]

theorem bootNoTripleD_of_coverXW (hcov : BootShapeCoverX p f)
    (hexo : Asc77.FrameExistsOnE p f (ExoticNoTwinPred p f)) : Disconnected.BootNoTripleD p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hdata hT
  refine S1.exact_p1_of_frames hnab hp2 hq hz hBelow hconn fun L hL w hw hnot => ?_
  have e := conjClass_eq_of_mem hL
  rw [← e] at hconn hdata hT hnot ⊢
  rcases hcov G hnab hp2 hq L w hw hBelow hconn hdata hT with hs | hs | hs | hs
  · exact chainFrames_noTriple G hnab hp2 hq L w hw hBelow hconn ⟨hs, hT⟩
  · exact twinFrames_weak G hnab hp2 hq L w hw hBelow hconn hs
  · exact absurd hs hnot
  · exact hexo G hnab hp2 hq L w hw hBelow hconn hs

end CFSG.ClassicalInvolution.NDB
