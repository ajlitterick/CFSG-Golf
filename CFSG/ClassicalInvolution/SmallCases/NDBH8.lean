module

public import CFSG.ClassicalInvolution.SmallCases.NDBH7
public import CFSG.ClassicalInvolution.SmallCases.NDBH2T5
public import CFSG.ClassicalInvolution.SmallCases.NDBH3T6
public import CFSG.ClassicalInvolution.SmallCases.NDBH3T1

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {p f : ℕ} [Fact p.Prime]

theorem noAllA1NarrowNT_of (h₁ : NDBH.NarrowKxN p f) (h₂ : NarrowTriangle p f) :
    NoAllA1NarrowNT p f :=
  fun G _ _ _ hnab hp2 hq K z hz hBelow hconn hno D hall N hN n hn hnz =>
    ⟨h₁ G hnab hp2 hq K z hz hBelow hconn hno D hall N hN n hn hnz,
      h₂ G hnab hp2 hq K z hz hBelow hconn hno D hall N hN n hn hnz⟩

theorem noAllA1Narrow_of_triangleA2 (hR : TriangleA2Partner p f) : NoAllA1Narrow p f :=
  noAllA1Narrow_of_nt (noAllA1NarrowNT_of NDBH.narrowKxN_holds (triangle_false_of_residual hR))

theorem noDataBootD_of_triangleA2 (hR : TriangleA2Partner p f) : SmallConn.NoDataBootD p f :=
  noDataBootD_of_narrowA (noAllA1Narrow_of_triangleA2 hR)

theorem bootNoTripleD_of_triangleA2 (hR : TriangleA2Partner p f) :
    Disconnected.BootNoTripleD p f :=
  bootNoTripleD_of_narrowA (noAllA1Narrow_of_triangleA2 hR)

end CFSG.ClassicalInvolution.NDB
