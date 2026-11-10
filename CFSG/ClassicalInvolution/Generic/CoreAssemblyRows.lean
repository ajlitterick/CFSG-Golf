module

public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
public import CFSG.ClassicalInvolution.RouteD.TypeAChain
public import CFSG.ClassicalInvolution.RouteD.TypeCMain
public import CFSG.ClassicalInvolution.RouteD.TypeDRecognition
public import CFSG.ClassicalInvolution.Balance.PassTwoConj

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

theorem oddCoverSL3_of_five_le (hq : 5 ≤ p ^ f) : OddCoverSL3 (GaloisField p f) := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  exact CFSG.ClassicalInvolution.ModelFacts.OddCover.noCover_odd_sl3.{0} (GaloisField.card p f hf)
    hq

theorem pieceSL7 : PieceSL7 p f := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, hn⟩ := hshape
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨D, -, -⟩ := routeD_typeA S.odd S.five (m := m) (by omega) S.inClass S.exact
    (mem_conjClass_self K) (single_class K) S.conn S.cls (localShapeA_of_T hS) S.p1
    (oddCoverSL3_of_five_le S.five)
  exact ⟨D⟩


theorem pieceSp4_of_pieces (h1 : PieceSp4P1 p f) (h2 : PieceSp4NoOther p f) :
    RowPiece p f ShapeSp4 := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, hn⟩ := hshape
  have hC : CSetupAll p f n (conjClass K) K z :=
    { odd := S.odd, five := S.five, three := by omega, inClass := S.inClass, exact := S.exact,
      mem := mem_conjClass_self K, cls := S.cls, single := single_class K,
      centerTriv := center_eq_bot hnab, shape := localShapeC_of_T hS,
      p1cl := fun _ _ y hy => h1 G hnab K z S n hn hS y hy.orderOf_eq_two, ih := S.ih,
      p1 := h1 G hnab K z S n hn hS, noOther := h2 G hnab K z S n hn hS }
  obtain ⟨D, -, -⟩ := routeD_typeC hC S.conn
  exact ⟨D⟩

theorem pieceSp4 : RowPiece p f ShapeSp4 := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, hn⟩ := hshape
  have hC : CSetup p f n (conjClass K) K z :=
    { odd := S.odd, five := S.five, three := by omega, inClass := S.inClass, exact := S.exact,
      mem := mem_conjClass_self K, cls := S.cls, single := single_class K,
      centerTriv := center_eq_bot hnab, shape := localShapeC_of_T hS,
      p1cl := Balance.localOddCentral_of_classicalMember S.odd (pos_of_five_le S.five) S.inClass
        ⟨K, mem_conjClass_self K, single_class K⟩ (mem_conjClass_self K) S.cls S.p1,
      ih := S.ih }
  obtain ⟨D, -, -⟩ := routeD_typeC_of_four hC hn S.conn
  exact ⟨D⟩

theorem pieceTwinD_of_chain (h : ChainPieceTwinD p f) : RowPiece p f ShapeTwinD := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, hn⟩ := hshape
  have hn' : n + 2 - 2 = n := by omega
  have hS' : LocalShapeT p f 2 .POmegaPlus (n + 2 - 2) (conjClass K) z := by rw [hn']; exact hS
  obtain ⟨U, hUΩ, hcomm, hpair⟩ := h G hnab K z S (n + 2) (by omega) hS'
  obtain ⟨D, -, -⟩ := routeD_typeD_of_chain S.odd S.five (n := n + 2) (by omega) S.inClass
    (mem_conjClass_self K) (single_class K) S.conn S.cls hS' S.p1 U hUΩ hcomm hpair
  exact ⟨D⟩

section Small


end Small

end CFSG.ClassicalInvolution.Generic.CoreAssembly
