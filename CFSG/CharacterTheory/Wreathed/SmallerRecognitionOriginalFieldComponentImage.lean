module

public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldReducedImage
public import CFSG.CharacterTheory.Wreathed.ComponentCoveringLocalQuotient

public noncomputable section
namespace CFSG.Wreathed.SmallerRecognitionOriginalField
open ComponentCoveringLocal FullSylowCoveringObstruction ReducedCentralizerInclusion
open SimpleOddIndexQuotient
open scoped Classical
variable {G : Type} [Group G] [Finite G]

@[expose] def componentCentralizerReducedIntersectionEquiv (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    Subgroup.centralizer {coveringInvolution n S e K hSK} ⧸
      CFSG.oddCore (Subgroup.centralizer {coveringInvolution n S e K hSK}) ≃*
      originalCentralizerSubgroup n S e K ⧸
        CFSG.oddCore (originalCentralizerSubgroup n S e K) :=
  QuotientGroup.congr _ _ (coveringCentralizerIntersectionEquiv n S e K hSK)
    (CFSG.ComponentClassification.OddCore.equiv_invariant
      (coveringCentralizerIntersectionEquiv n S e K hSK))


@[expose] def componentCentralizerReducedImageEquiv (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hnormal : (originalImage n S e K).Normal) :
    Subgroup.centralizer {coveringInvolution n S e K hSK} ⧸
      CFSG.oddCore (Subgroup.centralizer {coveringInvolution n S e K hSK}) ≃*
        originalImage n S e K :=
  (componentCentralizerReducedIntersectionEquiv n S e K hSK).trans
    (Classical.choose (original_centralizer_odd_core_quotient_equiv n S e K hnormal))


@[expose] def componentSimpleReducedCentralizerImage
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hnormal : (originalImage n S e K).Normal)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index) :
    coveringSimpleReducedCentralizer n hn S e K hSK L hodd →* originalImage n S e K :=
  reducedCentralizerImageInclusion (CFSG.oddCore K) (actual_oddCore_odd K) L hodd
    (coveringInvolution n S e K hSK) (coveringInvolution_order n hn S e K hSK)
    (originalImage n S e K) (componentCentralizerReducedImageEquiv n S e K hSK hnormal)


@[expose] def componentSimpleReducedCentralizerInclusion
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hnormal : (originalImage n S e K).Normal)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index) :
    coveringSimpleReducedCentralizer n hn S e K hSK L hodd →*
      centralizerOddCoreQuotient n S e :=
  (originalImage n S e K).subtype.comp
    (componentSimpleReducedCentralizerImage n hn S e K hSK hnormal L hodd)


end CFSG.Wreathed.SmallerRecognitionOriginalField
