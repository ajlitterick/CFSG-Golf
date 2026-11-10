module

public import CFSG.CharacterTheory.Wreathed.CentralizerFullQuotient

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u v

variable {G : Type u} [Group G]


@[expose] def centralizerArbitraryResidualImage (n : ℕ)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) :
    Subgroup (centralizerOddCoreQuotient n S e) := K.map (centralizerOddCoreMap n S e)

instance centralizerArbitraryResidualImage_normal (n : ℕ)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] :
    (centralizerArbitraryResidualImage n S e K).Normal :=
  Subgroup.Normal.map inferInstance _ (centralizerOddCoreMap_surjective n S e)


@[expose] def centralizerArbitraryDihedralImage [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) : Subgroup (centralizerFullQuotient n hn S e) :=
  (centralizerArbitraryResidualImage n S e K).map (centralizerFullQuotientMap n hn S e)

instance centralizerArbitraryDihedralImage_normal [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] :
    (centralizerArbitraryDihedralImage n hn S e K).Normal :=
  Subgroup.Normal.map inferInstance _ (centralizerFullQuotientMap_surjective n hn S e)


end CFSG.Wreathed
