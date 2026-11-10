module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ReducedProjection
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalBlockDefects

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers


theorem brauerCorr_of_scalar_congr (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] (subgroup overgroup : Subgroup G)
    (hnormalizer : overgroup ≤ Subgroup.normalizer (subgroup : Set G))
    {block : Set (G → ℂ)} {localBlock : Set (overgroup → ℂ)}
    (hblock : BlocksIsBlock m G block) (hlocalBlock : BlocksIsBlock m overgroup localBlock)
    {character : G → ℂ} {localCharacter : overgroup → ℂ}
    (hcharacter : character ∈ block) (hlocalCharacter : localCharacter ∈ localBlock)
    (hcongr : ∀ coefficients : G → ℂ, BlocksIsCentralR m coefficients →
      BlocksCentralChar character coefficients -
        BlocksCentralChar localCharacter (BlocksBrauerProj subgroup overgroup coefficients) ∈
          BlocksLocalMaxIdeal m) :
    BlocksBrauerCorr m subgroup overgroup localBlock block := by
  intro coefficients hcoefficients left hleft right hright
  have hleftScalar := block_centralChar_congr m hm G hblock hcharacter hleft hcoefficients
  have hrightScalar := block_centralChar_congr m hm overgroup hlocalBlock hlocalCharacter hright
    (brauerProj_central m hm subgroup overgroup hnormalizer hcoefficients)
  have hnegative := localMaxIdeal_neg m hrightScalar
  have hnegative' : BlocksCentralChar localCharacter (BlocksBrauerProj subgroup overgroup coefficients) -
      BlocksCentralChar right (BlocksBrauerProj subgroup overgroup coefficients) ∈ BlocksLocalMaxIdeal m := by
    simpa only [neg_sub] using hnegative
  exact localMaxIdeal_trans m hm
    (localMaxIdeal_trans m hm hleftScalar (hcongr coefficients hcoefficients)) hnegative'


end CFSG.BrauerThirdMainTheorem.Helpers
