module

public import CFSG.CharacterTheory.Semidihedral.LocalCoverFactorization

public noncomputable section

namespace CFSG.Semidihedral.LocalSylowNormalizerFactorization

open CFSG.Open
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.StationaryOddLocalization
open CFSG.Semidihedral.LocalCoverFactorization
open CFSG.Wreathed.OriginalSylowNormalizerWitness

universe u

@[expose] def localSylowInCentralizer {G : Type u} [Group G] (t : G) {ell : ℕ}
    (P : Sylow ell (N t)) : Subgroup (C t) :=
  (P : Subgroup (N t)).map (N t).subtype

@[expose] def localSylowAmbient {G : Type u} [Group G] (t : G) {ell : ℕ}
    (P : Sylow ell (N t)) : Subgroup G :=
  (localSylowInCentralizer t P).map (C t).subtype

@[expose] def localSylowNormalizer {G : Type u} [Group G] (t : G) {ell : ℕ}
    (P : Sylow ell (N t)) : Subgroup G :=
  Subgroup.normalizer (localSylowAmbient t P : Set G)

theorem local_sylow_normalizer_in_original_centralizer
    {G : Type u} [Group G] (t : G) {ell : ℕ} (P : Sylow ell (N t)) :
    (localSylowNormalizer t P).subgroupOf (C t) =
      Subgroup.normalizer (localSylowInCentralizer t P : Set (C t)) := by
  change (Subgroup.normalizer
    ((localSylowInCentralizer t P).map (C t).subtype : Set G)).comap (C t).subtype = _
  rw [Subgroup.comap_normalizer_eq_of_le_range
    ((Subgroup.map_subtype_le _).trans_eq (C t).range_subtype.symm),
    Subgroup.comap_map_eq_self_of_injective (C t).subtype_injective]


end CFSG.Semidihedral.LocalSylowNormalizerFactorization
