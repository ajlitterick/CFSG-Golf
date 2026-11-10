module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerSubgroups
public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantCentralizerImages

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

noncomputable def mappedSignalizer {G : Type u} {H : Type v} [Group G] [Group H]
    (homomorphism : G →* H) (actor : Subgroup G) (signalizer : G → Subgroup G) : H → Subgroup H :=
  fun target => ⨆ (preimage : G) (_ : preimage ∈ actor) (_ : homomorphism preimage = target),
    (signalizer preimage).map homomorphism

theorem mappedSignalizer_apply_eq {G : Type u} {H : Type v} [Group G] [Group H]
    (homomorphism : G →* H) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hinjective : Set.InjOn homomorphism (actor : Set G))
    (element : G) (hmem : element ∈ actor) :
    mappedSignalizer homomorphism actor signalizer (homomorphism element) =
      (signalizer element).map homomorphism := by
  apply le_antisymm
  · apply iSup_le
    intro preimage
    apply iSup_le
    intro hpreimage
    apply iSup_le
    intro heq
    have hequal : preimage = element := hinjective hpreimage hmem heq
    rw [hequal]
  · exact le_iSup_of_le element (le_iSup_of_le hmem (le_iSup_of_le rfl le_rfl))

theorem map_conjugate_subgroup_eq {G : Type u} {H : Type v} [Group G] [Group H]
    (homomorphism : G →* H) (subgroup : Subgroup G) (element : G) :
    (subgroup.map (MulAut.conj element).toMonoidHom).map homomorphism =
      (subgroup.map homomorphism).map (MulAut.conj (homomorphism element)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext member
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]


theorem SignalizerCompatible.map {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (actor : Subgroup G) (signalizer : G → Subgroup G) (hpgroup : IsPGroup prime actor)
    (hinjective : Set.InjOn homomorphism (actor : Set G)) (subgroup : Subgroup G)
    (hcompatible : SignalizerCompatible prime actor signalizer subgroup) :
    SignalizerCompatible prime (actor.map homomorphism)
      (mappedSignalizer homomorphism actor signalizer) (subgroup.map homomorphism) := by
  have : Group.IsSolvable subgroup := hcompatible.solvable
  refine ⟨?_, Group.isSolvable_of_surjective (f := homomorphism.subgroupMap subgroup)
    (homomorphism.subgroupMap_surjective subgroup),
    fun hdiv => hcompatible.primeComplement (hdiv.trans (Subgroup.card_map_dvd _ _)), ?_⟩
  · apply Subgroup.le_normalizer_iff.mpr
    rintro member ⟨memberPreimage, hmemberPreimage, rfl⟩ element ⟨preimage, hpreimage, rfl⟩
    have hconjugate := Subgroup.le_normalizer_iff.mp hcompatible.normalized
      memberPreimage hmemberPreimage preimage hpreimage
    have hmapped := Subgroup.mem_map_of_mem homomorphism hconjugate
    simpa only [map_mul, map_inv] using hmapped
  · intro element helement hne
    obtain ⟨preimage, hpreimage, rfl⟩ := helement
    have hpreimageNe : preimage ≠ 1 := fun heq => hne (heq ▸ map_one homomorphism)
    rw [mappedSignalizer_apply_eq homomorphism actor signalizer hinjective preimage hpreimage,
      ← normalized_prime_complement_singleton_centralizer_map_eq prime hprime homomorphism
        actor subgroup hpgroup hcompatible.primeComplement hcompatible.normalized preimage hpreimage]
    exact Subgroup.map_mono (hcompatible.fixed_le preimage hpreimage hpreimageNe)

end CFSG.RankThreeEvenClassification.Helpers
