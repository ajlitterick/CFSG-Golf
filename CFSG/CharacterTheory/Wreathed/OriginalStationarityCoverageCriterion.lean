module

public import CFSG.CharacterTheory.Wreathed.OriginalSylowCentralizerCoverage
public import CFSG.CharacterTheory.Wreathed.OriginalNonstationaryWreathAction

public noncomputable section
namespace CFSG.Wreathed.OriginalStationarityCoverageCriterion
open CFSG.Wreathed.OriginalSylowNormalizerWitness
open CFSG.Wreathed.OriginalSylowCentralizerCoverage
open CFSG.Wreathed.OriginalNonstationaryWreathAction
open CFSG.Wreathed.OriginalCoveringSylowNormalizer
open scoped Classical Pointwise
universe u v

theorem cyclic_Sylow_two_oddCore_factorization {X : Type u} [Group X] [Finite X]
    (T : Sylow 2 X) (hT : IsCyclic (T : Subgroup X)) :
    CFSG.oddCore X ⊔ (T : Subgroup X) = ⊤ := by
  by_cases heven : Even (Nat.card X)
  · obtain ⟨D, hDchar, hDodd, hDT, hDmem⟩ :=
      CFSG.TwoRankLowerBound.Helpers.exists_characteristic_odd_complement_of_cyclic_sylow_two
        T hT heven
    let : D.Characteristic := hDchar
    have hDle : D ≤ CFSG.oddCore X := le_sSup ⟨inferInstance, hDodd⟩
    have hcorele : CFSG.oddCore X ≤ D := by
      intro d hd
      exact (hDmem d).mpr ((CFSG.ComponentClassification.OddCore.odd_card X).of_dvd_nat
        ((CFSG.oddCore X).orderOf_dvd_natCard hd))
    rw [le_antisymm hcorele hDle]
    exact hDT.sup_eq_top
  · have hodd : Odd (Nat.card X) := Nat.not_even_iff_odd.mp heven
    have hcore : CFSG.oddCore X = ⊤ := by
      apply top_le_iff.mp
      apply le_sSup
      refine ⟨inferInstance, ?_⟩
      simpa only [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).toEquiv]
        using hodd
    rw [hcore, top_sup_eq]


@[expose] def OriginalStationarity {X : Type u} [Group X] {ell : ℕ}
    (N : Subgroup X) (P : Sylow ell (CFSG.oddCore N)) : Prop :=
  ∃ Q : Sylow ell (ambientOddCore (Subgroup.normalizer (ambientSylow N P : Set X))),
    (Q : Subgroup _).map (ambientOddCore
      (Subgroup.normalizer (ambientSylow N P : Set X))).subtype = ambientSylow N P

@[expose] def OriginalCoverage {X : Type u} [Group X] {ell : ℕ}
    (n : ℕ) (S : Sylow 2 X) (e : S ≃* Wreath (2 ^ n))
    (P : Sylow ell (centralizerOddCore n S e)) : Prop :=
  (originalPrimeCentralizer n S e P ⊓
    (CFSG.layer (centralizerOddCoreQuotient n S e)).comap
      (centralizerOddCoreMap n S e)).map (centralizerOddCoreMap n S e) =
        CFSG.layer (centralizerOddCoreQuotient n S e)


variable {G : Type u} [Group G] [Finite G]


@[expose] def OriginalAllPrimeStationarity (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) : Prop :=
  ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) →
    ∃ P : Sylow ell (centralizerOddCore n S e),
      OriginalStationarity (involutionCentralizer n S e) P

@[expose] def OriginalAllPrimeCoverage (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) : Prop :=
  ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) →
    ∃ P : Sylow ell (centralizerOddCore n S e), OriginalCoverage n S e P

@[expose] def OriginalAllPrimeNonsolvableCentralizers (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) : Prop :=
  ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) →
    ∃ P : Sylow ell (centralizerOddCore n S e),
      (S : Subgroup G) ≤ Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G) ∧
      ∃ Q : Sylow ell (ambientOddCore (Subgroup.normalizer
        (ambientSylow (involutionCentralizer n S e) P : Set G))),
        (S : Subgroup G) ≤ Subgroup.normalizer (((Q : Subgroup _).map
          (ambientOddCore (Subgroup.normalizer
            (ambientSylow (involutionCentralizer n S e) P : Set G))).subtype) : Set G) ∧
        ¬ Group.IsSolvable (Subgroup.normalizer
          (ambientSylow (involutionCentralizer n S e) P : Set G) ⊓
            Subgroup.centralizer (((Q : Subgroup _).map (ambientOddCore (Subgroup.normalizer
              (ambientSylow (involutionCentralizer n S e) P : Set G))).subtype) : Set G) :
                Subgroup G)


omit [Finite G] in
theorem original_trivial_oddCore_all_prime_vacuity
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hR : centralizerOddCore n S e = ⊥) :
    OriginalAllPrimeStationarity n S e ∧ OriginalAllPrimeCoverage n S e ∧
      OriginalAllPrimeNonsolvableCentralizers n S e := by
  have hno : ∀ ell : ℕ, ell.Prime → ¬ ell ∣ Nat.card (centralizerOddCore n S e) := by
    intro ell hell hdiv
    have hcard : Nat.card (centralizerOddCore n S e) = 1 := by rw [hR]; simp
    exact hell.not_dvd_one (hcard ▸ hdiv)
  exact ⟨fun ell hell hdiv => (hno ell hell hdiv).elim,
    fun ell hell hdiv => (hno ell hell hdiv).elim,
    fun ell hell hdiv => (hno ell hell hdiv).elim⟩

end CFSG.Wreathed.OriginalStationarityCoverageCriterion
