module
public import CFSG.CharacterTheory.Wreathed.OriginalCoveringLocalFamilySameField
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionPrimeNormalizer

public noncomputable section
open scoped Classical Pointwise
namespace CFSG.Wreathed.OriginalCoveringLocalFamily
open CFSG.Assembly.LowTwoRank FullSylowCoveringObstruction SmallerRecognitionOriginalField
open OriginalCoveringSylowNormalizer OriginalSylowNormalizerWitness
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem original_component_core_forces_trivial_odd_core
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcore : OriginalComponentCoreConclusion n hn S e p f K hSK) : CFSG.oddCore K = ⊥ := by
  let L := SimpleOddIndexQuotient.involutionClosure (K ⧸ CFSG.oddCore K)
  rcases hcore with ⟨hLN, hLne, hmin, huniq, hsimple, hnonabL, hindex,
    hSL, hcent, hcoord, hmodel, hident⟩
  let : L.Normal := hLN
  let : IsSimpleGroup L := hsimple
  exact same_field_simple_odd_index_quotient_trivial_odd_kernel
    hnonab n hn S e hfour p f hp hpodd hf hq hlocal K hSK (CFSG.oddCore K)
    (CFSG.ComponentClassification.OddCore.odd_card K) L hindex hnonabL hmodel


end CFSG.Wreathed.OriginalCoveringLocalFamily
