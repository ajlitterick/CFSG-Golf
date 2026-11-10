module
public import CFSG.CharacterTheory.Wreathed.TwoCommutingComponentCoverConjugation
public import CFSG.CharacterTheory.Wreathed.ComponentCoveringLocalQuotient

public noncomputable section
namespace CFSG.Wreathed.TwoCommutingComponentCover
open scoped Classical
universe u
variable {G : Type u} [Group G]

theorem originalConjugatedFullEquiv_simpleLayer [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G) :
    (centralizerSimpleLayer n hn S e).map (originalConjugatedFullEquiv n hn S e g).toMonoidHom =
      centralizerSimpleLayer n hn (conjugatedSylow S g) (conjugatedCoordinates S e g) :=
  generalizedFitting_map_equiv _

@[expose] def originalConjugatedSimpleLayerEquiv [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G) :
    centralizerSimpleLayer n hn S e ≃*
      centralizerSimpleLayer n hn (conjugatedSylow S g) (conjugatedCoordinates S e g) :=
  ((originalConjugatedFullEquiv n hn S e g).subgroupMap (centralizerSimpleLayer n hn S e)).trans
    (MulEquiv.subgroupCongr (originalConjugatedFullEquiv_simpleLayer n hn S e g))


theorem original_conjugated_nonSym4 [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) (g : G) :
    ¬ Nonempty (centralizerFullQuotient n hn (conjugatedSylow S g)
      (conjugatedCoordinates S e g) ≃* Equiv.Perm (Fin 4)) := by
  rintro ⟨a⟩
  exact hfour ⟨(originalConjugatedFullEquiv n hn S e g).trans a⟩

theorem original_conjugated_same_PSL2_model
    {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) (g : G) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn (conjugatedSylow S g) (conjugatedCoordinates S e g))
        .PSL 2 p f := by
  rcases hmodel with ⟨hadm, F, hF, hfinite, hcard, ⟨a⟩⟩
  exact ⟨hadm, F, hF, hfinite, hcard,
    ⟨(originalConjugatedSimpleLayerEquiv n hn S e g).symm.trans a⟩⟩

theorem original_involution_conjugator [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (y : G) (hy : orderOf y = 2) :
    ∃ g : G, wreathModelHom (conjugatedSylow S g) (conjugatedCoordinates S e g)
      (Original.x (2 ^ n)) = y := by
  have hx : orderOf (wreathModelHom S e (Original.x (2 ^ n))) = 2 :=
    (orderOf_injective _ (wreathModelHom_injective S e) _).trans
      (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (all_involutions_conjugate_of_simple_wreathed hnonab n hn S e _ y hx hy)
  exact ⟨g, hg⟩


@[expose] def actualReducedCentralizer (y : G) : Type u :=
  Subgroup.centralizer ({y} : Set G) ⧸ CFSG.oddCore (Subgroup.centralizer ({y} : Set G))

instance actualReducedCentralizerGroup (y : G) : Group (actualReducedCentralizer y) :=
  inferInstanceAs (Group (Subgroup.centralizer ({y} : Set G) ⧸
    CFSG.oddCore (Subgroup.centralizer ({y} : Set G))))

instance actualReducedCentralizerFinite [Finite G] (y : G) :
    Finite (actualReducedCentralizer y) :=
  inferInstanceAs (Finite (Subgroup.centralizer ({y} : Set G) ⧸
    CFSG.oddCore (Subgroup.centralizer ({y} : Set G))))


end CFSG.Wreathed.TwoCommutingComponentCover

