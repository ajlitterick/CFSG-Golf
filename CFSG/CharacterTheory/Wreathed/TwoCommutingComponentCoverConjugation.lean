module
public import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Wreathed.CentralizerFullQuotient

public noncomputable section
namespace CFSG.Wreathed.TwoCommutingComponentCover
open scoped Classical
universe u v
variable {G : Type u} [Group G]

@[expose] def conjugatedSylow (S : Sylow 2 G) (g : G) : Sylow 2 G := g • S

@[expose] def conjugatedCoordinates {m : ℕ} (S : Sylow 2 G)
    (e : S ≃* Wreath m) (g : G) : conjugatedSylow S g ≃* Wreath m :=
  (S.equivSMul g).symm.trans e


theorem centralizer_map_equiv {H : Type v} [Group H] (phi : G ≃* H) (x : G) :
    (Subgroup.centralizer ({x} : Set G)).map phi.toMonoidHom =
      Subgroup.centralizer ({phi x} : Set H) := by
  ext h
  constructor
  · rintro ⟨a, ha, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change phi a * phi x = phi x * phi a
    simpa only [map_mul] using congrArg phi (Subgroup.mem_centralizer_singleton_iff.mp ha)
  · intro hh
    refine Subgroup.mem_map.mpr ⟨phi.symm h, ?_, phi.apply_symm_apply h⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply phi.injective
    simpa only [map_mul, phi.apply_symm_apply] using
      Subgroup.mem_centralizer_singleton_iff.mp hh

@[expose] def centralizerEquiv {H : Type v} [Group H] (phi : G ≃* H) (x : G) :
    Subgroup.centralizer ({x} : Set G) ≃* Subgroup.centralizer ({phi x} : Set H) :=
  ((Subgroup.centralizer ({x} : Set G)).equivMapOfInjective
    phi.toMonoidHom phi.injective).trans
      (MulEquiv.subgroupCongr (centralizer_map_equiv phi x))


theorem centralizerEquiv_oddCore {H : Type v} [Group H] (phi : G ≃* H) (x : G) :
    (CFSG.oddCore (Subgroup.centralizer ({x} : Set G))).map
      (centralizerEquiv phi x).toMonoidHom =
        CFSG.oddCore (Subgroup.centralizer ({phi x} : Set H)) :=
  CFSG.ComponentClassification.OddCore.equiv_invariant (centralizerEquiv phi x)

@[expose] def reducedCentralizerEquiv {H : Type v} [Group H] (phi : G ≃* H) (x : G) :
    Subgroup.centralizer ({x} : Set G) ⧸ CFSG.oddCore (Subgroup.centralizer ({x} : Set G)) ≃*
      Subgroup.centralizer ({phi x} : Set H) ⧸
        CFSG.oddCore (Subgroup.centralizer ({phi x} : Set H)) :=
  QuotientGroup.congr _ _ (centralizerEquiv phi x) (centralizerEquiv_oddCore phi x)


theorem generalizedFitting_map_equiv {H : Type v} [Group H] (phi : G ≃* H) :
    (CFSG.generalizedFitting G).map phi.toMonoidHom = CFSG.generalizedFitting H :=
  CFSG.WholeGroup.generalizedFitting_map_mulEquiv phi


@[expose] def originalConjugatedReducedEquiv
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G) :
    centralizerOddCoreQuotient n S e ≃*
      centralizerOddCoreQuotient n (conjugatedSylow S g) (conjugatedCoordinates S e g) :=
  reducedCentralizerEquiv (MulAut.conj g) (wreathModelHom S e (Original.x (2 ^ n)))


theorem originalConjugatedReducedEquiv_center [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G) :
    (centralizerFullCenterImage n hn S e).map
      (originalConjugatedReducedEquiv n S e g).toMonoidHom =
        centralizerFullCenterImage n hn (conjugatedSylow S g) (conjugatedCoordinates S e g) := by
  rw [← centralizerOddCoreQuotient_center_eq_fullCenterImage,
    ← centralizerOddCoreQuotient_center_eq_fullCenterImage]
  exact Subgroup.map_center_eq (originalConjugatedReducedEquiv n S e g)

@[expose] def originalConjugatedFullEquiv [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (g : G) :
    centralizerFullQuotient n hn S e ≃*
      centralizerFullQuotient n hn (conjugatedSylow S g) (conjugatedCoordinates S e g) :=
  QuotientGroup.congr _ _ (originalConjugatedReducedEquiv n S e g)
    (originalConjugatedReducedEquiv_center n hn S e g)


end CFSG.Wreathed.TwoCommutingComponentCover

