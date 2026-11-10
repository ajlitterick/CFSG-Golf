module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoordinateClass
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLargeTorusLinear
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXOneSpareTorus
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoordinateCore
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCyclePerm

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix Matrix.ProjGenLinGroup CFSG.Open LinearFlag CFSG.LocalAnalysis.GorensteinLyons
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)

variable {F : Type} [Field F] [Finite F]

theorem conj_injective_projectiveSL {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  obtain ⟨g, rfl⟩ := proj_surjective n F s
  rw [← conjAut_toGL, conjAut_eq_one_iff hn] at hs
  obtain ⟨u, hu⟩ := hs
  have hgu : (g : Matrix (Fin n) (Fin n) F) = scalar (Fin n) (u : F) := by
    have h1 := congrArg (fun M : GL (Fin n) F => (M : Matrix (Fin n) (Fin n) F)) hu
    simpa [GeneralLinearGroup.coe_scalar] using h1
  have hun : u ^ n = 1 := by
    apply Units.ext
    have h1 := g.2
    rw [hgu, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h1
    rw [Units.val_pow_eq_pow_val, h1, Units.val_one]
  exact (QuotientGroup.eq_one_iff g).2 ⟨u, hun, hgu⟩


end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
