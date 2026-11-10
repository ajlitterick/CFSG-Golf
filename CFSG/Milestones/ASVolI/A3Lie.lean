module

public import CFSG.Milestones.ASVolI.A3
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner

public section

namespace CFSG.ASVolI

open CFSG.Open
open CFSG.ASVolI.ChA
open scoped Pointwise MatrixGroups

noncomputable def burnsideA315h_e (F : Type) [Field F] :
    PSL(3, F) ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
  CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F

theorem burnsideA315h_e_mk (F : Type) [Field F] (s : SL(3, F)) :
    burnsideA315h_e F (QuotientGroup.mk s) = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F s := by
  unfold burnsideA315h_e
  exact QuotientGroup.quotientMulEquivOfEq_mk _ s

theorem burnsideA315h_e_symm_proj (F : Type) [Field F] (s : SL(3, F)) :
    (burnsideA315h_e F).symm (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F s) =
      QuotientGroup.mk s := by
  rw [MulEquiv.symm_apply_eq, burnsideA315h_e_mk]

theorem burnsideA315h_pslOfSL_mk {F : Type} [Field F] (e : SL(3, F) ≃* SL(3, F)) (s : SL(3, F)) :
    pslOfSL e (QuotientGroup.mk s) = QuotientGroup.mk (e s) :=
  QuotientGroup.congr_mk' _ _ _ _ s

noncomputable def burnsideA315h_Phi (F : Type) [Field F] :
    MulAut PSL(3, F) ≃* MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
  MulAut.congr (burnsideA315h_e F)

theorem burnsideA315h_Phi_apply_proj (F : Type) [Field F] (α : MulAut PSL(3, F)) (s : SL(3, F)) :
    burnsideA315h_Phi F α (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F s) =
      burnsideA315h_e F (α (QuotientGroup.mk s)) := by
  unfold burnsideA315h_Phi
  show burnsideA315h_e F (α ((burnsideA315h_e F).symm _)) = _
  rw [burnsideA315h_e_symm_proj]

theorem burnsideA315h_Phi_diag (F : Type) [Field F] (g : GL (Fin 3) F) :
    burnsideA315h_Phi F (psl3DiagAut g) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 F g := by
  ext x
  obtain ⟨s, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 F x
  rw [burnsideA315h_Phi_apply_proj, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj]
  unfold psl3DiagAut
  rw [burnsideA315h_pslOfSL_mk, burnsideA315h_e_mk]
  have h : slConj g s = CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
      3 F g s := by
    apply Subtype.ext
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix]
    rfl
  rw [h]

theorem burnsideA315h_Phi_field (F : Type) [Field F] (σ : RingAut F) :
    burnsideA315h_Phi F (psl3FieldAut σ) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut 3 F σ := by
  ext x
  obtain ⟨s, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 F x
  rw [burnsideA315h_Phi_apply_proj, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut_proj]
  unfold psl3FieldAut
  rw [burnsideA315h_pslOfSL_mk, burnsideA315h_e_mk]
  rfl

theorem burnsideA315h_Phi_graph (F : Type) [Field F] :
    burnsideA315h_Phi F psl3GraphAut =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut 3 F := by
  ext x
  obtain ⟨s, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 F x
  rw [burnsideA315h_Phi_apply_proj, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut_proj]
  unfold psl3GraphAut
  rw [burnsideA315h_pslOfSL_mk, burnsideA315h_e_mk]
  rfl


theorem burnsideA315h_diag_one (F : Type) [Field F] : psl3DiagAut (1 : GL (Fin 3) F) = 1 := by
  apply (burnsideA315h_Phi F).injective
  rw [burnsideA315h_Phi_diag, map_one, map_one]

theorem burnsideA315h_diag_mul {F : Type} [Field F] (g h : GL (Fin 3) F) :
    psl3DiagAut (g * h) = psl3DiagAut g * psl3DiagAut h := by
  apply (burnsideA315h_Phi F).injective
  simp only [map_mul, burnsideA315h_Phi_diag]

theorem burnsideA315h_field_one (F : Type) [Field F] : psl3FieldAut (1 : RingAut F) = 1 := by
  apply (burnsideA315h_Phi F).injective
  rw [burnsideA315h_Phi_field, map_one, map_one]


theorem burnsideA315h_graph_diag {F : Type} [Field F] (g : GL (Fin 3) F) :
    psl3GraphAut * psl3DiagAut g * psl3GraphAut =
      psl3DiagAut (Matrix.GeneralLinearGroup.inverseTranspose g) := by
  apply (burnsideA315h_Phi F).injective
  simp only [map_mul, burnsideA315h_Phi_graph, burnsideA315h_Phi_diag]
  exact (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.standard_automorphism_transport
    (K := F) (n := 3)).2.2.2.2.1 g


theorem burnsideA315h_classification {F : Type} [Field F] [Finite F] (α : MulAut PSL(3, F)) :
    ∃ (g : GL (Fin 3) F) (σ : RingAut F) (ε : ℕ), ε ≤ 1 ∧
      α = psl3DiagAut g * psl3FieldAut σ * psl3GraphAut ^ ε := by
  obtain ⟨g, σ, ε, hε, h⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation (K := F) (n := 3)
      le_rfl).2 (burnsideA315h_Phi F α)
  refine ⟨g, σ, ε, hε, ?_⟩
  apply (burnsideA315h_Phi F).injective
  rw [h]
  simp only [map_mul, map_pow, burnsideA315h_Phi_diag, burnsideA315h_Phi_field,
    burnsideA315h_Phi_graph]


theorem burnsideA315h_diagfield_eq_one {F : Type} [Field F] [Finite F] {g : GL (Fin 3) F}
    {σ : RingAut F} (h : psl3DiagAut g * psl3FieldAut σ = 1) :
    σ = 1 ∧ ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c = g := by
  have h' := congrArg (burnsideA315h_Phi F) h
  simp only [map_mul, burnsideA315h_Phi_diag, burnsideA315h_Phi_field, map_one] at h'
  exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one
    le_rfl g σ h'


end CFSG.ASVolI

