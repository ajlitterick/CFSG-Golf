module

public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.J1ModelTransport

public noncomputable section

namespace CFSG.Open

open Matrix
open scoped MatrixGroups


theorem goldschmidtJ1_matrix_generators_eq :
    ({goldschmidtJ1GenA, goldschmidtJ1GenB} :
      Set (Matrix (Fin 7) (Fin 7) (ZMod 11))) = properTwoGenCoreJ1Gens := rfl

theorem goldschmidtJ1_gl_generators_eq :
    {g : GL (Fin 7) (ZMod 11) |
      (g : Matrix (Fin 7) (Fin 7) (ZMod 11)) = goldschmidtJ1GenA ∨
      (g : Matrix (Fin 7) (Fin 7) (ZMod 11)) = goldschmidtJ1GenB} =
    {g : GL (Fin 7) (ZMod 11) |
      (g : Matrix (Fin 7) (Fin 7) (ZMod 11)) ∈ properTwoGenCoreJ1Gens} := by
  ext g
  rw [← goldschmidtJ1_matrix_generators_eq]
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]

theorem goldschmidtJ1_eq_properTwoGenCoreJ1 :
    goldschmidtJ1 = properTwoGenCoreJ1 := by
  unfold goldschmidtJ1 properTwoGenCoreJ1
  rw [goldschmidtJ1_gl_generators_eq]

@[expose] def goldschmidtJ1_exact_model_equiv :
    goldschmidtJ1 ≃* CFSG.Blueprint.NativeSporadic.J1 :=
  (MulEquiv.subgroupCongr goldschmidtJ1_eq_properTwoGenCoreJ1).trans
    CFSG.ProperTwoGeneratedCore.j1_exact_model_equiv

theorem goldschmidtJ1_iso_iff_native {L : Type} [Group L] :
    Nonempty (L ≃* goldschmidtJ1) ↔ CFSG.Blueprint.NativeSporadic.IsSporadic L .J1 := by
  change Nonempty (L ≃* goldschmidtJ1) ↔
    Nonempty (L ≃* CFSG.Blueprint.NativeSporadic.J1)
  constructor
  · rintro ⟨e⟩
    exact ⟨e.trans goldschmidtJ1_exact_model_equiv⟩
  · rintro ⟨e⟩
    exact ⟨e.trans goldschmidtJ1_exact_model_equiv.symm⟩


end CFSG.Open
