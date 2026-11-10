module

public import CFSG.LocalAnalysis.StandardType.GGSelectedPSUModel
public import CFSG.LocalAnalysis.StandardType.GGSelectedModelOfChevalley
public import CFSG.LocalAnalysis.StandardType.GGCompatNbrSomeDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPSU

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.LieType.Steinberg CFSG.StandardType.ClassicalPosition
open CFSG.StandardType.SelectedRoot CFSG.StandardType.SelectedRoot.SelPSU
open Matrix

namespace SelectedRoot

theorem exists_selectedModel_PSU_chart_rootPair_at
    {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (i : Fin n) (hi : i ≠ Fin.rev i) :
    ∃ model : SelectedSL2Model (Unitary.rootDatum hF n) (fixedSubfield F 2 f)
        (InnerDiagSU.twoWtRoot n i),
      model.phi.range = (Unitary.rootDatum hF n).rootGroup
          (InnerDiagSU.twoWtRoot n i) ⊔
        (Unitary.rootDatum hF n).rootGroup (-InnerDiagSU.twoWtRoot n i) ∧
      ∀ A : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F 2 f),
        (((model.phi A : SU (unitaryInvolution F 2 f) n) : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) =
          embM (pairCoord i)
            ((fixedSubfield F 2 f).subtype.mapMatrix (A : Matrix (Fin 2) (Fin 2) _)) := by
  classical
  let γ : Fin (Unitary.rootDatum hF n).rank → ℤ := InnerDiagSU.twoWtRoot n i
  let σ := unitaryInvolution F 2 f
  let k := fixedSubfield F 2 f
  have hσ : ∀ c : F, σ (σ c) = c := unitaryInvolution_involutive hF
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hk : ∀ c ∈ k, σ c = c := fun c hc => mem_fixedSubfield.mp hc
  have hrev : Fin.rev i ≠ Fin.rev (Fin.rev i) := by
    rw [Fin.rev_rev]
    exact hi.symm
  have hneg : toStd n (-γ) = 2 • weight n (Fin.rev i) :=
    toStd_neg_eq_two_weight_rev (InnerDiagSU.toStd_twoWtRoot i)
  obtain ⟨model, hmat⟩ := exists_selectedModel_PSU_chart_twoWt_at hF i hi
  have hphi : ∀ A, model.phi A =
      chart σ k (pairCoord_injective hi) (pairCoord_rev i) h2 hk A := by
    intro A
    apply Subtype.ext
    apply Units.ext
    exact hmat A
  have hlow : Set.range (fun t : k => model.phi (sl2Lower t)) =
      ((Unitary.rootDatum hF n).rootGroup (-γ) : Set (SU σ n)) := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      change model.phi (sl2Lower t) ∈ (Unitary.rootDatum hF n).rootGroup (-γ)
      rw [hphi, chart_lower σ k hi h2 hk]
      exact SUExtras.longRootHom_mem hσ hrev hneg.symm _
    · intro hy
      obtain ⟨c, rfl⟩ := rootGroup_le_range_long hσ hrev hneg.symm hy
      let t : k := ⟨((Multiplicative.toAdd c : traceZero σ) : F),
        mem_fixedSubfield.mpr (fixed_of_mem_traceZero σ h2 (Multiplicative.toAdd c).2)⟩
      refine ⟨t, ?_⟩
      change model.phi (sl2Lower t) = (longRootHom σ hrev) c
      rw [hphi, chart_lower σ k hi h2 hk]
      congr 1
  refine ⟨model, ?_, hmat⟩
  exact SelectedSL2Model.ofRootMap_range _ _ model.root_mem model.phi model.injective
    model.upper_eq model.diag_mem
    (fun h hh => by obtain ⟨c, hc⟩ := model.scalar h hh; exact ⟨c, hc⟩) hlow


end SelectedRoot


section Canonical


end Canonical

end CFSG.StandardType

end
