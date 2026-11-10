module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHBase
public import CFSG.ClassicalInvolution.Asc77.AscIH8Rest
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHRed

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance.LocalBalance (commute_of_isComponent_of_ne)
open scoped commutatorElement MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

section Components

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem thm5IH_isComponent_comp (hΩ : ConjInvariant Ω) (D : OmegaLie p f Ω) (i : Fin D.card) :
    CFSG.IsComponent (D.comp i) := by
  refine ⟨?_, ?_⟩
  · have hopen := ModelFacts.isQuasisimple_modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out
      (isFundTag_modelFacts (D.isFundTag i)) (D.admissible i)
    have hq := @CFSG.ComponentClassification.Quasisimple.central_quotient _ _ hopen
      (D.hom i).ker (MonoidHom.normal_ker (D.hom i)) (D.ker_le_center i)
    have hrange : CFSG.Open.IsQuasisimple (D.hom i).range :=
      CFSG.ComponentClassification.Components.quasisimple_of_equiv
        (QuotientGroup.quotientKerEquivRange (D.hom i)).symm hq
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hrange
  · have hY : (omegaGen Ω).Normal := omegaGen_normal hΩ
    refine Subgroup.IsSubnormal.step (D.comp i) (omegaGen Ω) (D.comp_le_omegaGen i)
      hY.isSubnormal ?_
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using D.mem_comp_conj g.2 hx

end Components


end CFSG.ClassicalInvolution.Asc77
