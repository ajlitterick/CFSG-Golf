module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorEquivariant
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddQuotientStrongEmbedding

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFchapter1section1

universe u v w x

variable {G : Type u} {F : Type v} {Omega : Type w} {Xi : Type x}
variable [Group G] [Group F]

theorem transitive_action_equiv_of_surjective_stabilizer_map
    [MulAction G Omega] [MulAction F Xi]
    (hOmega : MulAction.IsPretransitive G Omega)
    (hXi : MulAction.IsPretransitive F Xi)
    (f : G →* F) (hf : Function.Surjective f) (a : Omega) (b : Xi)
    (hker : f.ker ≤ MulAction.stabilizer G a)
    (hstab : (MulAction.stabilizer G a).map f = MulAction.stabilizer F b) :
    ∃ phi : Omega ≃ Xi, phi a = b ∧
      ∀ (g : G) (y : Omega), phi (g • y) = f g • phi y := by
  let : MulAction G Xi := MulAction.compHom Xi f
  have htrans : MulAction.IsPretransitive G Xi := by
    constructor
    intro y y'
    obtain ⟨k, hk⟩ := hXi.exists_smul_eq y y'
    obtain ⟨g, hg⟩ := hf k
    exact ⟨g, by change f g • y = y'; rw [hg]; exact hk⟩
  have hcomp : MulAction.stabilizer G b = (MulAction.stabilizer F b).comap f := by
    ext g
    rfl
  have hsame : MulAction.stabilizer G a = MulAction.stabilizer G b := by
    rw [hcomp, ← hstab, Subgroup.comap_map_eq_self hker]
  exact transitive_action_equiv_of_stabilizer_eq hOmega htrans a b hsame


end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
