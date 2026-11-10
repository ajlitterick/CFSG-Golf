module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Defs

open CFSG.RankThree.PartOne.CTP
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne


section Entry

variable {τ : Tag} {K : Type} [Field K]

abbrev rootLabel {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : Label τ := Sum.inr ⟨γ, hγ⟩

abbrev negLabel {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : Label τ := rootLabel (isRoot_neg_iff.2 hγ)

@[expose] noncomputable def entry (g : adjointGroup τ K) (a b : Label τ) : K :=
  (endHom K g) (Finsupp.single b 1) a

theorem entry_entrywiseAdjointAut (σ : K ≃+* K) (g : adjointGroup τ K) (a b : Label τ) :
    entry (entrywiseAdjointAut τ σ g) a b = σ (entry g a b) := by
  have h : endHom K (entrywiseAdjointAut τ σ g) = entrywise σ.toRingHom (endHom K g) := rfl
  unfold entry
  rw [h, entrywise_single]
  simp


end Entry

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
