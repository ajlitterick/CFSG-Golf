module

public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley SteinbergBT

variable {τ : Tag} {K : Type} [Field K]

variable (τ) in
@[expose] def subfieldImage (k : Subfield K) : Subgroup (ModGL τ K) :=
  (adjointGroup τ k).map (baseChangeGL k.subtype)

theorem subfieldImage_le (k : Subfield K) : subfieldImage τ k ≤ adjointGroup τ K := by
  rintro _ ⟨g, hg, rfl⟩
  exact baseChangeGL_mem_adjointGroup k.subtype hg


theorem units_map_entrywiseHom_of_mem_subfieldImage {k : Subfield K} {β : K ≃+* K}
    (hβ : ∀ c ∈ k, β c = c) {g : ModGL τ K} (hg : g ∈ subfieldImage τ k) :
    Units.map (entrywiseHom β.toRingHom) g = g := by
  obtain ⟨g', -, rfl⟩ := hg
  have hcomp : β.toRingHom.comp k.subtype = k.subtype := RingHom.ext fun x => hβ x x.2
  rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, hcomp]


end CFSG.RankThree.Chevalley
