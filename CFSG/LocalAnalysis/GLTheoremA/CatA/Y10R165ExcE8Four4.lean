module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Four3
public import CFSG.LieType.AlgebraicGroups.KernelRootGroup

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.ComponentClassification.CatLeafProof CFSG.ClassicalInvolution.RouteD.Exotic

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four


theorem canonicalRep_d4d4W_mem_torus_sup_rootSpan {L : Type} [Field L] :
    canonicalRep (coxeterSystem .E8) L d4d4W ∈
      torusGroup .E8 L ⊔ rootSpan .E8 L (kernelRoots d4d4Char) :=
  CFSG.LieType.AlgebraicGroups.canonicalRep_mem_torus_sup_rootSpan_kernelRoots
    (τ := .E8) (χ := d4d4Char) (L := L) d4d4W_mem_closure

theorem exists_fourLang (K : Type) [Field K] [Finite K] (L : Type) [Field L] [Algebra K L]
    [IsAlgClosure K L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP K ℓ] [CharP L ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) :
    ∃ g : ModGL .E8 L,
      g ∈ torusGroup .E8 L ⊔ rootSpan .E8 L (kernelRoots d4d4Char) ∧
        entrywiseFrobGL .E8 L ℓ f g =
          g * canonicalRep (coxeterSystem .E8) L d4d4W := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨z, hz, hz'⟩ := CFSG.LieType.AlgebraicGroups.lang_torus_sup_rootSpan
    (τ := .E8) (L := L) (ℓ := ℓ) (χ := d4d4Char) (e := f) hf
    (canonicalRep (coxeterSystem .E8) L d4d4W) (canonicalRep_d4d4W_mem_torus_sup_rootSpan (L := L))
  refine ⟨z, hz, ?_⟩
  have h : z⁻¹ * entrywiseFrobGL .E8 L ℓ f z =
      canonicalRep (coxeterSystem .E8) L d4d4W := hz'
  calc entrywiseFrobGL .E8 L ℓ f z
      = z * (z⁻¹ * entrywiseFrobGL .E8 L ℓ f z) := by group
    _ = z * canonicalRep (coxeterSystem .E8) L d4d4W := by rw [h]


end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four
