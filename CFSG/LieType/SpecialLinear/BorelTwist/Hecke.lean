module

public import CFSG.LieType.SpecialLinear.BorelTwist.CoverType
public import CFSG.LieType.SpecialLinear.BorelTwist.Upper
public import CFSG.LieType.SpecialLinear.TwoEnd.CoverType
public import CFSG.LocalAnalysis.StandardType.GGTypeAFiveProofCrossMat
public import CFSG.LieType.SpecialLinear.NormalizerLift.FieldGraph

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
  CFSG.LieType.Universal.SpecialLinear CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open scoped MatrixGroups

variable (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
variable (A : GL (Fin (m + 1)) F)


theorem coverType_intertwine_unique (hA : IsUpperGL A) (σ : F ≃+* F) {ε : ℕ} (hε : ε = 1)
    {k : Type} {V : Type} [Field k] [Algebra F k] [AddCommGroup V] [Module k V]
    [CharP k 2]
    {ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : _ → k} {J : Finset (Fin m)}
    {T : V ≃ₗ[k] V}
    (hT : ∀ g v, T (ρ g v) = ρ (borelStd (m + 1) F A σ ε g) (T v))
    (ht : IsCoverType (rankOne m F 2) ρ y χ J) :
    (∀ h ∈ (curtisDatum m F 2).H,
        ((χ ∘ CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ) ∘
          borelGraph (m + 1) F) h = χ h) ∧
      borelStdSet (m := m) J ε = J := by
  have htw := isCoverType_comp_borelStd (m := m) (F := F) (A := A) hA σ (ε := ε)
    (by rw [hε]) ht
  have hsymm : ∀ g v,
      T.symm ((ρ.comp (borelStd (m + 1) F A σ ε).toMonoidHom) g v) = ρ g (T.symm v) := by
    intro g v
    have h := congrArg T.symm (hT g (T.symm v))
    simpa [T.apply_symm_apply] using h.symm
  have htrans := IsCoverType.of_linearEquiv (e := T.symm) hsymm htw
  have htrans' : IsCoverType (rankOne m F 2) ρ (T.symm y)
      ((χ ∘ CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ) ∘
        borelGraph (m + 1) F) (borelStdSet (m := m) J ε) := by
    simpa [borelStdChar, hε] using htrans
  exact isCoverType_unique_sl (m := m) (F := F) (p := 2) hρ htrans' ht

theorem coverType_rev_eq_of_intertwine (hA : IsUpperGL A) (σ : F ≃+* F) {ε : ℕ} (hε : ε = 1)
    {k : Type} {V : Type} [Field k] [Algebra F k] [AddCommGroup V] [Module k V]
    [CharP k 2]
    {ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : _ → k} {J : Finset (Fin m)}
    {T : V ≃ₗ[k] V}
    (hT : ∀ g v, T (ρ g v) = ρ (borelStd (m + 1) F A σ ε g) (T v))
    (ht : IsCoverType (rankOne m F 2) ρ y χ J) :
    J.map Fin.revPerm.toEmbedding = J := by
  have h := (coverType_intertwine_unique (m := m) (F := F) A hA σ hε hρ hT ht).2
  simpa [borelStdSet, hε] using h

theorem mem_iff_rev_mem_of_intertwine (hA : IsUpperGL A) (σ : F ≃+* F) {ε : ℕ} (hε : ε = 1)
    {k : Type} {V : Type} [Field k] [Algebra F k] [AddCommGroup V] [Module k V]
    [CharP k 2]
    {ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : _ → k} {J : Finset (Fin m)}
    {T : V ≃ₗ[k] V}
    (hT : ∀ g v, T (ρ g v) = ρ (borelStd (m + 1) F A σ ε g) (T v))
    (ht : IsCoverType (rankOne m F 2) ρ y χ J) (s : Fin m) :
    s ∈ J ↔ Fin.rev s ∈ J := by
  have h := coverType_rev_eq_of_intertwine (m := m) (F := F) A hA σ hε hρ hT ht
  constructor
  · intro hs
    have hm : Fin.rev s ∈ J.map Fin.revPerm.toEmbedding :=
      Finset.mem_map.mpr ⟨s, hs, rfl⟩
    rwa [h] at hm
  · intro hs
    have hm : s ∈ J.map Fin.revPerm.toEmbedding :=
      Finset.mem_map.mpr ⟨Fin.rev s, hs, by simp [Fin.revPerm]⟩
    rwa [h] at hm

end CFSG.LieType.SpecialLinear
