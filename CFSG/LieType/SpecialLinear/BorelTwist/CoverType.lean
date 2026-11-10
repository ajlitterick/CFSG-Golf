module

public import CFSG.LieType.SpecialLinear.BorelTwist.Basic
public import CFSG.LieType.SpecialLinear.EndNode.CoverDatum
public import CFSG.LieType.SpecialLinear.Block222.Basic

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
  CFSG.LieType.Universal.SpecialLinear
  CFSG.Quasithin.SmithCurtis CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open scoped MatrixGroups

variable (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]


theorem coverId_datum_heckeT_eq {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V) (s : Fin m) (v : V) :
    (coverId m F 2).datum.heckeT ρ s v = (curtisDatum m F 2).heckeT ρ s v := by
  let : Fintype ↥((curtisDatum m F 2).X s) := Fintype.ofFinite _
  let : Fintype ↥((coverId m F 2).lX s) := Fintype.ofFinite _
  let : Fintype ↥((coverId m F 2).datum.X s) := Fintype.ofFinite _
  rw [CurtisDatum.heckeT_apply, CurtisDatum.heckeT_apply]
  let e : ↥((coverId m F 2).datum.X s) ≃ ↥((curtisDatum m F 2).X s) :=
    (Equiv.cast (congrArg (fun t : Subgroup (SpecialLinearGroup (Fin (m + 1)) F) => ↥t)
      (show (coverId m F 2).datum.X s = (coverId m F 2).lX s from rfl))).trans
      ((coverId m F 2).lXEquiv s)
  refine Fintype.sum_equiv e _ _ ?_
  intro x
  change ρ ((x : SpecialLinearGroup (Fin (m + 1)) F) * (coverId m F 2).nhat s) v =
    ρ (((e x : ↥((curtisDatum m F 2).X s)) : SpecialLinearGroup (Fin (m + 1)) F) *
      (curtisDatum m F 2).n s) v
  have hx : (((e x : ↥((curtisDatum m F 2).X s)) : SpecialLinearGroup (Fin (m + 1)) F)) =
      (x : SpecialLinearGroup (Fin (m + 1)) F) := rfl
  rw [hx]
  have hn : (coverId m F 2).nhat s = (curtisDatum m F 2).n s := by
    rw [CentralCoverData.nhat]
    have h := (coverId m F 2).map_nhatW ((curtisCoxeterSystem m).simple s)
    simp only [MonoidHom.id_apply] at h
    rw [h, CentralCoverData.nW_simple]
  rw [hn]


@[expose] def borelStdSet (J : Finset (Fin m)) (ε : ℕ) : Finset (Fin m) :=
  if ε = 0 then J else J.map Fin.revPerm.toEmbedding

@[expose] noncomputable def borelStdChar {k : Type*} (χ : SpecialLinearGroup (Fin (m + 1)) F → k)
    (σ : F ≃+* F) (ε : ℕ) : SpecialLinearGroup (Fin (m + 1)) F → k :=
  if ε = 0 then χ ∘ CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ
  else (χ ∘ CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ) ∘
    borelGraph (m + 1) F

end CFSG.LieType.SpecialLinear
