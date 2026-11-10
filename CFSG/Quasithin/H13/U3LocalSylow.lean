module

public import CFSG.Quasithin.H13.U3ElemNine
public import CFSG.Quasithin.H13.U3FrameKernel
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open
open scoped Pointwise commutatorElement


theorem center_eq_bot_of_isSimpleGroup_of_noncomm {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((mem_center_iff.mp (h ▸ mem_top b)) a)


variable {G : Type} [Group G]

theorem map_conj_eq_self_of_mem {E : Subgroup G} {t : G} (ht : t ∈ E) :
    E.map (MulAut.conj t).toMonoidHom = E := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact E.mul_mem (E.mul_mem ht hy) (E.inv_mem ht)
  · intro hx
    refine ⟨t⁻¹ * x * t, E.mul_mem (E.mul_mem (E.inv_mem ht) hx) ht, ?_⟩
    change t * (t⁻¹ * x * t) * t⁻¹ = x
    group


end CFSG.Quasithin.H13.U3
