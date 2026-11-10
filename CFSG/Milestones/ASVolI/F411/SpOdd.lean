module

public import CFSG.Milestones.ASVolI.F411.KeyGen
public import CFSG.Milestones.ASVolI.F411.SpOddT
public import CFSG.Milestones.ASVolI.F411.Main
import all CFSG.Milestones.ASVolI.F4
import all CFSG.RankThree.PartOne.AUTSL.SpTwoCenter

public section

namespace CFSG.ASVolI

open Matrix Subgroup CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.AUTSL.SpTwo

section Model

variable {K : Type} [Field K]

theorem burnsideF411_projStab_inf :
    projStabilizer 2 K (flag 2 K 1) ⊓ projStabilizer 2 K (flag 2 K 2) = projBorel 2 K := by
  rw [projStabilizer, projStabilizer, ← burnsideF4h_cl_map_inf_of_ker_le _ (by
    rw [ker_proj]; exact spScalars_le_stabilizer _), burnsideF4h_cl_sp_stab_inf]
  rfl


theorem burnsideF411_projBorel_le_normalizer :
    projBorel 2 K ≤ Subgroup.normalizer (projUnipotent 2 K : Set (StatedProj (StatedSp 2 K))) := by
  have hn := (unipotent_subgroupOf_borelSubgroup_normal (r := 2) (K := K))
  refine burnsideF411_le_normalizer ?_
  rintro _ ⟨b, hb, rfl⟩ _ ⟨u, hu, rfl⟩
  have h1 : (⟨b, hb⟩ : borelSubgroup 2 K) * ⟨u, unipotent_le_borelSubgroup hu⟩ *
      (⟨b, hb⟩ : borelSubgroup 2 K)⁻¹ ∈ (unipotent 2 K).subgroupOf (borelSubgroup 2 K) :=
    hn.conj_mem _ (Subgroup.mem_subgroupOf.mpr hu) _
  refine ⟨b * u * b⁻¹, Subgroup.mem_subgroupOf.mp h1, ?_⟩
  rw [map_mul, map_mul, map_inv]


end Model

section Transport


end Transport


end CFSG.ASVolI
