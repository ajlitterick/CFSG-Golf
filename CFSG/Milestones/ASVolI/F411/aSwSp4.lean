module

public import CFSG.Milestones.ASVolI.F411.aSwCore
public import CFSG.Quasithin.Vol2.F134LieSp4
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F4Native

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.QuasithinUnique.Lin2.Five (tauSp tauEquiv tauAut tauAut_proj)

section Tau

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem burnsideF411a_map_tauEquiv_stabilizer :
    (stabilizer 2 K (flag 2 K 1)).map (tauEquiv (F := K)).toMonoidHom =
        stabilizer 2 K (flag 2 K 2) ∧
      (stabilizer 2 K (flag 2 K 2)).map (tauEquiv (F := K)).toMonoidHom =
        stabilizer 2 K (flag 2 K 1) := by
  have h12 : (stabilizer 2 K (flag 2 K 1)).map (tauEquiv (F := K)).toMonoidHom ≤
      stabilizer 2 K (flag 2 K 2) := by
    rintro _ ⟨g, hg, rfl⟩
    exact CFSG.Quasithin.F134.Sp4.tauSp_mem_stabilizer_two hg
  have h21 : (stabilizer 2 K (flag 2 K 2)).map (tauEquiv (F := K)).toMonoidHom ≤
      stabilizer 2 K (flag 2 K 1) := by
    rintro _ ⟨g, hg, rfl⟩
    exact CFSG.Quasithin.F134.Sp4.tauSp_mem_stabilizer_one hg
  have hc : ∀ W : Submodule K (Fin 2 ⊕ Fin 2 → K),
      Nat.card ((stabilizer 2 K W).map (tauEquiv (F := K)).toMonoidHom) =
        Nat.card (stabilizer 2 K W) := fun W =>
    Subgroup.card_map_of_injective (f := (tauEquiv (F := K)).toMonoidHom)
      (tauEquiv (F := K)).injective
  have c1 := Subgroup.card_le_of_le h12
  have c2 := Subgroup.card_le_of_le h21
  rw [hc] at c1 c2
  exact ⟨Subgroup.eq_of_le_of_card_ge h12 (by rw [hc]; exact c2),
    Subgroup.eq_of_le_of_card_ge h21 (by rw [hc]; exact c1)⟩

theorem burnsideF411a_map_tauAut_projStabilizer {a b : ℕ}
    (h : (stabilizer 2 K (flag 2 K a)).map (tauEquiv (F := K)).toMonoidHom =
      stabilizer 2 K (flag 2 K b)) :
    (projStabilizer 2 K (flag 2 K a)).map (tauAut (F := K)).toMonoidHom =
      projStabilizer 2 K (flag 2 K b) := by
  rw [projStabilizer, projStabilizer, Subgroup.map_map, ← h, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun g => tauAut_proj g

end Tau


end CFSG.ASVolI
