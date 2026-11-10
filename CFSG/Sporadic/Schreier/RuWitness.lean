module

public import CFSG.Sporadic.Schreier.RuCertData
public import CFSG.Sporadic.Schreier.RuCheckWit

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem ruLGens_eq : ruLGens = [ruLGen 1, ruLGen 2, ruLGen 3] := by
  simp [ruLGen, ruLGens, ruLMWords]

theorem ruM_mem : ruM1 ∈ ruP ∧ ruM2 ∈ ruP := slotRun_mem ruMProg ruA0_mem ruA1_mem

theorem ruWw_mem : ruWw ∈ ruP := evalSigned_mem (pair_mem ruA0_mem ruA1_mem) _

theorem ruRw_mem : ruRw ∈ ruP := evalSigned_mem (pair_mem ruM_mem.1 ruM_mem.2) _

theorem ruUw_mem : ruUw ∈ ruP :=
  ruP.mul_mem (ruP.mul_mem (ruP.mul_mem ruWw_mem ruRw_mem) (ruP.inv_mem ruWw_mem)) ruA0_mem

theorem ruHw_mem : ruHw ∈ ruP := ruP.mul_mem (ruP.pow_mem ruUw_mem 7) ruWw_mem

theorem ruLGens_mem : ∀ g ∈ ruLGens, g ∈ ruP := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact ruP.mul_mem (ruP.mul_mem ruHw_mem (evalSigned_mem (pair_mem ruM_mem.1 ruM_mem.2) w))
    (ruP.inv_mem ruHw_mem)

theorem getD_mem_of_mem {G : Type*} [Group G] {H : Subgroup G} {l : List G}
    (h : ∀ g ∈ l, g ∈ H) (i : ℕ) : l.getD i 1 ∈ H := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => exact H.one_mem
  | some g => exact h g (List.mem_of_getElem? hi)


theorem ruLGen_memL (i : ℕ) : ruLGen i ∈ ruL :=
  getD_mem_of_mem (fun _ hg => Subgroup.subset_closure hg) _

theorem ruL_le : ruL ≤ ruP := closure_list_le ruLGens_mem

theorem ruFusX_mem (i : ℕ) : ruFusX i ∈ ruS :=
  evalSigned_mem (fun _ hg => Subgroup.subset_closure hg) _

theorem ruFusG_mem (i : ℕ) : ruFusG i ∈ ruP := evalSigned_mem (pair_mem ruA0_mem ruA1_mem) _

theorem ruFusH_mem (i : ℕ) : ruFusH i ∈ ruP :=
  ruP.mul_mem (ruP.pow_mem (ruP.mul_mem (ruP.mul_mem (ruP.mul_mem (ruFusG_mem i) ruA0_mem)
    (ruP.inv_mem (ruFusG_mem i))) (ruS_le (ruFusX_mem i))) _) (ruFusG_mem i)

theorem ruYp_memL (p : ℕ) : ruYp p ∈ ruL :=
  evalSigned_mem (fun _ hg => Subgroup.subset_closure hg) _


end CFSG.Sporadic.RuSchreier
