module

public import CFSG.Quasithin.Background.RonanH143Data
public import CFSG.Quasithin.Background.RonanH143Gen
public import CFSG.Quasithin.Background.RonanH143Orb

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin


theorem exists_Zq_of_smul_Qstd {g : P24} (hg : g • Qstd = Qstd) (i : Fin 5) :
    ∃ j, g • Zq i = Zq j := by
  have hmem : g • Zq i ∈ Qstd := by
    rw [← hg]
    exact Finset.smul_mem_smul_finset ((mem_Qstd_iff _).2 ⟨i, rfl⟩)
  obtain ⟨j, hj⟩ := (mem_Qstd_iff _).1 hmem
  exact ⟨j, hj.symm⟩


theorem mem_MY_iff {Γ : Subgroup P24} {α : Type*} [MulAction P24 α] {Y : α} {g : P24} :
    g ∈ MY Γ Y ↔ g ∈ Γ ∧ g • Y = Y := by
  simp [MY, MulAction.mem_stabilizer_iff]


theorem exists_piQ (Γ : Subgroup P24) :
    ∃ π : ↥(MY Γ Qstd) →* Equiv.Perm (Fin 5),
      ∀ (g : ↥(MY Γ Qstd)) (i : Fin 5), Zq (π g i) = (g : P24) • Zq i :=
  exists_labAct Zq Zq_injective (MY Γ Qstd) fun g hg i =>
    exists_Zq_of_smul_Qstd (mem_MY_iff.1 hg).2 i

noncomputable def piQ (Γ : Subgroup P24) : ↥(MY Γ Qstd) →* Equiv.Perm (Fin 5) :=
  Classical.choose (exists_piQ Γ)


end CFSG.Quasithin.RonanH143
