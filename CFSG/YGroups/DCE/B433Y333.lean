module

public import CFSG.YGroups.Y433.Bound
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.DCE.OrbitLower
public import CFSG.YGroups.DCE.B433Check

public section

namespace CFSG.YGroups.DCE.B433

open CFSG.YGroups.DCE.B433Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)
open scoped Pointwise

@[expose] noncomputable def J432 : Subgroup (YGroup 4 3 2) :=
  Subgroup.closure (yGen 4 3 2 '' {c | c < 10 ∧ c ≠ 4})


@[expose] def Pt432 : Type := Fin 31671


noncomputable instance :
    MulAction (YGroup 4 3 2) Pt432 :=
  MulAction.compHom (Fin 31671) rho432F

instance : Fintype Pt432 := inferInstanceAs (Fintype (Fin 31671))

instance : Finite Pt432 := inferInstanceAs (Finite (Fin 31671))


@[expose] noncomputable def P333 : Subgroup B433 :=
  Subgroup.closure ((fun l => qB (yGen 4 3 3 l)) '' {l | l < 11 ∧ l ≠ 4})

theorem tB_mem_P333 : tB ∈ P333 :=
  Subgroup.subset_closure ⟨10, ⟨by norm_num, by norm_num⟩, rfl⟩

theorem map_J432_le_P333 : J432.map psi ≤ P333 := by
  rw [J432, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨c, ⟨hc, hc4⟩, rfl⟩, rfl⟩
  refine Subgroup.subset_closure ⟨c, ⟨by omega, hc4⟩, ?_⟩
  show qB (yGen 4 3 3 c) = psi (yGen 4 3 2 c)
  rw [psi, MonoidHom.comp_apply, psiU_yGen hc]


section Records


end Records


end CFSG.YGroups.DCE.B433
