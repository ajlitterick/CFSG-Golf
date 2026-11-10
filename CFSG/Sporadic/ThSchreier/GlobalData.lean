
module

public import CFSG.Sporadic.ThSchreier.GlobalDataBase

public import CFSG.Sporadic.ThSchreier.BFS
public import CFSG.Sporadic.ThSchreier.Row

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.LySchreier
  Pointwise

noncomputable abbrev planeX :
    Set (Set RowV) := MulAction.orbit J planeWSet

@[expose] noncomputable def planeGens : List (Set RowV → Set RowV) :=
  [fun U => a • U, fun U => b • U]

open Classical in
@[expose] noncomputable def iotaList : List (Set RowV) :=
  bfsList planeGens planeWSet planeX.ncard

@[expose] noncomputable def nPlanes : ℕ := iotaList.length

theorem planeX_finite : planeX.Finite := Set.toFinite _

theorem closure_ab_J :
    Subgroup.closure ({a, b} : Set J) = ⊤ := closure_ab

open Classical in
theorem iotaList_facts :
    iotaList.Nodup ∧ (∀ U, U ∈ iotaList ↔ U ∈ planeX) ∧ iotaList.length ≤ planeX.ncard :=
  bfsList_orbit closure_ab_J planeWSet planeX_finite le_rfl

theorem iotaList_nodup : iotaList.Nodup := iotaList_facts.1

theorem mem_iotaList
    {U : Set RowV} : U ∈ iotaList ↔ U ∈ planeX := iotaList_facts.2.1 U


@[expose] noncomputable def iota
    (i : Fin nPlanes) : Set RowV := iotaList[i.val]'i.isLt

theorem iota_mem (i : Fin nPlanes) : iota i ∈ planeX :=
  mem_iotaList.1 (List.getElem_mem _)

theorem iota_injective : Function.Injective iota := by
  intro i j h
  exact Fin.ext ((List.Nodup.getElem_inj_iff iotaList_nodup).1 h)

theorem iota_surjective
    {U : Set RowV} (hU : U ∈ planeX) : ∃ i, iota i = U := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (mem_iotaList.2 hU)
  exact ⟨⟨i, hi⟩, rfl⟩

@[expose] noncomputable def iotaEquiv : Fin nPlanes ≃ planeX :=
  Equiv.ofBijective (fun i => ⟨iota i, iota_mem i⟩)
    ⟨fun i j h => iota_injective (congrArg Subtype.val h),
      fun U => by
        obtain ⟨i, hi⟩ := iota_surjective U.2
        exact ⟨i, Subtype.ext hi⟩⟩


noncomputable instance instMulActionIndex :
    MulAction J (Fin nPlanes) := iotaEquiv.mulAction J

@[expose] noncomputable def phi :
    J →* Equiv.Perm (Fin nPlanes) := MulAction.toPermHom J _

@[expose] noncomputable def alphaPerm :
    Equiv.Perm (Fin nPlanes) := phi a


theorem iota_smul
    (g : J) (i : Fin nPlanes) : iota (g • i) = g • iota i := by
  have h : iotaEquiv (g • i) = g • iotaEquiv i := by
    show iotaEquiv (iotaEquiv.symm (g • iotaEquiv i)) = g • iotaEquiv i
    rw [Equiv.apply_symm_apply]
  have := congrArg Subtype.val h
  exact this

theorem iota_phi
    (g : J) (i : Fin nPlanes) : iota (phi g i) = g • iota i := iota_smul g i


end CFSG.Sporadic.ThSchreier
