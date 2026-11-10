
module

public import CFSG.Monster.B.Rep4371.FaithfulImageBase

public import CFSG.Monster.B.Rep4371.SmallFaithful
public import CFSG.Monster.B.Gen.PacketGeneration
public import Certificates.Certificate16021
public import CFSG.Monster.B.Gen.Max2AssemblyBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.VisQuot CFSG.Monster.B.Rep4371
open scoped Matrix


theorem gramPauli_mul_self : gramPauli * gramPauli = 1 :=
  Certificates.certificate16021

theorem linearIndependent_ePauli' :
    LinearIndependent (ZMod 2) fun k => Multiplicative.toAdd (psiBar ⟨ePauli' k, ePauli'_mem_Ebar k⟩) :=
  linearIndependent_psi_of_gram ePauli' ePauli'_mem_Ebar gramPauli gramPauli gramPauli_mul_self
    ePauli'_rel

theorem Ebar_eq_closure_pauli :
    Ebar = Subgroup.closure (Set.range ePauli) := by
  set H := Subgroup.closure (Set.range ePauli)
  apply le_antisymm
  · intro e he
    set β := psiBasis ePauli' ePauli'_mem_Ebar linearIndependent_ePauli'
    set c : Fin 22 → ZMod 2 := fun k => β.repr (Multiplicative.toAdd (psiBar ⟨e, he⟩)) k
    set e' : Cbar := ((List.finRange 22).map fun k => ePauli' k ^ (c k).val).prod
    have he'H : e' ∈ H := Subgroup.list_prod_mem H fun x hx => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      exact H.pow_mem (Subgroup.subset_closure ⟨_, rfl⟩) _
    have he'E : e' ∈ Ebar := Subgroup.list_prod_mem Ebar fun x hx => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      exact Ebar.pow_mem (ePauli'_mem_Ebar k) _
    have hpsi : psiBar ⟨e', he'E⟩ = psiBar ⟨e, he⟩ := by
      rw [hom_eq_sum_of_eq_prod psiBar ePauli' ePauli'_mem_Ebar xbar_mem_Ebar
        ((psiBar_eq_one_iff _).2 (Or.inr rfl)) he'E c 0 (by rw [pow_zero, mul_one])]
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd]
      have hsum := β.sum_repr (Multiplicative.toAdd (psiBar ⟨e, he⟩))
      rw [← hsum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [psiBasis_apply]
    have hq : psiBar (⟨e', he'E⟩⁻¹ * ⟨e, he⟩) = 1 := by
      rw [map_mul, map_inv, hpsi, inv_mul_cancel]
    rcases (psiBar_eq_one_iff _).1 hq with h | h
    · have : e = e' := by
        have := congrArg Subtype.val h
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at this
        exact (inv_mul_eq_one.1 this).symm
      rw [this]
      exact he'H
    · have hx : e = e' * xbar := by
        have := congrArg Subtype.val h
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
        rw [← this, mul_inv_cancel_left]
      rw [hx]
      refine H.mul_mem he'H ?_
      rw [← ePauli_zero]
      exact Subgroup.subset_closure ⟨0, rfl⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ePauli_mem_Ebar i


end CFSG.Monster.B
