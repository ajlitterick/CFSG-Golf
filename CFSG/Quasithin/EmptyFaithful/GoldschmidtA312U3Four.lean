module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Geom

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {F : Type} [Field F]

section FourGroup

variable (h : UnitaryFieldData p f F)

@[expose] def dS (k : Fin 3) : ↥(unitarySU p f F 3) := ⟨dsignGL F k, dsignGL_mem h k⟩


@[expose] def E₀ : Subgroup ↥(unitarySU p f F 3) := Subgroup.closure (Set.range (dS h))


theorem exists_sylow_le_of_odd_index {G : Type*} [Group G] [Finite G] {M : Subgroup G}
    (hodd : Odd M.index) : ∃ Q : Sylow 2 G, (Q : Subgroup G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Pm⟩ : Nonempty (Sylow 2 ↥M) := inferInstance
  obtain ⟨Q, hQ⟩ := Sylow.exists_comap_subtype_eq Pm
  refine ⟨Q, ?_⟩
  have hfac : (Nat.card G).factorization 2 = (Nat.card M).factorization 2 := by
    rw [← Subgroup.card_mul_index M, Nat.factorization_mul Nat.card_pos.ne'
      (Subgroup.index_ne_zero_of_finite), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (Nat.not_even_iff_odd.mpr hodd |> fun _ =>
        hodd.not_two_dvd_nat), add_zero]
  have hcardQ : Nat.card (Q : Subgroup G) = 2 ^ (Nat.card M).factorization 2 := by
    rw [Sylow.card_eq_multiplicity Q, hfac]
  have hsub : (Q : Subgroup G).subgroupOf M = (Pm : Subgroup ↥M) := hQ
  have hcardP : Nat.card ((Q : Subgroup G).subgroupOf M) = 2 ^ (Nat.card M).factorization 2 := by
    rw [hsub, Sylow.card_eq_multiplicity Pm]
  have hmap : ((Q : Subgroup G).subgroupOf M).map M.subtype = (Q : Subgroup G) ⊓ M :=
    Subgroup.subgroupOf_map_subtype _ _
  have hinf : Nat.card ↥((Q : Subgroup G) ⊓ M) = Nat.card (Q : Subgroup G) := by
    rw [← hmap, Subgroup.card_map_of_injective M.subtype_injective, hcardP, hcardQ]
  have heq : (Q : Subgroup G) ⊓ M = (Q : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hinf])
  intro x hx
  have hx' : x ∈ (Q : Subgroup G) ⊓ M := by
    rw [heq]
    exact hx
  exact hx'.2


end FourGroup

end CFSG.Quasithin.A312U3
