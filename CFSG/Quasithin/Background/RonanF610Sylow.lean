module

public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Foundations.Basic
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Quasithin.RonanF610

open CFSG.Open

theorem not_isCyclic_sylow_two_of_isPerfect {G : Type*} [Group G] [Finite G]
    (hperf : Group.IsPerfect G) (P : Sylow 2 G) (hP : Nat.card ↥(P : Subgroup G) ≠ 1) :
    ¬ IsCyclic ↥(P : Subgroup G) := by
  intro hcyc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := P.isPGroup'.exists_card_eq
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hP (by simpa using ha)
  have h2 : 2 ∣ Nat.card G :=
    (dvd_pow_self 2 ha0).trans (ha ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup G))
  have hmin : (Nat.card G).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2
  have hnorm := IsCyclic.normalizer_le_centralizer hmin hcyc
  have hcomp := IsCyclic.isComplement' hmin hcyc
  let f := MonoidHom.transferSylow P hnorm
  have hle : commutator G ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def,
      (IsMulCommutative.is_comm (M := ↥(P : Subgroup G))).comm (f g₁) (f g₂)]
    group
  have hker : f.ker = ⊤ := by
    rw [hperf.commutator_eq_top] at hle
    exact top_le_iff.mp hle
  have hcard := hcomp.card_mul_card
  rw [hker, Subgroup.card_top] at hcard
  exact hP (Nat.eq_of_mul_eq_mul_left Nat.card_pos (hcard.trans (mul_one _).symm))


end CFSG.Quasithin.RonanF610
