module

public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.Quasithin.Background.RonanE114D4LowBound
import CFSG.Quasithin.Background.RonanE111Core
import CFSG.Quasithin.Background.RonanE114G2F4
import CFSG.Quasithin.Background.RonanE114C5Clauses
import CFSG.Quasithin.Background.RonanE114J4Main
import CFSG.Quasithin.Background.RonanE114SevenL35Main
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve

public section

namespace CFSG.ASVolI

namespace ChE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b
open scoped commutatorElement


end ChE

open ChE CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b
open scoped commutatorElement


@[expose] def E_1_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup ↥(CFSG.generalizedFitting G) → IsSylowIn 2 T ⊤ →
    CFSG.generalizedFitting G ⊔ T = ⊤ →
      ((∀ n : ℕ, 1 ≤ n →
        (IsPSL 2 2 n ↥(CFSG.generalizedFitting G) ∨ IsSz n ↥(CFSG.generalizedFitting G) ∨
          IsPSU 3 2 n ↥(CFSG.generalizedFitting G) ∨ IsPSL 3 2 n ↥(CFSG.generalizedFitting G) ∨
          (IsPSp4 2 n ↥(CFSG.generalizedFitting G) ∨
            (n = 1 ∧ IsAlt 6 ↥(CFSG.generalizedFitting G))) ∨
          (Is2F4 n ↥(CFSG.generalizedFitting G) ∨
            (n = 1 ∧ IsTits ↥(CFSG.generalizedFitting G))) ∨
          (IsG2 2 n ↥(CFSG.generalizedFitting G) ∨
            (n = 1 ∧ IsPSU 3 3 1 ↥(CFSG.generalizedFitting G)))) →
          nParam (⊤ : Subgroup G) = (n : ℕ∞)) ∧
      (IsPSL 4 2 1 ↥(CFSG.generalizedFitting G) ∨ IsPSL 5 2 1 ↥(CFSG.generalizedFitting G) →
        nParam (⊤ : Subgroup G) = 1)) ∧
      (∀ n : ℕ, 1 ≤ n → Is3D4 2 n ↥(CFSG.generalizedFitting G) →
        nParam (⊤ : Subgroup G) = ((3 * n : ℕ) : ℕ∞)) ∧
      (IsAlt 7 ↥(CFSG.generalizedFitting G) → nParam (⊤ : Subgroup G) = 1) ∧
      (IsSporadic .M11 ↥(CFSG.generalizedFitting G) ∨ IsSporadic .M12 ↥(CFSG.generalizedFitting G) ∨
          IsSporadic .M24 ↥(CFSG.generalizedFitting G) ∨
          IsSporadic .He ↥(CFSG.generalizedFitting G) → nParam (⊤ : Subgroup G) = 1) ∧
      (IsSporadic .J1 ↥(CFSG.generalizedFitting G) ∨ IsSporadic .J2 ↥(CFSG.generalizedFitting G) ∨
          IsSporadic .J4 ↥(CFSG.generalizedFitting G) ∨
          IsSporadic .M22 ↥(CFSG.generalizedFitting G) ∨
          IsSporadic .M23 ↥(CFSG.generalizedFitting G) ∨
          IsSporadic .HS ↥(CFSG.generalizedFitting G) ∨
          IsSporadic .Ru ↥(CFSG.generalizedFitting G) → nParam (⊤ : Subgroup G) ≤ 2) ∧
      (∀ p e : ℕ, p.Prime → p ≠ 2 → 5 < p ^ e → IsPSL 2 p e ↥(CFSG.generalizedFitting G) →
        nParam (⊤ : Subgroup G) = 1) ∧
      (∀ (s : Bool) (p : ℕ), p.Prime → p ≠ 2 → IsPSLEps3 s p 1 ↥(CFSG.generalizedFitting G) →
        nParam (⊤ : Subgroup G) = 1)

@[expose] def E_1_14_seven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup ↥(CFSG.generalizedFitting G) → IsSylowIn 2 T ⊤ →
    CFSG.generalizedFitting G ⊔ T = ⊤ →
      ∀ (s : Bool) (p : ℕ), p.Prime → p ≠ 2 → IsPSLEps3 s p 1 ↥(CFSG.generalizedFitting G) →
        nParam (⊤ : Subgroup G) = 1

section E114

theorem e_1_14_of_seven (h7 : E_1_14_seven) : E_1_14 := by
  intro G _ _ T hSQ hFs hT hFT
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, h7 G T hSQ hFs hT hFT⟩
  · intro n hn hL
    rcases hL with h | h | h | h | (h | ⟨rfl, h⟩) | (h | ⟨rfl, h⟩) | (h | ⟨rfl, h⟩)
    · exact RonanE114.clause_one_typeLie G T hSQ hFs hT hFT n hn (Or.inl h)
    · exact RonanE114.clause_one_typeLie G T hSQ hFs hT hFT n hn (Or.inr (Or.inl h))
    · exact RonanE114.clause_one_typeLie G T hSQ hFs hT hFT n hn (Or.inr (Or.inr (Or.inl h)))
    · exact RonanE114.clause_one_typeLie G T hSQ hFs hT hFT n hn
        (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact RonanE114.clause_one_typeLie G T hSQ hFs hT hFT n hn
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact RonanE114.clause_one_typeLie G T hSQ hFs hT hFT 1 hn
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)))))
    · exact RonanE114.clause_one_2F4 G T hSQ hFs hT hFT n hn h
    · exact_mod_cast RonanE114.clause_one_tits G T hSQ hFs hT hFT h
    · exact RonanE114.clause_one_G2 G T hSQ hFs hT hFT n hn h
    · exact_mod_cast RonanE114.clause_one_u33 G T hSQ hFs hT hFT h
  · rintro (h | h)
    · exact RonanE114.clause_one_l42 G T hSQ hFs hT hFT h
    · exact RonanE114.clause_one_l52 G T hSQ hFs hT hFT h
  · exact CFSG.Quasithin.RonanE114Low.e_1_14_two_printed_local G T hSQ hFs hT hFT
  · exact RonanE114.clause_three G T hSQ hFs hT hFT
  · rintro (h | h | h | h)
    · exact RonanE114.clause_four_M11 G T hSQ hFs hT hFT h
    · exact RonanE114.clause_four_M12 G T hSQ hFs hT hFT h
    · exact RonanE114.clause_four_M24 G T hSQ hFs hT hFT h
    · exact RonanE114.clause_four_He G T hSQ hFs hT hFT h
  · exact RonanE114.clause_five G T hSQ hFs hT hFT
      (RonanE114.clause_five_J4 G T hSQ hFs hT hFT)
  · exact RonanE114.clause_six G T hSQ hFs hT hFT

end E114

section E114Target

theorem as_E_1_14 : E_1_14 :=
  e_1_14_of_seven fun G _ _ T hSQ hFs hT hFT => RonanE114.clause_seven G T hSQ hFs hT hFT

end E114Target

end CFSG.ASVolI
