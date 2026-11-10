module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSwapBLiftSchur
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLiftBasic
public import CFSG.LieType.Steinberg.CentralExt.CoprimeSplit

public section

namespace CFSG.SeitzReduction.SeitzQ2

open Subgroup
open scoped commutatorElement
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial)
open CFSG.SeitzReduction.UnitaryPilot (OddCentralSplit)
open CFSG.LieType.Steinberg (pullback pullbackFst pullbackFst_surjective ker_pullbackFst_le_center
  snd_mem_ker_of_mem_ker_pullbackFst mem_pullback commutatorElement_mul_mul_of_mem_center)
open CFSG.LieType.Steinberg.CentralExt.CoprimeSplit (copPart mem_copPart
  exists_pow_prime_pow_mem_copPart)

theorem charTwo_of_natCard_eq_two_pow {K : Type} [Field K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CharP K 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  let := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [← Nat.card_eq_fintype_card, hK])

theorem oddSchurTrivial_of_oddCentralSplit {S : Type} [Group S] (h : OddCentralSplit S) :
    OddSchurTrivial S := by
  intro P _ _ hP η hη hcen hodd
  obtain ⟨σ, hσ⟩ := h P η hη hcen hodd
  have := hP
  exact F4Pilot.injective_of_section_of_perfect η hcen σ hσ


section Pullback

variable {S Q P : Type} [Group S] [Group Q] [Group P] {β : S →* Q} {η : P →* Q}

theorem odd_card_ker_pullbackFst (hodd : Odd (Nat.card η.ker)) :
    Odd (Nat.card (pullbackFst β η).ker) := by
  let f : (pullbackFst β η).ker →* η.ker :=
    { toFun := fun y =>
        ⟨((y : pullback β η) : S × P).2, (snd_mem_ker_of_mem_ker_pullbackFst y.2).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun y z hyz => by
    have h2 : ((y : pullback β η) : S × P).2 = ((z : pullback β η) : S × P).2 :=
      congrArg Subtype.val hyz
    have h1y := (snd_mem_ker_of_mem_ker_pullbackFst y.2).1
    have h1z := (snd_mem_ker_of_mem_ker_pullbackFst z.2).1
    exact Subtype.ext (Subtype.ext (Prod.ext (h1y.trans h1z.symm) h2))
  exact hodd.of_dvd_nat (Subgroup.card_dvd_of_injective f hf)

theorem exists_surjective_of_oddCentralSplit [Finite S] [Finite P] [Group.IsPerfect P]
    (hS : OddCentralSplit S) (hβ : Function.Surjective β) (hη : Function.Surjective η)
    (hcen : η.ker ≤ center P) (hodd : Odd (Nat.card η.ker)) :
    ∃ α : S →* P, (∀ s, η (α s) = β s) ∧ Function.Surjective α ∧ η.ker = β.ker.map α := by
  obtain ⟨σ, hσ⟩ := hS (pullback β η) (pullbackFst β η) (pullbackFst_surjective hη)
    (ker_pullbackFst_le_center hcen) (odd_card_ker_pullbackFst hodd)
  let α : S →* P := ((MonoidHom.snd S P).comp (pullback β η).subtype).comp σ
  have hα : ∀ s, η (α s) = β s := fun s => by
    have hmem := mem_pullback.1 (σ s).2
    have h1 : ((σ s : pullback β η) : S × P).1 = s := hσ s
    change η ((σ s : pullback β η) : S × P).2 = β s
    rw [← hmem, h1]
  have hdecomp : ∀ x : P, ∃ s, x * (α s)⁻¹ ∈ center P := fun x => by
    obtain ⟨s, hs⟩ := hβ (η x)
    refine ⟨s, hcen ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hα, hs, mul_inv_cancel]
  have hsurj : Function.Surjective α := by
    have hcomm : commutator P ≤ α.range := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨s, hs⟩ := hdecomp x
      obtain ⟨t, ht⟩ := hdecomp y
      have e : ⁅x, y⁆ = ⁅α s, α t⁆ := by
        have h := commutatorElement_mul_mul_of_mem_center hs ht (α s) (α t)
        rwa [inv_mul_cancel_right, inv_mul_cancel_right] at h
      rw [e, ← map_commutatorElement]
      exact ⟨_, rfl⟩
    intro x
    exact hcomm (by rw [Group.IsPerfect.commutator_eq_top]; exact mem_top x)
  refine ⟨α, hα, hsurj, ?_⟩
  ext c
  constructor
  · intro hc
    obtain ⟨s, rfl⟩ := hsurj c
    refine ⟨s, MonoidHom.mem_ker.2 ?_, rfl⟩
    rw [← hα]
    exact hc
  · rintro ⟨s, hs, rfl⟩
    rw [MonoidHom.mem_ker, hα]
    exact hs

theorem card_ker_dvd_of_oddCentralSplit [Finite S] [Finite P] [Group.IsPerfect P]
    (hS : OddCentralSplit S) (hβ : Function.Surjective β) (hη : Function.Surjective η)
    (hcen : η.ker ≤ center P) (hodd : Odd (Nat.card η.ker)) :
    Nat.card η.ker ∣ Nat.card β.ker := by
  obtain ⟨α, -, -, he⟩ := exists_surjective_of_oddCentralSplit hS hβ hη hcen hodd
  rw [he]
  exact card_map_dvd _ _

end Pullback

section Quotient


end Quotient

end CFSG.SeitzReduction.SeitzQ2
