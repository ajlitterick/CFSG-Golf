module

public import CFSG.LocalAnalysis.ComponentInitial.BinaryBilinearExtension
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open BinExt

variable (K : Type*) [Field K] [Module (ZMod 2) K]

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

@[expose] noncomputable def suzukiTwistBilin (φ : K ≃+* K) : K →ₗ[ZMod 2] K →ₗ[ZMod 2] K :=
  LinearMap.mk₂ (ZMod 2) (fun x y => x * φ y) (fun x x' y => add_mul _ _ _)
    (fun c x y => by rcases zmod2_cases c with rfl | rfl <;> simp)
    (fun x y y' => by rw [map_add, mul_add])
    (fun c x y => by rcases zmod2_cases c with rfl | rfl <;> simp)


abbrev SuzukiA (φ : K ≃+* K) : Type _ := BinExt (suzukiTwistBilin K φ)

variable {K}

instance [Finite K] (φ : K ≃+* K) : Finite (SuzukiA K φ) :=
  Finite.of_equiv (K × K) ⟨fun p => ⟨p.1, p.2⟩, fun x => (x.fst, x.snd), fun _ => rfl, fun _ => rfl⟩


theorem finrank_eq_of_card [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Module.finrank (ZMod 2) K = n := by
  have : Fintype K := Fintype.ofFinite K
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
  rw [ZMod.card, ← Nat.card_eq_fintype_card, hK] at h
  exact (Nat.pow_right_injective le_rfl h).symm


end CFSG.LocalAnalysis.ComponentInitial
