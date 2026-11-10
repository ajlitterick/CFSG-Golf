module

public import CFSG.ClassicalInvolution.Q3.Q3TCD4
public import CFSG.ClassicalInvolution.Q3.Q3TCP1

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TC

open scoped MatrixGroups Matrix
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair B12 B23)
open CFSG.ClassicalInvolution.RouteD.NonClassical (le_centralizer_of_commutes)

theorem statedLieAdmissible_sl4_three : StatedLieAdmissible .PSL 4 3 1 :=
  ⟨Nat.prime_three, Nat.one_pos, by show 2 ≤ 4; omega,
    fun h => by have := congrArg Prod.fst h; simp at this,
    fun h => by have := congrArg Prod.fst h; simp at this⟩

theorem statedLieAdmissible_plus4_three : StatedLieAdmissible .POmegaPlus 4 3 1 :=
  ⟨Nat.prime_three, Nat.one_pos, le_rfl⟩

section Statements


@[expose] def D4LinearClique3 : Prop :=
  ∀ R₁ ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D,
    ∀ R₂ ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D,
      ∀ R₃ ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D,
        Commutes R₁ R₂ → (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₃) →
          ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₂ R₃


end Statements

section Lift

theorem not_three_dvd_card_center_of_cop {K : Type} [Group K] [Finite K]
    (h : ∀ w ∈ Subgroup.center K, ¬ 3 ∣ orderOf w) : ¬ 3 ∣ Nat.card (Subgroup.center K) := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) 3 h3
  exact h (x : K) x.2 (by rw [Subgroup.orderOf_coe, hx])


theorem exists_lin_of_map_pow3 {KY X : Type} [Group KY] [Group X] [Finite KY]
    (hC : ¬ 3 ∣ Nat.card (Subgroup.center KY)) (ψ : KY →* X)
    (hker : ψ.ker ≤ Subgroup.center KY) {R₁ R₂ : Subgroup KY} (hR₁ : Pow3 R₁) (hR₂ : Pow3 R₂)
    (h : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R₁.map ψ) (R₂.map ψ)) :
    ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₂ := by
  obtain ⟨W, hW⟩ := h
  obtain ⟨θ, hrange, hθ, hU, hV⟩ := WeakCT.pair_normalize hW
  have hWsup := Gaps.linear_eq_sup hW
  have hle : θ.range ≤ ψ.range := by
    rw [hrange, hWsup]
    exact sup_le (Subgroup.map_le_range ψ R₁) (Subgroup.map_le_range ψ R₂)
  let θ' : SL(3, GaloisField 3 1) →* ψ.range := θ.codRestrict ψ.range fun s => hle ⟨s, rfl⟩
  have hπ : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
  have hπker : ψ.rangeRestrict.ker ≤ Subgroup.center KY := by
    rwa [MonoidHom.ker_rangeRestrict]
  have hπC : ¬ 3 ∣ Nat.card ψ.rangeRestrict.ker := fun hd =>
    hC (hd.trans (Subgroup.card_dvd_of_le hπker))
  obtain ⟨α, hα, -⟩ := ModelFacts.LinearAut.sl_existsUnique_lift (n := 3) (K := GaloisField 3 1)
    (p := 3) (by norm_num) hπ hπker hπC θ'
  have hαψ : ∀ s, ψ (α s) = θ s := fun s => congrArg Subtype.val (DFunLike.congr_fun hα s)
  have hψα : ψ.comp α = θ := MonoidHom.ext hαψ
  have hcop : ∀ z ∈ ψ.ker, ¬ 3 ∣ orderOf z := fun z hz h3 =>
    hC (h3.trans (Subgroup.orderOf_dvd_natCard _ (hker hz)))
  have hp₁ : Pow3 ((B12 (GaloisField 3 1)).map α) := (pow3_range_sl2 card_gf3 _).map α
  have hp₂ : Pow3 ((B23 (GaloisField 3 1)).map α) := (pow3_range_sl2 card_gf3 _).map α
  have hR₁' : (B12 (GaloisField 3 1)).map α = R₁ :=
    eq_of_map_eq_of_pow3 ψ hker hcop hp₁ hR₁ (by rw [Subgroup.map_map, hψα, hU])
  have hR₂' : (B23 (GaloisField 3 1)).map α = R₂ :=
    eq_of_map_eq_of_pow3 ψ hker hcop hp₂ hR₂ (by rw [Subgroup.map_map, hψα, hV])
  have hid : (MulAut.conj (1 : SL(3, GaloisField 3 1))⁻¹).toMonoidHom = MonoidHom.id _ := by
    ext
    simp
  refine ⟨α.range, α, 1, rfl, fun s hs => hθ ?_, Or.inl ⟨?_, ?_⟩⟩
  · rw [MonoidHom.mem_ker, ← hαψ, hs, map_one]
  · rw [hid, Subgroup.map_id, hR₁']
  · rw [hid, Subgroup.map_id, hR₂']

end Lift

section Bridge


end Bridge

end CFSG.ClassicalInvolution.Q3.Q3TC
