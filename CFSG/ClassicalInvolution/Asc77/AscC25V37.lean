module

public import CFSG.ClassicalInvolution.Asc77.AscC25V33
public import CFSG.ClassicalInvolution.Asc77.AscC25V34
public import CFSG.ClassicalInvolution.Asc77.AscC25V19
public import CFSG.ClassicalInvolution.Asc77.AscC25Y6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G]


theorem exists_fixed_lift {Z : Type*} [Group Z] [Finite Z] (O : Subgroup Z) [O.Normal]
    (hO : Odd (Nat.card O)) {ζ : Z} (hζ : ζ * ζ = 1) {x₀ : Z}
    (hx : (QuotientGroup.mk (ζ * x₀ * ζ⁻¹) : Z ⧸ O) = QuotientGroup.mk x₀) :
    ∃ t₀ : Z, (QuotientGroup.mk t₀ : Z ⧸ O) = QuotientGroup.mk x₀ ∧ ζ * t₀ * ζ⁻¹ = t₀ := by
  classical
  let := Fintype.ofFinite Z
  let α : Type _ := {x : Z // (QuotientGroup.mk x : Z ⧸ O) = QuotientGroup.mk x₀}
  have hζi : ζ⁻¹ = ζ := inv_eq_of_mul_eq_one_right hζ
  have hmem : ∀ x : α, (QuotientGroup.mk (ζ * x.1 * ζ⁻¹) : Z ⧸ O) = QuotientGroup.mk x₀ := by
    intro x
    have h1 := (QuotientGroup.eq.mp x.2)
    have h2 := (QuotientGroup.eq.mp hx)
    rw [QuotientGroup.eq]
    have h3 : (ζ * x.1 * ζ⁻¹)⁻¹ * x₀ = (ζ * x.1 * ζ⁻¹)⁻¹ * (ζ * x₀ * ζ⁻¹) *
        ((ζ * x₀ * ζ⁻¹)⁻¹ * x₀) := by group
    rw [h3]
    refine Subgroup.mul_mem _ ?_ h2
    have h4 : (ζ * x.1 * ζ⁻¹)⁻¹ * (ζ * x₀ * ζ⁻¹) = ζ * (x.1⁻¹ * x₀) * ζ⁻¹ := by group
    rw [h4]
    have : ζ * (x.1⁻¹ * x₀) * ζ⁻¹ ∈ O := (inferInstance : O.Normal).conj_mem _ (by
      have := (QuotientGroup.eq.mp x.2)
      exact this) ζ
    exact this
  let σ : Equiv.Perm α :=
    { toFun := fun x => ⟨ζ * x.1 * ζ⁻¹, hmem x⟩
      invFun := fun x => ⟨ζ * x.1 * ζ⁻¹, hmem x⟩
      left_inv := fun x => Subtype.ext (by
        change ζ * (ζ * x.1 * ζ⁻¹) * ζ⁻¹ = x.1
        calc ζ * (ζ * x.1 * ζ⁻¹) * ζ⁻¹ = (ζ * ζ) * x.1 * (ζ * ζ)⁻¹ := by group
          _ = x.1 := by rw [hζ]; group)
      right_inv := fun x => Subtype.ext (by
        change ζ * (ζ * x.1 * ζ⁻¹) * ζ⁻¹ = x.1
        calc ζ * (ζ * x.1 * ζ⁻¹) * ζ⁻¹ = (ζ * ζ) * x.1 * (ζ * ζ)⁻¹ := by group
          _ = x.1 := by rw [hζ]; group) }
  have hσ2 : σ ^ 2 ^ 1 = 1 := by
    ext x
    change ζ * (ζ * x.1 * ζ⁻¹) * ζ⁻¹ = x.1
    calc ζ * (ζ * x.1 * ζ⁻¹) * ζ⁻¹ = (ζ * ζ) * x.1 * (ζ * ζ)⁻¹ := by group
      _ = x.1 := by rw [hζ]; group
  have hcard : Nat.card α = Nat.card O := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x₀⁻¹ * x.1, QuotientGroup.eq.mp x.2.symm⟩
        invFun := fun o => ⟨x₀ * o.1, by
          rw [QuotientGroup.eq]
          simp⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun o => Subtype.ext (by simp) }
  have hodd : ¬ 2 ∣ Fintype.card α := by
    rw [← Nat.card_eq_fintype_card, hcard]
    have := Nat.odd_iff.mp hO
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxσ⟩ := Equiv.Perm.exists_fixed_point_of_prime hodd hσ2
  refine ⟨x.1, x.2, ?_⟩
  have := congrArg Subtype.val hxσ
  exact this

omit [Finite G] in
theorem conjSub_perfectCoreIn_eq {K : Subgroup G} {a c : G}
    (hc : c ∈ Subgroup.centralizer ({a} : Set G)) (hcK : c ∈ Subgroup.normalizer (K : Set G)) :
    conjSub (⟨c, hc⟩ : ↥(Subgroup.centralizer ({a} : Set G))) (perfectCoreIn K a) =
      perfectCoreIn K a := by
  have hnN : c ∈ Subgroup.normalizer
      ((K ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    rw [conjSub, Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective]
    change conjSub c K ⊓ conjSub c (Subgroup.centralizer ({a} : Set G)) = _
    rw [conjSub_eq_of_mem_normalizer hcK,
      conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hc)]
  have h1 := conjSub_eq_of_mem_normalizer (perfectResidualOf_normalizer_contains _ hnN)
  unfold perfectCoreIn
  rw [conjSub_subgroupOf _ ⟨c, hc⟩, h1]


end Basic

section Omega5

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' a : G}


local notation "Lₐ" => perfectCoreIn K' a


end Omega5

end CFSG.ClassicalInvolution.Asc77.C25V
