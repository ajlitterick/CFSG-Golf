module

public import CFSG.CharacterTheory.Wreathed.SameFieldOddKernelFaithful
public import CFSG.CharacterTheory.TwoRankLowerBound.FiniteCharacters

public noncomputable section

namespace CFSG.Wreathed.SameFieldOddKernel

open CFSG.TwoRankLowerBound.Helpers
open scoped ComplexOrder

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

@[expose] def fixedSpaceLayerRepresentation (ρ : Representation ℂ G V)
    (K : Subgroup G) (O : Subgroup K) [O.Normal] (L : Subgroup (K ⧸ O)) :
    Representation ℂ L (Representation.invariants ((ρ.comp K.subtype).comp O.subtype)) :=
  (fixedSpaceQuotientRepresentation ρ K O).comp L.subtype


variable [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
theorem fixedSpaceLayerRepresentation_character (ρ : Representation ℂ G V)
    (K : Subgroup G) (O : Subgroup K) [O.Normal] (L : Subgroup (K ⧸ O)) (g : L) :
    (fixedSpaceLayerRepresentation ρ K O L).character g =
      (fixedSpaceQuotientRepresentation ρ K O).character (g : K ⧸ O) := rfl


@[expose] def fixedSpaceLayerComplexRepresentation (ρ : Representation ℂ G V)
    (K : Subgroup G) (O : Subgroup K) [O.Normal] (L : Subgroup (K ⧸ O)) :
    FiniteComplexRepresentation.{0, 0} L where
  vector := Representation.invariants ((ρ.comp K.subtype).comp O.subtype)
  representation := fixedSpaceLayerRepresentation ρ K O L


theorem fixedSpaceLayerRepresentation_cyclic_sections [Fintype G]
    (ρ : Representation ℂ G V) (K : Subgroup G) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (L : Subgroup (K ⧸ O))
    (y : K) (a : ℕ) (ha : 1 ≤ a) (hy : orderOf y = 2 ^ a)
    (yL : L) (hyL : (yL : K ⧸ O) = QuotientGroup.mk' O y) (c : ℂ)
    (hc : ∀ h : ℤ, Odd h → ∀ z : G, Odd (orderOf z) →
      z ∈ Subgroup.centralizer ({(y : G)} : Set G) →
      ρ.character ((y : G) ^ h * z) = c) :
    ∀ h : ℤ, Odd h → ∀ z : L, Odd (orderOf z) →
      z ∈ Subgroup.centralizer ({yL} : Set L) →
      (fixedSpaceLayerRepresentation ρ K O L).character (yL ^ h * z) = c := by
  intro h hh z hz hzy
  have hzX : Odd (orderOf (z : K ⧸ O)) := by rwa [Subgroup.orderOf_coe]
  have hzyX : (z : K ⧸ O) ∈
      Subgroup.centralizer ({QuotientGroup.mk' O y} : Set (K ⧸ O)) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hzy ⊢
    have h := congrArg Subtype.val hzy
    simpa only [Subgroup.coe_mul, hyL] using h
  have hvalue := (odd_kernel_fixed_space_character_preserves_cyclic_two_sections
    K O hO y a ha hy ρ c hc).2.2.1 h hh (z : K ⧸ O) hzX hzyX
  rw [fixedSpaceLayerRepresentation_character]
  simpa only [Subgroup.coe_mul, Subgroup.coe_zpow, hyL, QuotientGroup.mk'_apply] using hvalue.1


end CFSG.Wreathed.SameFieldOddKernel
