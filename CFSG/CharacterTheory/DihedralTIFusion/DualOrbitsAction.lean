module

public import CFSG.CharacterTheory.DihedralTIFusion.OrbitCount
public import CFSG.CharacterTheory.OddOrderBasics.ClassAlgebra
public import CFSG.CharacterTheory.Wreathed.CentralSL2.CharacterTools
public import CFSG.CharacterTheory.Wreathed.AbelianInertiaInduction

public section

open scoped BigOperators Classical

namespace CFSG.DihedralTIFusion

open Wreathed

theorem blocksIrr_linear {H : Type} [Group H] [IsMulCommutative H] {μ : H → ℂ}
    (hμ : μ ∈ BlocksIrr H) : μ 1 = 1 ∧ ∀ x y : H, μ (x * y) = μ x * μ y := by
  have h1 : μ 1 = 1 := by
    obtain ⟨V, _, _, _, ρ, hirr, rfl⟩ := hμ
    rw [Representation.char_one,
      Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ, Nat.cast_one]
  exact ⟨h1, Wreathed.CentralSL2.blocksIrr_degree_one_mul hμ h1⟩

theorem linear_inv_mul_self {H : Type} [Group H] {μ : H → ℂ} (h1 : μ 1 = 1)
    (hmul : ∀ x y : H, μ (x * y) = μ x * μ y) (x : H) : μ x⁻¹ * μ x = 1 := by
  rw [← hmul, inv_mul_cancel, h1]

theorem natCard_blocksIrr_of_isMulCommutative (H : Type) [Group H] [Fintype H]
    [IsMulCommutative H] : Nat.card (BlocksIrr H) = Nat.card H := by
  have h := (OddOrderBasics.regular_character_degree_square_sum H).2
  have h1 : ∀ θ ∈ (BlockSectionOrthogonality.Helpers.irreducibles_finite H).toFinset,
      θ 1 ^ 2 = 1 := by
    intro θ hθ
    rw [(blocksIrr_linear ((Set.Finite.mem_toFinset _).mp hθ)).1, one_pow]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [Nat.card_eq_card_finite_toFinset (BlockSectionOrthogonality.Helpers.irreducibles_finite H)]
  exact_mod_cast h

variable {N : Type} [Group N] {K : Subgroup N}


theorem commutator_map_injective [K.Normal]
    (hfree : ∀ n : N, n ∉ K → K ⊓ Subgroup.centralizer ({n} : Set N) = ⊥) {n : N}
    (hn : n ∉ K) {a b : N} (ha : a ∈ K) (hb : b ∈ K)
    (hab : a⁻¹ * (n⁻¹ * a * n) = b⁻¹ * (n⁻¹ * b * n)) : a = b := by
  have hc : b * a⁻¹ ∈ K := K.mul_mem hb (K.inv_mem ha)
  have hfix : n⁻¹ * (b * a⁻¹) * n = b * a⁻¹ := by
    have hxb : n⁻¹ * b * n = b * (a⁻¹ * (n⁻¹ * a * n)) := by rw [hab]; group
    calc n⁻¹ * (b * a⁻¹) * n = (n⁻¹ * b * n) * (n⁻¹ * a * n)⁻¹ := by group
      _ = b * a⁻¹ := by rw [hxb]; group
  by_contra hne
  have hc1 : b * a⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h).symm
  have hmem : b * a⁻¹ ∈ K ⊓ Subgroup.centralizer ({n} : Set N) := by
    refine ⟨hc, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc b * a⁻¹ * n = n * (n⁻¹ * (b * a⁻¹) * n) := by group
      _ = n * (b * a⁻¹) := by rw [hfix]
  rw [hfree n hn, Subgroup.mem_bot] at hmem
  exact hc1 hmem

theorem conjugateNormalCharacter_eq_self_iff [Finite N] [K.Normal] (hab : IsMulCommutative K)
    (hfree : ∀ n : N, n ∉ K → K ⊓ Subgroup.centralizer ({n} : Set N) = ⊥) {μ : K → ℂ}
    (hμ : μ ∈ BlocksIrr K) (hμ1 : μ ≠ 1) (n : N) :
    conjugateNormalCharacter K μ n = μ ↔ n ∈ K := by
  have hclass : BlocksIsClassFunction μ := by
    obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hμ
    exact fun g h => Representation.char_conj ρ g h
  refine ⟨fun h => ?_, fun hn => le_characterInertiaSubgroup K hclass hn⟩
  by_contra hn
  apply hμ1
  obtain ⟨h1, hmul⟩ := blocksIrr_linear hμ
  let δ : K → K := fun k => ⟨(k : N)⁻¹ * (n⁻¹ * k * n),
    K.mul_mem (K.inv_mem k.2) (Subgroup.Normal.conj_mem' inferInstance _ k.2 n)⟩
  have hδ : Function.Injective δ := fun a b hab => Subtype.ext
    (commutator_map_injective hfree hn a.2 b.2 (congrArg Subtype.val hab))
  have hδs := Finite.injective_iff_surjective.mp hδ
  funext k'
  obtain ⟨k, rfl⟩ := hδs k'
  have hsplit : δ k = k⁻¹ * ⟨n⁻¹ * k * n, Subgroup.Normal.conj_mem' inferInstance _ k.2 n⟩ :=
    Subtype.ext rfl
  have hconj : μ ⟨n⁻¹ * k * n, Subgroup.Normal.conj_mem' inferInstance _ k.2 n⟩ = μ k :=
    congrFun h k
  rw [hsplit, hmul, hconj, linear_inv_mul_self h1 hmul]
  rfl


end CFSG.DihedralTIFusion
