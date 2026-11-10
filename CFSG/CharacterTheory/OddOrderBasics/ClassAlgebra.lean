module

public import CFSG.Adapters.QiuzhenLegacy.Theory.Character.Divisibility
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Divisibility
public import CFSG.CharacterTheory.Blocks.IrreducibleCharacterBasis
public import CFSG.LocalAnalysis.SignalizerFunctor.RegularCharacterValues

public section

open scoped BigOperators Classical

namespace CFSG.OddOrderBasics

open BlockSectionOrthogonality.Helpers

theorem regular_character_degree_square_sum (H : Type) [Group H] [Fintype H] :
    (Representation.leftRegular ℂ H).character =
        ∑ θ ∈ (irreducibles_finite H).toFinset, θ 1 • θ ∧
      ∑ θ ∈ (irreducibles_finite H).toFinset, θ 1 ^ 2 = (Nat.card H : ℂ) := by
  set Reg := (Representation.leftRegular ℂ H).character with hRegdef
  have hReg : ∀ g, Reg g = if g = 1 then (Nat.card H : ℂ) else 0 := fun g => by
    rw [hRegdef, SignalizerFunctor.Helpers.finite_group_regular_character]
  have hclass : BlocksIsClassFunction Reg := fun g h =>
    Representation.char_conj (Representation.leftRegular ℂ H) g h
  have hcoeff : ∀ θ ∈ BlocksIrr H, BlocksInnerProduct Reg θ = θ 1 := by
    intro θ hθ
    obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hθ
    have hcard : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    rw [BlocksInnerProduct, Finset.sum_eq_single (1 : H)]
    · rw [hReg, ite_eq_left rfl, Representation.char_one, Complex.conj_natCast]
      field_simp
    · intro g _ hg
      rw [hReg, ite_eq_right hg, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hexp := (irreducible_character_basis H).2.2.2 Reg hclass
  have hexp' : Reg = ∑ θ ∈ (irreducibles_finite H).toFinset, θ 1 • θ := by
    rw [hexp]
    refine Finset.sum_congr rfl fun θ hθ => ?_
    rw [hcoeff θ ((Set.Finite.mem_toFinset _).mp hθ)]
  refine ⟨hexp', ?_⟩
  have h1 := congrFun hexp' 1
  rw [hReg, ite_eq_left rfl, Finset.sum_apply] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, sq]

theorem irreducible_character_degree_divides_order {G : Type} [Group G] [Finite G]
    (θ : G → ℂ) (hθ : θ ∈ BlocksIrr G) :
    ∃ d : ℕ, 0 < d ∧ θ 1 = d ∧ d ∣ Nat.card G ∧
      ∀ p : ℕ, p.Prime → IsPGroup p G → ∃ a : ℕ, d = p ^ a := by
  obtain ⟨V, _, _, _, ρ, hirr, rfl⟩ := hθ
  have : Nontrivial V := Theory.Character.irreducible_nontrivial ρ
  refine ⟨Module.finrank ℂ V, Module.finrank_pos, Representation.char_one ρ,
    Theory.Character.irreducible_dimension_dvd_group_order ρ, fun p hp hG => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hG.exists_card_eq
  have hdvd := Theory.Character.irreducible_dimension_dvd_group_order ρ
  rw [hn] at hdvd
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact ⟨a, ha⟩


end CFSG.OddOrderBasics
