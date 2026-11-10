module

public import CFSG.CharacterTheory.BlockBasics.Defects
public import CFSG.CharacterTheory.PSL2Table.Blocks
public import CFSG.CharacterTheory.PSL2Table.DirectProduct

public section

namespace CFSG.PSL2Table

open Matrix
open scoped MatrixGroups
open CFSG CFSG.BrauerThirdMainTheorem.Helpers CFSG.DirectProduct

section General

variable (m : Ideal BlocksAlgInt)

theorem charP_two (hm : m.IsMaximal) (h2 : (2 : BlocksAlgInt) ∈ m) :
    CharP (BlocksAlgInt ⧸ m) 2 := by
  have := Ideal.Quotient.nontrivial_iff.mpr hm.ne_top
  rw [CharP.charP_iff_prime_eq_zero Nat.prime_two, ← map_natCast (Ideal.Quotient.mk m) 2,
    Ideal.Quotient.eq_zero_iff_mem]
  exact_mod_cast h2

theorem intCast_not_mem_localMaxIdeal (hm : m.IsMaximal) (h2 : (2 : BlocksAlgInt) ∈ m) {n : ℤ}
    (hn : Odd n) : (n : ℂ) ∉ BlocksLocalMaxIdeal m := by
  intro h
  apply odd_not_mem m hm h2 hn
  rw [← localMaxIdeal_algInt_iff m hm]
  simpa using h

theorem mem_of_odd_mul_mem (hm : m.IsMaximal) (h2 : (2 : BlocksAlgInt) ∈ m) {n : ℤ}
    (hn : Odd n) {s : ℂ} (h : (n : ℂ) * s ∈ BlocksLocalMaxIdeal m) :
    s ∈ BlocksLocalMaxIdeal m := by
  have hn0 : (n : ℂ) ≠ 0 := by
    have : n ≠ 0 := by
      rintro rfl
      exact Int.not_even_iff_odd.mpr hn ⟨0, rfl⟩
    exact_mod_cast this
  have := localMaxIdeal_mul_localRing m hm h (inv_odd_mem_localRing m hm h2 hn)
  rwa [mul_comm (n : ℂ) s, mul_assoc, mul_inv_cancel₀ hn0, mul_one] at this

theorem pow_mem_localRing (hm : m.IsMaximal) {x : ℂ} (hx : x ∈ BlocksLocalRing m) (n : ℕ) :
    x ^ n ∈ BlocksLocalRing m := by
  induction n with
  | zero => simpa using localRing_one m hm
  | succ n ih =>
    rw [pow_succ]
    exact localRing_mul m hm ih hx


theorem mk_conj_eq {G : Type} [Group G] (g h : G) :
    ConjClasses.mk (h * g * h⁻¹) = ConjClasses.mk g :=
  ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h, rfl⟩).symm


end General

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]


theorem not_four_dvd_orderOf (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (h8 : Fintype.card F % 8 = 3 ∨ Fintype.card F % 8 = 5)
    (g : PSL(2, F)) : ¬ 4 ∣ orderOf g := by
  have hT := card_splitTorus (Ring.two_ne_zero hF) (F := F)
  have hS := card_nonsplitTorus hF hν
  have hP := card_unipotent (Ring.two_ne_zero hF) (F := F)
  have key : ∀ {H : Subgroup PSL(2, F)}, ¬ 4 ∣ Nat.card H → ∀ x ∈ H, x ≠ 1 → ¬ 4 ∣ orderOf x :=
    fun hH x hx _ h4 => hH (h4.trans (Subgroup.orderOf_dvd_natCard _ hx))
  apply forall_of_families hF hq hν (P := fun g => ¬ 4 ∣ orderOf g)
  · intro g h hg
    have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective g
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rwa [this] at hg
  · rw [orderOf_one]
    omega
  · exact key (by omega)
  · exact key (by omega)
  · exact key (by omega)


end CFSG.PSL2Table
