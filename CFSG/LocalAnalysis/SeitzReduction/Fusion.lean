module

public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.SeitzReduction

open Subgroup

section Group

variable {G : Type*} [Group G]


end Group

section Field

open Polynomial

theorem natCard_le_of_forall_pow_eq_self {K : Type*} [Field K] {q : ℕ} (hq : 1 < q) (S : Set K)
    (hS : ∀ x ∈ S, x ^ q = x) : Nat.card S ≤ q := by
  classical
  have hne := FiniteField.X_pow_card_sub_X_ne_zero K hq
  have hsub : S ⊆ ((X ^ q - X : K[X]).roots.toFinset : Set K) := fun x hx => by
    simp [Polynomial.mem_roots hne, hS x hx]
  calc Nat.card S ≤ Nat.card ((X ^ q - X : K[X]).roots.toFinset : Set K) :=
        Nat.card_mono (Finset.finite_toSet _) hsub
    _ = (X ^ q - X : K[X]).roots.toFinset.card := by
        rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    _ ≤ Multiset.card (X ^ q - X : K[X]).roots := Multiset.toFinset_card_le _
    _ ≤ (X ^ q - X : K[X]).natDegree := Polynomial.card_roots' _
    _ = q := FiniteField.X_pow_card_sub_X_natDegree_eq K hq

theorem pow_pow_eq_self_of_natCard_eq_sq {K : Type*} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (c : K) : (c ^ q) ^ q = c := by
  have := Fintype.ofFinite K
  rw [← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem exists_add_pow_eq_of_pow_eq {K : Type*} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) {d : K} (hd : d ^ 2 ^ f = d) :
    ∃ c : K, c + c ^ 2 ^ f = d := by
  set q := 2 ^ f
  have hq : 1 < q := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.2 inferInstance
    rw [hK] at h1
    by_contra h
    have h' : q ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hadd : ∀ a b : K, (a + b) ^ q = a ^ q + b ^ q := fun a b => add_pow_char_pow a b 2 f
  have hqq := pow_pow_eq_self_of_natCard_eq_sq hK
  let F : AddSubgroup K :=
    { carrier := {x | x ^ q = x}
      add_mem' := fun {a b} (ha : a ^ q = a) (hb : b ^ q = b) =>
        show (a + b) ^ q = a + b by rw [hadd, ha, hb]
      zero_mem' := show (0 : K) ^ q = 0 from zero_pow (by omega)
      neg_mem' := fun {a} (ha : a ^ q = a) => show (-a) ^ q = -a by rw [CharTwo.neg_eq, ha] }
  let T : K →+ F :=
    { toFun := fun c => ⟨c + c ^ q, show (c + c ^ q) ^ q = c + c ^ q by rw [hadd, hqq, add_comm]⟩
      map_zero' := Subtype.ext (show (0 : K) + 0 ^ q = 0 by rw [zero_pow (by omega), add_zero])
      map_add' := fun a b => Subtype.ext (show (a + b) + (a + b) ^ q = (a + a ^ q) + (b + b ^ q) by
        rw [hadd]; abel) }
  have hF : Nat.card F ≤ q := natCard_le_of_forall_pow_eq_self hq (F : Set K) fun _ hx => hx
  have hker : Nat.card T.ker ≤ q := natCard_le_of_forall_pow_eq_self hq (T.ker : Set K)
    fun x hx => (CharTwo.add_eq_zero.1 (congrArg Subtype.val (AddMonoidHom.mem_ker.1 hx))).symm
  have hsurj : Function.Surjective T := by
    refine AddMonoidHom.surjective_of_card_ker_le_div T (hker.trans ?_)
    rw [hK, Nat.le_div_iff_mul_le Nat.card_pos, sq]
    exact Nat.mul_le_mul_left q hF
  obtain ⟨c, hc⟩ := hsurj ⟨d, hd⟩
  exact ⟨c, congrArg Subtype.val hc⟩


end Field

end CFSG.SeitzReduction
