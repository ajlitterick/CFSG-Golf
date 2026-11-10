module

public import Mathlib
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.GroupTheory.GroupAction.FixedPointTransport
public import CFSG.GroupTheory.Utils
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.section_2_2.example_3

public section

namespace CFSG

open scoped commutatorElement

namespace BrauerSuzuki.Helpers

theorem quat_unique_order_two {N : ℕ} [NeZero N]
    {q : QuaternionGroup N} (hq : orderOf q = 2) :
    q = QuaternionGroup.a (N : ZMod (2 * N)) := by
  cases q with
  | xa i =>
      have hfour := QuaternionGroup.orderOf_xa i
      omega
  | a i =>
      have hi_ne : i ≠ 0 := by
        intro hi
        subst i
        simp at hq
      have hpow := pow_orderOf_eq_one (QuaternionGroup.a i)
      rw [hq] at hpow
      rw [pow_two, QuaternionGroup.a_mul_a, QuaternionGroup.one_def,
        QuaternionGroup.a.injEq] at hpow
      have hcast : ((2 * i.val : ℕ) : ZMod (2 * N)) = 0 := by
        calc
          (↑(2 * i.val) : ZMod (2 * N)) =
              2 * (↑i.val : ZMod (2 * N)) := by norm_num
          _ = i + i := by rw [ZMod.natCast_zmod_val]; noncomm_ring
          _ = 0 := hpow
      have hdvd2 : 2 * N ∣ 2 * i.val :=
        (ZMod.natCast_eq_zero_iff (2 * i.val) (2 * N)).mp hcast
      have hdvd : N ∣ i.val :=
        Nat.dvd_of_mul_dvd_mul_left (by omega) hdvd2
      have hval_ne : i.val ≠ 0 := by
        simpa [ZMod.val_eq_zero] using hi_ne
      have hval : i.val = N :=
        Nat.eq_of_dvd_of_lt_two_mul hval_ne hdvd (ZMod.val_lt i)
      rw [← ZMod.natCast_zmod_val i, hval]

theorem unique_order_two_of_mulEquiv_quaternion
    {P : Type*} [Group P] {N : ℕ} [NeZero N]
    (e : P ≃* QuaternionGroup N) {x y : P}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  apply e.injective
  rw [quat_unique_order_two (e.orderOf_eq x |>.trans hx),
    quat_unique_order_two (e.orderOf_eq y |>.trans hy)]

theorem unique_order_two_in_quaternion_sylow
    {G : Type*} [Group G] (n : ℕ) (P : Sylow 2 G)
    (hquat : Nonempty ((P : Subgroup G) ≃* QuaternionGroup (2 ^ (n - 2))))
    {x y : G} (hxP : x ∈ (P : Subgroup G)) (hyP : y ∈ (P : Subgroup G))
    (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  obtain ⟨e⟩ := hquat
  have hxy : (⟨x, hxP⟩ : (P : Subgroup G)) = ⟨y, hyP⟩ := by
    apply unique_order_two_of_mulEquiv_quaternion e
    · simpa only [Subgroup.orderOf_mk] using hx
    · simpa only [Subgroup.orderOf_mk] using hy
  exact congrArg Subtype.val hxy

theorem normal_odd_le_oddCore {G : Type*} [Group G] (N : Subgroup G)
    (hN : N.Normal) (hodd : Odd (Nat.card N)) : N ≤ oddCore G := by
  exact (le_sSup ⟨hN, hodd⟩ : N ≤ oddCore G)

theorem quotient_mk_mem_center_iff {G : Type*} [Group G]
    {N : Subgroup G} [N.Normal] {t : G} :
    (QuotientGroup.mk t : G ⧸ N) ∈ Subgroup.center (G ⧸ N) ↔
      ∀ g : G, ⁅g, t⁆ ∈ N := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro ht g
    have hg := ht ((QuotientGroup.mk' N) g)
    rw [← commutatorElement_eq_one_iff_mul_comm,
      ← QuotientGroup.mk'_apply N t, ← map_commutatorElement,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hg
    exact hg
  · intro ht q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [← commutatorElement_eq_one_iff_mul_comm,
      ← QuotientGroup.mk'_apply N t, ← map_commutatorElement,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ht g

theorem odd_natCard_iff_no_involution (H : Type*) [Group H] [Finite H] :
    Odd (Nat.card H) ↔ ∀ x : H, orderOf x ≠ 2 := by
  constructor
  · intro hodd x hx
    apply hodd.not_two_dvd_nat
    rw [← hx]
    exact orderOf_dvd_natCard x
  · intro hno
    rw [← Nat.not_even_iff_odd]
    intro heven
    obtain ⟨x, hx⟩ :=
      exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
    exact hno x hx

end BrauerSuzuki.Helpers

end CFSG
