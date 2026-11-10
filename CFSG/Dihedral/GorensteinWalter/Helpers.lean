module

public import CFSG.Dihedral.GorensteinWalter.Support
public import Mathlib.GroupTheory.Focal
public import Mathlib.GroupTheory.Perm.Subgroup
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG

open scoped commutatorElement Pointwise

namespace GorensteinWalter.Helpers

def dihedralRotations (n : ℕ) : Subgroup (DihedralGroup n) where
  carrier := Set.range DihedralGroup.r
  one_mem' := ⟨0, DihedralGroup.r_zero⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, (DihedralGroup.r_mul_r i j).symm⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨-i, (DihedralGroup.inv_r i).symm⟩

@[simp]
lemma r_mem_dihedralRotations {n : ℕ} (i : ZMod n) :
    DihedralGroup.r i ∈ dihedralRotations n :=
  ⟨i, rfl⟩

@[simp]
lemma sr_not_mem_dihedralRotations {n : ℕ} (i : ZMod n) :
    DihedralGroup.sr i ∉ dihedralRotations n := by
  rintro ⟨j, h⟩
  injection h

private def rotationSubgroup {G : Type*} [Group G] (P : Sylow 2 G) {n : ℕ}
    (e : P ≃* DihedralGroup n) : Subgroup G :=
  (dihedralRotations n).map ((P : Subgroup G).subtype.comp e.symm.toMonoidHom)


private lemma dihedralIndex_eq_two_pow {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) {n : ℕ}
    (h : Nonempty ((P : Subgroup G) ≃* DihedralGroup n)) :
    ∃ m : ℕ, n = 2 ^ m := by
  obtain ⟨e⟩ := h
  let : Finite (DihedralGroup n) := Finite.of_equiv _ e.toEquiv
  obtain ⟨r, hr⟩ := (P.isPGroup'.of_equiv e).exists_card_eq
  rw [DihedralGroup.nat_card] at hr
  cases r with
  | zero => simp at hr
  | succ m =>
      rw [pow_succ, Nat.mul_comm (2 ^ m) 2] at hr
      exact ⟨m, Nat.mul_left_cancel zero_lt_two hr⟩

lemma commutator_eq_top_of_noncommutative {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : commutator G = ⊤ := by
  rcases (Subgroup.commutator_normal (⊤ : Subgroup G) (⊤ : Subgroup G)).eq_bot_or_eq_top with h | h
  · obtain ⟨a, b, hab⟩ := hnonab
    exact (hab ((isMulCommutative_iff.mp ((commutator_eq_bot_iff G).mp h)) a b)).elim
  · exact h

lemma center_eq_bot_of_noncommutative {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnonab
    exact (hab ((isMulCommutative_iff.mp (Subgroup.center_eq_top_iff.mp h)) a b)).elim

private lemma sylow_ne_top_of_noncommutative {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) :
    (P : Subgroup G) ≠ ⊤ := by
  intro htop
  have hpTop : IsPGroup 2 (⊤ : Subgroup G) := by
    rw [← htop]
    exact P.isPGroup'
  have hpG : IsPGroup 2 G := hpTop.of_equiv Subgroup.topEquiv
  let : Nontrivial (Subgroup.center G) := hpG.center_nontrivial
  simpa [center_eq_bot_of_noncommutative hnonab] using
    (Finite.one_lt_card (α := Subgroup.center G))

private lemma dihedralIndex_ne_one {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) {n : ℕ}
    (h : Nonempty ((P : Subgroup G) ≃* DihedralGroup n)) : n ≠ 1 := by
  intro hn
  subst n
  obtain ⟨e⟩ := h
  have hPcard : Nat.card P = 2 := by
    calc
      Nat.card P = Nat.card (DihedralGroup 1) := Nat.card_congr e.toEquiv
      _ = 2 := by simpa using (DihedralGroup.card (n := 1))
  have htwo : 2 ∣ Nat.card G := hPcard ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup G)
  have hmin : (Nat.card G).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr htwo
  have hcyc : IsCyclic P := e.isCyclic.mpr (DihedralGroup.isCyclic_iff.mpr rfl)
  let hnorm := hcyc.normalizer_le_centralizer hmin
  let K := (MonoidHom.transferSylow P hnorm).ker
  have hcomp : K.IsComplement' P := MonoidHom.ker_transferSylow_isComplement' P hnorm
  have hKnormal : K.Normal := inferInstance
  rcases hKnormal.eq_bot_or_eq_top with hKbot | hKtop
  · have hPtop : (P : Subgroup G) = ⊤ := by
      rw [hKbot] at hcomp
      exact Subgroup.isComplement'_bot_left.mp hcomp
    exact sylow_ne_top_of_noncommutative hnonab P hPtop
  · have hPbot : (P : Subgroup G) = ⊥ := by
      rw [hKtop] at hcomp
      exact Subgroup.isComplement'_top_left.mp hcomp
    rw [hPbot, Subgroup.card_bot] at hPcard
    omega

lemma dihedralIndex_eq_two_pow_pos {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) {n : ℕ}
    (h : Nonempty ((P : Subgroup G) ≃* DihedralGroup n)) :
    ∃ m > 0, n = 2 ^ m := by
  obtain ⟨m, hm⟩ := dihedralIndex_eq_two_pow P h
  have hn1 := dihedralIndex_ne_one hnonab P h
  have hm0 : m ≠ 0 := by
    intro hm0
    apply hn1
    simpa [hm0] using hm
  exact ⟨m, Nat.pos_of_ne_zero hm0, hm⟩


private lemma odd_index_of_sylow_le {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (H : Subgroup G) (hPH : (P : Subgroup G) ≤ H) :
    Odd H.index := by
  rw [← Nat.not_even_iff_odd]
  intro hEven
  apply P.not_dvd_index
  exact (even_iff_two_dvd.mp hEven).trans (Subgroup.index_dvd_of_le hPH)


noncomputable local instance quotientFintype {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} : Fintype (G ⧸ H) :=
  Fintype.ofFinite (G ⧸ H)

noncomputable local instance quotientDecidableEq {G : Type*} [Group G]
    {H : Subgroup G} : DecidableEq (G ⧸ H) :=
  Classical.decEq (G ⧸ H)


private lemma faithfulSMul_quotient_of_normalCore_eq_bot {G : Type*} [Group G]
    (H : Subgroup G) (hcore : H.normalCore = ⊥) : FaithfulSMul G (G ⧸ H) := by
  rw [faithfulSMul_iff]
  intro g hg
  have hgKer : g ∈ (MulAction.toPermHom G (G ⧸ H)).ker := by
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro q
    change g • q = q
    exact hg q
  have hgCore : g ∈ H.normalCore := by
    rw [H.normalCore_eq_ker]
    exact hgKer
  rw [hcore] at hgCore
  simpa using hgCore


end GorensteinWalter.Helpers

end CFSG
