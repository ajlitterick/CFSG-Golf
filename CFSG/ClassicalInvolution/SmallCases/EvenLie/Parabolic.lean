module

public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Basic
public import CFSG.Blueprint.Catalog
import CFSG.LieType.BorelTits.AllModels

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem centralizer_eq_normalizer_zpowers_of_orderOf_eq_two {F : Type*} [Group F] {z : F}
    (hz : orderOf z = 2) :
    Subgroup.centralizer ({z} : Set F) =
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup F) : Set F) := by
  apply le_antisymm
  · rw [← centralizer_zpowers_eq z]
    exact Subgroup.centralizer_le_normalizer _
  · intro g hg
    rw [Subgroup.mem_normalizer_iff] at hg
    have h1 : g * z * g⁻¹ ∈ Subgroup.zpowers z := (hg z).mp (Subgroup.mem_zpowers z)
    have hne : g * z * g⁻¹ ≠ 1 := by
      intro h
      have : z = 1 := by
        have h2 := congrArg (fun x => g⁻¹ * x * g) h
        simpa [mul_assoc] using h2
      rw [this, orderOf_one] at hz
      exact absurd hz (by norm_num)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hmod : z ^ (n % 2) = z ^ n := by
      have := zpow_mod_orderOf z n
      rwa [hz, Nat.cast_ofNat] at this
    have hcase : g * z * g⁻¹ = z := by
      rcases Int.emod_two_eq_zero_or_one n with h0 | h0
      · exfalso
        apply hne
        rw [← hn, ← hmod, h0, zpow_zero]
      · rw [← hn, ← hmod, h0, zpow_one]
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (mul_inv_eq_iff_eq_mul.mp hcase).symm

theorem isTwoLocal_centralizer_of_orderOf_eq_two {F : Type*} [Group F] {z : F}
    (hz : orderOf z = 2) : IsTwoLocal (Subgroup.centralizer ({z} : Set F)) :=
  ⟨Subgroup.zpowers z, (isPGroup_zpowers_of_orderOf_eq_two hz).2,
    (isPGroup_zpowers_of_orderOf_eq_two hz).1,
    centralizer_eq_normalizer_zpowers_of_orderOf_eq_two hz⟩

theorem NoNonsolvableClassical.of_isCharTwoType {F : Type*} [Group F] [Finite F]
    (h : IsCharTwoType F) : NoNonsolvableClassical F :=
  fun _ hz => NoNonsolvableClassicalAt.of_twoConstrained
    (h _ (isTwoLocal_centralizer_of_orderOf_eq_two hz)) hz


end CFSG.ClassicalInvolution
