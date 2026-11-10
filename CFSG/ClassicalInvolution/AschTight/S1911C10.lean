module

public import CFSG.ClassicalInvolution.AschTight.Hall196Basic
public import CFSG.ClassicalInvolution.AschTight.S1911EtaY

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

theorem le_sec19X_member (hd : Sec19Data p f K z S W) : K ≤ sec19X K z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htb := hd.tight.toTightBranch
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_tight htb
  set N : Subgroup K := (sec19X K z).subgroupOf K with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    have hk := Hall196.centralizer_le_normalizer_sec19X K z (hKz k.2)
    simpa using (Subgroup.mem_normalizer_iff.mp hk n).mp hn
  obtain ⟨Q⟩ : Nonempty (Sylow 2 K) := inferInstance
  have hQN : (Q : Subgroup K) ≤ N := by
    intro x hx
    rw [hN, Subgroup.mem_subgroupOf]
    refine le_iSup₂ (f := fun (B : Subgroup G) (_ : (B ∈ USet (CoreAssembly.conjClass K) ∨
      B ∈ RSet (CoreAssembly.conjClass K)) ∧ B ≤ Subgroup.centralizer ({z} : Set G)) => B)
      ((Q : Subgroup K).map K.subtype)
      ⟨Or.inr ⟨K, CoreAssembly.mem_conjClass_self K, Q, rfl⟩,
        (Subgroup.map_subtype_le _).trans hKz⟩ ⟨x, hx, rfl⟩
  have hodd : Odd (Nat.card (K ⧸ N)) := by
    rw [← Subgroup.index]
    have h1 : N.index ∣ (Q : Subgroup K).index := Subgroup.index_dvd_of_le hQN
    have h2 : ¬ 2 ∣ (Q : Subgroup K).index := Q.not_dvd_index
    exact Nat.not_even_iff_odd.mp fun h => h2 ((even_iff_two_dvd.mp h).trans h1)
  have hsol : Group.IsSolvable (K ⧸ N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Group.IsPerfect K := hd.tight.branch.member.perfect
  have hsub : Subsingleton (K ⧸ N) := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable (K ⧸ N) hsol
  intro k hk
  have h1 : (QuotientGroup.mk ⟨k, hk⟩ : K ⧸ N) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf] at h1
  exact h1


omit [Finite G] in
theorem mem_oddCore_of_mem {M : Subgroup G} [Finite M]
    (hKM : K ≤ Subgroup.normalizer (M : Set G)) (hM : Odd (Nat.card M)) {k : K}
    (hk : (k : G) ∈ M) : k ∈ classicalInvolutionOddCore K := by
  have hle : (K ⊓ M).subgroupOf K ≤ classicalInvolutionOddCore K := by
    unfold classicalInvolutionOddCore
    refine le_sSup ⟨⟨fun n hn g => ?_⟩, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hn ⊢
      refine ⟨K.mul_mem (K.mul_mem g.2 hn.1) (K.inv_mem g.2), ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp (hKM g.2) n).mp hn.2
      simpa using this
    · have e : Nat.card ((K ⊓ M).subgroupOf K) = Nat.card ↥(K ⊓ M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
      rw [e]
      exact hM.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  exact hle (Subgroup.mem_subgroupOf.mpr ⟨k.2, hk⟩)


end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
