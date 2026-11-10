module

public import CFSG.Quasithin.Recognition.Stroth.BenderOmega
public import CFSG.Quasithin.Recognition.Stroth.BenderH7
public import CFSG.Quasithin.Recognition.Stroth.BenderDisplacement
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518D5
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15410Section

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

private theorem isSzU3Quot_oTwoQuot_congr {H K : Subgroup G} (hHK : H = K) {q : ℕ}
    (h : IsSzU3Quot (oTwoQuot ↥H) q) : IsSzU3Quot (oTwoQuot ↥K) q := by
  subst hHK
  exact h


private theorem sup_eq_one_of_S_eq {L1 L2 S : Subgroup G}
    (hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S) : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
  have h1 : L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) := by
    conv_lhs => rw [hS1]
  rw [h1]
  conv_lhs => rw [← sup_assoc]
  rw [show L1 ⊔ (S ⊓ L1) = L1 from le_antisymm (sup_le le_rfl inf_le_right) le_sup_left]

private theorem pCoreOf_sup_one_of_S_eq {L1 L2 S : Subgroup G} (hF : Hyp111 L1 L2 S)
    (hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S) :
    pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
  conv_lhs => rw [sup_eq_one_of_S_eq hS1]
  exact pCoreOf_sup_pCoreOf hF

private theorem isSzU3Quot_sup_one_of_S_eq {L1 L2 S : Subgroup G} {q : ℕ}
    (hF : Hyp111 L1 L2 S) (hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S)
    (hq : IsSzU3Quot (oTwoQuot ↥L1) q) : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) q :=
  isSzU3Quot_oTwoQuot_congr (sup_eq_one_of_S_eq hS1).symm
    (IsSzU3Quot.of_mulEquiv (oTwoQuotSupEquiv hF) hq)

private theorem isSylowTwoOf_sup_one_of_hyp111
    {L1 L2 S : Subgroup G} (hF : Hyp111 L1 L2 S) : IsSylowTwoOf S (L1 ⊔ S) := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF
  have hP : IsSylowTwoOf S (P1 L1 L2 S) := F112W.isSylowTwoOf_parabolic hR
  refine F7.isSylowTwoOf_mono_right hP le_sup_right ?_
  exact sup_le le_sup_left
    ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)

private theorem inf_centralizer_le_of_hyp111 {L1 L2 S : Subgroup G} (hF : Hyp111 L1 L2 S) :
    (L1 ⊔ S) ⊓ Subgroup.centralizer (Q1 L1 L2 S : Set G) ≤ Q1 L1 L2 S := by
  have hP : P1 L1 L2 S = L1 ⊔ S ⊔ borelOf L2 S := by
    have hB1 : borelOf L1 S ≤ L1 := F1.borelOf_le L1 S
    rw [P1, bigB]
    calc L1 ⊔ (borelOf L1 S ⊔ borelOf L2 S ⊔ S)
        = L1 ⊔ (borelOf L1 S ⊔ (borelOf L2 S ⊔ S)) := by rw [sup_assoc]
      _ = (L1 ⊔ borelOf L1 S) ⊔ (borelOf L2 S ⊔ S) := by rw [← sup_assoc]
      _ = L1 ⊔ (borelOf L2 S ⊔ S) := by rw [sup_eq_left.mpr hB1]
      _ = (L1 ⊔ S) ⊔ borelOf L2 S := by rw [sup_comm (borelOf L2 S) S, sup_assoc]
  have hH : L1 ⊔ S ≤ P1 L1 L2 S := by
    rw [hP]
    exact le_sup_left
  have hchar : CharTwo (P1 L1 L2 S) := by
    rw [hP]
    exact hF.h1.charTwo
  exact (inf_le_inf_right (Subgroup.centralizer (Q1 L1 L2 S : Set G)) hH).trans hchar

theorem oTwoUpper_le_of_lemmaT
    {H Q Y : Subgroup G} {s : G}
    (hQH : Q ≤ H) (hQN : H ≤ Subgroup.normalizer (Q : Set G)) (hQ2 : IsPGroup 2 Q)
    (hM4 : ∀ K : Subgroup G, K ≤ H → H ≤ Subgroup.normalizer (K : Set G) → Q ≤ K →
      K = H ∨ ∀ k ∈ K, (∃ n : ℕ, k ^ (2 ^ n) = 1) → k ∈ Q)
    (hCQ : H ⊓ Subgroup.centralizer (Q : Set G) ≤ Q)
    (hYQ : Y ≤ Q) (hYn : H ≤ Subgroup.normalizer (Y : Set G))
    (hYc : ⁅Y, oTwoUpper H⁆ = ⊥)
    (hsH : s ∈ H) (hs2 : ∃ n : ℕ, s ^ (2 ^ n) = 1) (hsQ : s ∉ Q)
    (hc : ∀ x ∈ Q, x * s * x⁻¹ * s⁻¹ ∈ Y) :
    oTwoUpper H ≤ Q := by
  set K : Subgroup G := centralizerMod Y H Q with hK
  have hKH : K ≤ H := by
    rw [hK]
    exact centralizerMod_le_left Y H Q
  have hKHn : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hK]
    exact le_normalizer_centralizerMod hYn Subgroup.le_normalizer hQN
  have hKQH : K ⊔ Q ≤ H := sup_le hKH hQH
  have hKQn : H ≤ Subgroup.normalizer (((K ⊔ Q : Subgroup G) : Set G)) :=
    F1.le_normalizer_sup hKHn hQN
  have hsK : s ∈ K := by
    rw [hK, mem_centralizerMod]
    refine ⟨hsH, hYn hsH, ?_⟩
    intro x hx
    have hxY := Y.inv_mem (hc x hx)
    convert hxY using 1
    group
  have htop : K ⊔ Q = H := by
    rcases hM4 (K ⊔ Q) hKQH hKQn le_sup_right with htop | h2
    · exact htop
    · exact absurd (h2 s (Subgroup.mem_sup_left hsK) hs2) hsQ
  have hO2K : oTwoUpper H ≤ K :=
    CFSG.Quasithin.Vol2.Ch11.SecD.oTwoUpper_le_of_le_sup'
      (le_of_eq htop.symm) hQ2 (fun _ hq' => hKHn (hQH hq'))
  have h5 : ⁅oTwoUpper H, Q⁆ ≤ Y := by
    rw [Subgroup.commutator_le]
    intro x hx u hu
    exact (mem_centralizerMod.mp (hO2K hx)).2.2 u hu
  have h6 : ⁅oTwoUpper H, Y⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hYc.le
  have hD : ∀ d ∈ Q, ∃ j : ℕ, d ^ (2 ^ j) ∈ (⊥ : Subgroup G) := by
    intro d hd
    obtain ⟨j, hj⟩ := hQ2.exists_pow_pow_eq_one ⟨d, hd⟩
    exact ⟨j, by simpa using congrArg Subtype.val hj⟩
  have hbot : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hcentral : ⁅oTwoUpper (oTwoUpper H), Q⁆ ≤ ⊥ :=
    CFSG.Quasithin.A4.commutator_le_of_oTwoUpper
      (A := oTwoUpper H) (N := ⊥) (B := Y) (D := Q)
      (by rw [hbot]; exact le_top) (by rw [hbot]; exact le_top) hYQ hD h5 h6
  have hcentral' : ⁅oTwoUpper H, Q⁆ ≤ ⊥ := by
    rwa [CFSG.Quasithin.EmptyFaithfulMultiple.oTwoUpper_oTwoUpper] at hcentral
  have hO2C : oTwoUpper H ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hcentral')
  exact (le_inf (oTwoUpper_le H) hO2C).trans hCQ

private theorem oTwoUpper_le_pCoreOf_of_data
    {L1 L2 S : Subgroup G} {q : ℕ} (hF : Hyp111 L1 L2 S)
    (hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S) (hq : IsSzU3Quot (oTwoQuot ↥L1) q)
    {Y : Subgroup G} (hYQ : Y ≤ Q1 L1 L2 S)
    (hYn : L1 ⊔ S ≤ Subgroup.normalizer (Y : Set G))
    (hYc : ⁅Y, oTwoUpper (L1 ⊔ S)⁆ = ⊥) {s : G} (hs : s ∈ S)
    (hsQ : s ∉ Q1 L1 L2 S)
    (hc : ∀ x ∈ Q1 L1 L2 S, x * s * x⁻¹ * s⁻¹ ∈ Y) :
    oTwoUpper (L1 ⊔ S) ≤ Q1 L1 L2 S := by
  set H : Subgroup G := L1 ⊔ S with hH
  set Q : Subgroup G := Q1 L1 L2 S with hQ
  have hQS : Q ≤ S := by
    rw [hQ]
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hQH : Q ≤ H := by
    rw [hH]
    exact hQS.trans le_sup_right
  have hHP1 : H ≤ P1 L1 L2 S := by
    rw [hH]
    exact sup_le le_sup_left
      ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hQN : H ≤ Subgroup.normalizer (Q : Set G) := by
    refine hHP1.trans ?_
    rw [hQ]
    exact le_normalizer_pCoreOf 2 (P1 L1 L2 S)
  have hQ2 : IsPGroup 2 Q := by
    rw [hQ]
    exact pCoreOf_isPGroup 2 (P1 L1 L2 S)
  have hpCore : pCoreOf 2 H = Q := by
    rw [hH, hQ]
    exact pCoreOf_sup_one_of_S_eq hF hS1
  have hM4 : ∀ K : Subgroup G, K ≤ H →
      H ≤ Subgroup.normalizer (K : Set G) → Q ≤ K →
      K = H ∨ ∀ k ∈ K, (∃ n : ℕ, k ^ (2 ^ n) = 1) → k ∈ Q := by
    intro K hKH hKn hQK
    have hqH : IsSzU3Quot (oTwoQuot ↥H) q := by
      rw [hH]
      exact isSzU3Quot_sup_one_of_S_eq hF hS1 hq
    have h := eq_or_mem_pCoreOf_of_normal hqH hKH hKn (by simpa [hpCore] using hQK)
    rwa [hpCore] at h
  have hCQ : H ⊓ Subgroup.centralizer (Q : Set G) ≤ Q := by
    rw [hH, hQ]
    exact inf_centralizer_le_of_hyp111 hF
  have hsH : s ∈ H := (le_sup_right : S ≤ H) hs
  have hs2 : ∃ n : ℕ, s ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := hF.h1.pgroup.exists_pow_pow_eq_one ⟨s, hs⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hres := oTwoUpper_le_of_lemmaT hQH hQN hQ2 hM4 hCQ hYQ hYn hYc
    hsH hs2 hsQ hc
  rwa [hH, hQ] at hres

theorem false_of_commutator_le_of_bender {L1 L2 S : Subgroup G}
    {q : ℕ} (hF : Hyp111 L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S) (hq : IsSzU3Quot (oTwoQuot ↥L1) q)
    {Y : Subgroup G} (hYQ : Y ≤ Q1 L1 L2 S)
    (hYn : L1 ⊔ S ≤ Subgroup.normalizer (Y : Set G))
    (hYc : ⁅Y, oTwoUpper (L1 ⊔ S)⁆ = ⊥) {s : G} (hs : s ∈ S)
    (hsQ : s ∉ Q1 L1 L2 S)
    (hc : ∀ x ∈ Q1 L1 L2 S, x * s * x⁻¹ * s⁻¹ ∈ Y) : False := by
  have hO2Q : oTwoUpper (L1 ⊔ S) ≤ Q1 L1 L2 S :=
    oTwoUpper_le_pCoreOf_of_data hF hS1 hq hYQ hYn hYc hs hsQ hc
  have hQS : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hHS : L1 ⊔ S = oTwoUpper (L1 ⊔ S) ⊔ S :=
    CFSG.Quasithin.H13.eq_oTwoUpper_sup_of_isSylowTwoOf
      (isSylowTwoOf_sup_one_of_hyp111 hF)
  have hL1S : L1 ≤ S := by
    have hle : L1 ⊔ S ≤ S := by
      rw [hHS]
      exact sup_le (hO2Q.trans hQS) le_rfl
    exact (le_sup_left : L1 ≤ L1 ⊔ S).trans hle
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF
  apply hR.r1.borel_ne
  have hS1' : S ⊓ L1 = L1 := le_antisymm inf_le_right (le_inf hL1S le_rfl)
  have hN : L1 ⊓ Subgroup.normalizer (L1 : Set G) = L1 := inf_eq_left.mpr Subgroup.le_normalizer
  rw [hS1', hN]

structure OrientedBenderPair (L1 L2 S : Subgroup G) (q r : ℕ) : Prop where
  hyp : Hyp111 L1 L2 S
  sB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)
  s1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S
  s2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S
  bender1 : IsSzU3Quot (oTwoQuot ↥L1) q
  bender2 : IsSzU3Quot (oTwoQuot ↥L2) r
  not_central : ¬ L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G)
  j_not_le : ¬ thompsonJ S ≤ Q1 L1 L2 S

namespace OrientedBenderPair


end OrientedBenderPair

end CFSG.Quasithin.Stroth

end
