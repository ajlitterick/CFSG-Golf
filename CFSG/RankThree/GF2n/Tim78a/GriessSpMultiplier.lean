module

public import CFSG.RankThree.GF2n.Tim79aCitedSp
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
public import CFSG.LocalAnalysis.EvenBN.Common.SL2CentralTwoSplit
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.Holt.H78.Schur

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.PerfectCover


private noncomputable def statedSpProjEquiv (n : ℕ) (K : Type) [Field K] [CharP K 2] [NeZero n] :
    StatedSp n K ≃* StatedProj (StatedSp n K) :=
  MulEquiv.ofBijective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj n K)
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo (r := n) (K := K))

private theorem statedClassicalModel_statedSp {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f)
    (hne2 : (n, f) ≠ (2, 1)) :
    StatedClassicalModel (StatedSp n (GaloisField 2 f)) .PSp n 2 f := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := by
    rw [GaloisField.card 2 f (by omega)]
  haveI : CharP (GaloisField 2 f) 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf hK
  have hadm : StatedLieAdmissible .PSp n 2 f := by
    refine ⟨Nat.prime_two, hf, hn, ?_⟩
    intro h
    have hn2 : n = 2 := congrArg Prod.fst h
    have hpow : 2 ^ f = 2 := congrArg Prod.snd h
    have hf1 : f = 1 := by
      have h' : (2 : ℕ) ^ f = 2 ^ 1 := by simpa using hpow
      exact (pow_right_injective₀ (by norm_num : (0 : ℕ) < 2) (by norm_num : (2 : ℕ) ≠ 1)) h'
    exact hne2 (by rw [hn2, hf1])
  exact ⟨hadm, GaloisField 2 f, inferInstance, inferInstance, hK,
    ⟨statedSpProjEquiv n (GaloisField 2 f)⟩⟩

private theorem genericOrders_psp_two_pow_eq_one {m f : ℕ} (hf : 1 ≤ f) :
    CFSG.Blueprint.Multiplier.genericOrders .PSp m 2 f = (1, 1) := by
  have h : Nat.gcd 2 (2 ^ f - 1) = 1 := by
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hodd : Odd (2 ^ f - 1) :=
      Nat.Even.sub_odd h1 (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    exact Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd)
  simp [CFSG.Blueprint.Multiplier.genericOrders, h]

private theorem exceptionalOrders_psp_two_pow_eq_one {m f : ℕ} (hf : 2 ≤ f) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSp m 2 f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all <;> omega

private theorem exceptionalOrders_psp_two_eq_one {m : ℕ} (hm : m ≠ 3) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSp m 2 1 = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all

private theorem commutator_and_subsingleton_statedSp {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f)
    (hne2 : (n, f) ≠ (2, 1)) (hne3 : (n, f) ≠ (3, 1)) :
    commutator (StatedSp n (GaloisField 2 f)) = ⊤ ∧
      Subsingleton (CFSG.Open.griessHopfMultiplier (StatedSp n (GaloisField 2 f))) := by
  classical
  let K := GaloisField 2 f
  have hcl : StatedClassicalModel (StatedSp n K) .PSp n 2 f :=
    statedClassicalModel_statedSp hn hf hne2
  have hq : 5 ≤ 2 ^ f ∨ 2 ^ f = 4 ∨ (2 ^ f = 2 ∧ 4 ≤ n) ∨ (2 ^ f = 3 ∧ 3 ≤ n) := by
    rcases Nat.lt_or_ge f 3 with hlt | hge
    · have hf12 : f = 1 ∨ f = 2 := by omega
      rcases hf12 with rfl | rfl
      · have hn4 : 4 ≤ n := by
          by_contra h
          have h23 : n = 2 ∨ n = 3 := by omega
          rcases h23 with rfl | rfl
          · exact hne2 rfl
          · exact hne3 rfl
        exact Or.inr (Or.inr (Or.inl ⟨by norm_num, hn4⟩))
      · exact Or.inr (Or.inl (by norm_num))
    · left
      calc 5 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hge
  obtain ⟨hperf, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessClassical.psp_row (X := StatedSp n K) hcl hq
  have hg : CFSG.Blueprint.Multiplier.genericOrders .PSp n 2 f = (1, 1) :=
    genericOrders_psp_two_pow_eq_one hf
  have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSp n 2 f = (1, 1) := by
    rcases Nat.lt_or_ge f 2 with hf1 | hf2
    · have hf1' : f = 1 := by omega
      subst hf1'
      exact exceptionalOrders_psp_two_eq_one (by
        intro h
        exact hne3 (by rw [h]))
    · exact exceptionalOrders_psp_two_pow_eq_one hf2
  haveI : Subsingleton (CFSG.Blueprint.Multiplier.generic .PSp n 2 f ×
      CFSG.Blueprint.Multiplier.exceptional .PSp n 2 f) := by
    unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
    rw [hg, he]
    infer_instance
  exact ⟨hperf, eM.toEquiv.subsingleton⟩

private theorem ker_eq_bot_of_griess_subsingleton {Γ X : Type} [Group Γ] [Group X]
    (hX : commutator X = ⊤) (hM : Subsingleton (CFSG.Open.griessHopfMultiplier X))
    (φ : Γ →* X) (hφ : Function.Surjective φ)
    (hcen : φ.ker ≤ Subgroup.center Γ) (hcom : φ.ker ≤ commutator Γ) :
    φ.ker = ⊥ := by
  haveI : Group.IsPerfect X := Group.isPerfect_def.2 hX
  haveI : Group.IsPerfect Γ := CFSG.Holt.H78.isPerfect_of_ker_le_commutator φ hφ hcom
  let ψ := hopfMultiplierToKer φ hφ hcen
  have hψ : Function.Surjective ψ := hopfMultiplierToKer_surjective φ hφ hcen
  haveI : Subsingleton (hopfMultiplier X) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := (hopfMultiplierEquivGriess X).surjective a
    obtain ⟨b', rfl⟩ := (hopfMultiplierEquivGriess X).surjective b
    rw [Subsingleton.elim a' b']
  haveI : Subsingleton φ.ker := hψ.subsingleton
  exact Subgroup.eq_bot_of_subsingleton _

private theorem ker_eq_bot_statedSp_one {f : ℕ} (hf3 : 3 ≤ f) {Γ : Type} [Group Γ]
    (φ : Γ →* StatedSp 1 (GaloisField 2 f)) (hφ : Function.Surjective φ)
    (hcen : φ.ker ≤ Subgroup.center Γ) (hcom : φ.ker ≤ commutator Γ) :
    φ.ker = ⊥ := by
  classical
  let K := GaloisField 2 f
  have hKcard : Nat.card K = 2 ^ f := by
    rw [GaloisField.card 2 f (by omega)]
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hKcard
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  haveI : Group.IsPerfect (StatedSp 1 K) :=
    CFSG.LieType.Steinberg.CentralExt.SpClosed.isPerfect_statedSp 1 K hK4
  let e : Matrix.SpecialLinearGroup (Fin 2) K ≃* StatedSp 1 K :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K
  let φ' : Γ →* Matrix.SpecialLinearGroup (Fin 2) K := e.symm.toMonoidHom.comp φ
  have hφ' : Function.Surjective φ' := e.symm.surjective.comp hφ
  have hker' : φ'.ker = φ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact e.symm.map_eq_one_iff
  have hcen' : φ'.ker ≤ Subgroup.center Γ := hker' ▸ hcen
  have hk : 5 ≤ Nat.card K := by
    rw [hKcard]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
  have hk9 : Nat.card K ≠ 9 := by
    rw [hKcard]
    intro h
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    rw [h] at h2
    omega
  obtain ⟨σ', hσ'⟩ :=
    CFSG.LocalAnalysis.EvenBN.Common.exists_section_of_central_sl2 hk hk9 hφ' hcen'
  let σ : StatedSp 1 K →* Γ := σ'.comp e.symm.toMonoidHom
  have hσ : ∀ g, φ (σ g) = g := by
    intro g
    have h1 := hσ' (e.symm g)
    change e.symm (φ (σ' (e.symm g))) = e.symm g at h1
    simpa [σ] using e.symm.injective h1
  haveI : Group.IsPerfect Γ := CFSG.Holt.H78.isPerfect_of_ker_le_commutator φ hφ hcom
  exact CFSG.LieType.Steinberg.CentralExt.SL2Closed.ker_eq_bot_of_section φ hcen σ hσ

theorem griessSpMultiplierStatement_holds : GriessSpMultiplierStatement := by
  intro n f hn hf h11 h12 h21 h31 Γ _ φ hφ hcen hcom
  by_cases hn1 : n = 1
  · subst hn1
    have hf3 : 3 ≤ f := by
      by_contra h
      have h12' : f = 1 ∨ f = 2 := by omega
      rcases h12' with rfl | rfl
      · exact h11 rfl
      · exact h12 rfl
    exact ker_eq_bot_statedSp_one hf3 φ hφ hcen hcom
  · have hn2 : 2 ≤ n := by omega
    obtain ⟨hX, hM⟩ := commutator_and_subsingleton_statedSp hn2 hf h21 h31
    exact ker_eq_bot_of_griess_subsingleton hX hM φ hφ hcen hcom

end CFSG.RankThree.GF2n.Tim79a
