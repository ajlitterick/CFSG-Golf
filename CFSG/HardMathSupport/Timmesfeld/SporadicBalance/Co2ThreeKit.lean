module

public import Certificates.Data.CFSGNative.Co3Schreier.Basic
public import CFSG.Certificates.NativeSchreierEnum
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction
public import CFSG.RankThree.Native.PrimeLines

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.Certificates.ChainArrays

theorem gLAPPrimeCoreOf_eq_bot_of_card_lt_three_mul {G : Type*} [Group G] [Finite G]
    {X T : Subgroup G} (hTX : T ≤ X) (hT : IsPGroup 3 T)
    (hCT : IsPGroup 3 ↥(Subgroup.centralizer (T : Set G)))
    (hlt : Nat.card X < 3 * Nat.card T) : GLAPPrimeCoreOf 3 X = ⊥ := by
  set N := GLAPPrimeCoreOf 3 X with hN
  have hNX : N ≤ X := GLAPPrimeCoreOf_le X
  have hcop : Nat.Coprime 3 (Nat.card N) := coprime_card_GLAPPrimeCoreOf Nat.prime_three X
  have hNT : N ⊓ T = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.inf_eq_bot_of_coprime_isPGroup
      Nat.prime_three hcop hT
  have hinj : Function.Injective fun x : ↥N × ↥T =>
      (⟨(x.1 : G) * x.2, X.mul_mem (hNX x.1.2) (hTX x.2.2)⟩ : ↥X) := by
    rintro ⟨n, t⟩ ⟨n', t'⟩ h
    have h1 : (n : G) * t = n' * t' := congrArg Subtype.val h
    have h2 : (n' : G)⁻¹ * n = t' * (t : G)⁻¹ := by
      calc (n' : G)⁻¹ * n = (n' : G)⁻¹ * (n * t) * (t : G)⁻¹ := by group
        _ = (n' : G)⁻¹ * (n' * t') * (t : G)⁻¹ := by rw [h1]
        _ = t' * (t : G)⁻¹ := by group
    have hmem : (n' : G)⁻¹ * n ∈ N ⊓ T :=
      ⟨N.mul_mem (N.inv_mem n'.2) n.2, h2 ▸ T.mul_mem t'.2 (T.inv_mem t.2)⟩
    rw [hNT, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    have hnn : n = n' := Subtype.ext hmem.symm
    subst hnn
    have htt : (t : G) = t' := mul_left_cancel h1
    rw [Subtype.ext htt]
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at hcard
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hN2 : Nat.card N ≤ 2 := by
    by_contra h
    have : 3 * Nat.card T ≤ Nat.card N * Nat.card T := Nat.mul_le_mul_right _ (by omega)
    omega
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  by_contra hw1
  have hwC : w ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hconj : t * w * t⁻¹ ∈ N := GLAPPrimeCoreOf_conj_mem t (hTX ht) w hw
    have hne : (⟨t * w * t⁻¹, hconj⟩ : ↥N) ≠ 1 := by
      intro h
      apply hw1
      have h' : t * w * t⁻¹ = 1 := congrArg Subtype.val h
      calc w = t⁻¹ * (t * w * t⁻¹) * t := by group
        _ = 1 := by rw [h']; group
    have hne' : (⟨w, hw⟩ : ↥N) ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
    have heq := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.eq_of_ne_one_of_card_le_two hN2
      hne hne'
    have heq' : t * w * t⁻¹ = w := congrArg Subtype.val heq
    calc t * w = t * w * t⁻¹ * t := by group
      _ = w * t := by rw [heq']
  obtain ⟨k, hk⟩ := hCT ⟨w, hwC⟩
  have hwk : w ^ 3 ^ k = 1 := congrArg Subtype.val hk
  have hord : orderOf (⟨w, hw⟩ : ↥N) ∣ Nat.card N := orderOf_dvd_natCard _
  have hord3 : orderOf (⟨w, hw⟩ : ↥N) ∣ 3 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext hwk
  have h1 : orderOf (⟨w, hw⟩ : ↥N) = 1 := by
    have hc : Nat.Coprime (3 ^ k) (Nat.card N) := Nat.Coprime.pow_left k hcop
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hord3 hc) hord
  rw [orderOf_eq_one_iff] at h1
  exact hw1 (congrArg Subtype.val h1)

variable {n : ℕ}

theorem anyLt_true {n : ℕ} {p : ℕ → Bool} (h : CFSG.Sporadic.Schreier.Co3.Native.anyLt n p = true) :
    ∃ i < n, p i = true := by
  unfold CFSG.Sporadic.Schreier.Co3.Native.anyLt at h
  rw [Nat.any_eq_finRange_any, List.any_eq_true] at h
  obtain ⟨⟨i, hi⟩, -, h⟩ := h
  exact ⟨i, hi, h⟩


@[expose] def dsearch (n : ℕ) (L : Array Level) (base : Array ℕ)
    (rels : Array (Option (ℕ × Array ℕ))) (pred : Array ℕ → Bool) :
    ℕ → ℕ → Array ℕ → Array ℕ → List (Array ℕ)
  | 0, _, acc, _ => if pred acc then [acc] else []
  | fuel + 1, i, acc, accI =>
    match rels.getD i none with
    | some (j, y) =>
      if (L[i]!).pos[accI[y[acc[base[j]!]!]!]!]! < (L[i]!).pts.size then
        dsearch n L base rels pred fuel (i + 1)
          (compA n acc (L[i]!).tr[(L[i]!).pos[accI[y[acc[base[j]!]!]!]!]!]!)
          (compA n (L[i]!).trInv[(L[i]!).pos[accI[y[acc[base[j]!]!]!]!]!]! accI)
      else []
    | none =>
      (List.range (L[i]!).pts.size).flatMap fun k =>
        dsearch n L base rels pred fuel (i + 1) (compA n acc (L[i]!).tr[k]!)
          (compA n (L[i]!).trInv[k]! accI)

variable {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
  {W : Array (List ℤ)} {chunks : ℕ}

section Facts

variable (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
  (hQ : ValidSchreier Q)
include hA hF hQ

theorem levT_pos_inv_mul_mem {i : ℕ} (hi : i < Q.baseCount) {h : Equiv.Perm (Fin n)}
    (hh : h ∈ Q.levelSubgroup i) :
    (lev n S base i).pos[((h (Q.base.get ⟨i, hi⟩) : Fin n) : ℕ)]! < (lev n S base i).pts.size ∧
      (levT n S base i (lev n S base i).pos[((h (Q.base.get ⟨i, hi⟩) : Fin n) : ℕ)]!)⁻¹ * h ∈
        Q.levelSubgroup (i + 1) := by
  set b := Q.base.get ⟨i, hi⟩ with hb
  have hx : h b ∈ Q.orbitPoints ⟨i, hi⟩ := by
    rw [Q.orbitPoints_eq_orbit]
    exact ⟨⟨h, hh⟩, rfl⟩
  obtain ⟨hk, -, ht⟩ := hA.orbitPoints_spec hF hi hx
  obtain ⟨-, hmem, hval⟩ := Q.transversal_getD_spec ⟨i, hi⟩ (h b) hx
  rw [ht] at hmem hval
  refine ⟨hk, ?_⟩
  set t := levT n S base i (lev n S base i).pos[((h b : Fin n) : ℕ)]! with htdef
  rw [Q.levelSubgroup_succ_eq_stabilizer hQ ⟨i, hi⟩]
  refine Subgroup.mem_inf.2
    ⟨(Q.levelSubgroup i).mul_mem ((Q.levelSubgroup i).inv_mem hmem) hh, ?_⟩
  have htb : t b = h b := hval
  rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, Equiv.Perm.mul_apply]
  change t⁻¹ (h b) = b
  rw [← htb]
  simp


end Facts

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T
