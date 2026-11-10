module

public import CFSG.Quasithin.Background.A3FactsAssembly
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
public import CFSG.Quasithin.Background.C116Three.Main
public import CFSG.Quasithin.Background.C116Two.Main
public import CFSG.Quasithin.Background.C116Bridge.Main
public import CFSG.Quasithin.Background.GoldschmidtTDC19
public import CFSG.Quasithin.Background.GoldschmidtTDC111Main
public import CFSG.Quasithin.H13.VolIC129Holds
public import CFSG.Quasithin.EmptyFaithful.Gold14610Blocks
public import CFSG.Quasithin.Vol2.Ch11C113b
public import CFSG.Quasithin.H13.VolIC113a
public import CFSG.Quasithin.H13.VolIC113c
public import CFSG.Quasithin.H13.VolIC113d
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC124Proved
public import CFSG.Alternating.Multipliers.Small
public import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
public import CFSG.Holt.SmallGroups
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerOrder168
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.C123TwoHolds
public import CFSG.Quasithin.H13.A7Nat1236Final
public import CFSG.Quasithin.H13.GoldschmidtC137SQA6
public import CFSG.Quasithin.H13.GoldschmidtC137SQExt
public import CFSG.Quasithin.H13.GoldschmidtC137SQRk

public section

namespace CFSG.ASVolI.ChC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G]


structure HypC_1_14 (X V T : Subgroup G) : Prop where
  charTwo : CharTwo X
  reduced : IsTwoReducedIn X V
  sylow : IsSylowTwoOf T X


@[expose] def IsNatVia {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (A V Z : Subgroup G) (α : ↥A →* Matrix.SpecialLinearGroup ι F)
    (β : ↥V →* Multiplicative (ι → F)) : Prop :=
  Function.Surjective β ∧ β.ker = Z.subgroupOf V ∧
    ∀ (a : ↥A) (u v : ↥V), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α a : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F).mulVec (Multiplicative.toAdd (β u))


structure SumOfTwoNat (L U : Subgroup G) (α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (U₁ U₂ : Subgroup G) (β₁ : ↥U₁ →* Multiplicative (Fin 3 → ZMod 2))
    (β₂ : ↥U₂ →* Multiplicative (Fin 3 → ZMod 2)) : Prop where
  alpha_onto : Function.Surjective α
  alpha_ker : α.ker = CFSG.pCore 2 ↥L
  le₁ : U₁ ≤ U
  le₂ : U₂ ≤ U
  join : U₁ ⊔ U₂ = U
  meet : U₁ ⊓ U₂ = ⊥
  norm₁ : L ≤ Subgroup.normalizer (U₁ : Set G)
  norm₂ : L ≤ Subgroup.normalizer (U₂ : Set G)
  nat₁ : IsNatVia L U₁ ⊥ α β₁
  nat₂ : IsNatVia L U₂ ⊥ α β₂


end CFSG.ASVolI.ChC

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise


section BurnsideC1a


end BurnsideC1a


section BurnsideC1b


end BurnsideC1b


section BurnsideC1d


end BurnsideC1d


section as_C_1_16


end as_C_1_16


section BurnsideC1c


end BurnsideC1c

section


end


@[expose] def C_1_24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X V T L R : Subgroup G), HypC_1_14 X V T →
    (X : Set G) = (L : Set G) * (T : Set G) → L ∈ cComp X → CharTwo L → ⁅V, L⁆ ≠ ⊥ →
    pCoreOf 2 X ≤ R → R ≤ T →
    ∀ m : ℕ, IsAltQuotient L (oTwoZIn L) m →
      ((m = 5 ∨ m = 7) ∨ (m = 6 ∧ autOn R V ≤ autOn L V) ∨
        (m = 6 ∧ Nat.card ↥(autOn R V) = 2)) →
      ((∃ D : Subgroup G, D ≠ ⊥ ∧ D ≤ baum R ∧ (D.subgroupOf (baum R)).Characteristic ∧
          X ≤ Subgroup.normalizer (D : Set G)) ∨
        IsChiBlock2 X L ∨ (IsBlock2 X L ∧ IsExcA7Block L) ∨
          (IsBlock2 X L ∧ IsAltBlockType L 6) ∨ (IsBlock2 X L ∧ IsHatA6Block L))

section BurnsideC124

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_addRight_pow_apply (n : ℕ) (x : ZMod 7) :
    ((Equiv.addRight (1 : ZMod 7)) ^ n) x = x + (n : ZMod 7) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Perm.mul_apply, Equiv.coe_addRight, ih]
    push_cast
    ring

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_finRotate_eq : (finRotate 7 : Perm (Fin 7)) =
    (Equiv.addRight (1 : ZMod 7) : Perm (Fin 7)) := by
  refine Equiv.ext fun z => ?_
  revert z
  decide

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_affine_of_shift {g : Perm (ZMod 7)} {j : ZMod 7}
    (h : ∀ x, g (x + 1) = g x + j) (x : ZMod 7) : g x = g 0 + j * x := by
  have key : ∀ n : ℕ, g (n : ZMod 7) = g 0 + j * n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      rw [h, ih]
      ring
  have := key x.val
  rwa [ZMod.natCast_zmod_val] at this

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_orderOf_addRight : orderOf (Equiv.addRight (1 : ZMod 7)) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7 : (Equiv.addRight (1 : ZMod 7)) ^ 7 = 1 := by
    refine Equiv.ext fun x => ?_
    rw [burnsideC124_addRight_pow_apply]
    simp only [Perm.coe_one, id_eq]
    rw [ZMod.natCast_self, add_zero]
  refine orderOf_eq_prime h7 fun h => ?_
  have := congrArg (fun f : Perm (ZMod 7) => f 0) h
  simp at this

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_sign_mulLeft (k : ZMod 7) (hk : k ≠ 0) :
    sign (Equiv.mulLeft₀ k hk) = 1 ↔ k = 1 ∨ k = 2 ∨ k = 4 := by
  revert k
  decide

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_sign_addRight (b : ZMod 7) : sign (Equiv.addRight b) = 1 := by
  revert b
  decide

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_slope_of_even {g : Perm (ZMod 7)} {b j : ZMod 7}
    (hg : ∀ x, g x = b + j * x) (hs : sign g = 1) : j = 1 ∨ j = 2 ∨ j = 4 := by
  have hj : j ≠ 0 := by
    intro h0
    have h01 : g 0 = g 1 := by rw [hg, hg, h0]; simp
    exact absurd (g.injective h01) (by decide)
  have : g = (Equiv.mulLeft₀ j hj).trans (Equiv.addRight b) := by
    refine Equiv.ext fun x => ?_
    simp [hg, add_comm]
  rw [this, Perm.sign_trans, burnsideC124_sign_addRight, one_mul] at hs
  exact (burnsideC124_sign_mulLeft j hj).1 hs

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_normalizer_affine {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) (hA : ∀ g ∈ M, sign g = 1) (g : ↥M)
    (hg : g ∈ Subgroup.normalizer
      ((zpowers (⟨Equiv.addRight (1 : ZMod 7), hc⟩ : ↥M) : Subgroup ↥M) : Set ↥M)) :
    ∃ b j : ZMod 7, (j = 1 ∨ j = 2 ∨ j = 4) ∧ ∀ x, (g : Perm (ZMod 7)) x = b + j * x := by
  classical
  set z : ↥M := ⟨Equiv.addRight (1 : ZMod 7), hc⟩ with hz
  have hzo : orderOf z = 7 := by
    rw [← Subgroup.orderOf_coe]
    exact burnsideC124_orderOf_addRight
  have hmem : g * z * g⁻¹ ∈ zpowers z :=
    (Subgroup.mem_normalizer_iff.1 hg z).1 (mem_zpowers z)
  rw [mem_zpowers_iff_mem_range_orderOf, hzo] at hmem
  obtain ⟨n, hn, hnz⟩ := Finset.mem_image.1 hmem
  have hn' := congrArg (fun a : ↥M => (a : Perm (ZMod 7))) hnz
  have hcz : ((z : ↥M) : Perm (ZMod 7)) = Equiv.addRight (1 : ZMod 7) := rfl
  simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, hcz] at hn'
  have hshift : ∀ x : ZMod 7,
      (g : Perm (ZMod 7)) (x + 1) = (g : Perm (ZMod 7)) x + (n : ZMod 7) := by
    intro x
    have h1 : (g : Perm (ZMod 7)) * Equiv.addRight (1 : ZMod 7) =
        (Equiv.addRight (1 : ZMod 7)) ^ n * (g : Perm (ZMod 7)) := by
      rw [hn']
      group
    have h2 := congrArg (fun f : Perm (ZMod 7) => f x) h1
    simp only [Perm.mul_apply, Equiv.coe_addRight, burnsideC124_addRight_pow_apply] at h2
    rw [h2]
  have haff := burnsideC124_affine_of_shift hshift
  refine ⟨(g : Perm (ZMod 7)) 0, (n : ZMod 7), ?_, haff⟩
  exact burnsideC124_slope_of_even (fun x => haff x) (hA g g.2)

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_normalizer_card {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) (hA : ∀ g ∈ M, sign g = 1) :
    Nat.card (Subgroup.normalizer
      ((zpowers (⟨Equiv.addRight (1 : ZMod 7), hc⟩ : ↥M) : Subgroup ↥M) : Set ↥M)) = 7 ∨
    Nat.card (Subgroup.normalizer
      ((zpowers (⟨Equiv.addRight (1 : ZMod 7), hc⟩ : ↥M) : Subgroup ↥M) : Set ↥M)) = 21 := by
  classical
  set z : ↥M := ⟨Equiv.addRight (1 : ZMod 7), hc⟩ with hz
  set N : Subgroup ↥M := Subgroup.normalizer ((zpowers z : Subgroup ↥M) : Set ↥M) with hN
  have hzo : orderOf z = 7 := by
    rw [← Subgroup.orderOf_coe]
    exact burnsideC124_orderOf_addRight
  have h7 : 7 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := zpowers z))
    rwa [Nat.card_zpowers, hzo] at this
  have hle : Nat.card N ≤ 21 := by
    let S : Finset (ZMod 7 × ZMod 7) := ({1, 2, 4} : Finset (ZMod 7)) ×ˢ Finset.univ
    have hS : S.card = 21 := by decide
    let F : ↥N → ↥S := fun g =>
      ⟨(((g : ↥M) : Perm (ZMod 7)) 1 - ((g : ↥M) : Perm (ZMod 7)) 0,
        ((g : ↥M) : Perm (ZMod 7)) 0), by
        obtain ⟨b, j, hj, hg⟩ := burnsideC124_normalizer_affine hc hA g g.2
        have e0 := hg 0
        have e1 := hg 1
        simp only [S, Finset.mem_product, Finset.mem_univ, and_true]
        have : ((g : ↥M) : Perm (ZMod 7)) 1 - ((g : ↥M) : Perm (ZMod 7)) 0 = j := by
          rw [e1, e0]; ring
        rw [this]
        rcases hj with rfl | rfl | rfl <;> decide⟩
    have hF : Function.Injective F := by
      intro g g' h
      have hh := Subtype.mk.inj h
      simp only [Prod.mk.injEq] at hh
      obtain ⟨b, j, hj, hg⟩ := burnsideC124_normalizer_affine hc hA g g.2
      obtain ⟨b', j', hj', hg'⟩ := burnsideC124_normalizer_affine hc hA g' g'.2
      have e : ∀ x, ((g : ↥M) : Perm (ZMod 7)) x = ((g' : ↥M) : Perm (ZMod 7)) x := by
        intro x
        have a0 : ((g : ↥M) : Perm (ZMod 7)) 0 = b := by rw [hg 0]; ring
        have a0' : ((g' : ↥M) : Perm (ZMod 7)) 0 = b' := by rw [hg' 0]; ring
        have a1 : ((g : ↥M) : Perm (ZMod 7)) 1 - ((g : ↥M) : Perm (ZMod 7)) 0 = j := by
          rw [hg 1, a0]; ring
        have a1' : ((g' : ↥M) : Perm (ZMod 7)) 1 - ((g' : ↥M) : Perm (ZMod 7)) 0 = j' := by
          rw [hg' 1, a0']; ring
        have hb : b = b' := by rw [← a0, ← a0']; exact hh.2
        have hj : j = j' := by rw [← a1, ← a1']; exact hh.1
        rw [hg x, hg' x, hb, hj]
      exact Subtype.ext (Subtype.ext (Equiv.ext e))
    have := Nat.card_le_card_of_injective F hF
    rwa [Nat.card_eq_fintype_card (α := ↥S), Fintype.card_coe, hS] at this
  have hodd : ¬ 2 ∣ Nat.card N := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 h2
    have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    obtain ⟨b, j, hj, hg⟩ := burnsideC124_normalizer_affine hc hA (t : ↥M) t.2
    have hsq : ∀ x, ((t : ↥M) : Perm (ZMod 7)) (((t : ↥M) : Perm (ZMod 7)) x) = x := by
      intro x
      have h3 : ((t : ↥M) : Perm (ZMod 7)) * ((t : ↥M) : Perm (ZMod 7)) = 1 := by
        have := congrArg (fun a : ↥N => ((a : ↥M) : Perm (ZMod 7))) ht2
        simpa [pow_two] using this
      have := congrArg (fun f : Perm (ZMod 7) => f x) h3
      simpa using this
    have e0 := hsq 0
    have e1 := hsq 1
    rw [hg 0, hg (b + j * 0)] at e0
    rw [hg 1, hg (b + j * 1)] at e1
    have key : ∀ b j : ZMod 7, (j = 1 ∨ j = 2 ∨ j = 4) → b + j * (b + j * 0) = 0 →
        b + j * (b + j * 1) = 1 → j = 1 ∧ b = 0 := by decide
    obtain ⟨hj1, hb0⟩ := key b j hj (by simpa using e0) (by simpa using e1)
    have : (t : ↥M) = 1 := by
      refine Subtype.ext (Equiv.ext fun x => ?_)
      rw [hg x, hj1, hb0]
      simp
    have ht1 : t = 1 := Subtype.ext this
    rw [ht1, orderOf_one] at ht
    omega
  obtain ⟨m, hm⟩ := h7
  rw [hm] at hle hodd ⊢
  have hm3 : m ≤ 3 := by omega
  interval_cases m <;> omega

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_sylow_count {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) (hdvd : Nat.card M ∣ 2520) (h7 : 7 ∣ Nat.card M) :
    ∃ n : ℕ, n ≡ 1 [MOD 7] ∧ Nat.card M = n * Nat.card (Subgroup.normalizer
      ((zpowers (⟨Equiv.addRight (1 : ZMod 7), hc⟩ : ↥M) : Subgroup ↥M) : Set ↥M)) := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set z : ↥M := ⟨Equiv.addRight (1 : ZMod 7), hc⟩ with hz
  have hzo : orderOf z = 7 := by
    rw [← Subgroup.orderOf_coe]
    exact burnsideC124_orderOf_addRight
  have hfac : (Nat.card M).factorization 7 = 1 := by
    have hpos : Nat.card M ≠ 0 := Nat.card_pos.ne'
    have h1 : 1 ≤ (Nat.card M).factorization 7 :=
      (Nat.Prime.dvd_iff_one_le_factorization (Fact.out) hpos).1 h7
    by_contra hne
    have h2 : 2 ≤ (Nat.card M).factorization 7 := by omega
    have : 7 ^ 2 ∣ Nat.card M := (Nat.Prime.pow_dvd_iff_le_factorization (Fact.out) hpos).2 h2
    have := this.trans hdvd
    norm_num at this
  let P : Sylow 7 ↥M := Sylow.ofCard (zpowers z) (by
    rw [Nat.card_zpowers, hzo, hfac, pow_one])
  refine ⟨Nat.card (Sylow 7 ↥M), card_sylow_modEq_one 7 ↥M, ?_⟩
  rw [Sylow.card_eq_index_normalizer P]
  have := Subgroup.card_mul_index (Subgroup.normalizer ((P : Subgroup ↥M) : Set ↥M))
  rw [mul_comm] at this
  exact this.symm

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_isPretransitive {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) : MulAction.IsPretransitive M (ZMod 7) := by
  refine ⟨fun x y => ?_⟩
  have hmem : Equiv.addRight (y - x) ∈ M := by
    have : Equiv.addRight (y - x) = (Equiv.addRight (1 : ZMod 7)) ^ (y - x).val := by
      refine Equiv.ext fun w => ?_
      rw [burnsideC124_addRight_pow_apply, ZMod.natCast_zmod_val]
      rfl
    rw [this]
    exact pow_mem hc _
  refine ⟨⟨Equiv.addRight (y - x), hmem⟩, ?_⟩
  show (Equiv.addRight (y - x)) x = y
  simp only [Equiv.coe_addRight]
  ring

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_isPreprimitive {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) : MulAction.IsPreprimitive M (ZMod 7) := by
  haveI := burnsideC124_isPretransitive hc
  refine MulAction.IsPreprimitive.of_prime_card ?_
  rw [Nat.card_zmod]
  norm_num

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_normal_eq_bot {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) (K : Subgroup ↥M) [K.Normal]
    (hK : ¬ 7 ∣ Nat.card K) : K = ⊥ := by
  haveI := burnsideC124_isPretransitive hc
  haveI := burnsideC124_isPreprimitive hc
  by_cases hfix : MulAction.fixedPoints K (ZMod 7) = Set.univ
  · rw [eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    refine Subtype.ext (Equiv.ext fun x => ?_)
    have hx : x ∈ MulAction.fixedPoints K (ZMod 7) := by rw [hfix]; exact Set.mem_univ x
    exact hx ⟨k, hk⟩
  · exfalso
    haveI : MulAction.IsPretransitive K (ZMod 7) :=
      MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfix
    have h1 := Subgroup.index_dvd_card (MulAction.stabilizer K (0 : ZMod 7))
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ, Nat.card_zmod] at h1
    exact hK h1

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_selfNormalizing {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) (hdvd : Nat.card M ∣ 2520) (h7 : 7 ∣ Nat.card M)
    (hN : Nat.card (Subgroup.normalizer
      ((zpowers (⟨Equiv.addRight (1 : ZMod 7), hc⟩ : ↥M) : Subgroup ↥M) : Set ↥M)) = 7) :
    Nat.card M = 7 := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set z : ↥M := ⟨Equiv.addRight (1 : ZMod 7), hc⟩ with hz
  have hzo : orderOf z = 7 := by
    rw [← Subgroup.orderOf_coe]
    exact burnsideC124_orderOf_addRight
  have hfac : (Nat.card M).factorization 7 = 1 := by
    have hpos : Nat.card M ≠ 0 := Nat.card_pos.ne'
    have h1 : 1 ≤ (Nat.card M).factorization 7 :=
      (Nat.Prime.dvd_iff_one_le_factorization (Fact.out) hpos).1 h7
    by_contra hne
    have h2 : 2 ≤ (Nat.card M).factorization 7 := by omega
    have : 7 ^ 2 ∣ Nat.card M := (Nat.Prime.pow_dvd_iff_le_factorization (Fact.out) hpos).2 h2
    have := this.trans hdvd
    norm_num at this
  let P : Sylow 7 ↥M := Sylow.ofCard (zpowers z) (by
    rw [Nat.card_zpowers, hzo, hfac, pow_one])
  have hPz : (P : Subgroup ↥M) = zpowers z := rfl
  have hNP : Subgroup.normalizer ((P : Subgroup ↥M) : Set ↥M) = (P : Subgroup ↥M) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.le_normalizer) ?_).symm
    rw [hPz, Nat.card_zpowers, hzo]
    omega
  have hcomm : ∀ a ∈ (P : Subgroup ↥M), ∀ b ∈ (P : Subgroup ↥M), b * a = a * b := by
    intro a ha b hb
    rw [hPz, mem_zpowers_iff] at ha hb
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    exact (Commute.zpow_zpow_self z j i).eq
  have hP : Subgroup.normalizer ((P : Subgroup ↥M) : Set ↥M) ≤
      Subgroup.centralizer ((P : Subgroup ↥M) : Set ↥M) := by
    rw [hNP]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcomm a ha b hb
  have hK := MonoidHom.not_dvd_card_ker_transferSylow P hP
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hP
  have hKbot : (MonoidHom.transferSylow P hP).ker = ⊥ :=
    burnsideC124_normal_eq_bot hc _ hK
  have hcard := hcompl.card_mul
  rw [hKbot, Subgroup.card_bot, one_mul, hPz, Nat.card_zpowers, hzo] at hcard
  exact hcard.symm

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_card_le_of_free {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M)
    (hfree : ∀ g ∈ M, g ≠ 1 → ∀ x y : ZMod 7, x ≠ y → g x = x → g y = y → False) :
    Nat.card M ≤ 42 := by
  haveI := burnsideC124_isPretransitive hc
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer M (0 : ZMod 7))
  rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ, Nat.card_zmod] at hmul
  have hle : Nat.card (MulAction.stabilizer M (0 : ZMod 7)) ≤ 6 := by
    let F : ↥(MulAction.stabilizer M (0 : ZMod 7)) → {x : ZMod 7 // x ≠ 0} := fun g =>
      ⟨((g : ↥M) : Perm (ZMod 7)) 1, by
        intro h0
        have hg0 : ((g : ↥M) : Perm (ZMod 7)) 0 = 0 := g.2
        exact absurd (((g : ↥M) : Perm (ZMod 7)).injective (h0.trans hg0.symm)) (by decide)⟩
    have hF : Function.Injective F := by
      intro g g' h
      have h1 : ((g : ↥M) : Perm (ZMod 7)) 1 = ((g' : ↥M) : Perm (ZMod 7)) 1 :=
        congrArg Subtype.val h
      have hg0 : ((g : ↥M) : Perm (ZMod 7)) 0 = 0 := g.2
      have hg0' : ((g' : ↥M) : Perm (ZMod 7)) 0 = 0 := g'.2
      by_contra hne
      have hne' : ((g' : ↥M) : Perm (ZMod 7))⁻¹ * ((g : ↥M) : Perm (ZMod 7)) ≠ 1 := by
        intro h2
        apply hne
        have : ((g : ↥M) : Perm (ZMod 7)) = ((g' : ↥M) : Perm (ZMod 7)) := by
          have := congrArg (fun f : Perm (ZMod 7) => ((g' : ↥M) : Perm (ZMod 7)) * f) h2
          simpa using this
        exact Subtype.ext (Subtype.ext this)
      refine hfree _ (M.mul_mem (M.inv_mem (g' : ↥M).2) (g : ↥M).2) hne' 0 1 (by decide) ?_ ?_
      · have hinv0 : ((g' : ↥M) : Perm (ZMod 7))⁻¹ 0 = 0 := by
          rw [Perm.inv_eq_iff_eq]
          exact hg0'.symm
        rw [Perm.mul_apply, hg0, hinv0]
      · rw [Perm.mul_apply, h1]
        simp
    have := Nat.card_le_card_of_injective F hF
    have h6 : Nat.card {x : ZMod 7 // x ≠ 0} = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide
    omega
  omega

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_multiset_six {s : Multiset ℕ} (hmem : ∀ n ∈ s, 2 ≤ n ∧ n ∣ 6)
    (hsum : s.sum ≤ 7) (hlcm : s.lcm = 6) (hev : Even (s.sum + Multiset.card s)) :
    s = {3, 2, 2} := by
  have hcard : Multiset.card s ≤ 3 := by
    have h2 : Multiset.card s • 2 ≤ s.sum := Multiset.card_nsmul_le_sum (fun x hx => (hmem x hx).1)
    simp only [smul_eq_mul] at h2
    omega
  have hdvd : ∀ n ∈ s, n = 2 ∨ n = 3 ∨ n = 6 := by
    intro n hn
    obtain ⟨h2, hd⟩ := hmem n hn
    have h6 : n ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    interval_cases n <;> first | omega | (exfalso; norm_num at hd)
  generalize hc : Multiset.card s = c at hcard
  interval_cases c
  · rw [Multiset.card_eq_zero] at hc
    subst hc
    simp at hlcm
  · rw [Multiset.card_eq_one] at hc
    obtain ⟨a, rfl⟩ := hc
    simp at hlcm hev hsum
    subst hlcm
    exact absurd hev (by decide)
  · rw [Multiset.card_eq_two] at hc
    obtain ⟨a, b, rfl⟩ := hc
    have ha := hdvd a (by simp)
    have hb := hdvd b (by simp)
    simp at hlcm hev hsum
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> first
      | omega
      | (exfalso; revert hlcm; decide)
      | (exfalso; revert hev; decide)
  · rw [Multiset.card_eq_three] at hc
    obtain ⟨a, b, c, rfl⟩ := hc
    have ha := hdvd a (by simp)
    have hb := hdvd b (by simp)
    have hc' := hdvd c (by simp)
    simp at hlcm hev hsum
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      rcases hc' with rfl | rfl | rfl <;> first
      | omega
      | (exfalso; revert hlcm; decide)
      | (exfalso; revert hev; decide)
      | decide

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_cycleType_six {g : Perm (ZMod 7)} (hs : sign g = 1) (ho : orderOf
    g = 6) :
    g.cycleType = {3, 2, 2} := by
  have hlcm := Equiv.Perm.lcm_cycleType g
  rw [ho] at hlcm
  have hsum : g.cycleType.sum ≤ 7 := by
    have := Equiv.Perm.sum_cycleType_le g
    rwa [ZMod.card] at this
  have hmem : ∀ n ∈ g.cycleType, 2 ≤ n ∧ n ∣ 6 := fun n hn =>
    ⟨Equiv.Perm.two_le_of_mem_cycleType hn, ho ▸ Equiv.Perm.dvd_of_mem_cycleType hn⟩
  have hsign := Equiv.Perm.sign_of_cycleType g
  rw [hs] at hsign
  have hev : Even (g.cycleType.sum + Multiset.card g.cycleType) :=
    (neg_one_pow_eq_one_iff_even (by decide)).1 hsign.symm
  exact burnsideC124_multiset_six hmem hsum hlcm hev

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_g0_sq :
    ((swap (0 : ZMod 7) 1 * swap 0 2) * swap 3 4 * swap 5 6) ^ 2 =
      (swap (0 : ZMod 7) 1 * swap 0 2) * (swap 0 1 * swap 0 2) := by
  decide

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_disj1 : Disjoint (swap (0 : ZMod 7) 1 * swap 0 2) (swap 3 4) := by
  intro x
  revert x
  decide

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_disj2 :
    Disjoint ((swap (0 : ZMod 7) 1 * swap 0 2) * swap 3 4) (swap 5 6) := by
  intro x
  revert x
  decide

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_g0_cycleType :
    ((swap (0 : ZMod 7) 1 * swap 0 2) * swap 3 4 * swap 5 6).cycleType = {3, 2, 2} := by
  have h3 : (swap (0 : ZMod 7) 1 * swap 0 2).IsThreeCycle :=
    isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  have h3ct : (swap (0 : ZMod 7) 1 * swap 0 2).cycleType = {3} := h3
  have h34 : (swap (3 : ZMod 7) 4).cycleType = {2} := by
    rw [(isCycle_swap (by decide)).cycleType, support_swap (by decide)]
    decide
  have h56 : (swap (5 : ZMod 7) 6).cycleType = {2} := by
    rw [(isCycle_swap (by decide)).cycleType, support_swap (by decide)]
    decide
  rw [burnsideC124_disj2.cycleType_mul, burnsideC124_disj1.cycleType_mul, h3ct, h34, h56]
  decide

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_sq_threeCycle {g : Perm (ZMod 7)} (hs : sign g = 1) (ho : orderOf
    g = 6) :
    (g ^ 2).IsThreeCycle := by
  have hct := burnsideC124_cycleType_six hs ho
  have h3 : (swap (0 : ZMod 7) 1 * swap 0 2).IsThreeCycle :=
    isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2
    (hct.trans burnsideC124_g0_cycleType.symm))
  have hct2 : (c * (g ^ 2) * c⁻¹).cycleType = (g ^ 2).cycleType := cycleType_conj
  have : c * (g ^ 2) * c⁻¹ = (swap (0 : ZMod 7) 1 * swap 0 2) * (swap 0 1 * swap 0 2) := by
    rw [← burnsideC124_g0_sq, ← hc, conj_pow]
  rw [this] at hct2
  exact hct2.symm.trans h3.isThreeCycle_sq

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_no_order_six {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) (hA : ∀ g ∈ M, sign g = 1)
    (hsmall : Nat.card M < 2520) (g : ↥M) : orderOf g ≠ 6 := by
  intro ho
  have ho' : orderOf ((g : ↥M) : Perm (ZMod 7)) = 6 := by rw [Subgroup.orderOf_coe]; exact ho
  have h3 := burnsideC124_sq_threeCycle (hA g g.2) ho'
  have hmem : ((g : ↥M) : Perm (ZMod 7)) ^ 2 ∈ M := pow_mem g.2 2
  have hle := Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
    (burnsideC124_isPreprimitive hc) h3 hmem
  have hcard := Subgroup.card_le_of_le hle
  rw [nat_card_alternatingGroup, Nat.card_zmod] at hcard
  have h7 : Nat.factorial 7 / 2 = 2520 := by decide
  rw [h7] at hcard
  omega

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_solvable_card_84 {Q : Type*} [Group Q] [Finite Q] (h : Nat.card Q
    = 84) :
    Group.IsSolvable Q := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 7 Q) := inferInstance
  have hfac : (Nat.card Q).factorization 7 = 1 := by
    have hpos : Nat.card Q ≠ 0 := Nat.card_pos.ne'
    have h1 : 1 ≤ (Nat.card Q).factorization 7 :=
      (Nat.Prime.dvd_iff_one_le_factorization (Fact.out) hpos).1 (by rw [h]; norm_num)
    by_contra hne
    have h2 : 2 ≤ (Nat.card Q).factorization 7 := by omega
    have : 7 ^ 2 ∣ Nat.card Q := (Nat.Prime.pow_dvd_iff_le_factorization (Fact.out) hpos).2 h2
    rw [h] at this
    norm_num at this
  have hPcard : Nat.card P = 7 := by rw [Sylow.card_eq_multiplicity, hfac, pow_one]
  have hidx : (P : Subgroup Q).index = 12 := by
    have := Subgroup.card_mul_index (P : Subgroup Q)
    rw [h] at this
    have hP' : Nat.card (P : Subgroup Q) = 7 := hPcard
    rw [hP'] at this
    omega
  have hn : Nat.card (Sylow 7 Q) ∣ 12 := hidx ▸ Sylow.card_dvd_index P
  have hmod : Nat.card (Sylow 7 Q) % 7 = 1 := card_sylow_modEq_one 7 Q
  have hn1 : Nat.card (Sylow 7 Q) = 1 := by
    have hle : Nat.card (Sylow 7 Q) ≤ 12 := Nat.le_of_dvd (by norm_num) hn
    have hpos : 0 < Nat.card (Sylow 7 Q) := Nat.card_pos
    generalize Nat.card (Sylow 7 Q) = n at hn hmod hle hpos
    interval_cases n <;> first | rfl | omega | (exfalso; norm_num at hn)
  haveI : Subsingleton (Sylow 7 Q) := (Nat.card_eq_one_iff_unique.1 hn1).1
  haveI : (P : Subgroup Q).Normal := Sylow.normal_of_subsingleton P
  haveI : Group.IsSolvable (P : Subgroup Q) :=
    CFSG.GroupTheory.groups_order_below_sixty_solvable (by
      have : Nat.card (P : Subgroup Q) = 7 := hPcard
      omega)
  haveI : Group.IsSolvable (Q ⧸ (P : Subgroup Q)) :=
    CFSG.GroupTheory.groups_order_below_sixty_solvable (by
      have : Nat.card (Q ⧸ (P : Subgroup Q)) = 12 := by rw [← Subgroup.index, hidx]
      omega)
  exact Group.isSolvable_of_subgroup_quotient (P : Subgroup Q)

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_solvable_of_card_dvd_168 {Q : Type*} [Group Q] [Finite Q]
    (h : Nat.card Q ∣ 168) (hlt : Nat.card Q < 168) : Group.IsSolvable Q := by
  by_cases h60 : Nat.card Q < 60
  · exact CFSG.GroupTheory.groups_order_below_sixty_solvable h60
  · have hpos : 0 < Nat.card Q := Nat.card_pos
    have h84 : Nat.card Q = 84 := by
      obtain ⟨k, hk⟩ := h
      have hk3 : k ≤ 2 := by
        by_contra hk3
        have : 60 * 3 ≤ Nat.card Q * k := Nat.mul_le_mul (by omega) (by omega)
        omega
      interval_cases k <;> omega
    exact burnsideC124_solvable_card_84 h84

open Equiv Equiv.Perm Subgroup CFSG.ProperTwoGeneratedCore.CosetNormalizer in
private theorem burnsideC124_isKGroupCat_168 {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) (hA : ∀ g ∈ M, sign g = 1)
    (hcard : Nat.card M = 168) :
    CFSG.SectionRank.IsKGroupCat ↥M := by
  classical
  by_cases hsolv : Group.IsSolvable ↥M
  · exact CFSG.Quasithin.H13.U3.GC137.SQ.isKGroupCat_of_solvable hsolv
  · have hnt : Nontrivial ↥M := Finite.one_lt_card_iff_nontrivial.1 (by
      have : 0 < Nat.card M := Nat.card_pos
      omega)
    have hsimple : IsSimpleGroup ↥M := by
      refine ⟨fun N hN => ?_⟩
      by_contra hne
      push Not at hne
      apply hsolv
      have hN1 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).2 hne.1
      have hQ1 : 1 < Nat.card (↥M ⧸ N) := Subgroup.one_lt_index_of_ne_top hne.2
      have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      rw [hcard] at hmul
      have hNlt : Nat.card N < 168 := by
        rw [hmul]
        exact lt_mul_left (by omega) hQ1
      have hQlt : Nat.card (↥M ⧸ N) < 168 := by
        rw [hmul]
        exact lt_mul_right (by omega) hN1
      have hNd : Nat.card N ∣ 168 := ⟨Nat.card (↥M ⧸ N), by rw [hmul, mul_comm]⟩
      have hQd : Nat.card (↥M ⧸ N) ∣ 168 := ⟨Nat.card N, by rw [hmul]⟩
      haveI := burnsideC124_solvable_of_card_dvd_168 hNd hNlt
      haveI := burnsideC124_solvable_of_card_dvd_168 hQd hQlt
      exact Group.isSolvable_of_subgroup_quotient N
    have hnonab : ∃ a b : ↥M, a * b ≠ b * a := by
      by_contra hcomm
      push Not at hcomm
      exact hsolv (Group.isSolvable_of_comm hcomm)
    have hsix : ∀ g : ↥M, orderOf g ≠ 6 :=
      burnsideC124_no_order_six hc hA (by omega)
    obtain ⟨-, -, -, -, -, -, -, hmodel⟩ :=
      simple_order_168_without_six_projective_seven_recognition ↥M hnonab hcard hsix
    have hcat : CFSG.Blueprint.Catalog ↥M :=
      CFSG.Blueprint.lieModel_catalog ↥M .PSL 2 7 1 (Or.inl ⟨by decide, hmodel⟩)
    exact CFSG.Quasithin.H13.U3.GC137.SQ.isKGroupCat_of_card_168 hcard hcat

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_addRight_mem {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) (a : ZMod 7) : Equiv.addRight a ∈ M := by
  have : Equiv.addRight a = (Equiv.addRight (1 : ZMod 7)) ^ a.val := by
    refine Equiv.ext fun w => ?_
    rw [burnsideC124_addRight_pow_apply, ZMod.natCast_zmod_val]
    rfl
  rw [this]
  exact pow_mem hc _

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_card_alt7 : Nat.card (alternatingGroup (ZMod 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_zmod]
  decide

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_card_dvd_2520 {M : Subgroup (Perm (ZMod 7))}
    (hA : ∀ g ∈ M, sign g = 1) : Nat.card M ∣ 2520 := by
  have hle : M ≤ alternatingGroup (ZMod 7) := fun g hg => Perm.mem_alternatingGroup.2 (hA g hg)
  have := Subgroup.card_dvd_of_le hle
  rwa [burnsideC124_card_alt7] at this

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_order_cases' {m n : ℕ} (hdvd : m ∣ 2520) (h42 : 42 ∣ m) (hlt : m <
    2520)
    (hn : n ≡ 1 [MOD 7]) (hm : m = n * 21) : m = 168 := by
  have hn' : n % 7 = 1 := hn
  have hn120 : n ∣ 120 := by
    rw [hm] at hdvd
    have : n * 21 ∣ 120 * 21 := by simpa using hdvd
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
  have hn2 : 2 ∣ n := by omega
  have hn119 : n < 120 := by omega
  interval_cases n <;> first | omega | (exfalso; norm_num at hn120) | (exfalso; norm_num at hn2)

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_isKGroupCat_transitive {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) (hA : ∀ g ∈ M, sign g = 1)
    (hlt : Nat.card M < 2520) : CFSG.SectionRank.IsKGroupCat ↥M := by
  classical
  by_cases h2 : ∃ g ∈ M, g ≠ 1 ∧ ∃ x y : ZMod 7, x ≠ y ∧ g x = x ∧ g y = y
  · obtain ⟨g, hg, hg1, x, y, hxy, hx, hy⟩ := h2
    have h42 : 42 ∣ Nat.card M :=
      CFSG.Holt.SmallGroups.forty_two_dvd_card_zmod (burnsideC124_addRight_mem hc) hg hg1 hxy hx hy
    have hdvd := burnsideC124_card_dvd_2520 hA
    have h7 : 7 ∣ Nat.card M := (Dvd.intro 6 (by norm_num : 7 * 6 = 42)).trans h42
    obtain ⟨n, hn, hm⟩ := burnsideC124_sylow_count hc hdvd h7
    rcases burnsideC124_normalizer_card hc hA with hN | hN
    · exfalso
      have h := burnsideC124_selfNormalizing hc hdvd h7 hN
      rw [h] at h42
      omega
    · rw [hN] at hm
      have h168 := burnsideC124_order_cases' hdvd h42 hlt hn hm
      exact burnsideC124_isKGroupCat_168 hc hA h168
  · push Not at h2
    have hle := burnsideC124_card_le_of_free hc
      (fun g hg hg1 x y hxy hx hy => h2 g hg hg1 x y hxy hx hy)
    exact CFSG.Quasithin.H13.U3.GC137.SQ.isKGroupCat_of_solvable
      (CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega))

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_isKGroupCat_stab (b : Fin 7) :
    CFSG.SectionRank.IsKGroupCat (MulAction.stabilizer (alternatingGroup (Fin 7)) b) := by
  have hK6 : CFSG.SectionRank.IsKGroupCat (alternatingGroup {x : Fin 7 // x ≠ b}) := by
    have hcard : Fintype.card {x : Fin 7 // x ≠ b} = Fintype.card (Fin 6) := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_fin]
      simp
    obtain ⟨e⟩ := Fintype.truncEquivOfCardEq hcard |>.nonempty
    exact CFSG.SectionRank.IsKGroupCat.of_mulEquiv
      CFSG.Quasithin.H13.U3.GC137.SQ.isKGroupCat_alternatingGroup_six e.altCongrHom
  let f₁ : alternatingGroup {x : Fin 7 // x ≠ b} →* Perm (Fin 7) :=
    Equiv.Perm.ofSubtype.comp (alternatingGroup _).subtype
  have hf₁ : ∀ a, f₁ a ∈ alternatingGroup (Fin 7) := fun a => by
    rw [mem_alternatingGroup]
    simpa [f₁, sign_ofSubtype] using mem_alternatingGroup.mp a.2
  let f₂ := f₁.codRestrict (alternatingGroup (Fin 7)) hf₁
  have hf₂ : ∀ a, f₂ a ∈ MulAction.stabilizer (alternatingGroup (Fin 7)) b := fun a => by
    rw [MulAction.mem_stabilizer_iff]
    exact ofSubtype_apply_of_not_mem _ (by simp)
  have hsurj : Function.Surjective (f₂.codRestrict _ hf₂) := by
    rintro ⟨⟨τ, hτ⟩, hτ0⟩
    have h0 : τ b = b := hτ0
    have h₁ : ∀ x, τ x ≠ b ↔ x ≠ b := fun x =>
      not_congr ⟨fun h => τ.injective (h.trans h0.symm), fun h => h ▸ h0⟩
    have hsub : ofSubtype (τ.subtypePerm (p := fun y => y ≠ b) h₁) = τ :=
      ofSubtype_subtypePerm (p := fun y => y ≠ b) h₁ fun x hx h => hx (h.symm ▸ h0)
    refine ⟨⟨τ.subtypePerm (p := fun y => y ≠ b) h₁, ?_⟩, ?_⟩
    · rw [mem_alternatingGroup, ← sign_ofSubtype, hsub]
      exact mem_alternatingGroup.mp hτ
    · exact Subtype.ext (Subtype.ext hsub)
  exact CFSG.SectionRank.IsKGroupCat.of_surjective hK6 _ hsurj

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_isKGroupCat_of_small_orbit
    {H : Subgroup (alternatingGroup (Fin 7))} {b : Fin 7}
    (hO : Nat.card (MulAction.orbit H b) ≤ 3) : CFSG.SectionRank.IsKGroupCat ↥H := by
  let ψ : ↥H →* Perm (MulAction.orbit H b) := MulAction.toPermHom H _
  refine CFSG.Quasithin.H13.U3.GC137.SQ.isKGroupCat_of_ker ψ ?_ ?_
  · let f : ψ.ker →* MulAction.stabilizer (alternatingGroup (Fin 7)) b :=
      ((H.subtype.comp ψ.ker.subtype).codRestrict
        (MulAction.stabilizer (alternatingGroup (Fin 7)) b) (fun g => by
          have hg := g.2
          rw [MonoidHom.mem_ker] at hg
          have := congrArg
            (fun p : Perm (MulAction.orbit H b) => (p ⟨b, MulAction.mem_orbit_self b⟩ : Fin 7)) hg
          rw [MulAction.mem_stabilizer_iff]
          simpa [ψ, MulAction.toPermHom_apply, Subgroup.smul_def] using this))
    refine CFSG.SectionRank.IsKGroupCat.of_injective (burnsideC124_isKGroupCat_stab b) f ?_
    intro g g' h
    have := congrArg (fun a : MulAction.stabilizer (alternatingGroup (Fin 7)) b =>
      ((a : alternatingGroup (Fin 7)) : Perm (Fin 7))) h
    exact Subtype.ext (Subtype.ext (Subtype.ext this))
  · refine CFSG.Quasithin.H13.U3.GC137.SQ.isKGroupCat_of_solvable
      (CFSG.GroupTheory.groups_order_below_sixty_solvable ?_)
    rw [Nat.card_perm]
    have : (Nat.card (MulAction.orbit H b)).factorial ≤ Nat.factorial 3 := Nat.factorial_le hO
    have h6 : Nat.factorial 3 = 6 := by decide
    omega

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_exists_small_orbit {H : Subgroup (alternatingGroup (Fin 7))}
    (h : ¬ MulAction.IsPretransitive H (Fin 7)) :
    ∃ b : Fin 7, Nat.card (MulAction.orbit H b) ≤ 3 := by
  by_contra hcon
  push Not at hcon
  apply h
  refine ⟨fun x y => ?_⟩
  by_contra hxy
  push Not at hxy
  have hy : y ∉ MulAction.orbit H x := fun ⟨g, hg⟩ => hxy g hg
  have hdisj : Disjoint (MulAction.orbit H x) (MulAction.orbit H y) := by
    rw [Set.disjoint_left]
    intro z hzx hzy
    apply hy
    have h1 : MulAction.orbit H z = MulAction.orbit H x := MulAction.orbit_eq_iff.2 hzx
    have h2 : MulAction.orbit H z = MulAction.orbit H y := MulAction.orbit_eq_iff.2 hzy
    have := MulAction.mem_orbit_self (M := H) y
    rwa [← h2, h1] at this
  have hx4 := hcon x
  have hy4 := hcon y
  rw [Nat.card_coe_set_eq] at hx4 hy4
  have hunion := Set.ncard_union_eq hdisj
  have hle : (MulAction.orbit H x ∪ MulAction.orbit H y).ncard ≤ 7 := by
    have := Set.ncard_le_ncard (Set.subset_univ (MulAction.orbit H x ∪ MulAction.orbit H y))
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_isKGroupCat_of_transitive {H : Subgroup (alternatingGroup (Fin 7))}
    (hH : H ≠ ⊤) (htr : MulAction.IsPretransitive H (Fin 7)) :
    CFSG.SectionRank.IsKGroupCat ↥H := by
  classical
  have hinj1 : Function.Injective (alternatingGroup (Fin 7)).subtype := Subtype.val_injective
  set H' : Subgroup (Perm (Fin 7)) := H.map (alternatingGroup (Fin 7)).subtype with hH'
  have hH'card : Nat.card H' = Nat.card H := Subgroup.card_map_of_injective hinj1
  have h7 : 7 ∣ Nat.card H := by
    have h1 := Subgroup.index_dvd_card (MulAction.stabilizer H (0 : Fin 7))
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    exact h1
  obtain ⟨σ, hσ⟩ := CFSG.Holt.SmallGroups.exists_finRotate_mem_map_conj (M := H') (hH'card ▸ h7)
  set M : Subgroup (Perm (Fin 7)) := H'.map (MulAut.conj σ).toMonoidHom with hMdef
  have hc : (Equiv.addRight (1 : ZMod 7) : Perm (Fin 7)) ∈ M := by
    have h := hσ
    rw [burnsideC124_finRotate_eq] at h
    exact h
  have hA : ∀ g ∈ M, sign g = 1 := by
    intro g hg
    obtain ⟨h, ⟨a, ha, rfl⟩, rfl⟩ := hg
    have hs : sign (a : Perm (Fin 7)) = 1 := Perm.mem_alternatingGroup.1 a.2
    show sign (σ * (a : Perm (Fin 7)) * σ⁻¹) = 1
    rw [map_mul, map_mul, hs, mul_one, map_inv, mul_inv_cancel]
  have hMcard : Nat.card M = Nat.card H := by
    rw [hMdef, Subgroup.card_map_of_injective (MulAut.conj σ).injective, hH'card]
  have hlt : Nat.card M < 2520 := by
    rw [hMcard]
    have hle := Subgroup.card_le_card_group H
    have hne : Nat.card H ≠ Nat.card (alternatingGroup (Fin 7)) := fun h =>
      hH (Subgroup.eq_top_of_card_eq H h)
    have h2520 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    omega
  have hK : CFSG.SectionRank.IsKGroupCat ↥M := burnsideC124_isKGroupCat_transitive hc hA hlt
  exact CFSG.SectionRank.IsKGroupCat.of_mulEquiv hK
    ((Subgroup.equivMapOfInjective H _ hinj1).trans
      (Subgroup.equivMapOfInjective H' (MulAut.conj σ).toMonoidHom (MulAut.conj σ).injective))

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_isKGroupCat_alt7 :
    CFSG.SectionRank.IsKGroupCat (alternatingGroup (Fin 7)) := by
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  refine CFSG.Quasithin.H13.U3.GC137.SQ.isKGroupCat_of_simple
    (Or.inr (Or.inl ⟨7, by norm_num, ⟨MulEquiv.refl _⟩⟩)) fun H hH N _ hs hnab => ?_
  have hKH : CFSG.SectionRank.IsKGroupCat ↥H := by
    by_cases htr : MulAction.IsPretransitive H (Fin 7)
    · exact burnsideC124_isKGroupCat_of_transitive hH htr
    · obtain ⟨b, hb⟩ := burnsideC124_exists_small_orbit htr
      exact burnsideC124_isKGroupCat_of_small_orbit hb
  haveI := hs
  exact CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hKH ⊤
    ((QuotientGroup.mk' N).comp (⊤ : Subgroup ↥H).subtype) (by
      intro q
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨⟨h, trivial⟩, rfl⟩)

open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers CFSG.RankThree.PartTwo in
private theorem burnsideC124_card_ker_dvd {E : Type} [Group E]
    [Finite E]
    [Group.IsPerfect E] {m : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 7)
    (q : E →* alternatingGroup (Fin m)) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center E) : Nat.card q.ker ∣ 6 := by
  have hsurj := hopfMultiplierToKer_surjective q hq hker
  have key := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (hopfMultiplierToKer q hq hker).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv] at key
  have hdvd : Nat.card q.ker ∣ Nat.card (hopfMultiplier (alternatingGroup (Fin m))) :=
    Dvd.intro _ key.symm
  rcases hm with rfl | rfl | rfl
  · rw [hopfMultiplier_alternatingGroup_five.2] at hdvd
    exact hdvd.trans (by norm_num)
  · rwa [hopfMultiplier_alternatingGroup_six.2] at hdvd
  · rwa [hopfMultiplier_alternatingGroup_seven.2] at hdvd

open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers CFSG.RankThree.PartTwo in
private theorem burnsideC124_card_alt {m : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 7) :
    Nat.card (alternatingGroup (Fin m)) = 60 ∨ Nat.card (alternatingGroup (Fin m)) = 360 ∨
      Nat.card (alternatingGroup (Fin m)) = 2520 := by
  rcases hm with rfl | rfl | rfl
  · left
    have := nat_card_alternatingGroup_fin 3
    simpa [Nat.factorial] using this
  · right; left
    have := nat_card_alternatingGroup_fin 4
    simpa [Nat.factorial] using this
  · right; right
    have := nat_card_alternatingGroup_fin 5
    simpa [Nat.factorial] using this

open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers CFSG.RankThree.PartTwo in
private theorem burnsideC124_card_dvd {E : Type} [Group E] [Finite E]
    [Group.IsPerfect E] {m : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 7)
    (q : E →* alternatingGroup (Fin m)) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center E) :
    Nat.card E = Nat.card (alternatingGroup (Fin m)) * Nat.card q.ker ∧ Nat.card E ∣ 15120 := by
  have hK := burnsideC124_card_ker_dvd hm q hq hker
  have hcard : Nat.card E = Nat.card (alternatingGroup (Fin m)) * Nat.card q.ker := by
    rw [q.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv]
  refine ⟨hcard, ?_⟩
  rw [hcard]
  have hA : Nat.card (alternatingGroup (Fin m)) ∣ 2520 := by
    rcases burnsideC124_card_alt hm with h | h | h <;> rw [h] <;> norm_num
  exact (Nat.mul_dvd_mul hA hK).trans (by norm_num)

open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers CFSG.RankThree.PartTwo in
private theorem burnsideC124_not_cube_dvd {N p : ℕ} (hN : N ∣ 15120) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) : ¬ p ^ 3 ∣ N := by
  intro hd
  have h1 : p ^ 3 ∣ 15120 := hd.trans hN
  have h2 : p ∣ 15120 := (dvd_pow_self p (by norm_num)).trans h1
  have h3 : p ≤ 15120 := Nat.le_of_dvd (by norm_num) h2
  have : p ^ 3 ≤ 15120 := Nat.le_of_dvd (by norm_num) h1
  have hp25 : p < 25 := by
    by_contra h
    have : 25 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases p <;> first
    | (exfalso; revert hp; norm_num; done)
    | omega
    | (exfalso; revert h1; norm_num; done)

open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers CFSG.RankThree.PartTwo in
private theorem burnsideC124_rankLeTwo {E : Type} [Group E]
    [Finite E]
    [hperf : Group.IsPerfect E] {m : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 7)
    (q : E →* alternatingGroup (Fin m)) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center E) : RankLeTwo E := by
  obtain ⟨hcard, hdvd⟩ := burnsideC124_card_dvd hm q hq hker
  have hK := burnsideC124_card_ker_dvd hm q hq hker
  intro p hp hp2 F hF
  by_cases hp3 : p = 3
  · subst hp3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ :=
      (CFSG.Quasithin.H13.U3.GC137.SQ.isPGroup_of_isElemAbelian (p := 3) hF).exists_card_eq
    have hFdvd : 3 ^ n ∣ Nat.card E := hn ▸ Subgroup.card_subgroup_dvd_card F
    have hn3 : n ≤ 3 := by
      by_contra h
      have h4 : 3 ^ 4 ∣ 15120 := (pow_dvd_pow 3 (by omega)).trans (hFdvd.trans hdvd)
      norm_num at h4
    rw [hn]
    by_cases h3 : n = 3
    · exfalso
      subst h3
      have h27 : 27 ∣ Nat.card E := by simpa using hFdvd
      have h3K : 3 ∣ Nat.card q.ker := by
        rw [hcard] at h27
        have hk6 : Nat.card q.ker ≤ 6 := Nat.le_of_dvd (by norm_num) hK
        have hkpos : 0 < Nat.card q.ker := Nat.card_pos
        rcases burnsideC124_card_alt hm with h | h | h <;> rw [h] at h27 <;>
          interval_cases hk : Nat.card q.ker <;> omega
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := q.ker) 3 h3K
      have hzo : orderOf (x : E) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
      have hzc : (x : E) ∈ Subgroup.center E := hker x.2
      have hFab : ∀ a b : F, a * b = b * a := fun a b => hF.1.is_comm.comm a b
      have hpow := KFacts.KS14.pow_index_eq_one_of_isPerfect F hFab hzc
      have hmul := F.card_mul_index
      rw [hn] at hmul
      have h81 : ¬ 3 ∣ F.index := by
        intro h3i
        have : 3 ^ 4 ∣ Nat.card E := by
          rw [← hmul]
          obtain ⟨c, hc⟩ := h3i
          rw [hc]
          exact ⟨c, by ring⟩
        have := this.trans hdvd
        norm_num at this
      exact h81 (hzo ▸ orderOf_dvd_of_pow_eq_one hpow)
    · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · exact card_le_of_cube_free hp (burnsideC124_not_cube_dvd hdvd hp hp2 hp3) hF

open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.Blueprint CFSG.SectionRank in
private theorem burnsideC124_card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have := CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 3
  simpa [Nat.factorial] using this

open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.Blueprint CFSG.SectionRank in
private theorem burnsideC124_five_le_of_dvd_factorial {k : ℕ} (h : 60 ∣ k.factorial) : 5 ≤ k := by
  by_contra hk
  have : k ≤ 4 := by omega
  interval_cases k <;> simp [Nat.factorial] at h

open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.Blueprint CFSG.SectionRank in
private theorem burnsideC124_isKGroupCat_alt5 : IsKGroupCat (alternatingGroup (Fin 5)) := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  refine isKGroupCat_of_simple (Or.inr (Or.inl ⟨5, le_rfl, ⟨MulEquiv.refl _⟩⟩))
    fun H hH N _ hs hnab => ?_
  exfalso
  have hdvd := card_dvd_factorial_index hH
  rw [burnsideC124_card_alt_five] at hdvd
  have h5 := burnsideC124_five_le_of_dvd_factorial hdvd
  have hmul := H.card_mul_index
  rw [burnsideC124_card_alt_five] at hmul
  obtain ⟨h60, hle⟩ := sixty_le_card_section N hs hnab
  have hH12 : Nat.card H ≤ 12 := by
    by_contra h
    have : 13 * 5 ≤ Nat.card H * H.index := Nat.mul_le_mul (by omega) h5
    omega
  omega

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.U3.GC137.SQ CFSG.SectionRank in
private theorem burnsideC124_mem_oTwoZIn_iff {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (x : ↥L) :
    (x : G) ∈ oTwoZIn L ↔
      (QuotientGroup.mk x : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
  unfold oTwoZIn preimageModTwoCore
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    subst this
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.U3.GC137.SQ CFSG.SectionRank in
private theorem burnsideC124_exists_hom {G : Type} [Group G] [Finite G] {L : Subgroup G} {m : ℕ}
    (halt : IsAltQuotient L (oTwoZIn L) m) :
    ∃ ψ : (↥L ⧸ CFSG.pCore 2 ↥L) →* alternatingGroup (Fin m), Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨φ, hφ, hker⟩ := halt
  have hmem : ∀ x : ↥L, φ x = 1 ↔ (QuotientGroup.mk x : ↥L ⧸ CFSG.pCore 2 ↥L) ∈
      Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    intro x
    rw [← burnsideC124_mem_oTwoZIn_iff, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hOle : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hmem]
    have : (QuotientGroup.mk x : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := (QuotientGroup.eq_one_iff x).2 hx
    rw [this]
    exact Subgroup.one_mem _
  refine ⟨QuotientGroup.lift _ φ hOle, ?_, ?_⟩
  · intro a
    obtain ⟨x, rfl⟩ := hφ a
    exact ⟨QuotientGroup.mk x, rfl⟩
  · intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    rw [MonoidHom.mem_ker] at hz
    exact (hmem x).1 hz

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.U3.GC137.SQ CFSG.SectionRank in
private theorem burnsideC124_sqtkGroup
    {G : Type} [Group G] [Finite G] {X T L : Subgroup G} {m : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 7)
    (hT : IsSylowTwoOf T X)
    (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) (hL : L ∈ cComp X)
    (halt : IsAltQuotient L (oTwoZIn L) m) : SQTKGroup ↥X := by
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hN : X ≤ Subgroup.normalizer (L : Set G) := C124.le_normalizer_of_prod hT hprod hL
  have hnorm : (L.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).2 hN
  have : (Subgroup.inclusion hLX).range.Normal := by
    rw [Subgroup.inclusion_range]
    exact hnorm
  have hq := isPGroup_quotient_of_prod hT hprod hLX
  have hO : IsPGroup 2 (CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
  obtain ⟨ψ, hψ, hψker⟩ := burnsideC124_exists_hom halt
  have hLperf : Group.IsPerfect ↥L := C124.isPerfect_of_comm_eq (perfect_of_mem_cComp hL)
  have hperf : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) := inferInstance
  have hKm : IsKGroupCat (alternatingGroup (Fin m)) := by
    rcases hm with rfl | rfl | rfl
    · exact burnsideC124_isKGroupCat_alt5
    · exact isKGroupCat_alternatingGroup_six
    · exact burnsideC124_isKGroupCat_alt7
  have hK : IsKGroupCat (↥L ⧸ CFSG.pCore 2 ↥L) := by
    refine isKGroupCat_of_ker ψ ?_ hKm
    refine isKGroupCat_of_solvable (Group.isSolvable_of_comm fun a b => Subtype.ext ?_)
    exact (Subgroup.mem_center_iff.1 (hψker a.2) b.1).symm
  have hR : RankLeTwo (↥L ⧸ CFSG.pCore 2 ↥L) := burnsideC124_rankLeTwo hm ψ hψ hψker
  exact ⟨stronglyQuasithin_of_rankLeTwo (rankLeTwo_of_hom (Subgroup.inclusion hLX)
      (Subgroup.inclusion_injective hLX) hq (CFSG.pCore 2 ↥L) hO hR),
    isKGroupCat_of_ext (Subgroup.inclusion hLX) (Subgroup.inclusion_injective hLX) hq
      (CFSG.pCore 2 ↥L) hO hK⟩

open CFSG.Quasithin CFSG.QuasithinUnique in
private theorem burnsideC124_le_of_autOn_le {G : Type} [Group G] [Finite G] {X V L R : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hLX : L ≤ X) (hRX : R ≤ X)
    (h : autOn R V ≤ autOn L V) : R ≤ L ⊔ (X ⊓ Subgroup.centralizer (V : Set G)) := by
  intro r hr
  have hrN : r ∈ Subgroup.normalizer (V : Set G) := hXN (hRX hr)
  obtain ⟨n, hnL, hn⟩ :=
    AutOn.mem_autOn_iff.1 (h (AutOn.conjAct_mem_autOn_of_mem hrN hr))
  have hc : (n : G)⁻¹ * r ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : G)) hn
    simp only [AutOn.coe_conjAct_apply] at h1
    calc v * ((n : G)⁻¹ * r) = (n : G)⁻¹ * ((n : G) * v * (n : G)⁻¹) * r := by group
      _ = (n : G)⁻¹ * (r * v * r⁻¹) * r := by rw [h1]
      _ = (n : G)⁻¹ * r * v := by group
  have hr' : r = (n : G) * ((n : G)⁻¹ * r) := by group
  rw [hr']
  exact Subgroup.mul_mem_sup hnL ⟨X.mul_mem (X.inv_mem (hLX hnL)) (hRX hr), hc⟩

open CFSG.Quasithin CFSG.QuasithinUnique in
private theorem burnsideC124_isChiBlock2 {G : Type} [Group G] [Finite G] {X L : Subgroup G}
    (h : IsChiBlock X L) : IsChiBlock2 X L := by
  obtain ⟨hb, hn | ⟨m, hmo, -, hmt⟩⟩ := h
  · exact ⟨hb, Or.inl hn⟩
  · exact ⟨hb, Or.inr ⟨m, hmo, hmt⟩⟩

end BurnsideC124

section

open CFSG.ASVolI.ChC CFSG.Quasithin CFSG.QuasithinUnique in
theorem as_C_1_24
    : C_1_24 := by
  intro G _ _ X V T L R hHyp hXLT hL hCL hVL hQR hRT m halt hm
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t := by
    intro x hx
    have hx' : x ∈ (X : Set G) := hx
    rw [hXLT] at hx'
    obtain ⟨l, hl, t, ht, rfl⟩ := Set.mem_mul.1 hx'
    exact ⟨l, hl, t, ht, rfl⟩
  have hmm : m = 5 ∨ m = 6 ∨ m = 7 := by
    rcases hm with (h | h) | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hSQ : SQTKGroup ↥X := burnsideC124_sqtkGroup hmm hHyp.sylow hprod hL halt
  have hRX : R ≤ X := hRT.trans hHyp.sylow.1
  have hm' : m = 5 ∨ m = 7 ∨ (m = 6 ∧ R ≤ L ⊔ (X ⊓ Subgroup.centralizer (V : Set G))) ∨
      (m = 6 ∧ Nat.card ↥(autOn R V) = 2) := by
    rcases hm with (h | h) | ⟨h, hle⟩ | ⟨h, hc⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨h, burnsideC124_le_of_autOn_le hHyp.reduced.2.1 hLX hRX hle⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h, hc⟩))
  rcases C124.c124StatementSQTK_holds G X T V L R m hHyp.charTwo hSQ hHyp.reduced hHyp.sylow
    hprod hL hCL hVL halt hQR hRT hm' with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (burnsideC124_isChiBlock2 h))
  · obtain ⟨hb, h1 | h2 | h3⟩ := h
    · exact Or.inr (Or.inr (Or.inl ⟨hb, h1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, h2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hb, h3⟩)))

end


section


end


section BurnsideA38b


end BurnsideA38b

section


end


section


end


end CFSG.ASVolI
