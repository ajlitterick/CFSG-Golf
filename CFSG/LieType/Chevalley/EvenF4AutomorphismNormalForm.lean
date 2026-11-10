module

public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenF4SimplePairs
import CFSG.LieType.Chevalley.EvenF4RawBorel
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B3Unconditional
public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagramRealized
import CFSG.LocalAnalysis.EvenBN.G2.Automorphisms
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CenterProofFastPart2
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagBasic
public import CFSG.LieType.Chevalley.RootCommutatorPairTable

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Ree RootOps
open scoped commutatorElement

section Generic

variable {K : Type} [Field K] [Finite K] (t : ReeTag) [CharP K t.prime]

theorem ree_two_mul_dvd_of_pow_eq_conj
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = t.prime ^ f)
    {i₀ : Fin t.tag.rank} (hi₀ : t.perm i₀ ≠ i₀) {k : ℕ} {h : adjointGroup t.tag K}
    (hk : t.finiteExceptionalAut K ^ k = MulAut.conj h) : 2 * f ∣ k := by
  have hp : t.prime.Prime := Fact.out
  have hA : MulAut.conj h ∈ unipotentPairAut t.tag K :=
    hk ▸ pow_mem (finiteExceptionalAut_mem_unipotentPairAut t) k
  obtain ⟨b, hb⟩ := exists_conj_eq_exactNormalAut_diag hA
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · obtain ⟨fr, hfr, hord, -⟩ := finite_field_automorphism_fixed_field_cardinality hp hf hK
    rw [finiteExceptionalAut_pow_two_mul, ← exactNormalAut_one_eq_finiteFrobeniusAut_pow
      t (σ := fr ^ j) (ringAut_pow_apply_of_frobenius hfr j), hb] at hk
    obtain ⟨-, h1⟩ := exactNormalAut_zero_injective hk
    exact Nat.mul_dvd_mul_left 2 (hord ▸ orderOf_dvd_of_pow_eq_one h1)
  · exfalso
    have e := congrArg (fun α : MulAut (adjointGroup t.tag K) => α (adjX t.tag K i₀ 1)) hk
    simp only [hb, exactNormalAut_zero_adjX] at e
    rw [pow_succ', MulAut.mul_apply, finiteExceptionalAut_pow_two_mul] at e
    have e2 : (t.finiteFrobeniusAut K ^ j) (adjX t.tag K i₀ 1) = adjX t.tag K i₀ 1 := by
      change (t.finiteFrobeniusAut K ^ j) (xElement _ 1) = xElement _ 1
      rw [ReeTag.finiteFrobeniusAut_pow_xElement, one_pow]
    have e3 : t.finiteExceptionalAut K (adjX t.tag K i₀ 1) = adjX t.tag K (t.perm i₀) 1 := by
      change t.finiteExceptionalAut K (xElement _ 1) = xElement _ 1
      rw [ReeTag.finiteExceptionalAut_xElement, one_pow]
    rw [e2, e3] at e
    have e' : xUnit t.tag K (t.perm i₀) 1 =
        xUnit t.tag K i₀ ((b i₀ : K) * (1 : K ≃+* K) 1) := congrArg Subtype.val e
    apply not_commute_xUnit_yUnit (τ := t.tag) (K := K) (t.perm i₀)
    rw [e']
    exact commute_xUnit_yUnit_of_ne' (Ne.symm hi₀) _ 1

theorem ree_exists_conj_mul_pow
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = t.prime ^ f)
    (hperm : ∀ β ∈ unipotentPairAut t.tag K, ∀ π : Equiv.Perm (Fin t.tag.rank),
      (∀ i, (simplePosSubgroup t.tag K i).map β.toMonoidHom = simplePosSubgroup t.tag K (π i) ∧
        (simpleNegSubgroup t.tag K i).map β.toMonoidHom = simpleNegSubgroup t.tag K (π i)) →
      π = 1 ∨ π = t.perm)
    (hdC : ∀ a : Fin t.tag.rank → Kˣ, rootDiagUnit t.tag a ∈ adjointGroup t.tag K)
    (α : MulAut (adjointGroup t.tag K)) :
    ∃ (g : adjointGroup t.tag K) (k : ℕ), α = MulAut.conj g * t.finiteExceptionalAut K ^ k := by
  have hp : t.prime.Prime := Fact.out
  have hφ2f : t.finiteExceptionalAut K ^ (2 * f) = 1 := by
    rw [finiteExceptionalAut_pow_two_mul]
    exact finiteFrobeniusAut_pow_card t hK
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem t.tag).length
  obtain ⟨c, β, hβ, rfl⟩ : ∃ (c : adjointGroup t.tag K)
      (β : MulAut (adjointGroup t.tag K)),
      β ∈ unipotentPairAut t.tag K ∧ α = MulAut.conj c * β := by
    by_cases ht : t = ReeTag.F4
    · subst t
      exact f4_exists_conj_mul_unipotentPair 2 w₀ hw₀ α
    · obtain ⟨c, β, hU, hV, hα⟩ :=
        (exceptional_ordinary_Sylow_opposition t.tag K t.prime w₀ hw₀).2.2.2.2.2 α
      exact ⟨c, β, ⟨hU, hV⟩, hα⟩
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin t.tag.rank), ∀ i,
      (simplePosSubgroup t.tag K i).map β.toMonoidHom = simplePosSubgroup t.tag K (π i) ∧
      (simpleNegSubgroup t.tag K i).map β.toMonoidHom = simpleNegSubgroup t.tag K (π i) := by
    by_cases ht : t = ReeTag.F4
    · subst t
      exact f4_exists_perm_map_simple hβ
    · exact exists_perm_map_simple hβ
  obtain ⟨ζ, ε, hζ, rfl⟩ : ∃ (ζ : MulAut (adjointGroup t.tag K)) (ε : ℕ),
      ζ ∈ rootPairAut t.tag K ∧ β = ζ * t.finiteExceptionalAut K ^ ε := by
    rcases hperm β hβ π hπ with rfl | rfl
    · exact ⟨β, 0, mem_rootPairAut.2 fun i => ⟨(hπ i).1, (hπ i).2⟩, by rw [pow_zero, mul_one]⟩
    · refine ⟨β * t.finiteExceptionalAut K, 2 * f - 1,
        mem_rootPairAut.2 fun i => ⟨?_, ?_⟩, ?_⟩
      · rw [map_toMonoidHom_mul_mulAut, map_simplePosSubgroup_finiteExceptionalAut, (hπ _).1,
          ReeTag.perm_perm]
      · rw [map_toMonoidHom_mul_mulAut, map_simpleNegSubgroup_finiteExceptionalAut, (hπ _).2,
          ReeTag.perm_perm]
      · rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega), hφ2f, mul_one]
  obtain ⟨p, hp', -⟩ :=
    (ordinary_Chevalley_root_pair_common_field_parameter t.tag K).1 ζ hζ
  have hζN : ζ = exactNormalAut t.tag K p.1 p.2 0 :=
    mulAut_ext_adjX_adjY (fun i c => by rw [(hp' i).1, exactNormalAut_zero_adjX])
      fun i c => by rw [(hp' i).2.1, exactNormalAut_zero_adjY]
  obtain ⟨fr, hfr, hord, htop, -⟩ := finite_field_automorphism_fixed_field_cardinality hp hf hK
  have hfin : IsOfFinOrder fr := orderOf_pos_iff.1 (by rw [hord]; omega)
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).1
    (hfin.mem_powers_iff_mem_zpowers.2 (by rw [htop]; exact Subgroup.mem_top p.2))
  have hN : exactNormalAut t.tag K p.1 p.2 0 =
      MulAut.conj (⟨rootDiagUnit t.tag p.1, hdC p.1⟩ : adjointGroup t.tag K) *
        t.finiteExceptionalAut K ^ (2 * m) := by
    calc exactNormalAut t.tag K p.1 p.2 0 = exactNormalAut t.tag K (p.1 * 1) p.2 0 := by
          rw [mul_one]
      _ = exactNormalAut t.tag K p.1 1 0 * exactNormalAut t.tag K 1 p.2 0 :=
          (exactNormalAut_diag_mul _ _ _ _).symm
      _ = _ := by
          rw [exactNormalAut_diag_eq_conj _ (hdC p.1), ← hm,
            exactNormalAut_one_eq_finiteFrobeniusAut_pow t (ringAut_pow_apply_of_frobenius hfr m),
            finiteExceptionalAut_pow_two_mul]
  refine ⟨c * ⟨rootDiagUnit t.tag p.1, hdC p.1⟩, 2 * m + ε, ?_⟩
  rw [hζN, hN, map_mul, pow_add]
  simp only [mul_assoc]

theorem ree_exact_automorphism_normal_form
    {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = t.prime ^ f)
    (hperm : ∀ β ∈ unipotentPairAut t.tag K, ∀ π : Equiv.Perm (Fin t.tag.rank),
      (∀ i, (simplePosSubgroup t.tag K i).map β.toMonoidHom = simplePosSubgroup t.tag K (π i) ∧
        (simpleNegSubgroup t.tag K i).map β.toMonoidHom = simpleNegSubgroup t.tag K (π i)) →
      π = 1 ∨ π = t.perm)
    (hdC : ∀ a : Fin t.tag.rank → Kˣ, rootDiagUnit t.tag a ∈ adjointGroup t.tag K)
    {i₀ : Fin t.tag.rank} (hi₀ : t.perm i₀ ≠ i₀) :
    orderOf (t.finiteExceptionalAut K) = 2 * f ∧
    (∀ α : MulAut (adjointGroup t.tag K),
      ∃! gk : adjointGroup t.tag K × Fin (2 * f),
        α = MulAut.conj gk.1 * t.finiteExceptionalAut K ^ (gk.2 : ℕ)) ∧
    (∃ Θ : MulAut (adjointGroup t.tag K) →* Multiplicative (ZMod (2 * f)),
      (∀ (α : MulAut (adjointGroup t.tag K)) (g : adjointGroup t.tag K) (k : ℕ),
        α = MulAut.conj g * t.finiteExceptionalAut K ^ k →
          Θ α = Multiplicative.ofAdd (k : ZMod (2 * f))) ∧
      Function.Surjective Θ ∧
      Θ.ker = (MulAut.conj : adjointGroup t.tag K →* MulAut (adjointGroup t.tag K)).range) ∧
    (∀ (α : MulAut (adjointGroup t.tag K)) (g : adjointGroup t.tag K) (k : ℕ),
      k < 2 * f → α = MulAut.conj g * t.finiteExceptionalAut K ^ k → α ^ 2 = 1 →
        k = 0 ∨ k = f) ∧
    ((t.finiteExceptionalAut K ^ f) ^ 2 = 1 ∧ t.finiteExceptionalAut K ^ f ≠ 1) ∧
    (∀ e : ℕ, f = 2 * e → t.finiteExceptionalAut K ^ f = t.finiteFrobeniusAut K ^ e) ∧
    ∀ a : ℕ, f = 2 * a + 1 →
      t.finiteExceptionalAut K ^ f = t.finiteExceptionalAut K * t.finiteFrobeniusAut K ^ a ∧
        t.finiteExceptionalAut K ^ f = t.finiteReeAut K a ∧
        ∀ g : adjointGroup t.tag K,
          g ∈ t.finiteReeFixedGroup K a ↔ (t.finiteExceptionalAut K ^ f) g = g := by
  have hφ2f : t.finiteExceptionalAut K ^ (2 * f) = 1 := by
    rw [finiteExceptionalAut_pow_two_mul]
    exact finiteFrobeniusAut_pow_card t hK
  obtain ⟨hord, hNF, hΘ, hinv⟩ := mulAut_cyclic_complement_normal_form center_adjointGroup_eq_bot
    (t.finiteExceptionalAut K) (by omega) hφ2f (ree_exists_conj_mul_pow t hf hK hperm hdC)
    fun k h hk => ree_two_mul_dvd_of_pow_eq_conj t hf hK hi₀ hk
  refine ⟨hord, hNF, hΘ, fun α g k hk hα h2 => ?_, ⟨?_, ?_⟩, fun e he => ?_, fun a ha => ?_⟩
  ·
    obtain ⟨m, rfl⟩ := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).1 (hinv α g k hα h2)
    have hm : m < 2 := Nat.lt_of_mul_lt_mul_left (by linarith : f * m < f * 2)
    interval_cases m <;> simp
  · rw [← pow_mul, mul_comm, hφ2f]
  · intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at this
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  · rw [he]
    exact finiteExceptionalAut_pow_two_mul t e
  · have hφf : t.finiteExceptionalAut K ^ f =
        t.finiteExceptionalAut K * t.finiteFrobeniusAut K ^ a := by
      rw [ha, pow_succ', finiteExceptionalAut_pow_two_mul]
    exact ⟨hφf, hφf, fun g => by rw [hφf]; exact Iff.rfl⟩

end Generic

section F4

variable {K : Type} [Field K]


theorem list_prod_pinnedX_one_ne_one
    (τ : Tag) {m : ℕ} (hm : 0 < m)
    (α : Fin m → Fin τ.rank → ℤ) (hα : Function.Injective α)
    (hpos : ∀ i, IsRoot τ (α i) ∧ 0 < height (α i)) :
    (List.ofFn fun i => pinnedX τ K (α i) 1).prod ≠ 1 := by
  intro h
  have h0 : (List.ofFn fun i => pinnedX τ K (α i) ((0 : Fin m → K) i)).prod = 1 := by
    simp [pinnedX_zero]
  have h1 := (positive_root_product_injectivity τ K α hα hpos).2 (h.trans h0.symm)
  exact one_ne_zero (congrFun h1 ⟨0, hm⟩)

variable [CharP K 2]


end F4

theorem even_F4_exact_automorphism_normal_form
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ f) :
    orderOf (ReeTag.F4.finiteExceptionalAut K) = 2 * f ∧
    (∀ α : MulAut (adjointGroup ReeTag.F4.tag K),
      ∃! gk : adjointGroup ReeTag.F4.tag K × Fin (2 * f),
        α = MulAut.conj gk.1 * ReeTag.F4.finiteExceptionalAut K ^ (gk.2 : ℕ)) ∧
    (∃ Θ : MulAut (adjointGroup ReeTag.F4.tag K) →* Multiplicative (ZMod (2 * f)),
      (∀ (α : MulAut (adjointGroup ReeTag.F4.tag K)) (g : adjointGroup ReeTag.F4.tag K) (k : ℕ),
        α = MulAut.conj g * ReeTag.F4.finiteExceptionalAut K ^ k →
          Θ α = Multiplicative.ofAdd (k : ZMod (2 * f))) ∧
      Function.Surjective Θ ∧
      Θ.ker = (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
        MulAut (adjointGroup ReeTag.F4.tag K)).range) ∧
    (∀ (α : MulAut (adjointGroup ReeTag.F4.tag K)) (g : adjointGroup ReeTag.F4.tag K) (k : ℕ),
      k < 2 * f → α = MulAut.conj g * ReeTag.F4.finiteExceptionalAut K ^ k → α ^ 2 = 1 →
        k = 0 ∨ k = f) ∧
    ((ReeTag.F4.finiteExceptionalAut K ^ f) ^ 2 = 1 ∧ ReeTag.F4.finiteExceptionalAut K ^ f ≠ 1) ∧
    (∀ e : ℕ, f = 2 * e →
      ReeTag.F4.finiteExceptionalAut K ^ f = ReeTag.F4.finiteFrobeniusAut K ^ e) ∧
    ∀ m : ℕ, f = 2 * m + 1 →
      ReeTag.F4.finiteExceptionalAut K ^ f =
          ReeTag.F4.finiteExceptionalAut K * ReeTag.F4.finiteFrobeniusAut K ^ m ∧
        ReeTag.F4.finiteExceptionalAut K ^ f = ReeTag.F4.finiteReeAut K m ∧
        ∀ g : adjointGroup ReeTag.F4.tag K,
          g ∈ ReeTag.F4.finiteReeFixedGroup K m ↔ (ReeTag.F4.finiteExceptionalAut K ^ f) g = g := by
  have hperm : ∀ β ∈ unipotentPairAut ReeTag.F4.tag K, ∀ π : Equiv.Perm (Fin ReeTag.F4.tag.rank),
      (∀ i, (simplePosSubgroup ReeTag.F4.tag K i).map β.toMonoidHom =
          simplePosSubgroup ReeTag.F4.tag K (π i) ∧
        (simpleNegSubgroup ReeTag.F4.tag K i).map β.toMonoidHom =
          simpleNegSubgroup ReeTag.F4.tag K (π i)) →
      π = 1 ∨ π = ReeTag.F4.perm := by
    intro β _ π hπ
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    exact f4_even_simple_pair_perm fun i => (hπ i).1
  obtain ⟨⟨B, hB, -⟩, hrest⟩ := G2_F4_root_character_diagonals_inner ReeTag.F4.tag (Or.inr rfl) K
  exact ree_exact_automorphism_normal_form ReeTag.F4 hf hK hperm (fun a => (hrest B hB a).2.2.1)
    (i₀ := ⟨0, by decide⟩) (by decide)

namespace F4NativeNormalForm

open CFSG.Blueprint
  CFSG.StandardType.F4ExplicitPos.B3Pinned
  CFSG.StandardType.F4ExplicitPos.B3Unconditional
  CFSG.StandardType.F4ExplicitPos.LangPosition
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.EvenBN.G2
  CFSG.ComponentClassification.OuterAutomorphisms

section

variable {K : Type} [Field K] [Finite K] [CharP K 2]


private noncomputable instance f4PacketFactPrimeFive : Fact (Nat.Prime 5) :=
  ⟨by norm_num⟩

private noncomputable instance f4PacketFintypeK : Fintype K :=
  Fintype.ofFinite K


end

end F4NativeNormalForm

end CFSG.LieType.Chevalley
