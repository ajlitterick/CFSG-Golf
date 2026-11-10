module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoIn
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodUntwist

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.Coordinator

namespace Bal209TwoOuterInAux

section Abstract


theorem conj_commute_iff {G : Type*} [Group G] (g a b : G) :
    (g⁻¹ * a * g) * (g⁻¹ * b * g) = (g⁻¹ * b * g) * (g⁻¹ * a * g) ↔ a * b = b * a := by
  have h1 : (g⁻¹ * a * g) * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
  have h2 : (g⁻¹ * b * g) * (g⁻¹ * a * g) = g⁻¹ * (b * a) * g := by group
  rw [h1, h2, mul_right_cancel_iff, mul_left_cancel_iff]


end Abstract

section TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial


variable {K : Type} [Field K] [Finite K]


theorem ringAut_facts_of_card_four (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2) :
    σ ≠ 1 ∧ σ ^ 2 = 1 ∧ ∀ δ : K ≃+* K, δ = 1 ∨ δ = σ := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  obtain ⟨σ', hσ', hord, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two le_rfl K hK'
  have hσσ' : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ]; norm_num
  rw [hσσ'] at hord
  have hσ1 : σ ≠ 1 := fun h => by rw [h, orderOf_one] at hord; exact absurd hord (by decide)
  have hσ2 : σ ^ 2 = 1 := by rw [← pow_orderOf_eq_one σ, hord]; rfl
  have hK2 : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  obtain ⟨hcard, -⟩ := card_ringAut_and_isCyclic Nat.prime_two K hK2
  refine ⟨hσ1, hσ2, fun δ => ?_⟩
  have hδ2 : δ ^ 2 = 1 := by
    have := pow_card_eq_one' (G := RingAut K) (x := δ)
    rwa [hcard] at this
  exact eq_one_or_eq_of_sq_eq_one Nat.prime_two hK2 hσ1 hσ2 hδ2


theorem mem_inn_sup_diag_of_pow_three (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    {δ : MulAut (twistedE6RootGroup K σ)} (hδ3 : δ ^ 3 = 1) :
    δ ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
  classical
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ]; norm_num
  obtain ⟨hσ1, hσsq, hRA⟩ := ringAut_facts_of_card_four hK σ hσ
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, -, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two le_rfl K hK2 σ hσ2
  rw [← hker]
  refine MonoidHom.mem_ker.2 ?_
  rcases hRA (Θ δ) with h | h
  · exact h
  · exfalso
    have h3 : Θ δ ^ 3 = 1 := by rw [← map_pow, hδ3, map_one]
    rw [h, pow_succ, hσsq, one_mul] at h3
    exact hσ1 h3

open CFSG.HardMathSupport.Timmesfeld.CrossChar in
theorem exists_ghat (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    {δ : MulAut (twistedE6RootGroup K σ)} (hδ3 : δ ^ 3 = 1) (hδ : δ ∉ twistedE6Inn K σ) :
    ∃ ĝ : ModGL TwistTag.E6.tag K, ĝ ∈ twistedE6InndiagGL K σ ∧ ĝ ∉ twistedE6RootGroup K σ ∧
      ĝ ^ 3 = 1 ∧ ∀ c : twistedE6RootGroup K σ,
        ((δ c : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) = ĝ * c * ĝ⁻¹ := by
  classical
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ]; norm_num
  have hmem := mem_inn_sup_diag_of_pow_three hK σ hσ hδ3
  rw [← range_twistedE6InndiagConj] at hmem
  obtain ⟨g, hg⟩ := hmem
  have hinj := twistedE6InndiagConj_injective Nat.prime_two le_rfl hK2 σ hσ2
  refine ⟨(g : ModGL TwistTag.E6.tag K), g.2, ?_, ?_, ?_⟩
  · intro hgC
    apply hδ
    refine ⟨⟨(g : ModGL TwistTag.E6.tag K), hgC⟩, ?_⟩
    rw [← hg]
    refine MulEquiv.ext fun c => Subtype.ext ?_
    rfl
  · have h1 : twistedE6InndiagConj K σ (g ^ 3) = 1 := by rw [map_pow, hg, hδ3]
    have h2 : g ^ 3 = 1 := hinj (h1.trans (map_one _).symm)
    exact congrArg Subtype.val h2
  · intro c
    rw [← hg]
    exact twistedE6InndiagConj_apply g c

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.LangTorus in
theorem conj_ghat_mem_model [CharP K 2] (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K)
      (iterateFrobenius (AlgebraicClosure K) 2 1) g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0)
    {ĝ : ModGL TwistTag.E6.tag K} (hĝ : ĝ ∈ twistedE6InndiagGL K σ) :
    g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) ĝ * g0 ∈
      twE6TwoModel (AlgebraicClosure K) := by
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ]; norm_num
  have hcL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hFr : ∀ c : AlgebraicClosure K, iterateFrobenius (AlgebraicClosure K) 2 1 c = c ^ (2 ^ 1) :=
    fun c => by rw [iterateFrobenius_two_one]; norm_num
  have h1 := map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two le_rfl hK2 σ hσ2
    (iterateFrobenius (AlgebraicClosure K) 2 1) hFr (Subgroup.mem_map_of_mem _ hĝ)
  set D := LangDatum.ofTwist TwistTag.E6 (iterateFrobenius (AlgebraicClosure K) 2 1) 2
    iterateFrobenius_two_one twE6W0 hg0C hg0 with hD
  have h2 := model_eq_map_twistedFixedGroup D
    (Fr := iterateFrobenius (AlgebraicClosure K) 2 1) rfl
  have h3 : MulAut.conj D.g0⁻¹ (baseChangeGL (algebraMap K (AlgebraicClosure K)) ĝ) ∈ D.model := by
    rw [h2]
    exact Subgroup.mem_map_of_mem _ h1
  change g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) ĝ * g0 ∈ D.model
  convert h3 using 1
  simp [hD, LangDatum.ofTwist, MulAut.conj_apply]

end TwE6


section Transport


end Transport

section Ext

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T


variable {K : Type} [Field K] {ω : Kˣ} {kb : List (List ℕ)}


end Ext

section Ext2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T


variable {K : Type} [Field K] {ω : Kˣ} {kb : List (List ℕ)}


end Ext2

section Hyper

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T Timmesfeld.Co1Leaf


variable {τ : Tag} {k : Type} [Field k] {G : Subgroup (ModGL τ k)} {ω : kˣ}


variable [Finite G]


end Hyper


section OuterCore

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T Timmesfeld.Co1Leaf

set_option linter.unusedSectionVars false


variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]


end OuterCore

section OuterFusion

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T Timmesfeld.Co1Leaf

set_option linter.unusedSectionVars false


variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

theorem exists_model_conj_of_cocycle {y : ModGL Tag.E6 L} (hy : y ∈ adjointGroup Tag.E6 L)
    (a : Fin Tag.E6.rank → Lˣ) (hc : y⁻¹ * twE6TwoF L y ∈ toralRootGroup Tag.E6 L a) :
    ∃ u' ∈ twE6TwoModel L, u' * rootDiagUnit Tag.E6 a * u'⁻¹ =
      y * rootDiagUnit Tag.E6 a * y⁻¹ := by
  obtain ⟨z, hz, hzc⟩ := toralRootGroup_lang_tw a _ hc
  obtain ⟨hzG, hzd⟩ := mem_toralCentralizer.1 (toralRootGroup_le a hz)
  have hFz : twE6TwoF L z = z * (y⁻¹ * twE6TwoF L y) := by rw [← hzc]; group
  have hadj : y * z⁻¹ ∈ adjointGroup Tag.E6 L := mul_mem hy (inv_mem hzG)
  refine ⟨y * z⁻¹, ⟨hadj, ?_⟩, ?_⟩
  · change twE6TwoF L (y * z⁻¹) = y * z⁻¹
    rw [map_mul, map_inv, hFz]
    group
  · have h1 : rootDiagUnit Tag.E6 a * z = z * rootDiagUnit Tag.E6 a := by
      rw [mul_inv_eq_iff_eq_mul] at hzd
      exact hzd
    calc y * z⁻¹ * rootDiagUnit Tag.E6 a * (y * z⁻¹)⁻¹ =
        y * (z⁻¹ * (rootDiagUnit Tag.E6 a * z)) * y⁻¹ := by group
      _ = y * (z⁻¹ * (z * rootDiagUnit Tag.E6 a)) * y⁻¹ := by rw [h1]
      _ = y * rootDiagUnit Tag.E6 a * y⁻¹ := by group

theorem exists_model_conj_dV {ω : Lˣ} {s y : ModGL Tag.E6 L} (hy : y ∈ adjointGroup Tag.E6 L)
    {a : Fin Tag.E6.rank → Lˣ} (hsy : s = y * rootDiagUnit Tag.E6 a * y⁻¹)
    (hc : y⁻¹ * twE6TwoF L y ∈ toralRootGroup Tag.E6 L a) {x : Fin Tag.E6.rank → ZMod 3}
    (hax : a = torV ω x) :
    ∃ m ∈ twE6TwoModel L, m * s * m⁻¹ = dV (τ := Tag.E6) ω x := by
  obtain ⟨u', hu'M, hu'⟩ := exists_model_conj_of_cocycle hy a hc
  have hu'G : u' ∈ adjointGroup Tag.E6 L := hu'M.1
  refine ⟨u'⁻¹, (twE6TwoModel L).inv_mem hu'M, ?_⟩
  have hd : dV (τ := Tag.E6) ω x = rootDiagUnit Tag.E6 a := by rw [hax]; rfl
  rw [hd, hsy, ← hu']
  group

theorem cocycle_mem_toralRootGroup_of_nonInner
    {s y : ModGL Tag.E6 L} (hsM : s ∈ twE6TwoModel L)
    (hy : y ∈ adjointGroup Tag.E6 L) {a : Fin Tag.E6.rank → Lˣ} (ha3 : ∀ i, a i ^ 3 = 1)
    (hsy : s = y * rootDiagUnit Tag.E6 a * y⁻¹) (hnon : rootChar a e6Omega3 ≠ 1) :
    y⁻¹ * twE6TwoF L y ∈ toralRootGroup Tag.E6 L a := by
  set d : ModGL Tag.E6 L := rootDiagUnit Tag.E6 a with hd
  have hd3 : d ^ 3 = 1 := by
    rw [hd, rootDiagUnit_pow]
    have : a ^ 3 = 1 := funext fun j => by simpa using ha3 j
    rw [this, rootDiagUnit_one]
  have hFd : twE6TwoF L d = d := by
    rw [hd, twE6TwoF_rootDiagUnit, ← hd, inv_pow]
    exact inv_eq_of_mul_eq_one_left (by rw [← pow_succ']; exact hd3)
  have hFs : twE6TwoF L (y * d * y⁻¹) = y * d * y⁻¹ := by
    rw [← hsy]
    exact hsM.2
  rw [map_mul, map_mul, map_inv, hFd] at hFs
  set c : ModGL Tag.E6 L := y⁻¹ * twE6TwoF L y with hc
  have hcd : c * d * c⁻¹ = d := by
    calc c * d * c⁻¹ = y⁻¹ * (twE6TwoF L y * d * (twE6TwoF L y)⁻¹) * y := by rw [hc]; group
      _ = y⁻¹ * (y * d * y⁻¹) * y := by rw [hFs]
      _ = d := by group
  have hFy : twE6TwoF L y ∈ adjointGroup Tag.E6 L := by
    have hy' : (y : ModGL TwistTag.E6.tag L) ∈ adjointGroup TwistTag.E6.tag L := hy
    have h3 := mul_mem (mul_mem
      (canonicalRep_mem_adjointGroup (coxeterSystem TwistTag.E6.tag) L twE6W0)
      (twistHom_mem_adjointGroup TwistTag.E6 L (iterateFrobenius L 2 1) hy'))
      (inv_mem (canonicalRep_mem_adjointGroup (coxeterSystem TwistTag.E6.tag) L twE6W0))
    exact h3
  have hcG : c ∈ adjointGroup Tag.E6 L := mul_mem (inv_mem hy) hFy
  have hcC : c ∈ toralCentralizer Tag.E6 L a := by
    refine mem_toralCentralizer.2 ⟨hcG, ?_⟩
    rw [← hd]
    have h1 : c * d = d * c := mul_inv_eq_iff_eq_mul.1 hcd
    calc d * c * d⁻¹ = c * d * d⁻¹ := by rw [← h1]
      _ = c := by group
  have hW : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a := fun w hw =>
    mem_kernelReflectionGroup_of_nonInner a ha3 hnon hw
  rw [← toralCentralizer_eq_toralRootGroup_of_stabilizer_le Tag.E6 L a hW]
  exact hcC


end OuterFusion

end Bal209TwoOuterInAux

section Model

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3


end Model

section Reduction

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in


end Reduction


end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
