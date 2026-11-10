module

public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkSplit
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestGen
public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProof

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTorusNoFix (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
      ∀ a ∈ A, (∀ n : L', GGTorusWeylElt p A n →
        MulAut.conj n * a * (MulAut.conj n)⁻¹ = a) → a = 1

section Transfer

variable {G : Type} [Group G] [Finite G]


theorem ggTBSpan_of_fix_le {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {x : G} (hx : x ^ p = 1)
    {Λ : Type} [Fintype Λ] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (ha : V) (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hfix : ∀ b : Bs, (∀ i, φ i b = b) → (b : G) ∈ Subgroup.zpowers x) :
    Submodule.span (ZMod p) (Set.range (ggOptFam ha h)) = ⊤ := by
  classical
  have hp : p.Prime := Fact.out
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let W : Submodule (ZMod p) (Module.Dual (ZMod p) V) := Submodule.span (ZMod p) (Set.range α)
  have hker : ∀ w ∈ W.dualCoannihilator, ((Additive.toMul (ι.symm w) : Bs) : G) ∈
      Subgroup.zpowers x := by
    intro w hw
    refine hfix _ fun i => ?_
    have hαi : α i w = 0 :=
      (Submodule.mem_dualCoannihilator w).mp hw _ (Submodule.subset_span ⟨i, rfl⟩)
    have h1 := hlin i w
    rw [hαi, zero_smul, sub_zero, ggLin_apply] at h1
    have h2 := congrArg ι.symm h1
    rw [AddEquiv.symm_apply_apply] at h2
    exact Additive.ofMul.injective (by rw [h2]; rfl)
  let e : W.dualCoannihilator → Subgroup.zpowers x := fun w => ⟨_, hker w.1 w.2⟩
  have he : Function.Injective e := by
    intro w w' hww
    have h0 : ((Additive.toMul (ι.symm w.1) : Bs) : G) =
        ((Additive.toMul (ι.symm w'.1) : Bs) : G) :=
      congrArg (fun z : Subgroup.zpowers x => (z : G)) hww
    have h1 : (Additive.toMul (ι.symm w.1) : Bs) = Additive.toMul (ι.symm w'.1) := Subtype.ext h0
    exact Subtype.ext (ι.symm.injective (Additive.toMul.injective h1))
  have hcard : Nat.card W.dualCoannihilator ≤ p := by
    refine (Nat.card_le_card_of_injective e he).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos hx
  have hkerrank : Module.finrank (ZMod p) W.dualCoannihilator ≤ 1 := by
    have h1 := FiniteField.pow_finrank_eq_natCard p W.dualCoannihilator
    have h2 : p ^ Module.finrank (ZMod p) W.dualCoannihilator ≤ p ^ 1 := by
      rw [h1, pow_one]; exact hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h2
  have hW : Module.finrank (ZMod p) W ≤ Fintype.card Λ := finrank_range_le_card (R := ZMod p) α
  have hV : Module.finrank (ZMod p) V ≤ Fintype.card Λ + 1 := by
    rw [← Subspace.finrank_add_finrank_dualCoannihilator_eq W]
    omega
  have hle := hind.fintype_card_le_finrank
  rw [Fintype.card_option] at hle
  exact hind.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_option]; omega)

theorem ggFixed_of_mem_closure {E : Type*} [Group E] {Λ : Type*} (φ : Λ → MulAut E) (b : E)
    (hb : ∀ i, φ i b = b) : ∀ ψ ∈ Subgroup.closure (Set.range φ), ψ b = b := by
  intro ψ hψ
  have hle : Subgroup.closure (Set.range φ) ≤ MulAction.stabilizer (MulAut E) b := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hb i
  exact hle hψ

end Transfer

theorem ggTBSpanInput_of_fix (hFix : GGTBFixInput) : GGTBSpanInput := by
  intro G _ _ p B Bs x L D J hC hO hI hNT y K hN hR hPm _ Λ _ _ M C V _ _ ι φ φa h α ha αa b c hM
    hCM hF hlin hlina hind hL hK
  obtain ⟨-, hBs, hxB, -, -⟩ := hC.tableB_facts
  have hx : x ^ p = 1 := hBs.2 x hxB
  refine ggTBSpan_of_fix_le hx ι φ h α ha hlin hind fun b hb => ?_
  refine hFix G p B Bs x L D J hC hO hI hNT y K hN hR hPm b ?_
  rw [hL]
  exact ggFixed_of_mem_closure φ b hb

theorem ggCoxeterForkLabelInput_of_fix (hFix : GGTBFixInput) (h5 : GGForkCrossGe5Input)
    (hR : GGForkWeylExtRestInput) : GGCoxeterForkLabelInput :=
  ggCoxeterForkLabelInput_of_split (ggTBSpanInput_of_fix hFix) h5 hR

end CFSG.StandardType
