module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelD

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Open CFSG.Assembly SpCoord

variable {G : Type} [Group G] [Finite G]

noncomputable def hdRo7CLCoordAux_subgroupOfEquiv (Bs X : Subgroup G) :
    ↥((Bs ⊓ X).subgroupOf X) ≃* ↥(Bs ⊓ X) where
  toFun x := ⟨((x : ↥X) : G), Subgroup.mem_subgroupOf.mp x.2⟩
  invFun x := ⟨⟨(x : G), x.2.2⟩, Subgroup.mem_subgroupOf.mpr x.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl

lemma hdRo7CLCoordAux_card_subgroupOf (Bs X : Subgroup G) :
    Nat.card ↥((Bs ⊓ X).subgroupOf X) = Nat.card ↥(Bs ⊓ X) :=
  Nat.card_congr (hdRo7CLCoordAux_subgroupOfEquiv Bs X).toEquiv

@[expose] def hdRo7CLCoordAux_SignedData (p : ℕ) (Bs X : Subgroup G) : Prop :=
  ∃ (k : ℕ) (τ : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ X)),
    Function.Injective τ ∧ Function.Surjective τ ∧
    (∀ i : Fin k, ∃ w : X, ∀ f,
      (w : G) * (τ f : G) * (w : G)⁻¹ = (τ (SpCoord.sgnAut i f) : G)) ∧
    (∀ σ : Equiv.Perm (Fin k), ∃ w : X, ∀ f,
      (w : G) * (τ f : G) * (w : G)⁻¹ = (τ (SpCoord.permAut σ f) : G)) ∧
    ∀ g : X, (∀ e : ↥(Bs ⊓ X), ∃ e' : ↥(Bs ⊓ X),
        (g : G) * (e : G) * (g : G)⁻¹ = (e' : G)) →
      ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p),
        (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', (g : G) * (τ f : G) * (g : G)⁻¹ = (τ f' : G) →
          ∀ i, Multiplicative.toAdd (f' (π i)) = ε i * Multiplicative.toAdd (f i)

lemma hdRo7CLCoordAux_signedData_of_signedEltSC {p : ℕ} {B Bs X : Subgroup G}
    (hBs : GGBstar p B Bs) (hZ : Subgroup.center X = ⊥)
    (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹)
    (hEab : IsElemAbelian p (Bs ⊓ X)) (h3 : p ^ 3 ≤ Nat.card ↥(Bs ⊓ X))
    (h : GGTorusSignedEltSC p ↥X) : hdRo7CLCoordAux_SignedData p Bs X := by
  have hEab' : IsElemAbelian p ((Bs ⊓ X).subgroupOf X) := hEab.subgroupOf X
  have h3' : p ^ 3 ≤ Nat.card ↥((Bs ⊓ X).subgroupOf X) := by
    rw [hdRo7CLCoordAux_card_subgroupOf]; exact h3
  have hsc : ∀ g : ↥X, (∀ e ∈ (Bs ⊓ X).subgroupOf X, g * e = e * g) → g ^ p = 1 →
      g ∈ (Bs ⊓ X).subgroupOf X := by
    intro g hgc hgp
    rw [Subgroup.mem_subgroupOf] at ⊢
    refine Subgroup.mem_inf.mpr ⟨hBs.2.2.2 (g : G) ?_ ?_, g.2⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨e, he, c, hc, rfl⟩ := ggBstar_split_of_inner hBs hZ hnorm hinner b hb
      have hge : (g : G) * (e : G) = (e : G) * (g : G) := by
        have h1 := hgc ⟨(e : G), he.2⟩ (Subgroup.mem_subgroupOf.mpr he)
        simpa only [Subgroup.coe_mul] using congrArg Subtype.val h1
      have hgc' : (g : G) * (c : G) = (c : G) * (g : G) :=
        Subgroup.mem_centralizer_iff.mp hc.2 (g : G) g.2
      have key : (g : G) * ((e : G) * (c : G)) = ((e : G) * (c : G)) * (g : G) := by
        calc (g : G) * ((e : G) * (c : G)) = ((g : G) * e) * c := by group
          _ = ((e : G) * g) * c := by rw [hge]
          _ = (e : G) * ((g : G) * c) := by group
          _ = (e : G) * ((c : G) * (g : G)) := by rw [hgc']
          _ = ((e : G) * (c : G)) * (g : G) := by group
      exact key.symm
    · simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val hgp
  obtain ⟨k, τ, hτinj, hτrange, hsgn, hperm, hnorm⟩ :=
    h ((Bs ⊓ X).subgroupOf X) hEab' h3' hsc
  let eτ : (Fin k → Multiplicative (ZMod p)) ≃* ↥(Bs ⊓ X) :=
    (MonoidHom.ofInjective hτinj).trans
      ((MulEquiv.subgroupCongr hτrange).trans (hdRo7CLCoordAux_subgroupOfEquiv Bs X))
  have hcoe : ∀ f, (eτ.toMonoidHom f : G) = (τ f : G) := fun f => rfl
  refine ⟨k, eτ.toMonoidHom, eτ.injective, eτ.surjective, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨w, hw⟩ := hsgn i
    refine ⟨w, fun f => ?_⟩
    rw [hcoe f, hcoe (SpCoord.sgnAut i f)]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val (hw f)
  · intro σ
    obtain ⟨w, hw⟩ := hperm σ
    refine ⟨w, fun f => ?_⟩
    rw [hcoe f, hcoe (SpCoord.permAut σ f)]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val (hw f)
  · intro g hg
    have hg' : ∀ e ∈ (Bs ⊓ X).subgroupOf X, g * e * g⁻¹ ∈ (Bs ⊓ X).subgroupOf X := by
      intro e he
      rw [Subgroup.mem_subgroupOf] at he
      obtain ⟨e', he'⟩ := hg ⟨(e : G), he⟩
      rw [Subgroup.mem_subgroupOf]
      have h1 : ((g * e * g⁻¹ : ↥X) : G) = (e' : G) := by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using he'
      rw [h1]
      exact e'.2
    obtain ⟨π, ε, hε, hrel⟩ := hnorm g hg'
    refine ⟨π, ε, hε, fun f f' hff' => hrel f f' ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe f, hcoe f'] at hff'
    exact hff'

theorem hdRo7CLCoordAux_card_inf_ge (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G) (hH : GGResHyp p B Bs x L D J y K)
    (hZL : Subgroup.center ↥L = ⊥) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ L, ∀ y ∈ L, b * y * b⁻¹ = x * y * x⁻¹) :
    p ^ 3 ≤ Nat.card ↥(Bs ⊓ L) := by
  have hp : Nat.Prime p := hH.1.tableB_facts.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hsplit := card_ggBstar_split hH.1.2.1 hZL hBsN hinner
  have hCeq : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    hdRo7CLCoordAux_bstar_centralizer_eq hH
  have hCcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = p := by
    rw [hCeq, Nat.card_zpowers,
      orderOf_eq_prime (hdRo7CLCoordAux_x_pow_eq_one hH) (hdRo7CLCoordAux_x_ne_one hH)]
  have h4 : p ^ 4 ≤ Nat.card ↥Bs := hdRo7CLCoordAux_card_bstar_ge hH
  have hle : p ^ 3 * p ≤ Nat.card ↥(Bs ⊓ L) * p := by
    calc p ^ 3 * p = p ^ 4 := by ring
      _ ≤ Nat.card ↥Bs := h4
      _ = Nat.card ↥(Bs ⊓ L) *
            Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := hsplit
      _ = Nat.card ↥(Bs ⊓ L) * p := by rw [hCcard]
  exact Nat.le_of_mul_le_mul_right hle hp.pos

theorem hdRo7CLCoordAux_signedData_L (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G) (hH : GGResHyp p B Bs x L D J y K)
    (R : Type) [Group R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (hZL : Subgroup.center ↥L = ⊥)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ L, ∀ y ∈ L, b * y * b⁻¹ = x * y * x⁻¹)
    (hTSC : GGTorusSignedEltSC p R) :
    hdRo7CLCoordAux_SignedData p Bs L := by
  have hBs : GGBstar p B Bs := hH.1.2.1
  have hEab : IsElemAbelian p (Bs ⊓ L) := hdRo7CLCoordAux_inf_ab hH
  have h3 : p ^ 3 ≤ Nat.card ↥(Bs ⊓ L) :=
    hdRo7CLCoordAux_card_inf_ge p B Bs x L D J y K hH hZL hBsN hinner
  let e₁ : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZL).trans QuotientGroup.quotientBot
  have hTSC_L : GGTorusSignedEltSC p ↥L :=
    ggTorusSignedEltSC_of_mulEquiv (e₁.symm.trans θ) hTSC
  exact hdRo7CLCoordAux_signedData_of_signedEltSC hBs hZL hBsN hinner hEab h3 hTSC_L


end CFSG.StandardType.HdRo7C

end
