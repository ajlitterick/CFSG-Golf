module

public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeNbr
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwo

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGRawFieldCentral : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∀ α : MulAut R, ∀ u ∈ I, ∀ f ∈ Subgroup.closure F, α * (u * f) * α⁻¹ * (u * f)⁻¹ ∈ I

@[expose] def GGRawFieldCentralInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → LargeEvenLabelAll lab GGRawFieldCentral

@[expose] def GGRawFieldConj (p : ℕ) : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∀ u ∈ I, ∀ f ∈ Subgroup.closure F, u * f ∉ I → (u * f) ^ p = 1 →
      ∃ f' ∈ F, ∃ u' ∈ I, orderOf f' = p ∧ u * f = u' * f' * u'⁻¹

@[expose] def GGRawFieldConjInput : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (GGRawFieldConj p)

@[expose] def GGL44iiiNotInnerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G),
    GGFieldCaseNoBL5 p B Bs x L D J X → GGTableBModule p Bs x L B₂ → GGL43 Bs x X →
      GGL44i p Bs x X → GGL44ii Bs x X B₂ →
      ∀ d ∈ D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)), d ≠ 1 →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        Subgroup.zpowers y = Subgroup.zpowers d →
        ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
          GGMarkingAll (K := ↥K) fun _ _ _ I F θ =>
            (∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
              ggLAut K θ ⟨b, hN hb⟩ = u * f) →
            ∃ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∉ I

@[expose] def GGL44iiiMcLaughlinInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G),
    GGFieldCaseNoBL5 p B Bs x L D J X → GGTableBModule p Bs x L B₂ → GGL43 Bs x X →
      GGL44i p Bs x X → B₂ < Bs →
      (∀ b : G, b ∈ Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ B₂ ↔
        ∃ g ∈ X, g * x * g⁻¹ * x⁻¹ = b) →
      ∀ d ∈ D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)), d ≠ 1 →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        Subgroup.zpowers y = Subgroup.zpowers d →
        ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
          GGMarkingAll (K := ↥K) fun _ _ _ I F θ =>
            (∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
              ggLAut K θ ⟨b, hN hb⟩ = u * f) →
            (∀ (b : G) (hb : b ∈ Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ B₂),
              ggLAut K θ ⟨b, hN hb.1.1⟩ ∈ I) →
            (∃ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∉ I) →
            ∀ (b : G) (hb : b ∈ Bs ⊓ Subgroup.centralizer (X : Set G)),
              ggLAut K θ ⟨b, hN hb.1⟩ ∈ I

section Proofs

variable {G : Type} [Group G]

theorem largeEvenMarking_mono_of_simple {X : Type*} [Group X] {P P' : LargeEvenMarkProp X}
    (hPP' : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : X ⧸ Subgroup.center X ≃* R), IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
        P lab R I F θ → P' lab R I F θ)
    (h : LargeEvenMarking X P) : LargeEvenMarking X P' := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, θ, hPP' lab R I F θ hs hna hθ⟩

theorem ggLAut_comm_mem {K : Subgroup G} {R : Type} [Group R] {I F : Set (MulAut R)}
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    (hcen : ∀ α : MulAut R, ∀ u ∈ I, ∀ f ∈ Subgroup.closure F,
      α * (u * f) * α⁻¹ * (u * f)⁻¹ ∈ I)
    {g x : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hx : x ∈ Subgroup.normalizer (K : Set G))
    (hxF : ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, ggLAut K θ ⟨x, hx⟩ = u * f)
    (h : g * x * g⁻¹ * x⁻¹ ∈ Subgroup.normalizer (K : Set G)) :
    ggLAut K θ ⟨g * x * g⁻¹ * x⁻¹, h⟩ ∈ I := by
  have e : (⟨g * x * g⁻¹ * x⁻¹, h⟩ : Subgroup.normalizer (K : Set G)) =
      ⟨g, hg⟩ * ⟨x, hx⟩ * (⟨g, hg⟩ : Subgroup.normalizer (K : Set G))⁻¹ *
        (⟨x, hx⟩ : Subgroup.normalizer (K : Set G))⁻¹ := Subtype.ext rfl
  obtain ⟨u, hu, f, hf, huf⟩ := hxF
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, huf]
  exact hcen _ u hu f hf

theorem ggL44iiiInner_of_first {Bs X K : Subgroup G} {x : G} {R : Type} [Group R]
    {I F : Set (MulAut R)} (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hXK : X ≤ Subgroup.normalizer (K : Set G))
    (hxBs : x ∈ Bs)
    (hcen : ∀ α : MulAut R, ∀ u ∈ I, ∀ f ∈ Subgroup.closure F,
      α * (u * f) * α⁻¹ * (u * f)⁻¹ ∈ I)
    (hgr : ∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
      ggLAut K θ ⟨b, hN hb⟩ = u * f)
    {S : Subgroup G} (hSBs : S ≤ Bs) (hS : ∀ b ∈ S, ∃ g ∈ X, g * x * g⁻¹ * x⁻¹ = b) :
    ∀ (b : G) (hb : b ∈ S), ggLAut K θ ⟨b, hN (hSBs hb)⟩ ∈ I := by
  intro b hb
  obtain ⟨g, hg, rfl⟩ := hS b hb
  exact ggLAut_comm_mem θ hcen (hXK hg) (hN hxBs) (hgr x hxBs) (hN (hSBs hb))

variable [Finite G]

theorem ggL44iiiMarking_core {p : ℕ} {Bs X K : Subgroup G} {x : G} {R : Type} [Group R]
    {I F : Set (MulAut R)} (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hxBs : x ∈ Bs) (hxp : x ^ p = 1)
    (hsplit : Bs = (Bs ⊓ Subgroup.centralizer (X : Set G)) ⊔ Subgroup.zpowers x)
    (hxc : ∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G), x * b = b * x)
    (hmul : ∀ φ ∈ I, ∀ ψ ∈ I, φ * ψ ∈ I) (hinv : ∀ φ ∈ I, φ⁻¹ ∈ I)
    (hone : (1 : MulAut R) ∈ I)
    (hlang : ∀ u ∈ I, ∀ f ∈ Subgroup.closure F, u * f ∉ I → (u * f) ^ p = 1 →
      ∃ f' ∈ F, ∃ u' ∈ I, orderOf f' = p ∧ u * f = u' * f' * u'⁻¹)
    (hgr : ∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
      ggLAut K θ ⟨b, hN hb⟩ = u * f)
    (hB₁ : ∀ (b : G) (hb : b ∈ Bs ⊓ Subgroup.centralizer (X : Set G)),
      ggLAut K θ ⟨b, hN hb.1⟩ ∈ I)
    (hS1 : ∃ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∉ I) :
    (∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G), ∃ φ ∈ I,
        LargeEvenInduces θ (fun k k' => (k' : G) = b⁻¹ * k * b) φ) ∧
      ∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧
        LargeEvenInduces θ (fun k k' => (k' : G) = x⁻¹ * k * x) (u * f * u⁻¹) := by
  set B₁ := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  have hpow : ∀ φ ∈ I, ∀ n : ℕ, φ ^ n ∈ I := by
    intro φ hφ n
    induction n with
    | zero => rw [pow_zero]; exact hone
    | succ n ih => rw [pow_succ]; exact hmul _ ih _ hφ
  refine ⟨fun b hb => ⟨ggLAut K θ ⟨b⁻¹, hN (Bs.inv_mem hb.1)⟩, hB₁ b⁻¹ (B₁.inv_mem hb),
    largeEvenInduces_ggLAut_inv K θ (hN (Bs.inv_mem hb.1))⟩, ?_⟩
  have hx' : x⁻¹ ∈ Subgroup.normalizer (K : Set G) := hN (Bs.inv_mem hxBs)
  obtain ⟨u, hu, f, hf, huf⟩ := hgr x⁻¹ (Bs.inv_mem hxBs)
  have hnot : u * f ∉ I := by
    rw [← huf]
    intro hxI
    obtain ⟨b, hb, hbI⟩ := hS1
    have hb' : b ∈ B₁ ⊔ Subgroup.zpowers x := by
      rw [← hsplit]
      exact hb
    obtain ⟨b₁, hb₁, j, rfl⟩ := exists_mem_mul_pow_of_mem_sup hxc hb'
    apply hbI
    have e : (⟨b₁ * x ^ j, hN hb⟩ : Subgroup.normalizer (K : Set G)) =
        ⟨b₁, hN hb₁.1⟩ * ((⟨x⁻¹, hx'⟩ : Subgroup.normalizer (K : Set G))⁻¹) ^ j := by
      ext
      simp
    rw [e, map_mul, map_pow, map_inv]
    exact hmul _ (hB₁ b₁ hb₁) _ (hpow _ (hinv _ hxI) j)
  have hord : (u * f) ^ p = 1 := by
    rw [← huf, ← map_pow]
    have e : (⟨x⁻¹, hx'⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 := by
      ext
      simp [inv_pow, hxp]
    rw [e, map_one]
  obtain ⟨f', hf', u', hu', hf'p, he⟩ := hlang u hu f hf hnot hord
  refine ⟨f', hf', u', hu', hf'p, ?_⟩
  rw [← he, ← huf]
  exact largeEvenInduces_ggLAut_inv K θ hx'

end Proofs


end CFSG.StandardType

end
