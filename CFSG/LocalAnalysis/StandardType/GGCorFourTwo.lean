module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoBridge
public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Automizer

variable {G : Type} [Group G]

theorem mem_ggInduced_iff {H Bs : Subgroup G} {φ : MulAut ↥Bs} :
    φ ∈ ggInduced H Bs ↔ ∃ g : Subgroup.normalizer (Bs : Set G), (g : G) ∈ H ∧
      Bs.normalizerMonoidHom g = φ := by
  constructor
  · rintro ⟨g, hgH, hgN, hφ⟩
    exact ⟨⟨g, hgN⟩, hgH, MulEquiv.ext fun b => Subtype.ext (hφ b).symm⟩
  · rintro ⟨⟨g, hgN⟩, hgH, rfl⟩
    exact ⟨g, hgH, hgN, fun b => rfl⟩

theorem mem_ggInduced_top_iff {Bs : Subgroup G} {φ : MulAut ↥Bs} :
    φ ∈ ggInduced ⊤ Bs ↔ φ ∈ Bs.normalizerMonoidHom.range := by
  rw [mem_ggInduced_iff]
  exact ⟨fun ⟨g, _, hg⟩ => ⟨g, hg⟩, fun ⟨g, hg⟩ => ⟨g, Subgroup.mem_top _, hg⟩⟩

theorem noNormalP_of_ggOpAutTrivial {p : ℕ} {Bs : Subgroup G} (hO : GGOpAutTrivial p Bs) :
    ∀ N : Subgroup (MulAut ↥Bs), N ≤ Bs.normalizerMonoidHom.range →
      (∀ a ∈ Bs.normalizerMonoidHom.range, ∀ n ∈ N, a * n * a⁻¹ ∈ N) → IsPGroup p N →
        N = ⊥ := by
  intro N hNr hNn hNp
  set κ := Bs.normalizerMonoidHom with hκ
  set X : Subgroup G := (N.comap κ).map (Subgroup.normalizer (Bs : Set G)).subtype with hX
  have hmemX : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (Bs : Set G)),
      g ∈ X ↔ κ ⟨g, hg⟩ ∈ N := by
    intro g hg
    constructor
    · rintro ⟨m, hm, hmg⟩
      have : m = ⟨g, hg⟩ := Subtype.ext hmg
      rw [← this]
      exact hm
    · intro h
      exact ⟨⟨g, hg⟩, h, rfl⟩
  have hXN : X ≤ Subgroup.normalizer (Bs : Set G) := Subgroup.map_subtype_le _
  have hCX : Subgroup.centralizer (Bs : Set G) ≤ X := by
    intro g hg
    have hgN : g ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.centralizer_le_normalizer _ hg
    rw [hmemX g hgN]
    have h1 : κ ⟨g, hgN⟩ = 1 := by
      ext b
      show g * b * g⁻¹ = b
      rw [← (Subgroup.mem_centralizer_iff.mp hg) b b.2, mul_inv_cancel_right]
    rw [h1]
    exact N.one_mem
  have hXn : (X.subgroupOf (Subgroup.normalizer (Bs : Set G))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [hmemX _ n.2] at hn
    rw [hmemX _ (g * n * g⁻¹).2]
    have : κ (g * n * g⁻¹) = κ g * κ n * (κ g)⁻¹ := by rw [map_mul, map_mul, map_inv]
    rw [show (⟨((g * n * g⁻¹ : Subgroup.normalizer (Bs : Set G)) : G), (g * n * g⁻¹).2⟩ :
        Subgroup.normalizer (Bs : Set G)) = g * n * g⁻¹ from rfl, this]
    exact hNn _ ⟨g, rfl⟩ _ hn
  have hXp : ∀ g ∈ X, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G) := by
    rintro g ⟨m, hm, rfl⟩
    obtain ⟨k, hk⟩ := hNp ⟨κ m, hm⟩
    refine ⟨k, ?_⟩
    have h1 : κ (m ^ p ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have h2 : m ^ p ^ k ∈ κ.ker := h1
    rw [hκ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h2
    simpa using h2
  have hXC := hO X hXN hCX hXn hXp
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨m, rfl⟩ := hNr hn
  have hm : (m : G) ∈ X := (hmemX m m.2).mpr hn
  have h2 : m ∈ κ.ker := by
    rw [hκ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    exact hXC hm
  rw [MonoidHom.mem_ker] at h2
  rw [h2]
  exact Subgroup.one_mem _

end Automizer


section NoTransvection

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_zpowers_mk_of_coe_mem {Bs : Subgroup G} {x : G} (hx : x ∈ Bs) {b : ↥Bs}
    (hb : (b : G) ∈ Subgroup.zpowers x) : b ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩


end NoTransvection

@[expose] def GGMarkingAll {K : Type*} [Group K] (Q : LargeEvenMarkProp K) : Prop :=
  ∀ P : LargeEvenMarkProp K, LargeEvenMarking K P →
    LargeEvenMarking K fun lab R _ I F θ => P lab R I F θ ∧ Q lab R I F θ

@[expose] def GGBstarNbrNormalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      Bs ≤ Subgroup.normalizer (K : Set G)

@[expose] def GGNbrGraphInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
        GGMarkingAll (K := ↥K) fun _ _ _ I F θ => ∀ (b : G) (hb : b ∈ Bs),
          ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, ggLAut K θ ⟨b, hN hb⟩ = u * f

@[expose] def GGNbrFieldTransvectionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
        GGMarkingAll (K := ↥K) fun _ _ _ I F θ =>
          (∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
            ggLAut K θ ⟨b, hN hb⟩ = u * f) →
          (∃ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∉ I) →
            ∃ φ ∈ ggInduced ⊤ Bs, GGIsTransvection p φ

section Induces

variable {G : Type} [Group G] (K : Subgroup G) {R : Type} [Group R]
  (θ : K ⧸ Subgroup.center K ≃* R)

theorem largeEvenInduces_ggLAut_inv {b : G} (hb : b⁻¹ ∈ Subgroup.normalizer (K : Set G)) :
    LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) (ggLAut K θ ⟨b⁻¹, hb⟩) := by
  intro l l' hll'
  rw [ggLAut_apply]
  congr 2
  apply Subtype.ext
  rw [normalizerMonoidHom_coe, hll', inv_inv]

end Induces


end CFSG.StandardType
