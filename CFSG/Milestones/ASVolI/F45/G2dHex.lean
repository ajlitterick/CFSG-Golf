module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexBase

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin

section CosetAct

@[expose, reducible] def burnsideF45_cosetAct {A : Type} [Group A] (G₀ G₁ G₂ : Subgroup A) :
    MulAction ↥G₀ (CosetGeom G₀ G₁ G₂) := inferInstance

@[expose, reducible] def burnsideF45_cosetSMul {A : Type} [Group A] (G₀ G₁ G₂ : Subgroup A) :
    SMul ↥G₀ (CosetGeom G₀ G₁ G₂) := inferInstance

end CosetAct

section Pred

variable {W : Type} (Γ : SimpleGraph W) (X : Type) [Group X] [MulAction X W]

@[expose] def burnsideF45_FaithfulAt (u : W) : Prop :=
  ∀ w, Γ.dist u w = 6 → ∀ t : X, t • u = u → t • w = w → (∀ a, Γ.Adj u a → t • a = a) → t = 1

@[expose] def burnsideF45_TwoAt (u : W) : Prop :=
  ∀ w, Γ.dist u w = 6 → ∀ a c a' c', Γ.Adj u a → Γ.Adj u c → a ≠ c → Γ.Adj u a' →
    Γ.Adj u c' → a' ≠ c' → ∃ t : X, t • u = u ∧ t • w = w ∧ t • a = a' ∧ t • c = c'

@[expose] def burnsideF45_TransAt (u : W) : Prop :=
  ∀ w w', Γ.dist u w = 6 → Γ.dist u w' = 6 → ∃ t : X, t • u = u ∧ t • w = w'


end Pred

structure burnsideF45_HexModel {W : Type} (Γ : SimpleGraph W) (X : Type) [Group X] [MulAction X W]
    (R : Subgroup X) (x₀ l₀ : W) : Prop where
  edge : IsPGroup 2 ↥(MulAction.stabilizer X x₀ ⊓ MulAction.stabilizer X l₀)
  faithx : burnsideF45_FaithfulAt Γ X x₀
  faithl : burnsideF45_FaithfulAt Γ X l₀
  twox : burnsideF45_TwoAt Γ X x₀
  twol : burnsideF45_TwoAt Γ X l₀
  transx : burnsideF45_TransAt Γ X x₀
  transl : burnsideF45_TransAt Γ X l₀
  signx : ∃ w, Γ.dist x₀ w = 6 ∧ ∃ y : X, y • x₀ = x₀ ∧ y • w = w ∧ y ∉ R
  signl : ∃ w, Γ.dist l₀ w = 6 ∧ ∃ y : X, y • l₀ = l₀ ∧ y • w = w ∧ y ≠ 1 ∧ y * y = 1 ∧ y ∈ R
  outer : ∃ y : X, y • x₀ = x₀ ∧ y • l₀ = l₀ ∧ y ∉ R

section Conj

variable {W : Type} {Γ : SimpleGraph W} {X : Type} [Group X] [MulAction X W] [GraphAction X Γ]


end Conj

section Three

variable {W : Type}

theorem burnsideF45_mem_three {N : Set W} (hN : N.ncard = 3) {p q r : W} (hp : p ∈ N) (hq : q ∈ N)
    (hr : r ∈ N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) {z : W} (hz : z ∈ N) :
    z = p ∨ z = q ∨ z = r := by
  have hfin : N.Finite := Set.finite_of_ncard_ne_zero (by rw [hN]; norm_num)
  have hsub : ({p, q, r} : Set W) ⊆ N := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hr
  have hcard : ({p, q, r} : Set W).ncard = 3 := Set.ncard_eq_three.2 ⟨p, q, r, hpq, hpr, hqr, rfl⟩
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hN, hcard]) hfin
  rw [← heq] at hz
  simpa using hz


end Three

section Card

variable {W : Type} {Γ : SimpleGraph W} {X : Type} [Group X] [MulAction X W] [GraphAction X Γ]


end Card

section Kernel

variable {W : Type} {Γ : SimpleGraph W} {G : Type} [Group G] [MulAction G W] [GraphAction G Γ]

variable (G Γ) in
@[expose] def burnsideF45_g2dKer (u : W) : Subgroup G where
  carrier := {g | g • u = u ∧ ∀ a, Γ.Adj u a → g • a = a}
  one_mem' := ⟨one_smul _ _, fun _ _ => one_smul _ _⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨by rw [mul_smul, hb.1, ha.1], fun w hw => by rw [mul_smul, hb.2 w hw, ha.2 w hw]⟩
  inv_mem' := fun {a} ha =>
    ⟨by rw [inv_smul_eq_iff, ha.1], fun w hw => by rw [inv_smul_eq_iff, ha.2 w hw]⟩

theorem burnsideF45_g2dKer_normalizer (u : W) :
    MulAction.stabilizer G u ≤ Subgroup.normalizer (burnsideF45_g2dKer Γ G u : Set G) := by
  intro h hh
  have hhu : h • u = u := MulAction.mem_stabilizer_iff.mp hh
  have hhu' : h⁻¹ • u = u := by rw [inv_smul_eq_iff, hhu]
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    refine ⟨by rw [mul_smul, mul_smul, hhu', hk.1, hhu], fun a ha => ?_⟩
    have ha' : Γ.Adj u (h⁻¹ • a) := by
      have := (GraphAction.adj_smul h⁻¹ u a).mpr ha
      rwa [hhu'] at this
    rw [mul_smul, mul_smul, hk.2 _ ha', smul_inv_smul]
  · intro hk
    refine ⟨?_, fun a ha => ?_⟩
    · have h1 := hk.1
      rw [mul_smul, mul_smul, hhu'] at h1
      have h2 := congrArg (fun z => h⁻¹ • z) h1
      simp only [inv_smul_smul] at h2
      rw [h2, hhu']
    · have ha' : Γ.Adj u (h • a) := by
        have := (GraphAction.adj_smul h u a).mpr ha
        rwa [hhu] at this
      have h1 := hk.2 _ ha'
      rw [mul_smul, mul_smul, inv_smul_smul] at h1
      have h2 := congrArg (fun z => h⁻¹ • z) h1
      simpa using h2

theorem burnsideF45_g2dKer_le_pCoreOf {p : ℕ} {u a₀ : W} (ha₀ : Γ.Adj u a₀)
    (hp : IsPGroup p ↥(MulAction.stabilizer G u ⊓ MulAction.stabilizer G a₀)) :
    burnsideF45_g2dKer Γ G u ≤ pCoreOf p (MulAction.stabilizer G u) := by
  have hle : burnsideF45_g2dKer Γ G u ≤ MulAction.stabilizer G u := fun g hg =>
    MulAction.mem_stabilizer_iff.mpr hg.1
  have hle' : burnsideF45_g2dKer Γ G u ≤ MulAction.stabilizer G u ⊓ MulAction.stabilizer G a₀ :=
    fun g hg => ⟨MulAction.mem_stabilizer_iff.mpr hg.1, MulAction.mem_stabilizer_iff.mpr (hg.2 a₀ ha₀)⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p hle
    (burnsideF45_g2dKer_normalizer u) (hp.to_le hle')

end Kernel

section HexGeom

variable {W : Type} {Γ : SimpleGraph W}


end HexGeom

section Main

variable {W : Type} {Γ : SimpleGraph W} {G X : Type} [Group G] [Group X] [MulAction G W]
  [MulAction X W] [GraphAction G Γ] [GraphAction X Γ]

structure burnsideF45_G2dHex (Γ : SimpleGraph W) (J : G →* X) (x₀ l₀ : W) : Prop where
  compat : ∀ (g : G) (w : W), J g • w = g • w
  inj : Function.Injective J
  index : J.range.index = 2
  poly : IsGenPolygon Γ 6
  three : ∀ w : W, (Γ.neighborSet w).ncard = 3
  col : ∃ c : W → Bool, (∀ a b, Γ.Adj a b → c a ≠ c b) ∧ (∀ g : G, c (g • x₀) = false) ∧
    ∀ g : G, c (g • l₀) = true
  vert : ∀ w, ∃ g : G, g • x₀ = w ∨ g • l₀ = w
  flag : ∀ u w, Γ.Adj u w → ∃ g : G, (g • x₀ = u ∧ g • l₀ = w) ∨ (g • x₀ = w ∧ g • l₀ = u)
  qfix : ∀ u, ∀ h ∈ pCoreOf 2 (MulAction.stabilizer G u), ∀ a, Γ.Adj u a → h • a = a
  model : burnsideF45_HexModel Γ X J.range x₀ l₀

namespace burnsideF45_G2dHex

variable {J : G →* X} {x₀ l₀ : W} (H : burnsideF45_G2dHex Γ J x₀ l₀)
include H


theorem mem_stab_iff (g : G) (u : W) : g ∈ MulAction.stabilizer G u ↔ J g • u = u := by
  rw [MulAction.mem_stabilizer_iff, H.compat]


theorem edge_G {u a : W} (hua : Γ.Adj u a) :
    IsPGroup 2 ↥(MulAction.stabilizer G u ⊓ MulAction.stabilizer G a) := by
  obtain ⟨g, hg⟩ := H.flag u a hua
  rintro ⟨h, hh⟩
  have hhu : J h • u = u := (H.mem_stab_iff h u).1 hh.1
  have hha : J h • a = a := (H.mem_stab_iff h a).1 hh.2
  have hfix : J h • (J g • x₀) = J g • x₀ ∧ J h • (J g • l₀) = J g • l₀ := by
    rw [H.compat g x₀, H.compat g l₀]
    rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact ⟨hhu, hha⟩
    · rw [h1, h2]; exact ⟨hha, hhu⟩
  have hy : (J g)⁻¹ * J h * J g ∈ MulAction.stabilizer X x₀ ⊓ MulAction.stabilizer X l₀ := by
    refine ⟨MulAction.mem_stabilizer_iff.mpr ?_, MulAction.mem_stabilizer_iff.mpr ?_⟩
    · rw [mul_smul, mul_smul, hfix.1, inv_smul_smul]
    · rw [mul_smul, mul_smul, hfix.2, inv_smul_smul]
  obtain ⟨k, hk⟩ := H.model.edge ⟨_, hy⟩
  refine ⟨k, Subtype.ext ?_⟩
  have hk' : ((J g)⁻¹ * J h * J g) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have e : ((J g)⁻¹ * J h * J g) ^ 2 ^ k = (J g)⁻¹ * (J h) ^ 2 ^ k * J g := by
    have := conj_pow (a := (J g)⁻¹) (b := J h) (i := 2 ^ k)
    simpa using this
  rw [e] at hk'
  have h1 : J (h ^ 2 ^ k) = 1 := by
    rw [map_pow]
    have := congrArg (fun z => J g * z * (J g)⁻¹) hk'
    simpa [mul_assoc] using this
  have h2 := H.inj (h1.trans (map_one J).symm)
  simpa using h2

theorem ker_le {u a₀ : W} (ha₀ : Γ.Adj u a₀) :
    burnsideF45_g2dKer Γ G u ≤ pCoreOf 2 (MulAction.stabilizer G u) :=
  burnsideF45_g2dKer_le_pCoreOf ha₀ (H.edge_G ha₀)


end burnsideF45_G2dHex

end Main

end CFSG.ASVolI
