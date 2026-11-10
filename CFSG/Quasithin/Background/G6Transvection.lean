module

public import CFSG.Quasithin.Background.G6Swap
public import CFSG.Quasithin.Background.G6SQTK
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

namespace G6

universe u

variable {V : Type u} [CommGroup V]

@[expose] def IsG64Type (Ki : Subgroup (MulAut V)) (Vi : Subgroup V) : Prop :=
  (∃ n, 2 ≤ n ∧ n ≤ 5 ∧ IsLnNatural Ki Vi n) ∨
  (∃ n, 5 ≤ n ∧ n ≤ 8 ∧ IsSymNatural Ki Vi n) ∨
  (∃ n, (n = 6 ∨ n = 8) ∧ IsSymCore Ki Vi n)

@[expose] def IsSmallG64Type (Ki : Subgroup (MulAut V)) : Prop :=
  Nonempty (Ki ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) ∨
  Nonempty (Ki ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) ∨
  Nonempty (Ki ≃* Equiv.Perm (Fin 5))

structure IsTransvectionDecomposition (K : Subgroup (MulAut V)) {s : ℕ}
    (Ks : Fin s → Subgroup (MulAut V)) : Prop where
  pos : 0 < s
  le_two : s ≤ 2
  iSup_eq : ⨆ i, Ks i = K
  indep : iSupIndep Ks
  centralize : ∀ i j, i ≠ j → Ks i ≤ Subgroup.centralizer (Ks j : Set (MulAut V))
  iSup_commV : ⨆ i, commV (Ks i) = ⊤
  commV_indep : iSupIndep fun i => commV (Ks i)
  commOn_eq_bot : ∀ i j, i ≠ j → commOn (Ks i) (commV (Ks j)) = ⊥
  isHSubmodule : ∀ i, IsHSubmodule (Ks i) (commV (Ks i))
  type : ∀ i, IsG64Type (Ks i) (commV (Ks i))
  small : s = 2 → ∀ i, IsSmallG64Type (Ks i)

def QuotedTransvectionClassification : Prop :=
  ∀ (V : Type u) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (K : Subgroup (MulAut V)) (D : Set (MulAut V)),
      pCoreOf 2 K = ⊥ → IsQuotientOfSQTK K →
      (∀ d ∈ D, d ∈ K ∧ d ≠ 1 ∧ Nat.card (commV (Subgroup.zpowers d)) = 2 ∧
        ∀ k ∈ K, k * d * k⁻¹ ∈ D) →
      Subgroup.closure D = K → commV K = ⊤ →
      ∃ (s : ℕ) (Ks : Fin s → Subgroup (MulAut V)), IsTransvectionDecomposition K Ks


theorem commV_zpowers_conj (g a : MulAut V) :
    commV (Subgroup.zpowers (g * a * g⁻¹)) = (commV (Subgroup.zpowers a)).map g.toMonoidHom :=
  CFSG.Quasithin.commV_zpowers_conj_eq a g

theorem card_commV_zpowers_conj (g a : MulAut V) :
    Nat.card (commV (Subgroup.zpowers (g * a * g⁻¹))) = Nat.card (commV (Subgroup.zpowers a)) := by
  rw [commV_zpowers_conj]
  exact Subgroup.card_map_of_injective g.injective

theorem iSup_fin_two {α : Type*} [CompleteLattice α] (f : Fin 2 → α) : ⨆ i, f i = f 0 ⊔ f 1 :=
  le_antisymm (iSup_le fun i => by fin_cases i <;> simp) (sup_le (le_iSup f 0) (le_iSup f 1))

theorem mem_sup_of_centralizes {G : Type*} [Group G] {H K : Subgroup G}
    (h : H ≤ Subgroup.centralizer (K : Set G)) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ a ∈ H, ∃ b ∈ K, a * b = x := by
  have hn : H ≤ Subgroup.normalizer (K : Set G) :=
    h.trans (Subgroup.centralizer_le_normalizer _)
  have := Subgroup.coe_mul_of_left_le_normalizer_right H K hn
  have hx' : x ∈ ((H ⊔ K : Subgroup G) : Set G) := hx
  rw [this] at hx'
  exact hx'

namespace IsTransvectionDecomposition

variable {K : Subgroup (MulAut V)} {s : ℕ} {Ks : Fin s → Subgroup (MulAut V)}

theorem comp (h : IsTransvectionDecomposition K Ks) (e : Fin s ≃ Fin s) :
    IsTransvectionDecomposition K (Ks ∘ e) where
  pos := h.pos
  le_two := h.le_two
  iSup_eq := by
    rw [← h.iSup_eq]
    exact e.iSup_comp (g := Ks)
  indep := h.indep.comp e.injective
  centralize := fun i j hij => h.centralize (e i) (e j) (e.injective.ne hij)
  iSup_commV := by
    rw [← h.iSup_commV]
    exact e.iSup_comp (g := fun i => commV (Ks i))
  commV_indep := h.commV_indep.comp e.injective
  commOn_eq_bot := fun i j hij => h.commOn_eq_bot (e i) (e j) (e.injective.ne hij)
  isHSubmodule := fun i => h.isHSubmodule (e i)
  type := fun i => h.type (e i)
  small := fun hs i => h.small hs (e i)

theorem apply_eq_of_ne (h : IsTransvectionDecomposition K Ks) {i j : Fin s} (hij : i ≠ j)
    {k : MulAut V} (hk : k ∈ Ks i) {v : V} (hv : v ∈ commV (Ks j)) : k v = v := by
  have := mem_commOn_of_mem hk hv
  rw [h.commOn_eq_bot i j hij, Subgroup.mem_bot, mul_inv_eq_one] at this
  exact this


end IsTransvectionDecomposition

section Apply

variable {X : Subgroup (MulAut V)} {a : MulAut V}

theorem closure_conj_set_eq (X : Subgroup (MulAut V)) (a : MulAut V) :
    Subgroup.closure {d | ∃ g ∈ X, d = g * a * g⁻¹} = classClosure X a := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro d ⟨g, hg, rfl⟩
    exact conj_mem_classClosure hg
  · unfold classClosure
    refine conjClosure_le fun g hg z hz => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [show g * a ^ k * g⁻¹ = (g * a * g⁻¹) ^ k from conj_zpow.symm]
    have hmem : g * a * g⁻¹ ∈ Subgroup.closure {d | ∃ g ∈ X, d = g * a * g⁻¹} :=
      Subgroup.subset_closure ⟨g, hg, rfl⟩
    exact Subgroup.zpow_mem _ hmem k

theorem pCoreOf_classClosure_eq_bot [Finite V] (h : Hypothesis61 X a) :
    pCoreOf 2 (classClosure X a) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := classClosure X a with hK
  have hnormK : X ≤ Subgroup.normalizer (K : Set (MulAut V)) :=
    le_normalizer_conjClosure (Subgroup.zpowers a) X
  have hNK : pCoreOf 2 K ≤ K := pCoreOf_le 2 K
  have hNX : pCoreOf 2 K ≤ X := hNK.trans (classClosure_le h.mem)
  have hnormN : X ≤ Subgroup.normalizer (pCoreOf 2 K : Set (MulAut V)) := fun g hg =>
    normalizer_le_normalizer_pCoreOf 2 K (hnormK hg)
  have := le_pCoreOf_of_le_normalizer 2 hNX hnormN (pCoreOf_isPGroup 2 K)
  rw [h.pCoreOf_eq_bot] at this
  exact le_bot_iff.1 this

theorem exists_decomposition [Finite V] (Q1 : QuotedTransvectionClassification.{u})
    (h : Hypothesis61 X a) (htr : Nat.card (commV (Subgroup.zpowers a)) = 2) :
    ∃ (s : ℕ) (Ks : Fin s → Subgroup (MulAut V)),
      IsTransvectionDecomposition (classClosure X a) Ks := by
  refine Q1 V h.sq_eq_one (classClosure X a) {d | ∃ g ∈ X, d = g * a * g⁻¹}
    (pCoreOf_classClosure_eq_bot h)
    (IsQuotientOfSQTK.of_le (classClosure_le h.mem) h.isQuotientOfSQTK) ?_
    (closure_conj_set_eq X a) (lemma_G62_1 h)
  rintro d ⟨g, hg, rfl⟩
  refine ⟨conj_mem_classClosure hg, ?_, ?_, ?_⟩
  · intro h1
    apply h.ne_one
    have : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [this, h1]
    group
  · rw [card_commV_zpowers_conj]
    exact htr
  · intro k hk
    have hkX : k ∈ X := classClosure_le h.mem hk
    refine ⟨k * g, X.mul_mem hkX hg, ?_⟩
    group

private theorem not_subsingleton_perm (n : ℕ) (hn : 2 ≤ n) :
    ¬ Subsingleton (Equiv.Perm (Fin n)) := by
  intro hs
  have h : Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ = 1 := Subsingleton.elim _ _
  have h2 := congrArg (fun f : Equiv.Perm (Fin n) => f ⟨0, by omega⟩) h
  simp at h2

theorem IsTransvectionDecomposition.ne_bot {K : Subgroup (MulAut V)} {s : ℕ}
    {Ks : Fin s → Subgroup (MulAut V)} (hd : IsTransvectionDecomposition K Ks) (i : Fin s) :
    Ks i ≠ ⊥ := by
  intro hbot
  have hcomm : commV (Ks i) = ⊥ := by
    rw [hbot, eq_bot_iff, commV_le_iff]
    intro x hx v
    rw [Subgroup.mem_bot] at hx
    subst hx
    simp
  have hsub : Subsingleton (Ks i) := by rw [hbot]; infer_instance
  rcases hd.type i with ⟨n, hn2, _, hL⟩ | ⟨n, hn5, _, ⟨θ, β, _, _, _⟩⟩ | ⟨n, hn, ⟨θ, β, _, _, _⟩⟩
  · have := hL.2.1
    rw [hcomm, Subgroup.card_bot] at this
    have : 2 ^ n ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  · have : Subsingleton (Equiv.Perm (Fin n)) := θ.surjective.subsingleton
    exact not_subsingleton_perm n (by omega) this
  · have : Subsingleton (Equiv.Perm (Fin n)) := θ.surjective.subsingleton
    exact not_subsingleton_perm n (by omega) this


structure G64Decomposition (X : Subgroup (MulAut V)) (a : MulAut V) {s : ℕ}
    (Ks : Fin s → Subgroup (MulAut V)) : Prop where
  decomp : IsTransvectionDecomposition (classClosure X a) Ks
  mem_first : ∃ hs : 0 < s, a ∈ Ks ⟨0, hs⟩
  permute : ∀ g ∈ X, ∀ i, ∃ j, conjSubgroup (Ks i) g = Ks j
  transitive : ∀ i j, ∃ g ∈ X, conjSubgroup (Ks i) g = Ks j


theorem conjSubgroup_inj {G : Type*} [Group G] {A B : Subgroup G} {g : G}
    (h : conjSubgroup A g = conjSubgroup B g) : A = B := by
  have := congrArg (fun C => conjSubgroup C g⁻¹) h
  simpa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] using this

theorem eq_of_mul_eq_mul_of_disjoint {G : Type*} [Group G] {A B : Subgroup G}
    (hdis : Disjoint A B) {a a' b b' : G} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B)
    (hb' : b' ∈ B) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, h]
  have hA : a'⁻¹ * a ∈ A := A.mul_mem (A.inv_mem ha') ha
  have hB : a'⁻¹ * a ∈ B := h1 ▸ B.mul_mem hb' (B.inv_mem hb)
  have h2 : a'⁻¹ * a = 1 := by
    have := hdis.le_bot ⟨hA, hB⟩
    simpa using this
  have h3 : a = a' := by
    rw [inv_mul_eq_one] at h2
    exact h2.symm
  refine ⟨h3, ?_⟩
  rw [h3] at h
  exact mul_left_cancel h


theorem IsTransvectionDecomposition.le_normalizer {K : Subgroup (MulAut V)} {s : ℕ}
    {Ks : Fin s → Subgroup (MulAut V)} (hd : IsTransvectionDecomposition K Ks) (i : Fin s) :
    K ≤ Subgroup.normalizer (Ks i : Set (MulAut V)) := by
  rw [← hd.iSup_eq]
  refine iSup_le fun j => ?_
  by_cases hij : j = i
  · subst hij
    exact Subgroup.le_normalizer
  · exact (hd.centralize j i hij).trans (Subgroup.centralizer_le_normalizer _)


end Apply

end G6

end CFSG.Quasithin
