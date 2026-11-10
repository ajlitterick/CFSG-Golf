module

public import CFSG.GH74.Generic.S1.SymSystem
public import CFSG.GH74.Generic.S1.SymMain
public import CFSG.GH74.Generic.S1.SymBlocksLin
public import CFSG.GH74.Generic.S1.SymBlocksUni

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic

@[expose] def S1LargeModel {C : Type} [Group C] (K : Subgroup C) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F % 4 = 3 ∧ 3 < Nat.card F ∧
      Nonempty (↥K ≃* ↥(StatedSL 4 F))) ∨
    (∃ (q : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ^ 2 ∧ q % 4 = 1 ∧
      Nonempty (↥K ≃* ↥(StatedSU 4 q F)))

@[expose] def S1LiftCentralProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → ∀ n ∈ liftL x K, proj x n = 1 → ∀ l ∈ liftL x K, n * l = l * n

@[expose] def S1SchurOddProp : Prop :=
  ∀ (K L : Type) [Group K] [Group L] [Finite L], IsSL4Model K → ∀ a : L →* K,
    Function.Surjective a → Group.IsPerfect L → a.ker ≤ Subgroup.center L →
      (∀ k ∈ a.ker, Odd (orderOf k)) → a.ker = ⊥

@[expose] def S1LiftExactProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → LiftExact x K


variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem s1LiftExact_of_central_schur (hC : S1LiftCentralProp) (hS : S1SchurOddProp) :
    S1LiftExactProp := by
  intro G _ _ x K hset hfront
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hset.comp.1.1
  have hLperf : Group.IsPerfect ↥(liftL x K) :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect (K.comap (proj x))
  have hcentral : (piL x K).ker ≤ Subgroup.center ↥(liftL x K) := by
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro g
    have hn1 : proj x (n : ↥(centralizer ({x} : Set G))) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hn)
      exact this
    exact Subtype.ext (hC G x K hset hfront _ n.2 hn1 _ g.2).symm
  have hodd : ∀ k ∈ (piL x K).ker, Odd (orderOf k) := by
    intro k hk
    have hk1 : proj x (k : ↥(centralizer ({x} : Set G))) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
      exact this
    have h1 := proj_odd x _ hk1
    rwa [Subgroup.orderOf_coe] at h1
  have hker := hS ↥K ↥(liftL x K) hset.shape.1 (piL x K) (piL_surjective hKperf) hLperf hcentral hodd
  intro l hl hl1
  have hmem : (⟨l, hl⟩ : ↥(liftL x K)) ∈ (piL x K).ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext hl1
  rw [hker] at hmem
  exact congrArg (fun z : ↥(liftL x K) => ((z : ↥(centralizer ({x} : Set G))))) (Subgroup.mem_bot.1 hmem)

theorem sym_layerData (hExact : S1LiftExactProp) (x : G) (u : Fin 4 → G) {F : Type} [Field F]
    {S : Subgroup (GL (Fin 4) F)}
    (hw : ∀ e j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G))
    (hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u e)))
      (hw' : ∀ j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G)),
        S1Setup G (symX x u e) K' ∧ S1Front G (symX x u e) K' ∧
        ∃ e' : ↥K' ≃* ↥S, ∀ j, ActsAsReflOn e' (barOf (hw' j)) (reflDiag F j)) :
    ∀ e : Fin 5, ∃ D : LayerData (symX x u e) S,
      D.K = layer (CentralizerBar (symX x u e)) ∧
        ∀ j, ActsAsReflOn D.iso (barOf (hw e j)) (reflDiag F j) := by
  intro e
  obtain ⟨K', hw', hset', hfront', iso, hiso⟩ := hloc e
  have hn : K'.Normal := normal_of_layer_eq hfront'.layer_eq
  exact ⟨⟨K', Subgroup.isPerfect_iff.mp hset'.comp.1.1, hn,
    fun P hP => hfront'.good_le P (Or.inl hP), hExact G _ K' hset' hfront', iso⟩,
    hfront'.layer_eq.symm, hiso⟩

omit [Finite G] in
theorem S1LinkedLin.congr {x : G} {K K' : Subgroup (CentralizerBar x)} (h : K' = K) {F : Type}
    [Field F] [Finite F] {J : Fin 4 → Subgroup G} (hJ : S1LinkedLin x K' F J) :
    S1LinkedLin x K F J := h ▸ hJ


omit [Finite G] in
theorem S1LinkedUni.congr {x : G} {K K' : Subgroup (CentralizerBar x)} (h : K' = K) {F : Type}
    [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] {J : Fin 4 → Subgroup G}
    (hJ : S1LinkedUni x K' F p f J) : S1LinkedUni x K F p f J := h ▸ hJ


omit [Finite G] in
theorem sym_model_four {x : G} {K : Subgroup (CentralizerBar x)} [Finite G] (hfront : S1Front G x K)
    {u : Fin 4 → G} {F : Type} [Field F] (hlin : S1SymFrameLin x u F) :
    Nonempty (↥K ≃* ↥(StatedSL 4 F)) := by
  obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := hlin 4
  have h : K' = K := hfront'.layer_eq.symm.trans hfront.layer_eq
  subst h
  exact ⟨e'⟩


end CFSG.GH74.Generic.S1
