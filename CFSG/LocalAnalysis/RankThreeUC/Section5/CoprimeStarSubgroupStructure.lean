module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.SstarQuotientFaithful.SstarQuotientFaithful
public import CFSG.LocalAnalysis.RankThreeUC.Section5.MaxInvariantOdd
public import CFSG.LocalAnalysis.RankThreeUC.Section5.NontrivialActor
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.CoprimeStarSubgroupStructure

open CFSG.LocalAnalysis.RankThreeUC.Section5

variable {G : Type} [Group G] [Finite G]

private theorem normalizer_eq_top {p : ℕ} {P T B : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h53 : FaithfulBinaryIrreducibleAction G p P T B ρ) :
    Subgroup.normalizer (P : Set G) = ⊤ :=
  Subgroup.normalizer_eq_top_iff.mpr h53.normal

theorem Xs_generated {p : ℕ} {P T B : Subgroup G} {e : ℕ} (h51 : OddPrimeClassTwoAction G p P T B e) :
    ⁅twoCoreCommutator T B, B⁆ = twoCoreCommutator T B := by
  set K := CFSG.Open.pCoreOf 2 (B ⊔ T) with hK
  have hKle : ⁅K, B⁆ ≤ K := SstarQuotientFaithful.Xs_le_pCoreOf T B le_sup_left
  have hBK : B ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hKle
  have hK2 : IsPGroup 2 K := (CFSG.LieType.BorelTits.pCore_isPGroup 2).map (B ⊔ T).subtype
  obtain ⟨n, hn⟩ := hK2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card B) (Nat.card K) := by
    rw [hn]
    refine Nat.Coprime.pow_right _ ?_
    exact Nat.coprime_two_right.mpr h51.setting.oddOrder
  apply le_antisymm
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (Subgroup.normalizer_commutator_ge_right K B)
  · exact le_of_eq (CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime K B hcop hBK).symm


private theorem ne_bot {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h51 : OddPrimeClassTwoAction G p P T B e) (h53 : FaithfulBinaryIrreducibleAction G p P T B ρ) :
    Sstar P T B ≠ ⊥ := by
  intro hbot
  have hN := normalizer_eq_top h53
  have h3 : ⁅P, ⁅CFSG.Open.pCoreOf 2 (B ⊔ T), B⁆⁆ ≠ ⊥ := by
    have hchar : ∀ φ : ↥B ≃* ↥B,
        Subgroup.map φ.toMonoidHom (B.subgroupOf B) = B.subgroupOf B := by
      intro φ
      rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.2 φ.surjective
    obtain ⟨_, _, h3⟩ := characteristic_actor_fixes_commutator_fixedSpace_and_centralizes_odd_invariants h51 h53 B le_rfl hchar
    exact h3 h51.actor_ne_bot
  apply h3
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro y hy x hx
  have hxN : x ∈ Subgroup.normalizer (P : Set G) := by rw [hN]; trivial
  have hmem : Subgroup.normalizerMonoidHom P ⟨x, hxN⟩ ∈ Sstar P T B :=
    ⟨⟨x, hxN⟩, (Subgroup.mem_subgroupOf).mpr hx, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have := congrArg (fun φ : MulAut ↥P => (φ ⟨y, hy⟩ : P).1) hmem
  simp at this
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
  have h2 : x * y = y * x := by
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [this]
  exact h2.symm


end CFSG.LocalAnalysis.RankThreeUC.Section5.CoprimeStarSubgroupStructure
