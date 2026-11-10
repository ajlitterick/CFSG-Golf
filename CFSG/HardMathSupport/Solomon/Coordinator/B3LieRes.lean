module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieCore
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Simple

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

@[expose] def BpSimpleLie : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    (∃ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ β : MulAut S, β ^ p = 1 →
        ⁅GLAPLayer p (fixSubgroup β), GLAPPrimeCoreOf p (fixSubgroup β)⁆ = ⊥

@[expose] def PerfectInLayer {S : Type*} [Group S] (β : MulAut S) : Prop :=
  ∀ P : Subgroup S, P ≤ fixSubgroup β → ⁅P, P⁆ = P → P ≤ GLALayer (fixSubgroup β)

@[expose] def LieSemisimpleCent : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ idx.1.characteristic → ∀ β : MulAut S, β ^ p = 1 →
        β ≠ 1 → PerfectInLayer β

@[expose] def LieDefCharOuter : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → p = idx.1.characteristic → ∀ β : MulAut S, β ^ p = 1 →
        (∀ a : S, MulAut.conj a ≠ β) →
          PerfectInLayer β ∨ GLAPPrimeCoreOf p (fixSubgroup β) = ⊥


@[expose] def LieUnipotentCore : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → p = idx.1.characteristic →
        ∀ x : S, x ≠ 1 → x ^ p = 1 →
          GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set S)) = ⊥

section Elementary

theorem b3Lie_isQuasisimple_of_simple {L : Type*} [Group L] [IsSimpleGroup L]
    (hL : ∃ a b : L, a * b ≠ b * a) : CFSG.Open.IsQuasisimple L := by
  have hZ : Subgroup.center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hL
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator L) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hL
      have : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp this)
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup

theorem b3Lie_center_eq_bot {L : Type*} [Group L] [IsSimpleGroup L]
    (hL : ∃ a b : L, a * b ≠ b * a) : Subgroup.center L = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hL
    exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)

theorem perfectInLayer_one {S : Type} [Group S] [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) :
    PerfectInLayer (1 : MulAut S) := by
  have hfix : fixSubgroup (1 : MulAut S) = ⊤ :=
    eq_top_iff.2 fun x _ => rfl
  have hq : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup S) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      Subgroup.topEquiv.symm (b3Lie_isQuasisimple_of_simple hS)
  intro P hP _
  rw [hfix]
  exact le_top.trans (le_sSup ⟨le_rfl, CFSG.Open.IsSubnormal.refl _, hq⟩)


end Elementary

theorem b3Lie_fixSubgroup_conj {S : Type*} [Group S] (x : S) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set S) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff]
  show x * g * x⁻¹ = g ↔ g * x = x * g
  constructor
  · intro h
    calc g * x = (x * g * x⁻¹) * x := by rw [h]
      _ = x * g := by group
  · intro h
    rw [← h]
    group


theorem bpSimpleLie_of_unipotentCore (hU : LieUnipotentCore) (hss : LieSemisimpleCent)
    (hout : LieDefCharOuter) : BpSimpleLie := by
  intro S _ _ hs hnc ⟨idx, he⟩ p hp hp2 β hβ
  have : Fact p.Prime := ⟨hp⟩
  by_cases hβ1 : β = 1
  · subst hβ1
    exact commutator_glaPLayer_eq_bot_of_perfect_le_layer (perfectInLayer_one hnc)
  by_cases hpc : p = idx.1.characteristic
  · by_cases hin : ∃ a : S, MulAut.conj a = β
    · obtain ⟨x, rfl⟩ := hin
      have hx1 : x ≠ 1 := fun h => hβ1 (by rw [h, map_one])
      have hxp : x ^ p = 1 := by
        have h1 : (MulAut.conj (x ^ p) : MulAut S) = 1 := by rw [map_pow]; exact hβ
        have hmem : x ^ p ∈ Subgroup.center S := by
          rw [Subgroup.mem_center_iff]
          intro g
          have := congrArg (fun f : MulAut S => f g) h1
          simp only [MulAut.conj_apply, MulAut.one_apply] at this
          calc g * x ^ p = (x ^ p * g * (x ^ p)⁻¹) * x ^ p := by rw [this]
            _ = x ^ p * g := by group
        rw [b3Lie_center_eq_bot hnc] at hmem
        exact hmem
      rw [b3Lie_fixSubgroup_conj, hU S hs hnc idx he p hp hp2 hpc x hx1 hxp]
      exact Subgroup.commutator_bot_right _
    · rcases hout S hs hnc idx he p hp hp2 hpc β hβ (not_exists.1 hin) with h | h
      · exact commutator_glaPLayer_eq_bot_of_perfect_le_layer h
      · rw [h]
        exact Subgroup.commutator_bot_right _
  · exact commutator_glaPLayer_eq_bot_of_perfect_le_layer
      (hss S hs hnc idx he p hp hp2 hpc β hβ hβ1)


theorem b3SimpleLie_of_unipotentCore (hU : LieUnipotentCore) (hss : LieSemisimpleCent)
    (hout : LieDefCharOuter) : B3SimpleLie := by
  intro S _ _ hs hnc hlie β hβ
  exact bpSimpleLie_of_unipotentCore hU hss hout S hs hnc hlie 3 Nat.prime_three (by norm_num) β hβ


end CFSG.HardMathSupport.Solomon.Coordinator
