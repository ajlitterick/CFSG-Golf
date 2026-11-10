module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts5
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1315b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz2

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open Equiv Equiv.Perm

theorem eq_five_of_alt_equiv {m : ℕ} (hm : 2 ≤ m)
    (g : alternatingGroup (Fin m) ≃* alternatingGroup (Fin 5)) : m = 5 := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  have h1 := two_mul_nat_card_alternatingGroup (α := Fin m)
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin 5)
  rw [Nat.card_congr g.toEquiv, h2, Nat.card_perm, Nat.card_perm, Nat.card_fin, Nat.card_fin] at h1
  exact (Nat.factorial_inj (by omega : 1 < m)).1 h1.symm

theorem isPiGroup_of_alt_pumpup {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (hcore : GLAPPrimeCore 3 K = ⊥) {n : ℕ} (f : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    {x : MulAut K} (hx : orderOf x = 3) {L : Subgroup K}
    (hL : GLAPComponent 3 (Prop1310a5.fixedSub x) L) (hL5 : IsAltType 5 (barOf 3 L)) :
    IsPiGroup 3 K := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn5 : 5 ≤ n := SchurFacts.five_le_of_isAltType hq ⟨f⟩
  have hρ := AltFacts5.isAltRep_of_equiv f
  have hZ : IsPGroup 3 ↥(Subgroup.center K) :=
    SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot Nat.prime_three hcore
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hA : ∀ a ∈ Subgroup.zpowers x, a ^ 3 = 1 := by
    intro a ha
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  obtain ⟨τ, -, hτ⟩ := AltFacts5.exists_tau (by decide : Odd 3) hn5 hq.1 f hA
  have htx : ∀ y : K, (alternatingGroup (Fin n)).subtype.comp
      (f.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) (x y) =
        τ ⟨x, Subgroup.mem_zpowers x⟩ * (alternatingGroup (Fin n)).subtype.comp
          (f.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) y *
        (τ ⟨x, Subgroup.mem_zpowers x⟩)⁻¹ :=
    fun y => hτ ⟨x, Subgroup.mem_zpowers x⟩ y
  have ht3 : (τ ⟨x, Subgroup.mem_zpowers x⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, Subgroup.mem_zpowers x⟩ : Subgroup.zpowers x) ^ 3 = 1 := Subtype.ext hx3
    rw [this, map_one]
  have hL' : GLAPComponent 3 (fixSub x) L := by
    have e : fixSub x = Prop1310a5.fixedSub x := Subgroup.ext fun _ => Iff.rfl
    rw [e]
    exact hL
  obtain ⟨h5, ⟨g⟩⟩ := AltFacts5.component_alt Nat.prime_three (by norm_num) hρ hZ htx ht3 hL'
  obtain ⟨g5⟩ := Lemma1315b.isAltType_center_quot le_rfl hL5
  have hfix : (τ ⟨x, Subgroup.mem_zpowers x⟩).supportᶜ.card = 5 :=
    eq_five_of_alt_equiv (by omega) (g.symm.trans g5)
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 3) (n := 1)
    (σ := τ ⟨x, Subgroup.mem_zpowers x⟩) (by rw [pow_one]; exact ht3)
  rw [hfix, Fintype.card_fin] at hmod
  have hn3 : n % 3 = 2 := by
    unfold Nat.ModEq at hmod
    omega
  have hnk : n = (n - 2) / 3 * 3 + 2 := by omega
  exact ⟨hq, hcore, Or.inl ⟨(n - 2) / 3, ⟨f.trans (Equiv.altCongrHom (finCongr hnk))⟩⟩⟩


end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz2

end
