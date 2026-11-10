module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_9
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem glaPPrimeCoreOf_eq_self_of_coprime {G : Type*} [Group G] {p : ℕ} {H : Subgroup G}
    (h : Nat.Coprime p (Nat.card H)) : GLAPPrimeCoreOf p H = H := by
  have hN : (⊤ : Subgroup ↥H) ≤ GLAPPrimeCore p ↥H :=
    le_sSup ⟨inferInstance, by
      rw [Nat.card_congr (Subgroup.topEquiv (G := ↥H)).toEquiv]; exact h⟩
  have htop : GLAPPrimeCore p ↥H = ⊤ := top_unique hN
  unfold GLAPPrimeCoreOf
  rw [htop, Subgroup.map_top, Subgroup.range_subtype]

theorem glaPPrimeCoreOf_top_eq_bot_of_eq_bot {Q : Type*} [Group Q] {p : ℕ}
    (h : GLAPPrimeCore p Q = ⊥) : GLAPPrimeCoreOf p (⊤ : Subgroup Q) = ⊥ := by
  have h1 := glaPPrimeCore_map_iso p (Subgroup.topEquiv (G := Q))
  rw [h] at h1
  have hsub : (⊤ : Subgroup Q).subtype = (Subgroup.topEquiv (G := Q)).toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  unfold GLAPPrimeCoreOf
  rw [hsub, h1]


end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
