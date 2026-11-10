module

public import CFSG.GH74.Defs
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
import CFSG.LocalAnalysis.ComponentInitial.ParabolicLocalCharacteristicTransfer

public section

namespace CFSG.GH74

open Subgroup

theorem pPrimeCore_quotient_pPrimeCore_eq_bot (Y : Type*) [Group Y] [Finite Y] (p : ℕ)
    [Fact p.Prime] : pPrimeCore p (Y ⧸ pPrimeCore p Y) = ⊥ :=
  _root_.CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p

theorem isTwoConstrained_of_layer_eq_bot {Y : Type*} [Group Y] [Finite Y]
    (h : layer (Y ⧸ pPrimeCore 2 Y) = ⊥) : IsTwoConstrained Y :=
  isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot _ 2
    (pPrimeCore_quotient_pPrimeCore_eq_bot Y 2) h


theorem isTwoConstrained_of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsTwoConstrained Y) : IsTwoConstrained Y' :=
  LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv
    (QuotientGroup.congr (pPrimeCore 2 Y) (pPrimeCore 2 Y') e (pPrimeCore_map_iso 2 e)) h

theorem centralizer_singleton_quotient_eq_map {N : Type*} [Group N] [Finite N] (p : ℕ)
    [Fact p.Prime] (M : Subgroup N) [M.Normal] (hM : Nat.Coprime p (Nat.card M)) {t : N}
    (ht : ∃ k : ℕ, orderOf t = p ^ k) :
    centralizer ({QuotientGroup.mk' M t} : Set (N ⧸ M)) =
      (centralizer ({t} : Set N)).map (QuotientGroup.mk' M) := by
  obtain ⟨k, hk⟩ := ht
  have : Fact (IsPGroup p (zpowers t)) :=
    ⟨IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])⟩
  have h := _root_.CFSG.centralizer_map_quotient_eq_map_centralizer p (zpowers t) M inferInstance hM
  simp only at h
  rwa [MonoidHom.map_zpowers, zpowers_eq_closure, zpowers_eq_closure, centralizer_closure,
    centralizer_closure] at h

theorem centralizer_singleton_pPrimeCore_quotient_eq_map {N : Type*} [Group N] [Finite N]
    (p : ℕ) [Fact p.Prime] {t : N} (ht : ∃ k : ℕ, orderOf t = p ^ k) :
    centralizer ({QuotientGroup.mk' (pPrimeCore p N) t} : Set (N ⧸ pPrimeCore p N)) =
      (centralizer ({t} : Set N)).map (QuotientGroup.mk' (pPrimeCore p N)) :=
  centralizer_singleton_quotient_eq_map p (pPrimeCore p N) pPrimeCore_coprime_card ht

theorem centralizer_involution_pPrimeCore_quotient_eq_map {N : Type*} [Group N] [Finite N] {t : N}
    (ht : orderOf t = 2) :
    centralizer ({QuotientGroup.mk' (pPrimeCore 2 N) t} : Set (N ⧸ pPrimeCore 2 N)) =
      (centralizer ({t} : Set N)).map (QuotientGroup.mk' (pPrimeCore 2 N)) :=
  centralizer_singleton_pPrimeCore_quotient_eq_map 2 ⟨1, by rw [ht, pow_one]⟩


end CFSG.GH74
