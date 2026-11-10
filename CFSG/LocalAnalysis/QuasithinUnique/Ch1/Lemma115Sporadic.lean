module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Families
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CharTwoTools
public import CFSG.Walter.Models
public import CFSG.Walter.J1Props.Aut

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Blueprint CFSG.QuasithinUnique

section J1

open CFSG.Walter.J1Props CFSG.Open

theorem a5_involution_products : ∀ x : alternatingGroup (Fin 5), x * x = 1 → x ≠ 1 →
    ∃ g : alternatingGroup (Fin 5), (x * (g * x * g⁻¹)) ^ 3 = 1 ∧ x * (g * x * g⁻¹) ≠ 1 := by
  decide +kernel

theorem pCoreOf_eq_bot_of_equiv_alternating_five {Y : Type*} [Group Y] [Finite Y] {F : Subgroup Y}
    (e : F ≃* alternatingGroup (Fin 5)) : pCoreOf 2 F = ⊥ := by
  apply pCoreOf_eq_bot_of_involution_products
  intro x hx hx2 hx1
  have hxF2 : (⟨x, hx⟩ : F) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
  have hxF1 : (⟨x, hx⟩ : F) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  obtain ⟨g', hg3, hg1⟩ := a5_involution_products (e ⟨x, hx⟩)
    (by rw [← map_mul, hxF2, map_one]) (fun h => hxF1 (e.injective (by rw [h, map_one])))
  refine ⟨((e.symm g' : F) : Y), (e.symm g').2, ?_, ?_⟩
  · have h3 : ((⟨x, hx⟩ : F) * (e.symm g' * ⟨x, hx⟩ * (e.symm g')⁻¹)) ^ 3 = 1 := by
      apply e.injective
      simpa [map_mul, map_pow, map_inv] using hg3
    simpa using congrArg Subtype.val h3
  · intro h
    apply hg1
    have h' : (⟨x, hx⟩ : F) * (e.symm g' * ⟨x, hx⟩ * (e.symm g')⁻¹) = 1 := Subtype.ext h
    have := congrArg e h'
    simpa [map_mul, map_inv] using this

theorem not_charTwo_centralizer_janko :
    ¬ CharTwo (Subgroup.centralizer ({jankoHyp₀.t} : Set walterJ1)) := by
  intro hC
  have hFC : jankoHyp₀.F ≤ Subgroup.centralizer ({jankoHyp₀.t} : Set walterJ1) :=
    jankoHyp₀.le_centralizer
  have hFt : ∀ f ∈ jankoHyp₀.F, f * jankoHyp₀.t = jankoHyp₀.t * f := fun f hf =>
    Subgroup.mem_centralizer_singleton_iff.mp (jankoHyp₀.le_centralizer hf)
  have htN : jankoHyp₀.t ∈ Subgroup.normalizer (jankoHyp₀.F : Set walterJ1) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr hFt)
  have hnorm : (jankoHyp₀.F.subgroupOf
      (Subgroup.centralizer ({jankoHyp₀.t} : Set walterJ1))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hFC, jankoHyp₀.centralizer_eq]
    exact sup_le (Subgroup.zpowers_le.mpr htN) Subgroup.le_normalizer
  have hF : CharTwo jankoHyp₀.F := CharTwo.of_normal hC hFC hnorm
  have hcard : Nat.card jankoHyp₀.F = 60 := by
    rw [Nat.card_congr jankoHyp₀.iso.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hFne : jankoHyp₀.F ≠ ⊥ := by
    intro hbot
    have : Nat.card jankoHyp₀.F = 1 := by rw [hbot]; exact Subgroup.card_bot
    omega
  have hp : pCoreOf 2 jankoHyp₀.F = ⊥ := pCoreOf_eq_bot_of_equiv_alternating_five jankoHyp₀.iso
  exact not_charTwo_of_pCoreOf_eq_bot hFne hp hF


theorem not_charTwo_centralizer_walterJ1
    {t : walterJ1} (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    ¬ CharTwo (Subgroup.centralizer ({t} : Set walterJ1)) := by
  intro hC
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  obtain ⟨c, hc⟩ := isConj_iff.mp (J1_isConj_involutions jankoHyp₀.orderOf_t hord)
  have h1 : CharTwo ((Subgroup.centralizer ({t} : Set walterJ1)).map
      (MulAut.conj c⁻¹).toMonoidHom) := charTwo_map_mulEquiv (MulAut.conj c⁻¹) hC
  have h2 : (Subgroup.centralizer ({t} : Set walterJ1)).map (MulAut.conj c⁻¹).toMonoidHom =
      Subgroup.centralizer ({jankoHyp₀.t} : Set walterJ1) := by
    have e1 : (MulAut.conj c⁻¹ : MulAut walterJ1) t = jankoHyp₀.t := by
      rw [MulAut.conj_apply, ← hc]
      group
    rw [map_centralizer_singleton, e1]
  rw [h2] at h1
  exact not_charTwo_centralizer_janko h1

theorem j1_involution_centralizer : ∀ (K : Type) [Group K] [Finite K],
    Nonempty (K ≃* NativeSporadic.Carrier .J1) →
    ∀ t : K, t ≠ 1 → t * t = 1 → ¬ CharTwo (Subgroup.centralizer ({t} : Set K)) := by
  intro K _ _ ⟨e⟩ t ht1 ht2 hC
  let ε : K ≃* walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
  have h1 : CharTwo ((Subgroup.centralizer ({t} : Set K)).map ε.toMonoidHom) :=
    charTwo_map_mulEquiv ε hC
  rw [map_centralizer_singleton] at h1
  exact not_charTwo_centralizer_walterJ1 (t := ε t) (fun h => ht1 (ε.injective (by rw [h, map_one])))
    (by rw [← map_mul, ht2, map_one]) h1

theorem isInnerAut_of_carrierJ1
    {K : Type} [Group K] (e : K ≃* NativeSporadic.Carrier .J1)
    (β : K ≃* K) : ∃ l : K, ∀ x : K, β x = l⁻¹ * x * l := by
  let ε : K ≃* walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
  obtain ⟨g, hg⟩ := J3_aut (ε.symm.trans (β.trans ε))
  refine ⟨ε.symm g⁻¹, fun x => ?_⟩
  apply ε.injective
  have h1 := congrArg (fun f : MulAut walterJ1 => f (ε x)) hg
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
  rw [h1]
  simp

end J1

@[expose] def SporadicAutInner : Prop :=
  ∀ (s : TauCeti.SporadicName), IsSQTKSporadicName s → s ≠ .J1 → ∀ (K : Type) [Group K] [Finite K],
    Nonempty (K ≃* NativeSporadic.Carrier s) → ∀ β : K ≃* K, (∀ x, β (β x) = x) →
      (∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) → IsInnerAut β


end CFSG.QuasithinUnique.Ch1
