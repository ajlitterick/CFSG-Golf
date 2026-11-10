module

public import CFSG.RankThree.GroupTheory.SteinbergBMCrossPrimeLocalCore
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCommutatorFactorization

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem map_actionCommutator_conj {K X : Subgroup G} (hXK : X ≤ normalizer (K : Set G))
    (K' : Subgroup K) :
    letI : MulDistribMulAction X K := MulDistribMulAction.compHom K (Subgroup.inclusion hXK)
    (actionCommutator X K').map K.subtype = ⁅K'.map K.subtype, X⁆ := by
  let : MulDistribMulAction X K := MulDistribMulAction.compHom K (Subgroup.inclusion hXK)
  have hsmul : ∀ (x : X) (k : K), ((x • k : K) : G) = x * k * (x : G)⁻¹ := fun _ _ => rfl
  unfold actionCommutator
  rw [MonoidHom.map_closure, Subgroup.commutator_def]
  refine le_antisymm ((closure_le _).2 ?_) ((closure_le _).2 ?_)
  · rintro _ ⟨_, ⟨k, hk, x, rfl⟩, rfl⟩
    have e : K.subtype (k⁻¹ * (x • k)) = ⁅(k : G)⁻¹, (x : G)⁆ := by
      rw [map_mul, map_inv, coe_subtype, hsmul, commutatorElement_def, inv_inv]
      group
    rw [e]
    exact subset_closure ⟨_, (K'.map K.subtype).inv_mem (mem_map_of_mem K.subtype hk), x, x.2,
      rfl⟩
  · rintro _ ⟨_, ⟨k, hk, rfl⟩, x, hx, rfl⟩
    have hmem : k⁻¹⁻¹ * ((⟨x, hx⟩ : X) • k⁻¹) ∈
        {y : K | ∃ h ∈ K', ∃ a : X, y = h⁻¹ * (a • h)} := ⟨k⁻¹, K'.inv_mem hk, ⟨x, hx⟩, rfl⟩
    refine subset_closure ⟨_, hmem, ?_⟩
    rw [map_mul, map_inv, coe_subtype, hsmul, commutatorElement_def]
    simp only [inv_inv, coe_inv]
    group

theorem le_normalizer_inf_centralizer {V K : Subgroup G} {b : G}
    (hKV : K ≤ normalizer (V : Set G)) (hKb : ∀ c ∈ K, c * b = b * c) :
    K ≤ normalizer ((V ⊓ centralizer ({b} : Set G) : Subgroup G) : Set G) := by
  refine le_normalizer_of_forall_conj_mem fun c hc x hx => ⟨?_, ?_⟩
  · exact (mem_normalizer_iff.mp (hKV hc) x).mp hx.1
  · have hcb := hKb c hc
    have hxb : x * b = b * x := mem_centralizer_singleton_iff.mp hx.2
    refine mem_centralizer_singleton_iff.mpr ?_
    calc c * x * c⁻¹ * b = c * x * (c⁻¹ * b * c) * c⁻¹ := by group
      _ = c * x * b * c⁻¹ := by
          rw [show c⁻¹ * b * c = b by rw [mul_assoc, ← hcb]; group]
      _ = c * b * x * c⁻¹ := by rw [mul_assoc c x b, hxb, ← mul_assoc]
      _ = b * (c * x * c⁻¹) := by rw [hcb]; group


end CFSG.RankThree.GroupTheory.SteinbergBM
