module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M22
public import CFSG.GroupTheory.NonabelianOrderSixCore
public import Certificates.Certificate9316

public section


namespace CFSG.ClassicalInvolution

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native
open scoped commutatorElement

theorem m22E8_check : m22E8Check = true :=
  Certificates.certificate9316

theorem m22E8_facts : M22E8Facts :=
  m22E8Facts_of_check m22E8_check

abbrev m22E8K : Subgroup (Equiv.Perm (Fin 22)) := m22CentQ1.originalSubgroup

theorem m22E8UL_data :
    (1 : Equiv.Perm (Fin 22)) ∈ m22E8UL ∧
      (∀ x ∈ m22E8UL, ∀ y ∈ m22E8UL, x * y ∈ m22E8UL) ∧
      (∀ x ∈ m22E8UL, x⁻¹ ∈ m22E8UL) ∧
      (∀ u ∈ m22E8UL, u ∈ m22E8KL) ∧
      (∀ u ∈ m22E8UL, u ^ 2 ^ 6 = 1) ∧
      (∀ g ∈ m22E8KL, ∀ u ∈ m22E8UL, g * u * g⁻¹ ∈ m22E8UL) ∧
      (∀ g ∈ m22E8KL, (∀ u ∈ m22E8UL, g * u = u * g) → g ∈ m22E8UL) := by
  have h := m22_U1_check
  simp only [twoConstrainedCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, hmul⟩, hinv⟩, hUK⟩, hpow⟩, hnorm⟩, hself⟩ := h
  refine ⟨by simpa [m22E8UL] using h1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    simpa [m22E8UL] using hmul x (by simpa [m22E8UL] using hx) y (by simpa [m22E8UL] using hy)
  · intro x hx
    simpa [m22E8UL] using hinv x (by simpa [m22E8UL] using hx)
  · intro u hu
    simpa [m22E8UL, m22E8KL] using hUK u (by simpa [m22E8UL] using hu)
  · intro u hu
    simpa [m22E8UL] using hpow u (by simpa [m22E8UL] using hu)
  · intro g hg u hu
    simpa [m22E8UL, m22E8KL] using hnorm g (by simpa [m22E8KL] using hg) u (by simpa [m22E8UL] using hu)
  · intro g hg hc
    rcases hself g (by simpa [m22E8KL] using hg) with hfalse | hmem
    · have htrue : (m22E8UL.all fun u => decide (g * u = u * g)) = true :=
        List.all_eq_true.2 fun u hu => decide_eq_true (hc u hu)
      have hfalseUL : (m22E8UL.all fun u => decide (g * u = u * g)) = false := by
        simpa [m22E8UL] using hfalse
      rw [htrue] at hfalseUL
      exact Bool.noConfusion hfalseUL
    · simpa [m22E8UL] using hmem

noncomputable abbrev m22E8U : Subgroup (Equiv.Perm (Fin 22)) :=
  subgroupOfList m22E8UL (m22E8UL_data.1) (m22E8UL_data.2.1) (m22E8UL_data.2.2.1)


theorem m22E8U_le_K :
    m22E8U ≤ m22E8K := by
  intro u hu
  exact (mem_enumerationTab_iff m22CentQ1 (m22_oddcore_cent1).1 u).1
    (m22E8UL_data.2.2.2.1 u hu)

theorem m22E8K_le_normalizer_U :
    m22E8K ≤ Subgroup.normalizer (m22E8U : Set _) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro u
  have hgL : g ∈ m22E8KL :=
    (mem_enumerationTab_iff m22CentQ1 (m22_oddcore_cent1).1 g).2 hg
  change (u ∈ m22E8UL ↔ g * u * g⁻¹ ∈ m22E8UL)
  refine ⟨fun huu => m22E8UL_data.2.2.2.2.2.1 g hgL u huu, fun huu => ?_⟩
  have hgi : g⁻¹ ∈ m22E8KL :=
    (mem_enumerationTab_iff m22CentQ1 (m22_oddcore_cent1).1 g⁻¹).2 (m22E8K.inv_mem hg)
  have hconj := m22E8UL_data.2.2.2.2.2.1 g⁻¹ hgi (g * u * g⁻¹) huu
  have heq : g⁻¹ * (g * u * g⁻¹) * (g⁻¹)⁻¹ = u := by group
  rwa [heq] at hconj


instance m22E8U_subgroupOf_normal :
    (m22E8U.subgroupOf m22E8K).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer m22E8U_le_K).2 m22E8K_le_normalizer_U


noncomputable abbrev m22E8E :
    Subgroup (Equiv.Perm (Fin 22)) :=
  subgroupOfList m22E8EL (m22E8_facts).el_one (m22E8_facts).el_mul (m22E8_facts).el_inv

theorem m22E8E_mem {x : Equiv.Perm (Fin 22)} :
    x ∈ m22E8E ↔ x ∈ m22E8EL := Iff.rfl


instance m22E8E_isMulCommutative :
    IsMulCommutative m22E8E :=
  IsMulCommutative.of_comm fun a b => Subtype.ext <| by
    exact (m22E8_facts).el_comm a.1 ((m22E8E_mem).1 a.2) b.1 ((m22E8E_mem).1 b.2)

instance m22E8E_isElementaryAbelian :
    IsElementaryAbelian 2 m22E8E where
  exponent_dvd_p := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    exact Subtype.ext <| by
      have hx : (x : Equiv.Perm (Fin 22)) ∈ m22E8EL := (m22E8E_mem).1 x.2
      simpa using (m22E8_facts).el_sq x.1 hx


end CFSG.ClassicalInvolution
