module

public import CFSG.Milestones.ASVolI.H13
public import CFSG.Quasithin.Background.F7TwoInvSporM22

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI CFSG.ASVolI.ChH CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Quasithin.F7Two
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.Quasithin.H.Mathieu

theorem exists_outer_involution_reps :
    ∃ α₁ α₂ : MulAut ↥NativeSporadic.M22, ∀ α : MulAut ↥NativeSporadic.M22, α * α = 1 →
      α ∉ inner ↥NativeSporadic.M22 →
      ∃ x : ↥NativeSporadic.M22, α = MulAut.conj x * α₁ * (MulAut.conj x)⁻¹ ∨
        α = MulAut.conj x * α₂ * (MulAut.conj x)⁻¹ := by
  obtain ⟨hr1, ho1, -⟩ := m22_out_rep_data1
  obtain ⟨hr2, ho2, -⟩ := m22_out_rep_data2
  have hr1' : m22Delta⁻¹ * m22OutRep1 ∈ NativeSporadic.M22 := by
    rwa [m22Certificate_originalSubgroup] at hr1
  have hr2' : m22Delta⁻¹ * m22OutRep2 ∈ NativeSporadic.M22 := by
    rwa [m22Certificate_originalSubgroup] at hr2
  have hinv1 : m22OutRep1⁻¹ = m22OutRep1 := by
    have h2 : m22OutRep1 * m22OutRep1 = 1 := by
      have := pow_orderOf_eq_one m22OutRep1
      rwa [ho1, pow_two] at this
    exact inv_eq_of_mul_eq_one_right h2
  have hinv2 : m22OutRep2⁻¹ = m22OutRep2 := by
    have h2 : m22OutRep2 * m22OutRep2 = 1 := by
      have := pow_orderOf_eq_one m22OutRep2
      rwa [ho2, pow_two] at this
    exact inv_eq_of_mul_eq_one_right h2
  have hnorm1 : ∀ h ∈ NativeSporadic.M22,
      m22OutRep1 * h * m22OutRep1⁻¹ ∈ NativeSporadic.M22 := by
    intro h hh
    have hy : (m22Delta⁻¹ * m22OutRep1) * h * (m22Delta⁻¹ * m22OutRep1)⁻¹ ∈
        NativeSporadic.M22 :=
      NativeSporadic.M22.mul_mem (NativeSporadic.M22.mul_mem hr1' hh)
        (NativeSporadic.M22.inv_mem hr1')
    have hconv : m22OutRep1 * h * m22OutRep1⁻¹ =
        m22Delta * ((m22Delta⁻¹ * m22OutRep1) * h * (m22Delta⁻¹ * m22OutRep1)⁻¹) *
          m22Delta⁻¹ := by group
    rw [hconv]
    exact m22_delta_normalizes _ hy
  have hnorm1' : ∀ h ∈ NativeSporadic.M22,
      m22OutRep1⁻¹ * h * m22OutRep1 ∈ NativeSporadic.M22 := by
    intro h hh
    have h1 := hnorm1 h hh
    rw [hinv1] at h1
    rw [hinv1]
    exact h1
  have hnorm2 : ∀ h ∈ NativeSporadic.M22,
      m22OutRep2 * h * m22OutRep2⁻¹ ∈ NativeSporadic.M22 := by
    intro h hh
    have hy : (m22Delta⁻¹ * m22OutRep2) * h * (m22Delta⁻¹ * m22OutRep2)⁻¹ ∈
        NativeSporadic.M22 :=
      NativeSporadic.M22.mul_mem (NativeSporadic.M22.mul_mem hr2' hh)
        (NativeSporadic.M22.inv_mem hr2')
    have hconv : m22OutRep2 * h * m22OutRep2⁻¹ =
        m22Delta * ((m22Delta⁻¹ * m22OutRep2) * h * (m22Delta⁻¹ * m22OutRep2)⁻¹) *
          m22Delta⁻¹ := by group
    rw [hconv]
    exact m22_delta_normalizes _ hy
  have hnorm2' : ∀ h ∈ NativeSporadic.M22,
      m22OutRep2⁻¹ * h * m22OutRep2 ∈ NativeSporadic.M22 := by
    intro h hh
    have h2 := hnorm2 h hh
    rw [hinv2] at h2
    rw [hinv2]
    exact h2
  refine ⟨conjOn NativeSporadic.M22 m22OutRep1 hnorm1 hnorm1',
    conjOn NativeSporadic.M22 m22OutRep2 hnorm2 hnorm2', ?_⟩
  intro α hα2 hαin
  have hδ' := inv_conj_mem NativeSporadic.M22 m22_delta_normalizes m22_delta_sq
  obtain ⟨g, hg, hαg⟩ := exists_eq_conj_of_outer NativeSporadic.M22 m22Delta
    m22_delta_normalizes m22_delta_sq m22_center_eq_bot' m22_delta_outer m22_mulAut_card α hαin
  let u : Equiv.Perm (Fin 22) := g * m22Delta
  have hαg' : ∀ h : NativeSporadic.M22,
      (α h : Equiv.Perm (Fin 22)) = u * (h : Equiv.Perm (Fin 22)) * u⁻¹ := by
    intro h
    simpa [u] using hαg h
  have hu : m22Delta⁻¹ * u ∈ NativeSporadic.M22 := by
    simpa [u, mul_assoc] using hδ' g hg
  have hu2N : u * u ∈ NativeSporadic.M22 := by
    have : u * u = g * (m22Delta * g * m22Delta⁻¹) * (m22Delta * m22Delta) := by
      simp only [u]
      group
    rw [this]
    exact NativeSporadic.M22.mul_mem
      (NativeSporadic.M22.mul_mem hg (m22_delta_normalizes g hg)) m22_delta_sq
  have hu2 : u * u = 1 := by
    have hc : (⟨u * u, hu2N⟩ : NativeSporadic.M22) ∈ Subgroup.center NativeSporadic.M22 := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := congrArg (fun φ : MulAut ↥NativeSporadic.M22 => (φ z : Equiv.Perm (Fin 22))) hα2
      simp only [MulAut.mul_apply, MulAut.one_apply] at hz
      rw [hαg', hαg'] at hz
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (z : Equiv.Perm (Fin 22)) * (u * u) = u * (u * z * u⁻¹) * u⁻¹ * (u * u) := by rw [hz]
        _ = u * u * z := by group
    rw [m22_center_eq_bot', Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hu1 : u ≠ 1 := by
    intro h1
    apply hαin
    refine ⟨1, MulEquiv.ext fun z => Subtype.ext ?_⟩
    rw [hαg', h1]
    simp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  obtain ⟨r, hr, c, hc, huc⟩ := m22_outer_cover_conj u hu ho
  refine ⟨⟨c, hc⟩, ?_⟩
  rcases hr with rfl | rfl
  · left
    apply MulEquiv.ext
    intro h
    apply Subtype.ext
    rw [hαg' h]
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_symm_apply, MulAut.inv_apply,
      conjOn_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [huc]
    group
  · right
    apply MulEquiv.ext
    intro h
    apply Subtype.ext
    rw [hαg' h]
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_symm_apply, MulAut.inv_apply,
      conjOn_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [huc]
    group

section Certs


end Certs

end CFSG.Quasithin.AppendixH.H14
