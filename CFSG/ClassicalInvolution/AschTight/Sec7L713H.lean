module

public import CFSG.ClassicalInvolution.AschTight.Sec7L713G

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

variable {G : Type} [Group G]

section S3

variable {Q : Type*} [Group Q] {x y α : Q}


theorem s3_conj_inv (hx : x * x = 1) (hy : y * y = 1) (hxy : (x * y) ^ 3 = 1) :
    (x * y * x)⁻¹ * y * (x * y * x)⁻¹⁻¹ = x := by
  have hb := braid_of_order_three hx hy hxy
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  calc (x * y * x)⁻¹ * y * (x * y * x)⁻¹⁻¹ = (x⁻¹ * y⁻¹ * x⁻¹) * y * (x * y * x) := by group
    _ = (y * x * y) * y * (x * y * x) := by rw [hxi, hyi, hb]
    _ = y * x * (y * y) * x * y * x := by group
    _ = y * (x * x) * y * x := by rw [hy]; group
    _ = (y * y) * x := by rw [hx]; group
    _ = x := by rw [hy, one_mul]

theorem s3_cent (hx : x * x = 1) (hy : y * y = 1) (hxy : (x * y) ^ 3 = 1)
    (hαx : α * x * α⁻¹ = y) (hα : α * α = 1) :
    (α * (x * y * x))⁻¹ * x * (α * (x * y * x)) * x⁻¹ = 1 := by
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα
  have h1 : α⁻¹ * x * α = y := by rw [← hαx, hαi]
  have h2 := s3_conj_inv hx hy hxy
  calc (α * (x * y * x))⁻¹ * x * (α * (x * y * x)) * x⁻¹ =
      (x * y * x)⁻¹ * (α⁻¹ * x * α) * (x * y * x)⁻¹⁻¹ * x⁻¹ := by group
    _ = x * x⁻¹ := by rw [h1, h2]
    _ = 1 := mul_inv_cancel x


end S3

theorem odd_of_zpowers_eq {g h : G} (heq : Subgroup.zpowers g = Subgroup.zpowers h)
    (h2 : 2 ∣ orderOf g) {i : ℤ} (hi : g ^ i = h) : Odd i := by
  have hg : g ∈ Subgroup.zpowers h := heq ▸ Subgroup.mem_zpowers g
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have h1 : g ^ (i * l - 1) = 1 := by
    rw [zpow_sub, zpow_one, zpow_mul, hi, hl, mul_inv_cancel]
  have h3 : (orderOf g : ℤ) ∣ i * l - 1 := orderOf_dvd_iff_zpow_eq_one.mpr h1
  have h4 : (2 : ℤ) ∣ i * l - 1 := (by exact_mod_cast h2 : (2 : ℤ) ∣ orderOf g).trans h3
  rw [← Int.not_even_iff_odd]
  intro hev
  have h5 : Odd (i * l - 1) := (hev.mul_right l).sub_odd odd_one
  exact (Int.not_even_iff_odd.mpr h5) (even_iff_two_dvd.mpr h4)


end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
