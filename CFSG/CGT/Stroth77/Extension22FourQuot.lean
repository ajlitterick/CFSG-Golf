module

public import CFSG.CGT.Stroth77.Extension22FourC4

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {m : ℕ}

theorem fourB_eq_bot_of_m_zero {D : StrothTypeData B (StrothTypeIndex.t100 0)} :
    fourB D = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨z, hz⟩ := (mem_fourB_iff D).mp hx
  have hz4 : (4 : ℕ) • z = 0 := by
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero]
    have h := addOrderOf_dvd_natCard z
    rw [natCard_torus] at h
    convert h using 1
    rw [show (StrothTypeIndex.t100 0).k 0 = 0 from by
        simpa [StrothTypeIndex.k] using k100_zero 0,
      show (StrothTypeIndex.t100 0).k 1 = 1 from by
        simpa [StrothTypeIndex.k] using k100_one 0,
      show (StrothTypeIndex.t100 0).k 2 = 1 from by
        simpa [StrothTypeIndex.k] using k100_two 0]
    norm_num
  have hec : D.ec x = 0 := hz ▸ hz4
  exact D.ec_injective (by simpa using hec)

theorem phiR_fixed_eq_zero_of_m_zero {x : Torus (Type100.k 0)}
    (h : (Type100.action 0).φρ x = x) : x = 0 := by
  obtain ⟨a, b, c, rfl⟩ := torus_eq_zsmul_gens (Type100.k 0) x
  rw [type100_rho_apply_gens] at h
  have h2 := congrFun h 2
  rw [gens_apply_two (k := Type100.k 0) (a := a - 2 * c) (b := -c) (c := b - c),
    gens_apply_two (k := Type100.k 0) (a := a) (b := b) (c := c)] at h2
  have hb2 : ((b : ℤ) : ZMod (2 ^ Type100.k 0 2)) = 0 := by
    rw [Int.cast_sub] at h2
    have hb2' : ((b : ℤ) : ZMod (2 ^ Type100.k 0 2)) =
        2 * ((c : ℤ) : ZMod (2 ^ Type100.k 0 2)) := by
      calc ((b : ℤ) : ZMod (2 ^ Type100.k 0 2))
          = ((b : ℤ) : ZMod (2 ^ Type100.k 0 2)) - ((c : ℤ) : ZMod (2 ^ Type100.k 0 2)) +
              ((c : ℤ) : ZMod (2 ^ Type100.k 0 2)) := by ring
        _ = ((c : ℤ) : ZMod (2 ^ Type100.k 0 2)) +
              ((c : ℤ) : ZMod (2 ^ Type100.k 0 2)) := by rw [h2]
        _ = 2 * ((c : ℤ) : ZMod (2 ^ Type100.k 0 2)) := by ring
    have h2eq : (2 : ZMod (2 ^ Type100.k 0 2)) = 0 := by
      rw [show Type100.k 0 2 = 1 from k100_two 0]
      decide
    rw [hb2', h2eq, zero_mul]
  have hb1 : ((b : ℤ) : ZMod (2 ^ Type100.k 0 1)) = 0 := by
    have hk : Type100.k 0 2 = Type100.k 0 1 := by rw [k100_two, k100_one]
    exact hk ▸ hb2
  have h1 := congrFun h 1
  rw [gens_apply_one (k := Type100.k 0) (a := a - 2 * c) (b := -c) (c := b - c),
    gens_apply_one (k := Type100.k 0) (a := a) (b := b) (c := c)] at h1
  have hc1 : ((c : ℤ) : ZMod (2 ^ Type100.k 0 1)) = 0 := by
    have hc1' : -((c : ℤ) : ZMod (2 ^ Type100.k 0 1)) =
        ((b : ℤ) : ZMod (2 ^ Type100.k 0 1)) := by
      simpa using h1
    rw [hb1] at hc1'
    simpa using hc1'
  have hc2 : ((c : ℤ) : ZMod (2 ^ Type100.k 0 2)) = 0 := by
    have hk : Type100.k 0 1 = Type100.k 0 2 := by rw [k100_two, k100_one]
    exact hk ▸ hc1
  have h0 : a • gen (Type100.k 0) 0 = 0 := by
    rw [zsmul_gen_eq_zero, show Type100.k 0 0 = 0 from k100_zero 0]
    change ((a : ℤ) : ZMod 1) = 0
    exact Subsingleton.elim _ _
  have h1z : b • gen (Type100.k 0) 1 = 0 := by
    rw [zsmul_gen_eq_zero]
    exact hb1
  have h2z : c • gen (Type100.k 0) 2 = 0 := by
    rw [zsmul_gen_eq_zero]
    exact hc2
  rw [h0, h1z, h2z, zero_add, zero_add]

theorem t100_fixed_rho_t_mod_four_of_mem_zero
    {D : StrothTypeData B (StrothTypeIndex.t100 0)} {y : B}
    (hρ : conjBy D.ρ_mem y * y⁻¹ ∈ fourB D) :
    y ∈ fourB D := by
  rw [fourB_eq_bot_of_m_zero] at hρ
  have hρy : conjBy D.ρ_mem y = y := by
    have hmem : conjBy D.ρ_mem y * y⁻¹ = 1 := by simpa using hρ
    exact mul_inv_eq_one.mp hmem
  have hfix : D.ec y = 0 := by
    have h := D.ρ_conj y
    rw [hρy] at h
    exact phiR_fixed_eq_zero_of_m_zero h.symm
  have hy : y = 1 := D.ec_injective (by rw [hfix, D.ec_one])
  rw [hy]
  exact (fourB D).one_mem


end CFSG.CGT.Stroth77
