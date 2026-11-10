module

public import CFSG.CGT.Stroth77.Stroth2Mho
public import CFSG.CGT.Stroth77.StrothFrameNE

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G] {X : StrothAmbient G}

theorem exists_two_mul_of_two_mul_eq_zero {k : ℕ} (hk : 2 ≤ k) {x : ZMod (2 ^ k)}
    (h : (2 : ℕ) * x = 0) : ∃ y : ZMod (2 ^ k), (2 : ℕ) * y = x := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, x = (n : ZMod (2 ^ k)) :=
    ⟨x.val, (ZMod.natCast_zmod_val x).symm⟩
  have hdvd : 2 ^ k ∣ 2 * n := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk
  have h4dvd : 4 ∣ 2 * n := h4.trans hdvd
  obtain ⟨t, ht⟩ := h4dvd
  have h2 : 2 ∣ n := by
    refine ⟨t, ?_⟩
    have h4 : 2 * n = 2 * (2 * t) := by rw [ht]; ring
    omega
  obtain ⟨t, rfl⟩ := h2
  refine ⟨(t : ZMod (2 ^ k)), ?_⟩
  push_cast
  ring


theorem commutator_mem_omegaIn_one_of_mem_centralizerInMho {Z : StrothDatum X} {x : G}
    (hx : x ∈ Z.centralizerInMho) {d : G} (hd : d ∈ Z.D) :
    x * d * x⁻¹ * d⁻¹ ∈ omegaIn 1 Z.D := by
  have hxN : x ∈ Subgroup.normalizer (Z.D : Set G) := hx.1.2
  have hxd : x * d * x⁻¹ ∈ Z.D := (Subgroup.mem_normalizer_iff.mp hxN d).mp hd
  have hd2 : d * d ∈ mhoOne Z.D := by
    simpa [pow_two] using
      CFSG.GroupTheory.HuppertProduct.pow_mem_mho (S := Z.D) (n := 2) hd
  have hcomm : (d * d) * x = x * (d * d) :=
    Subgroup.mem_centralizer_iff.mp hx.2 (d * d) hd2
  have hv2 : (x * d * x⁻¹) * (x * d * x⁻¹) = d * d := by
    have h1 : x * (d * d) * x⁻¹ = d * d := by rw [← hcomm]; group
    calc (x * d * x⁻¹) * (x * d * x⁻¹)
        = x * (d * d) * x⁻¹ := by group
      _ = d * d := h1
  have hcommD : (x * d * x⁻¹) * d = d * (x * d * x⁻¹) :=
    congrArg Subtype.val
      (Z.dataD.isMulCommutative.is_comm.comm (⟨x * d * x⁻¹, hxd⟩ : Z.D) ⟨d, hd⟩)
  have hvdinv : (x * d * x⁻¹) * d⁻¹ = d⁻¹ * (x * d * x⁻¹) := by
    have h' : d⁻¹ * ((x * d * x⁻¹) * d) * d⁻¹ = d⁻¹ * (d * (x * d * x⁻¹)) * d⁻¹ := by
      rw [hcommD]
    simpa [mul_assoc] using h'.symm
  have hu2 : ((x * d * x⁻¹) * d⁻¹) * ((x * d * x⁻¹) * d⁻¹) = 1 := by
    calc ((x * d * x⁻¹) * d⁻¹) * ((x * d * x⁻¹) * d⁻¹)
        = (x * d * x⁻¹) * (d⁻¹ * (x * d * x⁻¹)) * d⁻¹ := by group
      _ = (x * d * x⁻¹) * ((x * d * x⁻¹) * d⁻¹) * d⁻¹ := by rw [← hvdinv]
      _ = ((x * d * x⁻¹) * (x * d * x⁻¹)) * (d⁻¹ * d⁻¹) := by group
      _ = (d * d) * (d⁻¹ * d⁻¹) := by rw [hv2]
      _ = 1 := by group
  have hmem : x * d * x⁻¹ * d⁻¹ ∈ Z.D :=
    Subgroup.mul_mem Z.D hxd (Z.D.inv_mem hd)
  have hsq : (x * d * x⁻¹ * d⁻¹) * (x * d * x⁻¹ * d⁻¹) = 1 := hu2
  exact mem_omegaIn_one_of_mul_self hmem hsq


end CFSG.CGT.Stroth77
