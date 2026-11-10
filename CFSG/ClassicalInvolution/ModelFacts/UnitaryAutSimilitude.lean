module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarCommutantSpace
public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismRealization

public section

namespace CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan

variable {p f : ℕ} {K : Type} [Field K]

theorem glAut_mem_unitarySU (h : UnitaryFieldData p f K) (φ : K ≃+* K) {d : ℕ}
    {y : GL (Fin d) K} (hy : y ∈ unitarySU p f K d) : glAut φ y ∈ unitarySU p f K d := by
  rw [mem_unitarySU_iff h] at hy ⊢
  obtain ⟨hdet, hu⟩ := hy
  refine ⟨?_, ?_⟩
  · rw [coe_glAut, show (y : Matrix (Fin d) (Fin d) K).map φ =
      (φ : K →+* K).mapMatrix (y : Matrix (Fin d) (Fin d) K) from rfl, ← RingHom.map_det, hdet,
      map_one]
  · rw [coe_glAut, map_bar_map_comm, ← transpose_map, ← map_mul_ringEquiv, hu,
      map_one_ringEquiv]


theorem eq_smul_one_of_commute (h : UnitaryFieldData p f K) (hp : p ≠ 2) {d : ℕ} (hd : 3 ≤ d)
    (B : Matrix (Fin d) (Fin d) K)
    (hB : ∀ y : GL (Fin d) K, y ∈ unitarySU p f K d →
      B * (y : Matrix (Fin d) (Fin d) K) = (y : Matrix (Fin d) (Fin d) K) * B) :
    ∃ a : K, B = a • 1 := by
  have : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have h3 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    have h4 := Nat.le_of_dvd two_pos ((CharP.cast_eq_zero_iff K p 2).mp h3)
    have := h.prime.two_le
    omega
  obtain ⟨c, hcN, hck⟩ := exists_norm_one_not_fixed h hp
  have hcomm : ∀ M : GL (Fin d) K, M ∈ gramSU h (1 : Matrix (Fin d) (Fin d) K) → ∀ u,
      ((Matrix.mulVecLin B).restrictScalars h.fixedField)
        ((M : Matrix (Fin d) (Fin d) K) *ᵥ u) =
      (M : Matrix (Fin d) (Fin d) K) *ᵥ
        ((Matrix.mulVecLin B).restrictScalars h.fixedField) u := by
    intro M hM u
    have hM' : M ∈ unitarySU p f K d := by rw [unitarySU_eq_gramSU h]; exact hM
    change B *ᵥ ((M : Matrix (Fin d) (Fin d) K) *ᵥ u) = (M : Matrix (Fin d) (Fin d) K) *ᵥ (B *ᵥ u)
    rw [mulVec_mulVec, mulVec_mulVec, hB M hM']
  obtain ⟨a, ha⟩ := coordinate_commutant_scalar h h2 hd hcN hck
    ((Matrix.mulVecLin B).restrictScalars h.fixedField)
    (fun i l hil u => by
      obtain ⟨M, hM, hMmem⟩ := unitSignDiag_mem h hil
      have := hcomm M hMmem u
      rwa [hM] at this)
    (fun i j hij u => by
      obtain ⟨M, hM, hMmem⟩ := unitLambdaDiag_mem h hcN hij
      have := hcomm M hMmem u
      rwa [hM] at this)
    (fun i j hij u => by
      obtain ⟨M, hM, hMmem⟩ := unitSignedSwapMatrix_mem h hij
      have := hcomm M hMmem u
      rwa [hM] at this)
  refine ⟨a, Matrix.ext fun i j => ?_⟩
  have h5 := congrFun (ha (Pi.single j 1)) i
  change (B *ᵥ Pi.single j 1) i = (a • (Pi.single j 1 : Fin d → K)) i at h5
  simpa [mulVec_single_one, Pi.single_apply, Matrix.smul_apply, Matrix.one_apply, eq_comm] using h5


end CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
