module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderDefs
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelComm

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups Matrix

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open CFSG.QuasithinUnique.Setup.X7
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
  {l : ℕ} (hF : Fintype.card F = 2 ^ (2 * l))

theorem mul_sig_mul_fix (hF : Fintype.card F = 2 ^ (2 * l)) (c a : F)
    (ha : a ^ 2 ^ l = a) :
    (c * c ^ 2 ^ l * a) ^ 2 ^ l = c * c ^ 2 ^ l * a := by
  rw [mul_pow, mul_pow]
  have hc : (c ^ 2 ^ l) ^ 2 ^ l = c := by
    rw [← pow_mul, ← pow_add, ← two_mul, ← hF, FiniteField.pow_card]
  rw [hc, ha]
  ring

private theorem exists_mul_sig_mul_eq (hF : Fintype.card F = 2 ^ (2 * l))
    (a b : F) (ha : a ^ 2 ^ l = a) (hb : b ^ 2 ^ l = b)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    ∃ c : F, c ≠ 0 ∧ c * c ^ 2 ^ l * a = b := by
  have hainv : a⁻¹ ^ 2 ^ l = a⁻¹ := by rw [inv_pow, ha]
  have hbdiv : (b * a⁻¹) ^ 2 ^ l = b * a⁻¹ := by rw [mul_pow, hb, hainv]
  obtain ⟨c, hc0, hc⟩ := exists_mul_sig_eq (hF := hF) hbdiv
    (mul_ne_zero hb0 (inv_ne_zero ha0))
  exact ⟨c, hc0, by rw [hc]; field_simp⟩

private theorem inv_tMat (c : F) (hc : c ≠ 0) :
    (tMat c hc)⁻¹ = tMat c⁻¹ (inv_ne_zero hc) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tMat_coe, Matrix.mul_apply, Fin.sum_univ_two, hc]

theorem tMat_mem_normalizer (c : F) (hc : c ≠ 0) :
    tMat c hc ∈ Subgroup.normalizer (upperSylow (F := F) : Set (SL(2, F))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨t, rfl⟩ := mem_upperSylow_iff.mp hg
    rw [tMat_conj]
    exact mem_upperSylow_iff.mpr ⟨c ^ 2 * t, rfl⟩
  · intro hg
    obtain ⟨t, ht⟩ := mem_upperSylow_iff.mp hg
    have h2 : g = (tMat c hc)⁻¹ * uMat t * tMat c hc := by
      calc g = (tMat c hc)⁻¹ * (tMat c hc * g * (tMat c hc)⁻¹) * tMat c hc := by group
        _ = (tMat c hc)⁻¹ * uMat t * tMat c hc := by rw [ht]
    have hlast : (tMat c⁻¹ (inv_ne_zero hc))⁻¹ = tMat c hc := by
      simpa using (inv_tMat (c⁻¹) (inv_ne_zero hc))
    rw [h2, inv_tMat c hc, ← hlast, tMat_conj]
    exact mem_upperSylow_iff.mpr ⟨(c⁻¹) ^ 2 * t, rfl⟩

theorem hermAct_tMat_hermDiag (c : F) (hc : c ≠ 0) (a : F) (ha : a ^ 2 ^ l = a) :
    hermAct l (sig_sig hF) (tMat c hc) (hermDiag l hF a ha) =
      hermDiag l hF (c * c ^ 2 ^ l * a) (mul_sig_mul_fix (hF := hF) c a ha) := by
  refine hermA_ext ?_ ?_ ?_
  · rw [hermAct_tMat_00, sig_apply, hermDiag_coe, hermDiag_coe]
    simp
  · rw [hermAct_tMat_01, hermDiag_coe, hermDiag_coe]
    simp
  · rw [hermAct_tMat_11, hermDiag_coe, hermDiag_coe]
    simp

theorem normalizer_transitive_fixed (v w : ↥(hermA l F))
    (hv : v ∈ fixedSub (hermRep l hF) upperSylow)
    (hw : w ∈ fixedSub (hermRep l hF) upperSylow) (hv0 : v ≠ 0) (hw0 : w ≠ 0) :
    ∃ n ∈ Subgroup.normalizer (upperSylow (F := F) : Set (SL(2, F))),
      hermRep l hF n v = w := by
  have hv' : v ∈ AddSubgroup.toZModSubmodule (n := 2) (herm1101 l F) := by
    rwa [← fixedSub_upperSylow (hF := hF)]
  have hw' : w ∈ AddSubgroup.toZModSubmodule (n := 2) (herm1101 l F) := by
    rwa [← fixedSub_upperSylow (hF := hF)]
  obtain ⟨h11, h01⟩ := hv'
  obtain ⟨k11, k01⟩ := hw'
  have hvE : v = hermDiag l hF ((v : Matrix (Fin 2) (Fin 2) F) 0 0)
      (hermA_00 (a := l) v) := eq_hermDiag_of_mem_herm1101 (hF := hF) v ⟨h11, h01⟩
  have hwE : w = hermDiag l hF ((w : Matrix (Fin 2) (Fin 2) F) 0 0)
      (hermA_00 (a := l) w) := eq_hermDiag_of_mem_herm1101 (hF := hF) w ⟨k11, k01⟩
  have ha0 : (v : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h
    apply hv0
    rw [hvE]
    apply Subtype.ext
    have hD : (hermDiag l hF ((v : Matrix (Fin 2) (Fin 2) F) 0 0) (hermA_00 (a := l) v) :
        Matrix (Fin 2) (Fin 2) F) = !![(v : Matrix (Fin 2) (Fin 2) F) 0 0, 0; 0, 0] := rfl
    rw [hD]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h]
  have hb0 : (w : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h
    apply hw0
    rw [hwE]
    apply Subtype.ext
    have hD : (hermDiag l hF ((w : Matrix (Fin 2) (Fin 2) F) 0 0) (hermA_00 (a := l) w) :
        Matrix (Fin 2) (Fin 2) F) = !![(w : Matrix (Fin 2) (Fin 2) F) 0 0, 0; 0, 0] := rfl
    rw [hD]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h]
  obtain ⟨c, hc0, hc⟩ := exists_mul_sig_mul_eq (hF := hF)
    ((v : Matrix (Fin 2) (Fin 2) F) 0 0) ((w : Matrix (Fin 2) (Fin 2) F) 0 0)
    (hermA_00 (a := l) v) (hermA_00 (a := l) w) ha0 hb0
  refine ⟨tMat c hc0, tMat_mem_normalizer (F := F) c hc0, ?_⟩
  rw [hvE, hwE, hermRep_apply,
    hermAct_tMat_hermDiag (hF := hF) c hc0 ((v : Matrix (Fin 2) (Fin 2) F) 0 0)
      (hermA_00 (a := l) v)]
  apply Subtype.ext
  change (!![c * c ^ 2 ^ l * (v : Matrix (Fin 2) (Fin 2) F) 0 0, 0; 0, 0] :
    Matrix (Fin 2) (Fin 2) F) = !![(w : Matrix (Fin 2) (Fin 2) F) 0 0, 0; 0, 0]
  rw [hc]


end CFSG.RankThree.GF2n.Tim81.Sec2
