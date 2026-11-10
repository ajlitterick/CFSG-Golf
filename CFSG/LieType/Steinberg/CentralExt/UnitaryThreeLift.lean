module

public import CFSG.LieType.Steinberg.CentralExt.UnitaryLift
public import CFSG.LieType.Steinberg.CentralExt.UnitaryGram
public import CFSG.LieType.Steinberg.CentralExt.PerfectLift
public import CFSG.LieType.Steinberg.CentralExt.UnitaryPerfect
public import CFSG.ClassicalGroups.Unitary.Perfect
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.LieType.Steinberg.CentralExt.HermitianBasis

public section

namespace CFSG.LieType.Steinberg

open CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.LocalAnalysis.ComponentInitial

section Quotient

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

local notation "σ₀" => unitaryInvolution K p f

theorem pow_ne_two_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (f : ℕ) : p ^ f ≠ 2 := by
  intro h
  rcases f with _ | f
  · simp at h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (h ▸ dvd_pow_self p (Nat.succ_ne_zero f)))

theorem isPerfect_SU_three (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) :
    Group.IsPerfect (SU σ₀ 3) := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hK 3
  have : Group.IsPerfect (SUid σ₀ 3) := CFSG.ClassicalGroups.Unitary.isPerfect_SUid
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK) le_rfl
    fun _ => CFSG.ClassicalGroups.Unitary.exists_norm_ne_one hK
      (pow_ne_two_of_ne_two Fact.out hp2 f)
  exact Group.IsPerfect.ofSurjective (f := (conjEquiv P hP).symm.toMonoidHom)
    (conjEquiv P hP).symm.surjective


omit [Finite K] in
theorem pow_three_eq_one_of_mem_statedScalars {S : Subgroup (GL (Fin 3) K)}
    (hS : ∀ x ∈ S, (x : Matrix (Fin 3) (Fin 3) K).det = 1) {x : S}
    (hx : x ∈ (StatedScalars (Fin 3) K).subgroupOf S) : x ^ 3 = 1 := by
  obtain ⟨c, hc⟩ : (x : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := hx
  have hdet := hS x x.2
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  have hc3 : c ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hdet)
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, ← hc, ← map_pow, hc3, map_one, Subgroup.coe_one]

universe w in

end Quotient

section Hermitian

variable {p f : ℕ} {K : Type} [Field K]

theorem unitaryFieldData_bar_eq (hK : UnitaryFieldData p f K) [Finite K] [Fact p.Prime]
    [CharP K p] :
    hK.bar = (unitaryInvolution K p f).toRingHom :=
  RingHom.ext fun c => (hK.bar_apply c).trans (unitaryInvolution_apply K p f c).symm

theorem card_eq_sq_of_unitaryFieldData (hK : UnitaryFieldData p f K) :
    Nat.card K = (p ^ f) ^ 2 := by
  rw [hK.card, ← pow_mul, mul_comm]

theorem nonempty_SUgram_mulEquiv (hK : UnitaryFieldData p f K) [Finite K]
    [Fact p.Prime] [CharP K p] {n : ℕ} {G₀ : Matrix (Fin n) (Fin n) K}
    (hG : ∀ i j, hK.bar (G₀ j i) = G₀ i j) (hdet : G₀.det ≠ 0) :
    Nonempty (SUgram hK.bar G₀ ≃* SU (unitaryInvolution K p f) n) := by
  have hF := card_eq_sq_of_unitaryFieldData hK
  have hGσ : conjTr (unitaryInvolution K p f) G₀ = G₀ := by
    ext i j
    rw [← hG i j, unitaryFieldData_bar_eq hK]
    rfl
  obtain ⟨P, hP⟩ := exists_conjTr_mul_mul_eq_one hF hGσ hdet
  obtain ⟨P', hP'⟩ := exists_wittMatrix hF n
  have hS : SUgram hK.bar G₀ = SUgram (unitaryInvolution K p f).toRingHom G₀ := by
    rw [unitaryFieldData_bar_eq hK]
  exact ⟨((MulEquiv.subgroupCongr hS).trans ((gramEquiv (τ := (unitaryInvolution K p f).toRingHom)
    (G₁ := 1) P hP).trans (MulEquiv.subgroupCongr (SUgram_one _)))).trans
      (conjEquiv P' hP').symm⟩

theorem det_eq_one_of_mem_SUgram {τ : K →+* K} {n : ℕ} {G₀ : Matrix (Fin n) (Fin n) K}
    {x : GL (Fin n) K} (hx : x ∈ SUgram τ G₀) : (x : Matrix (Fin n) (Fin n) K).det = 1 :=
  hx.1


universe w in

universe v w in

end Hermitian

end CFSG.LieType.Steinberg
