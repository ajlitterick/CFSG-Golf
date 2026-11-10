module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2
public import CFSG.CharacterTheory.Semidihedral.QuaternionDoubleCoverUniqueness

public section

namespace CFSG.Semidihedral.ProjectiveSL2Cover

open Matrix
open CFSG.Assembly.LowTwoRank

universe u v

section NativeScalarQuotient

variable (F : Type u) [Field F]

@[expose] def minusIdentity : SpecialLinearGroup (Fin 2) F :=
  ⟨Matrix.scalar (Fin 2) (-1), by simp⟩

theorem minusIdentity_matrix :
    (minusIdentity F : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (-1) := rfl

theorem minusIdentity_eq_neg_one :
    minusIdentity F = (-1 : SpecialLinearGroup (Fin 2) F) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [minusIdentity]

theorem minusIdentity_square : (minusIdentity F) ^ 2 = 1 := by
  apply Subtype.ext
  change (Matrix.scalar (Fin 2) (-1 : F)) ^ 2 = (1 : Matrix (Fin 2) (Fin 2) F)
  rw [← map_pow]
  simp

theorem minusIdentity_mem_center :
    minusIdentity F ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  exact Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨-1, by simp, rfl⟩

theorem minusIdentity_ne_one (hF : ringChar F ≠ 2) : minusIdentity F ≠ 1 := by
  intro h
  have hentry := congrArg (fun g : SpecialLinearGroup (Fin 2) F => g 0 0) h
  exact Ring.neg_one_ne_one_of_char_ne_two hF (by simpa [minusIdentity] using hentry)

theorem minusIdentity_order (hF : ringChar F ≠ 2) : orderOf (minusIdentity F) = 2 := by
  exact orderOf_eq_prime (minusIdentity_square F) (minusIdentity_ne_one F hF)

theorem mem_center_iff_eq_one_or_minusIdentity (g : SpecialLinearGroup (Fin 2) F) :
    g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ↔
      g = 1 ∨ g = minusIdentity F := by
  constructor
  · intro hg
    obtain ⟨a, ha, hmatrix⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
    have ha2 : a ^ 2 = 1 := by simpa using ha
    rcases sq_eq_one_iff.mp ha2 with rfl | rfl
    · left
      apply Subtype.ext
      simpa using hmatrix.symm
    · right
      exact Subtype.ext hmatrix.symm
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact minusIdentity_mem_center F

theorem center_eq_zpowers_minusIdentity :
    Subgroup.center (SpecialLinearGroup (Fin 2) F) = Subgroup.zpowers (minusIdentity F) := by
  apply le_antisymm
  · intro g hg
    rcases (mem_center_iff_eq_one_or_minusIdentity F g).mp hg with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · exact Subgroup.zpowers_le.mpr (minusIdentity_mem_center F)

theorem center_card (hF : ringChar F ≠ 2) :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) F)) = 2 := by
  rw [center_eq_zpowers_minusIdentity, Nat.card_zpowers, minusIdentity_order F hF]

@[expose] def nativeQuotient :
    SpecialLinearGroup (Fin 2) F →* ProjectiveSpecialLinearGroup (Fin 2) F :=
  QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F))

theorem nativeQuotient_surjective : Function.Surjective (nativeQuotient F) :=
  QuotientGroup.mk'_surjective _

theorem nativeQuotient_ker :
    (nativeQuotient F).ker = Subgroup.zpowers (minusIdentity F) := by
  rw [nativeQuotient, QuotientGroup.ker_mk', center_eq_zpowers_minusIdentity]

theorem nativeQuotient_minusIdentity : nativeQuotient F (minusIdentity F) = 1 := by
  exact (QuotientGroup.eq_one_iff _).mpr (minusIdentity_mem_center F)

theorem quarterTurn_square :
    (CFSG.Semidihedral.OddLinearNormals.quarterTurn F) ^ 2 = minusIdentity F := by
  exact Subtype.ext (CFSG.Semidihedral.OddLinearNormals.quarterTurn_square_matrix F)

end NativeScalarQuotient

section ActualNativeScalarQuotient

variable (F : Type u) [Field F]

@[expose] def nativeScalarKernel (n : ℕ) : Subgroup (SpecialLinearGroup (Fin n) F) :=
  ((GeneralLinearGroup.scalar (Fin n)).range).comap Matrix.SpecialLinearGroup.toGL

theorem nativeScalarKernel_eq_center (n : ℕ) :
    nativeScalarKernel F n = Subgroup.center (SpecialLinearGroup (Fin n) F) := by
  ext g
  change Matrix.SpecialLinearGroup.toGL g ∈ (GeneralLinearGroup.scalar (Fin n)).range ↔ _
  rw [← GeneralLinearGroup.center_eq_range_scalar]
  exact Matrix.SpecialLinearGroup.toGL_mem_center_iff g

instance nativeScalarKernel_normal (n : ℕ) : (nativeScalarKernel F n).Normal := by
  rw [nativeScalarKernel_eq_center]
  infer_instance


theorem nativeScalarKernel_two_eq_zpowers :
    nativeScalarKernel F 2 = Subgroup.zpowers (minusIdentity F) := by
  rw [nativeScalarKernel_eq_center, center_eq_zpowers_minusIdentity]

theorem nativeScalarKernel_two_card (hF : ringChar F ≠ 2) :
    Nat.card (nativeScalarKernel F 2) = 2 := by
  rw [nativeScalarKernel_two_eq_zpowers, Nat.card_zpowers, minusIdentity_order F hF]

abbrev NativeScalarProjective (n : ℕ) :=
  SpecialLinearGroup (Fin n) F ⧸ nativeScalarKernel F n

@[expose] def scalarQuotient (n : ℕ) :
    SpecialLinearGroup (Fin n) F →* NativeScalarProjective F n :=
  QuotientGroup.mk' (nativeScalarKernel F n)

theorem scalarQuotient_surjective (n : ℕ) : Function.Surjective (scalarQuotient F n) :=
  QuotientGroup.mk'_surjective _

theorem scalarQuotient_two_ker :
    (scalarQuotient F 2).ker = Subgroup.zpowers (minusIdentity F) := by
  exact (QuotientGroup.ker_mk' _).trans (nativeScalarKernel_two_eq_zpowers F)

@[expose] def scalarProjectiveEquivNative (n : ℕ) :
    NativeScalarProjective F n ≃* ProjectiveSpecialLinearGroup (Fin n) F :=
  QuotientGroup.quotientMulEquivOfEq (nativeScalarKernel_eq_center F n)


end ActualNativeScalarQuotient

section StatedScalarQuotient

variable (K : Type) [Field K]

@[expose] def statedScalarKernel (n : ℕ) : Subgroup (StatedSL n K) :=
  (StatedScalars (Fin n) K).subgroupOf (StatedSL n K)

instance statedScalarKernel_normal (n : ℕ) : (statedScalarKernel K n).Normal := by
  dsimp only [statedScalarKernel]
  infer_instance

theorem mem_statedSL_iff_det_eq_one (n : ℕ) (A : GL (Fin n) K) :
    A ∈ StatedSL n K ↔ (A : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff


@[expose] noncomputable def statedMinusIdentity : StatedSL 2 K :=
  specialLinearGroupEquivStatedSL 2 K (minusIdentity K)


theorem statedMinusIdentity_order (hK : ringChar K ≠ 2) :
    orderOf (statedMinusIdentity K) = 2 := by
  rw [statedMinusIdentity, (specialLinearGroupEquivStatedSL 2 K).orderOf_eq,
    minusIdentity_order K hK]


theorem statedScalarKernel_eq_center (n : ℕ) :
    statedScalarKernel K n = Subgroup.center (StatedSL n K) := by
  rw [statedScalarKernel, ← map_center_eq_statedScalars]
  exact Subgroup.map_center_eq (specialLinearGroupEquivStatedSL n K)

theorem mem_statedScalarKernel_two_iff (g : StatedSL 2 K) :
    g ∈ statedScalarKernel K 2 ↔ g = 1 ∨ g = statedMinusIdentity K := by
  obtain ⟨a, rfl⟩ := (specialLinearGroupEquivStatedSL 2 K).surjective g
  have hm : specialLinearGroupEquivStatedSL 2 K a ∈ statedScalarKernel K 2 ↔
      a ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
    rw [statedScalarKernel, ← map_center_eq_statedScalars]
    constructor
    · rintro ⟨b, hb, hba⟩
      exact (specialLinearGroupEquivStatedSL 2 K).injective hba ▸ hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  rw [hm, mem_center_iff_eq_one_or_minusIdentity]
  constructor
  · rintro (rfl | rfl)
    · left
      exact map_one _
    · right
      rfl
  · rintro (h | h)
    · left
      apply (specialLinearGroupEquivStatedSL 2 K).injective
      exact h.trans (map_one _).symm
    · right
      exact (specialLinearGroupEquivStatedSL 2 K).injective h


@[expose] noncomputable def scalarProjectiveEquivStated (n : ℕ) :
    NativeScalarProjective K n ≃* StatedProj (StatedSL n K) :=
  (scalarProjectiveEquivNative K n).trans (projectiveSpecialLinearGroupEquivStatedProj n K)


end StatedScalarQuotient

section OriginalProjectionTransport

variable (K : Type) [Field K] {E : Type u} [Group E]


end OriginalProjectionTransport

section OriginalScalarProjectionTransport

variable (F : Type u) [Field F] {E : Type v} [Group E]


end OriginalScalarProjectionTransport

section OriginalCoverCardinality

variable (F : Type u) [Field F] {E : Type v} [Group E]


end OriginalCoverCardinality

section FiniteOddField

variable (F : Type u) [Field F] [Finite F]

theorem odd_card_of_odd_characteristic (hF : ringChar F ≠ 2) : Odd (Nat.card F) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Nat.odd_iff]
  exact FiniteField.odd_card_of_char_ne_two hF


end FiniteOddField

section SuppliedQuaternionSylow

variable {E : Type u} [Group E]


end SuppliedQuaternionSylow

section NativeCover

variable (F : Type u) [Field F] [Finite F] {E : Type v} [Group E] [Finite E]

theorem quaternion_central_double_cover_native
    (hF : ringChar F ≠ 2) (z : E) (hz : orderOf z = 2) (hc : z ∈ Subgroup.center E)
    (pi : E →* ProjectiveSpecialLinearGroup (Fin 2) F) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z)
    (S : Sylow 2 E) (n : ℕ) (hn : 3 ≤ n)
    (e : S ≃* QuaternionGroup (2 ^ (n - 2))) :
    ∃ iso : E ≃* SpecialLinearGroup (Fin 2) F,
      (nativeQuotient F).comp iso.toMonoidHom = pi ∧ iso z = minusIdentity F := by
  let P : Sylow 2 (SpecialLinearGroup (Fin 2) F) := Classical.choice inferInstance
  obtain ⟨m, hm, ⟨f⟩⟩ := OddFieldSL2.sylow_two_quaternion F
    (odd_card_of_odd_characteristic F hF) P
  obtain ⟨_, iso, hpiiso, hziso⟩ :=
    QuaternionDoubleCoverUniqueness.quaternion_sylow_central_double_cover_uniqueness
      z hz hc pi hpi hker S n hn e
      (minusIdentity F) (minusIdentity_order F hF) (minusIdentity_mem_center F)
      (nativeQuotient F) (nativeQuotient_surjective F) (nativeQuotient_ker F)
      P m hm f
  exact ⟨iso, MonoidHom.ext hpiiso, hziso⟩


end NativeCover

section StatedCover


end StatedCover

end CFSG.Semidihedral.ProjectiveSL2Cover
