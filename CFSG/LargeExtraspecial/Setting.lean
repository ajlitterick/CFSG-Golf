module

public import CFSG.RankThree.Literature.FSmithForm
public import CFSG.GroupTheory.ExtraspecialCentralizerInnerAut
public import CFSG.Assembly.LowTwoRankDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup QuadraticMap CFSG.RankThree.Literature.FSmith

structure Setting (G : Type*) [Group G] where
  z : G
  orderOf_z : orderOf z = 2
  Q : Subgroup (centralizer ({z} : Set G))
  normal : Q.Normal
  extraspecial : IsExtraspecialPGroup 2 Q
  centralizer_le : centralizer (Q : Set (centralizer ({z} : Set G))) ≤ Q
  le_of_normal : ∀ P : Subgroup (centralizer ({z} : Set G)), P.Normal → IsPGroup 2 P → P ≤ Q

namespace Setting

variable {G : Type*} [Group G] (S : Setting G)

abbrev M : Subgroup G := centralizer ({S.z} : Set G)

@[expose] def zM : S.M := ⟨S.z, mem_centralizer_singleton_iff.mpr rfl⟩

@[simp] theorem coe_zM : (S.zM : G) = S.z := rfl

theorem z_ne_one : S.z ≠ 1 := by
  intro h
  have := S.orderOf_z
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem z_mul_z : S.z * S.z = 1 := by
  rw [← pow_two, ← S.orderOf_z, pow_orderOf_eq_one]

theorem zM_mem_center : S.zM ∈ center S.M :=
  mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)

theorem zM_mem_Q : S.zM ∈ S.Q :=
  S.centralizer_le (mem_centralizer_iff.mpr fun g _ => (mem_center_iff.mp S.zM_mem_center g))

@[expose] def QG : Subgroup G := S.Q.map S.M.subtype

theorem QG_le_M : S.QG ≤ S.M := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem z_mem_QG : S.z ∈ S.QG := ⟨S.zM, S.zM_mem_Q, rfl⟩

theorem mem_QG_iff {x : G} : x ∈ S.QG ↔ ∃ h : x ∈ S.M, (⟨x, h⟩ : S.M) ∈ S.Q := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

@[expose] def zQ : S.Q := ⟨S.zM, S.zM_mem_Q⟩

theorem zQ_mem_center : S.zQ ∈ center S.Q :=
  mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp S.zM_mem_center g)

theorem zQ_ne_one : S.zQ ≠ 1 := fun h => S.z_ne_one (congrArg (fun x : S.Q => ((x : S.M) : G)) h)


theorem mem_center_Q_iff {x : S.Q} : x ∈ center S.Q ↔ x = 1 ∨ x = S.zQ := by
  constructor
  · intro hx
    by_cases h1 : x = 1
    · exact Or.inl h1
    · exact Or.inr (eq_of_mem_center S.extraspecial hx S.zQ_mem_center h1 S.zQ_ne_one)
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact S.zQ_mem_center

instance instModuleQt : Module (ZMod 2) (Additive (Abelianization S.Q)) :=
  CFSG.GroupTheory.extraspecialQuotientModule S.extraspecial

abbrev Qt : Type _ := Additive (Abelianization S.Q)

@[expose] def toQt (x : S.Q) : S.Qt := Additive.ofMul (Abelianization.of x)

theorem toQt_mul (x y : S.Q) : S.toQt (x * y) = S.toQt x + S.toQt y := by
  simp [toQt]

theorem toQt_inv (x : S.Q) : S.toQt x⁻¹ = -S.toQt x := by
  simp [toQt]

theorem toQt_one : S.toQt 1 = 0 := by
  simp [toQt]

theorem exists_toQt (v : S.Qt) : ∃ x : S.Q, S.toQt x = v := exists_ofMul_of v

theorem toQt_eq_zero_iff (x : S.Q) : S.toQt x = 0 ↔ x ∈ center S.Q :=
  ofMul_of_eq_zero_iff S.extraspecial x

theorem toQt_eq_zero_iff' (x : S.Q) : S.toQt x = 0 ↔ x = 1 ∨ x = S.zQ := by
  rw [toQt_eq_zero_iff, mem_center_Q_iff]

variable [Finite G]

noncomputable abbrev q : QuadraticForm (ZMod 2) S.Qt := extraspecialQuadForm S.extraspecial

theorem q_toQt_eq_zero_iff (x : S.Q) : S.q (S.toQt x) = 0 ↔ x ^ 2 = 1 := by
  change extraspecialQuadForm S.extraspecial (Additive.ofMul (Abelianization.of x)) = 0 ↔ _
  rw [extraspecialQuadForm_apply]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' h⟩


theorem polar_q_toQt_eq_zero_iff (x y : S.Q) :
    polar S.q (S.toQt x) (S.toQt y) = 0 ↔ x * y = y * x :=
  polar_extraspecialQuadForm_eq_zero_iff S.extraspecial x y

theorem q_nondegenerate : S.q.polarBilin.Nondegenerate :=
  extraspecialQuadForm_nondegenerate S.extraspecial

noncomputable abbrev O : Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt) := TauCeti.QuadraticMap.orthogonalGroup S.q

@[expose] noncomputable def ρ : S.M →* S.O := extraspecialConjOrth S.extraspecial S.normal

theorem ρ_toQt (g : S.M) (x : S.Q) :
    ((S.ρ g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.toQt x) =
      S.toQt (conjAut S.normal g x) := rfl

theorem mem_Q_of_ρ_eq_one {g : S.M} (hg : S.ρ g = 1) : g ∈ S.Q :=
  mem_of_extraspecialConjOrth_eq_one S.extraspecial S.normal S.centralizer_le hg

theorem ρ_eq_one_of_mem_Q {g : S.M} (hg : g ∈ S.Q) : S.ρ g = 1 := by
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  obtain ⟨x, rfl⟩ := S.exists_toQt v
  change S.toQt (conjAut S.normal g x) = S.toQt x
  have h : conjAut S.normal g x = ⟨g, hg⟩ * x * (⟨g, hg⟩ : S.Q)⁻¹ :=
    Subtype.ext (by rw [conjAut_apply]; rfl)
  rw [h, S.toQt_mul, S.toQt_mul, S.toQt_inv]
  abel

theorem ker_ρ : S.ρ.ker = S.Q :=
  le_antisymm (fun _ hg => S.mem_Q_of_ρ_eq_one hg) (fun _ hg => S.ρ_eq_one_of_mem_Q hg)

@[expose] noncomputable def Mbar : Subgroup S.O := S.ρ.range

theorem zQ_mul_zQ : S.zQ * S.zQ = 1 := Subtype.ext (Subtype.ext S.z_mul_z)

theorem zpowers_zQ_le_center : Subgroup.zpowers S.zQ ≤ center S.Q :=
  Subgroup.zpowers_le.mpr S.zQ_mem_center

theorem center_le_zpowers_zQ : center S.Q ≤ Subgroup.zpowers S.zQ := by
  intro x hx
  rw [mem_center_Q_iff] at hx
  rcases hx with rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩

theorem center_Q_eq_zpowers_setting : center S.Q = Subgroup.zpowers S.zQ :=
  le_antisymm S.center_le_zpowers_zQ S.zpowers_zQ_le_center

theorem card_center_Q : Nat.card (center S.Q) = 2 := by
  rw [S.center_Q_eq_zpowers_setting, Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact S.zQ_mul_zQ) S.zQ_ne_one

def conjHom : S.M →* MulAut S.Q := by
  letI := S.normal
  exact MulAut.conjNormal


end Setting

end CFSG.LargeExtraspecial
