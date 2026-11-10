module

public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedQuaternion
public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreQuotient
public import CFSG.ClassicalInvolution.Balance.BootstrapTriple
public import CFSG.ClassicalInvolution.Balance.PassTwoConj

public section

namespace CFSG.ClassicalInvolution.Generic.TypeCSetup

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem quaternion_aux (N m : ℕ) [NeZero N] (hN : N = 2 * m) :
    ((QuaternionGroup.xa 0 : QuaternionGroup N) * QuaternionGroup.xa 0 =
        QuaternionGroup.a (N : ZMod (2 * N))) ∧
      (QuaternionGroup.a (m : ZMod (2 * N)) * QuaternionGroup.xa 0 =
        QuaternionGroup.xa 0 * QuaternionGroup.a (N : ZMod (2 * N)) *
          QuaternionGroup.a (m : ZMod (2 * N))) := by
  subst hN
  refine ⟨?_, ?_⟩
  · rw [QuaternionGroup.xa_mul_xa]
    simp
  · rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_a]
    congr 1
    have h2 : ((2 * m : ℕ) : ZMod (2 * (2 * m))) + ((2 * m : ℕ) : ZMod (2 * (2 * m))) = 0 := by
      have : ((2 * m + 2 * m : ℕ) : ZMod (2 * (2 * m))) = 0 := by
        have h : 2 * m + 2 * m = 2 * (2 * m) := by ring
        rw [h]
        exact ZMod.natCast_self _
      simpa using this
    have h3 : ((2 * m : ℕ) : ZMod (2 * (2 * m))) =
        (m : ZMod (2 * (2 * m))) + (m : ZMod (2 * (2 * m))) := by
      push_cast
      ring
    rw [zero_sub, zero_add]
    have h4 : ((2 * m : ℕ) : ZMod (2 * (2 * m))) + (m : ZMod (2 * (2 * m))) +
        (m : ZMod (2 * (2 * m))) = 0 := by
      rw [add_assoc, ← h3]
      exact h2
    linear_combination (-1 : ZMod (2 * (2 * m))) * h4

theorem exists_sq_eq_involution [Finite G] {K : Subgroup G} {z : G} (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hz : IsClassicalMember p f K z) :
    ∃ t w : G, t ∈ K ∧ w ∈ K ∧ t * t = z ∧ w * t = t * z * w := by
  classical
  set z' : ↥K := ⟨z, hz.mem⟩ with hz'
  have hz'2 : orderOf z' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hz.orderOf_eq_two
  have hP : IsPGroup 2 (Subgroup.zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'2]; simp)
  obtain ⟨T, hT⟩ := hP.exists_le_sylow
  have hzT : z' ∈ (T : Subgroup ↥K) := hT (Subgroup.mem_zpowers z')
  obtain ⟨r, hr, ⟨e⟩⟩ :=
    CFSG.ClassicalInvolution.Disconnected.quaternion_sylow_of_isClassicalMember hp2 hq hz T
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℕ, 0 < m ∧ 2 ^ (r - 2) = 2 * m := by
    refine ⟨2 ^ (r - 3), pow_pos (by norm_num) _, ?_⟩
    have : r - 2 = (r - 3) + 1 := by omega
    rw [this, pow_succ]
    ring
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
  obtain ⟨hsq, hcomm⟩ := quaternion_aux (2 ^ (r - 2)) m hm
  set zT : ↥(T : Subgroup ↥K) := ⟨z', hzT⟩ with hzT'
  have hzT2 : orderOf zT = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hz'2
  have hez : e zT = QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))) :=
    CFSG.ClassicalInvolution.QuaternionStructure.quaternionGroup_eq_a_of_orderOf_eq_two
      ((e.orderOf_eq zT).trans hzT2)
  have h1 : e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.xa 0) = zT := by
    apply e.injective
    rw [map_mul, MulEquiv.apply_symm_apply, hsq, hez]
  have h2 : e.symm (QuaternionGroup.a (m : ZMod (2 * 2 ^ (r - 2)))) *
      e.symm (QuaternionGroup.xa 0) = e.symm (QuaternionGroup.xa 0) * zT *
        e.symm (QuaternionGroup.a (m : ZMod (2 * 2 ^ (r - 2)))) := by
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply, hez]
    exact hcomm
  refine ⟨(((e.symm (QuaternionGroup.xa 0) : ↥(T : Subgroup ↥K)) : ↥K) : G),
    (((e.symm (QuaternionGroup.a (m : ZMod (2 * 2 ^ (r - 2)))) : ↥(T : Subgroup ↥K)) : ↥K) : G),
    ((e.symm (QuaternionGroup.xa 0) : ↥(T : Subgroup ↥K)) : ↥K).2,
    ((e.symm (QuaternionGroup.a (m : ZMod (2 * 2 ^ (r - 2)))) : ↥(T : Subgroup ↥K)) : ↥K).2,
    ?_, ?_⟩
  · have := congrArg (fun x : ↥(T : Subgroup ↥K) => ((x : ↥K) : G)) h1
    simpa [zT, z'] using this
  · have := congrArg (fun x : ↥(T : Subgroup ↥K) => ((x : ↥K) : G)) h2
    simpa [zT, z', mul_assoc] using this

section Edge

variable [Finite G]


end Edge

section Triple


theorem mem_closure_pair {x y g : G} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)
    (hg : g ∈ Subgroup.closure ({x, y} : Set G)) : g = 1 ∨ g = x ∨ g = y ∨ g = x * y := by
  have c : y * x = x * y := hxy.symm
  have s1' : ∀ b, x * (x * b) = b := fun b => by rw [← mul_assoc, hx, one_mul]
  have c' : ∀ b, y * (x * b) = x * (y * b) := fun b => by rw [← mul_assoc, c, mul_assoc]
  have i1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have i2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  refine Subgroup.closure_induction
    (p := fun g _ => g = 1 ∨ g = x ∨ g = y ∨ g = x * y) ?_ ?_ ?_ ?_ hg
  · intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with hu | hu <;> subst hu <;> simp
  · simp
  · rintro a b - - (ha | ha | ha | ha) (hb | hb | hb | hb) <;> subst ha <;> subst hb <;>
      simp [mul_assoc, hx, hy, s1', c, c']
  · rintro a - (ha | ha | ha | ha) <;> subst ha <;> simp [i1, i2, c]


structure DepTriple (p f : ℕ) [Fact p.Prime] (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ : G) : Prop where
  cls₁ : IsClassicalMember p f K₁ z₁
  cls₂ : IsClassicalMember p f K₂ z₂
  cls₃ : IsClassicalMember p f K₃ z₃
  comm₁₂ : Commutes K₁ K₂
  comm₁₃ : Commutes K₁ K₃
  comm₂₃ : Commutes K₂ K₃
  ne : z₁ ≠ z₂
  prod : z₁ * z₂ = z₃

variable {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}

namespace DepTriple

theorem sq₁ (T : DepTriple p f K₁ K₂ K₃ z₁ z₂ z₃) : z₁ * z₁ = 1 := T.cls₁.isCentralInvolution.sq

theorem sq₂ (T : DepTriple p f K₁ K₂ K₃ z₁ z₂ z₃) : z₂ * z₂ = 1 := T.cls₂.isCentralInvolution.sq

theorem sq₃ (T : DepTriple p f K₁ K₂ K₃ z₁ z₂ z₃) : z₃ * z₃ = 1 := T.cls₃.isCentralInvolution.sq


end DepTriple

@[expose] def axis (z₁ z₂ t₁ t₂ t₃ : G) : Subgroup G :=
  Subgroup.closure ({z₁, z₂, t₁ * t₂ * t₃} : Set G)


end Triple

end CFSG.ClassicalInvolution.Generic.TypeCSetup
