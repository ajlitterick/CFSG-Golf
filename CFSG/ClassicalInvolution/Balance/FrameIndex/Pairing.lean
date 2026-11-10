module

public import CFSG.ClassicalInvolution.Balance.FrameIndex.RootFamily
public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.ClassicalInvolution.Generic
open scoped IsMulCommutative

variable {F : Type*} [Field F] {G : Type*} [Group G]

@[expose] def PairingAdj (E K L : Subgroup G) : Prop :=
  ∃ z, IsUniqueInvolution L z ∧ z ∉ axisSub E K


@[expose] def PairingSymmetric (E : Subgroup G) (S : Set (Subgroup G)) : Prop :=
  ∀ K ∈ S, ∀ L ∈ S, PairingAdj E K L → PairingAdj E L K

@[expose] def PairingConnected (E : Subgroup G) (S : Set (Subgroup G)) : Prop :=
  ∀ K L : ↥S, Relation.ReflTransGen (fun K' L' : ↥S => PairingAdj E K' L') K L

open scoped Classical in
@[expose] noncomputable def axisChar (E K : Subgroup G) (e : G) : ZMod 2 :=
  if e ∈ axisSub E K then 0 else 1

theorem axisChar_of_mem {E K : Subgroup G} {e : G} (h : e ∈ axisSub E K) : axisChar E K e = 0 := by
  simp [axisChar, h]

theorem axisChar_of_not_mem {E K : Subgroup G} {e : G} (h : e ∉ axisSub E K) :
    axisChar E K e = 1 := by
  simp [axisChar, h]

theorem axisChar_eq_zero_iff {E K : Subgroup G} {e : G} : axisChar E K e = 0 ↔ e ∈ axisSub E K := by
  by_cases h : e ∈ axisSub E K
  · simp [axisChar_of_mem h, h]
  · rw [axisChar_of_not_mem h]
    simp [h]


private theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem pairingAdj_iff {E K L : Subgroup G} {z : G} (hz : IsUniqueInvolution L z) :
    PairingAdj E K L ↔ z ∉ axisSub E K := by
  constructor
  · rintro ⟨z', hz', h⟩
    rwa [hz.eq hz']
  · exact fun h => ⟨z, hz, h⟩

section Frame

variable {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}

theorem frame_comm (Fr : ToralFrame F Ω E S) {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    x * y = y * x := by
  have h1 := Fr.elem (x * y) (E.mul_mem hx hy)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (Fr.elem x hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (Fr.elem y hy)
  have hxyi : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h1
  calc x * y = (x * y)⁻¹ := hxyi.symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hxi, hyi]


theorem axisChar_mul_of_frame (Fr : ToralFrame F Ω E S) {K : Subgroup G} (hK : K ∈ S) {x y : G}
    (hx : x ∈ E) (hy : y ∈ E) :
    axisChar E K (x * y) = axisChar E K x + axisChar E K y := by
  obtain ⟨a, haE, haN, hsplit⟩ := (Fr.inSigma hK).exists_split
  by_cases h1 : x ∈ axisSub E K <;> by_cases h2 : y ∈ axisSub E K
  · have h3 : x * y ∈ axisSub E K := (axisSub E K).mul_mem h1 h2
    rw [axisChar_of_mem h3, axisChar_of_mem h1, axisChar_of_mem h2]
    rfl
  · have h3 : x * y ∉ axisSub E K := fun h => h2 (by
      have := (axisSub E K).mul_mem ((axisSub E K).inv_mem h1) h
      simpa using this)
    rw [axisChar_of_not_mem h3, axisChar_of_mem h1, axisChar_of_not_mem h2]
    simp
  · have h3 : x * y ∉ axisSub E K := fun h => h1 (by
      have := (axisSub E K).mul_mem h ((axisSub E K).inv_mem h2)
      simpa using this)
    rw [axisChar_of_not_mem h3, axisChar_of_not_mem h1, axisChar_of_mem h2]
    simp
  · have hxa : x * a ∈ axisSub E K := (hsplit x hx).resolve_left h1
    have hya : y * a ∈ axisSub E K := (hsplit y hy).resolve_left h2
    have h3 : x * y ∈ axisSub E K := by
      have h4 := (axisSub E K).mul_mem hxa hya
      have e1 : x * a * (y * a) = x * y := by
        calc x * a * (y * a) = x * (a * y) * a := by group
          _ = x * (y * a) * a := by rw [frame_comm Fr haE hy]
          _ = x * y * (a * a) := by group
          _ = x * y := by rw [Fr.elem a haE, mul_one]
      rwa [e1] at h4
    rw [axisChar_of_mem h3, axisChar_of_not_mem h1, axisChar_of_not_mem h2]
    decide


theorem frame_conj_inv_of_not_mem_axis (Fr : ToralFrame F Ω E S) {K : Subgroup G}
    (hK : K ∈ S) {zK : G} (hzK : IsUniqueInvolution K zK) {w : G} (hw : w ∈ normPart K E)
    (hw' : w ∉ centPart K E) {e : G} (he : e ∈ E) (hn : e ∉ axisSub E K) :
    w⁻¹ * e * w = e * zK := by
  have := Fr.finite
  have h1 : w * e * w⁻¹ = e * zK :=
    (Fr.inSigma hK).conj_eq_mul_of_not_mem_axis Fr.odd hzK hw hw' he hn
  have h2 : w * w = zK := (Fr.inSigma hK).sq_eq_of_mem Fr.odd hzK hw hw'
  have h4 : w⁻¹ * zK * w = zK := by
    rw [← h2]
    group
  have h5 : w⁻¹ * (e * zK) * w = e := by
    rw [← h1]
    group
  have h6 : w⁻¹ * (e * zK) * w = (w⁻¹ * e * w) * (w⁻¹ * zK * w) := by group
  rw [h6, h4] at h5
  calc w⁻¹ * e * w = (w⁻¹ * e * w) * (zK * zK) := by rw [hzK.sq, mul_one]
    _ = ((w⁻¹ * e * w) * zK) * zK := (mul_assoc _ _ _).symm
    _ = e * zK := by rw [h5]

theorem axisChar_conjSub (Fr : ToralFrame F Ω E S) {K L : Subgroup G} (hK : K ∈ S)
    (hL : L ∈ S) {zK : G} (hzK : IsUniqueInvolution K zK) {w : G} (hw : w ∈ normPart K E)
    (hw' : w ∉ centPart K E) {e : G} (he : e ∈ E) :
    axisChar E (conjSub w L) e = axisChar E L e + axisChar E L zK * axisChar E K e := by
  have := Fr.finite
  have hwN : w ∈ Subgroup.normalizer (E : Set G) := (mem_normPart_iff.mp hw).2
  have hzKE : zK ∈ E := Fr.mem_of_isUniqueInvolution hK hzK
  have key : e ∈ axisSub E (conjSub w L) ↔ w⁻¹ * e * w ∈ axisSub E L := by
    rw [axisSub_conjSub hwN L, mem_conjSub_iff]
  have h1 : axisChar E (conjSub w L) e = axisChar E L (w⁻¹ * e * w) := by
    by_cases h : w⁻¹ * e * w ∈ axisSub E L
    · rw [axisChar_of_mem h, axisChar_of_mem (key.mpr h)]
    · rw [axisChar_of_not_mem h, axisChar_of_not_mem (fun h' => h (key.mp h'))]
  rw [h1]
  by_cases he' : e ∈ axisSub E K
  · have h2 : w⁻¹ * e * w = e := by
      have := InSigma.conj_eq_of_mem_axis (K.inv_mem (normPart_le_left K E hw)) he'
      simpa using this
    rw [h2, axisChar_of_mem he', mul_zero, add_zero]
  · rw [frame_conj_inv_of_not_mem_axis Fr hK hzK hw hw' he he',
      axisChar_mul_of_frame Fr hL he hzKE, axisChar_of_not_mem he', mul_one]


section Construction

variable (Fr : ToralFrame F Ω E S)

private noncomputable def frameZg (K : ↥S) : G :=
  Classical.choose (Fr.exists_isUniqueInvolution K.2)

private theorem isUniqueInvolution_frameZg (K : ↥S) :
    IsUniqueInvolution (K : Subgroup G) (frameZg Fr K) :=
  Classical.choose_spec (Fr.exists_isUniqueInvolution K.2)

private theorem frameZg_mem (K : ↥S) : frameZg Fr K ∈ E :=
  Fr.mem_of_isUniqueInvolution K.2 (isUniqueInvolution_frameZg Fr K)

private noncomputable def frameZ (K : ↥S) : Additive ↥E :=
  Additive.ofMul ⟨frameZg Fr K, frameZg_mem Fr K⟩


end Construction


end Frame

end CFSG.ClassicalInvolution.Balance
