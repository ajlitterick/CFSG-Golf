module

public import CFSG.RankThree.GroupTheory.ThetaComponents
public import CFSG.RankThree.GroupTheory.SteinbergCECentralQuotientCore
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open scoped commutatorElement Pointwise

theorem commutatorElement_mul_of_mem_center_left {X : Type*} [Group X] (a b : X) {k : X}
    (hk : k ∈ Subgroup.center X) : ⁅a * k, b⁆ = ⁅a, b⁆ := by
  have hkb : k * b = b * k := (Subgroup.mem_center_iff.mp hk b).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * k * b * (a * k)⁻¹ * b⁻¹ = a * (k * b) * k⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * k) * k⁻¹ * a⁻¹ * b⁻¹ := by rw [hkb]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_of_mem_center_right {X : Type*} [Group X] (a b : X) {k : X}
    (hk : k ∈ Subgroup.center X) : ⁅a, b * k⁆ = ⁅a, b⁆ := by
  have hka : k * a⁻¹ = a⁻¹ * k := (Subgroup.mem_center_iff.mp hk a⁻¹).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * k) * a⁻¹ * (b * k)⁻¹ = a * b * (k * a⁻¹) * k⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * k) * k⁻¹ * b⁻¹ := by rw [hka]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutator_sup_eq_of_le_center {X : Type*} [Group X] (L K : Subgroup X)
    (hK : K ≤ Subgroup.center X) : ⁅L ⊔ K, L ⊔ K⁆ = ⁅L, L⁆ := by
  have : K.Normal := Subgroup.normal_of_le_center hK
  refine le_antisymm ?_ (Subgroup.commutator_mono le_sup_left le_sup_left)
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have ha' : a ∈ (L : Set X) * (K : Set X) := by rw [← Subgroup.mul_normal]; exact ha
  have hb' : b ∈ (L : Set X) * (K : Set X) := by rw [← Subgroup.mul_normal]; exact hb
  obtain ⟨l, hl, k, hk, rfl⟩ := ha'
  obtain ⟨l', hl', k', hk', rfl⟩ := hb'
  rw [commutatorElement_mul_of_mem_center_left _ _ (hK hk),
    commutatorElement_mul_of_mem_center_right _ _ (hK hk')]
  exact Subgroup.commutator_mem_commutator hl hl'

theorem isQuasisimple_thetaQuotient_iff_of_surjective {L M : Type*} [Group L] [Group M]
    [Finite L] [Finite M] {p : ℕ} (hp : p.Prime) (hL : Group.IsPerfect L) (g : L →* M)
    (hg : Function.Surjective g) (hker : g.ker ≤ Subgroup.center L) :
    IsQuasisimple (L ⧸ aschbacherSolvableCore p L) ↔
      IsQuasisimple (M ⧸ aschbacherSolvableCore p M) := by
  have hθ := central_quotient_solvable_prime_complement_core hp g hg hker
  have hle : aschbacherSolvableCore p L ≤ (aschbacherSolvableCore p M).comap g := by
    rw [← hθ]
    exact Subgroup.le_comap_map _ _
  set gbar := QuotientGroup.map _ _ g hle
  have hsurj : Function.Surjective gbar :=
    QuotientGroup.map_surjective_of_surjective _ _ g ((QuotientGroup.mk_surjective).comp hg) hle
  have := hL
  refine LocalCores.isQuasisimple_iff_of_surjective inferInstance gbar hsurj fun x hx => ?_
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MonoidHom.mem_ker, QuotientGroup.map_mk, QuotientGroup.eq_one_iff, ← hθ] at hx
  obtain ⟨t, ht, hgt⟩ := hx
  have hlt : l * t⁻¹ ∈ g.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgt, mul_inv_cancel]
  have heq : (l : L ⧸ aschbacherSolvableCore p L) = ((l * t⁻¹ : L) : L ⧸ _) := by
    rw [QuotientGroup.eq]
    simpa using inv_mem ht
  rw [heq, Subgroup.mem_center_iff]
  intro y
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp (hker hlt) y']


end CFSG.RankThree.GroupTheory.SteinbergBY
