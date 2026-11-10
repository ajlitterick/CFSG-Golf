module

public import CFSG.CharacterTheory.Semidihedral.ActualSimpleLayerLocalPackage

public noncomputable section

namespace CFSG.Semidihedral.LocalProjectiveKernelQuotients

open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

universe u

variable {G : Type u} [Group G]

abbrev originalCentralizerSubgroup (i : G) (W : Subgroup G) : Subgroup (C i) :=
  W.comap (C i).subtype

abbrev originalProjectiveComposite (i : G) : C i →* Gamma i :=
  (barKappa i).comp (nu i)

abbrev originalLayer (i : G) : Subgroup (Gamma i) :=
  CFSG.generalizedFitting (Gamma i)

abbrev originalLayerPreimage (i : G) : Subgroup (C i) :=
  ((originalLayer i).comap (barKappa i)).comap (nu i)

abbrev originalAmbientLayerPreimage (i : G) : Subgroup G :=
  (originalLayerPreimage i).map (C i).subtype

abbrev originalAmbientOddCore (i : G) : Subgroup G :=
  (N i).map (C i).subtype


@[expose] def originalCentralizerEquiv (i : G) (W : Subgroup G) (hWC : W ≤ C i) :
    W ≃* originalCentralizerSubgroup i W where
  toFun w := ⟨Subgroup.inclusion hWC w, w.property⟩
  invFun w := ⟨((w : C i) : G), w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl


@[expose] def originalProjectiveRestriction (i : G) (W : Subgroup G) (hWC : W ≤ C i) :
    W →* Gamma i :=
  (originalProjectiveComposite i).comp (Subgroup.inclusion hWC)


theorem original_mem_ambientLayerPreimage (i : G) (x : C i) :
    (x : G) ∈ originalAmbientLayerPreimage i ↔ x ∈ originalLayerPreimage i := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (Subtype.ext hxy : y = x) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩


theorem original_odd_projective_eq_one_iff (i : G) (hi : orderOf i = 2)
    (W : Subgroup G) (hodd : Odd (Nat.card W)) (x : C i) (hxW : (x : G) ∈ W) :
    originalProjectiveComposite i x = 1 ↔ x ∈ N i := by
  constructor
  · intro hx
    have hq : nu i x ∈ Subgroup.zpowers (nu i (tInC i)) := by
      rw [← barKappa_kernel i]
      exact hx
    have hiC : orderOf (tInC i) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hi
    have htwo : orderOf (nu i x) ∣ 2 :=
      (orderOf_dvd_of_mem_zpowers hq).trans
        ((orderOf_map_dvd (nu i) (tInC i)).trans (dvd_of_eq hiC))
    have hcard : orderOf (nu i x) ∣ Nat.card W :=
      (orderOf_map_dvd (nu i) x).trans (by
        rw [← Subgroup.orderOf_coe]
        exact W.orderOf_dvd_natCard hxW)
    have horder : orderOf (nu i x) = 1 :=
      Nat.eq_one_of_dvd_coprimes hodd.coprime_two_left htwo hcard
    exact (QuotientGroup.eq_one_iff (N := N i) x).mp (orderOf_eq_one_iff.mp horder)
  · intro hx
    have hnu : nu i x = 1 := (QuotientGroup.eq_one_iff (N := N i) x).mpr hx
    change barKappa i (nu i x) = 1
    rw [hnu, map_one]

theorem originalProjectiveRestriction_ker (i : G) (hi : orderOf i = 2)
    (W : Subgroup G) (hWC : W ≤ C i) (hodd : Odd (Nat.card W)) :
    (originalProjectiveRestriction i W hWC).ker = (N i).comap (Subgroup.inclusion hWC) := by
  ext w
  exact original_odd_projective_eq_one_iff i hi W hodd (Subgroup.inclusion hWC w) w.property


@[expose] def originalLayerRestriction (i : G) (W : Subgroup G) (hWC : W ≤ C i)
    (hWY : W ≤ originalAmbientLayerPreimage i) : W →* originalLayer i :=
  (originalProjectiveRestriction i W hWC).codRestrict (originalLayer i) fun w =>
    (original_mem_ambientLayerPreimage i (Subgroup.inclusion hWC w)).mp (hWY w.property)


theorem originalLayerRestriction_ker (i : G) (W : Subgroup G) (hWC : W ≤ C i)
    (hWY : W ≤ originalAmbientLayerPreimage i) :
    (originalLayerRestriction i W hWC hWY).ker =
      (originalProjectiveRestriction i W hWC).ker := by
  exact MonoidHom.ker_codRestrict _ _ _


end CFSG.Semidihedral.LocalProjectiveKernelQuotients
