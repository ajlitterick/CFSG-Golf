module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65SylowCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65Inversion
import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.SignalizerFunctorTheorem.NonLocalExc

private theorem map_injective_of_injective {G N : Type*} [Group G] [Group N]
    (f : G →* N) (hf : Function.Injective f) {H K : Subgroup G}
    (h : H.map f = K.map f) : H = K := by
  apply le_antisymm
  · intro x hx
    exact (Subgroup.mem_map_iff_mem hf).mp (h ▸ Subgroup.mem_map_of_mem f hx)
  · intro x hx
    exact (Subgroup.mem_map_iff_mem hf).mp (h.symm ▸ Subgroup.mem_map_of_mem f hx)

private theorem conj_comp {G : Type*} [Group G] (a b : G) :
    (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj (a * b)).toMonoidHom := by
  ext x
  simp [MulAut.conj_apply, mul_assoc]


theorem sylowCenterWeaklyClosed_of_exists_sylow {Y : Type} [Group Y] [Finite Y]
    (Q₀ : Sylow 3 Y)
    (h : ∀ Z : Subgroup Y, Z ≤ (Q₀ : Subgroup Y) →
      Z ≤ Subgroup.centralizer ((Q₀ : Subgroup Y) : Set Y) → Nat.card Z = 3 →
      ∀ g : Y, CFSG.conjugate Z g ≤ (Q₀ : Subgroup Y) → CFSG.conjugate Z g = Z) :
    SylowCenterWeaklyClosed Y := by
  classical
  unfold SylowCenterWeaklyClosed
  intro Q Z hZQ hZc hZcard g hconj
  obtain ⟨h0, hh0⟩ := MulAction.exists_smul_eq Y Q₀ Q
  have hQ : (Q : Subgroup Y) = (Q₀ : Subgroup Y).map (MulAut.conj h0).toMonoidHom := by
    rw [← hh0, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  let x : Y := h0⁻¹
  have hQc : (Q : Subgroup Y) = CFSG.conjugate (Q₀ : Subgroup Y) x := by
    rw [hQ]
    simp [x, CFSG.conjugate]
  have hcomp : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x⁻¹).toMonoidHom =
      MonoidHom.id Y := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have hQx : (Q : Subgroup Y).map (MulAut.conj x).toMonoidHom = (Q₀ : Subgroup Y) := by
    rw [hQc, CFSG.conjugate, Subgroup.map_map, hcomp, Subgroup.map_id]
  let Z0 : Subgroup Y := Z.map (MulAut.conj x).toMonoidHom
  have hZ0conj : Z0 = CFSG.conjugate Z x⁻¹ := by
    simp [Z0, CFSG.conjugate]
  let g' : Y := x * g * x⁻¹
  have hZ0Q0 : Z0 ≤ (Q₀ : Subgroup Y) := by
    have h1 : Z0 ≤ (Q : Subgroup Y).map (MulAut.conj x).toMonoidHom :=
      Subgroup.map_mono hZQ
    rwa [hQx] at h1
  have hZ0c : Z0 ≤ Subgroup.centralizer ((Q₀ : Subgroup Y) : Set Y) := by
    intro z hz
    obtain ⟨z₀, hz₀Z, rfl⟩ := Subgroup.mem_map.mp hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyQ : x⁻¹ * y * x ∈ (Q : Subgroup Y) := by
      rw [hQc]
      show x⁻¹ * y * x ∈ (Q₀ : Subgroup Y).map (MulAut.conj x⁻¹).toMonoidHom
      rw [Subgroup.mem_map]
      exact ⟨y, hy, by simp⟩
    have hcomm : (x⁻¹ * y * x) * z₀ = z₀ * (x⁻¹ * y * x) :=
      Subgroup.mem_centralizer_iff.mp (hZc hz₀Z) (x⁻¹ * y * x) hyQ
    have hconj := congrArg (fun t => x * t * x⁻¹) hcomm
    simpa [MulAut.conj_apply, mul_assoc] using hconj
  have hZ0card : Nat.card Z0 = 3 := by
    have hZ0 : Z0 = Z.map (MulAut.conj x).toMonoidHom := rfl
    rw [hZ0, Subgroup.card_map_of_injective (f := (MulAut.conj x).toMonoidHom)
      (MulAut.conj x).injective, hZcard]
  have harg : g'⁻¹ * x = x * g⁻¹ := by
    simp only [g']
    group
  have hstep : CFSG.conjugate Z0 g' =
      (CFSG.conjugate Z g).map (MulAut.conj x).toMonoidHom := by
    have hZ0 : Z0 = Z.map (MulAut.conj x).toMonoidHom := rfl
    rw [hZ0, CFSG.conjugate, CFSG.conjugate, Subgroup.map_map, Subgroup.map_map,
      conj_comp, conj_comp, harg]
  have hg' : CFSG.conjugate Z0 g' ≤ (Q₀ : Subgroup Y) := by
    rw [hstep]
    have h2 : (CFSG.conjugate Z g).map (MulAut.conj x).toMonoidHom ≤
        (Q : Subgroup Y).map (MulAut.conj x).toMonoidHom := Subgroup.map_mono hconj
    rwa [hQx] at h2
  have hres : CFSG.conjugate Z0 g' = Z0 := h Z0 hZ0Q0 hZ0c hZ0card g' hg'
  have hkey : CFSG.conjugate (CFSG.conjugate Z x⁻¹) g' = CFSG.conjugate Z x⁻¹ := by
    rw [← hZ0conj]
    exact hres
  rw [CFSG.conjugate_conjugate] at hkey
  have hfinal := congrArg (fun H : Subgroup Y => CFSG.conjugate H x) hkey
  rw [CFSG.conjugate_conjugate, CFSG.conjugate_conjugate] at hfinal
  have harg2 : (x⁻¹ * g') * x = g := by
    simp only [g']
    group
  rw [harg2, inv_mul_cancel, CFSG.conjugate_one] at hfinal
  exact hfinal

theorem sylowCenterWeaklyClosed_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] [Finite Y]
    [Finite Y'] (e : Y ≃* Y') (h : SylowCenterWeaklyClosed Y') : SylowCenterWeaklyClosed Y := by
  classical
  unfold SylowCenterWeaklyClosed at h ⊢
  intro Q Z hZQ hZc hZcard g hconj
  let Q' : Sylow 3 Y' := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Q
  have hQ' : (Q' : Subgroup Y') = (Q : Subgroup Y).map e.toMonoidHom := by
    simp [Q']
  let Z' : Subgroup Y' := Z.map e.toMonoidHom
  let g' : Y' := e g
  have hZ'Q' : Z' ≤ (Q' : Subgroup Y') := by
    rw [hQ']
    exact Subgroup.map_mono hZQ
  have hZ'c : Z' ≤ Subgroup.centralizer ((Q' : Subgroup Y') : Set Y') := by
    rw [hQ']
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
    have hcomm := Subgroup.mem_centralizer_iff.mp (hZc hz) q hq
    calc e.toMonoidHom q * e.toMonoidHom z = e.toMonoidHom (q * z) :=
          (map_mul e.toMonoidHom q z).symm
      _ = e.toMonoidHom (z * q) := by rw [hcomm]
      _ = e.toMonoidHom z * e.toMonoidHom q := map_mul e.toMonoidHom z q
  have hZ'card : Nat.card Z' = 3 := by
    have hZ'map : Z' = Z.map e.toMonoidHom := rfl
    rw [hZ'map, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hZcard]
  have hconj'_eq : CFSG.conjugate Z' g' = (CFSG.conjugate Z g).map e.toMonoidHom := by
    simpa [Z', g'] using (CFSG.map_conjugate e.toMonoidHom Z g).symm
  have hconj' : CFSG.conjugate Z' g' ≤ (Q' : Subgroup Y') := by
    rw [hconj'_eq, hQ']
    exact Subgroup.map_mono hconj
  have hres : CFSG.conjugate Z' g' = Z' := h Q' Z' hZ'Q' hZ'c hZ'card g' hconj'
  have hmap : (CFSG.conjugate Z g).map e.toMonoidHom = Z.map e.toMonoidHom := by
    rw [← hconj'_eq, hres]
  exact map_injective_of_injective e.toMonoidHom e.injective hmap


theorem sylowCenterInverted_of_lieModel_psu3
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Blueprint.LieModel Y .PSU 3 3 1) :
    SylowCenterInverted Y := by
  unfold SylowCenterInverted
  intro Q z hzQ hzc hz3
  obtain ⟨t, -, ht⟩ := u33_inverting_of_lieModel hY Q hzQ hzc hz3
  exact ⟨t, ht⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
