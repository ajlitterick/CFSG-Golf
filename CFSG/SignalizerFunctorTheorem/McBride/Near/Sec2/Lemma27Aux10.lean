module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux7
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux8

public section

open CFSG.Open
open scoped Pointwise
open CFSG.SignalizerFunctorTheorem.Nonsolvable (simpleComponents IsASimple)
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27

variable {Γ : Type u} [Group Γ]

theorem qpre_mono (V : Subgroup Γ) {U U' : Subgroup (QG V)} (h : U ≤ U') :
    qpre V U ≤ qpre V U' := fun x hx => by
  obtain ⟨hn, hxU⟩ := mem_qpre_iff.mp hx
  exact mem_qpre_iff.mpr ⟨hn, h hxU⟩


theorem isChiefFactorOf_qimg {V H M N : Subgroup Γ} (hH : H ≤ nrm V) (hVN : V ≤ N)
    (h : IsChiefFactorOf H M N) : IsChiefFactorOf (qimg V H) (qimg V M) (qimg V N) := by
  obtain ⟨hNH, hMH, hNM, hmin⟩ := h
  have hMn : M ≤ nrm V := hMH.1.trans hH
  have hNn : N ≤ nrm V := hNH.1.trans hH
  have hVM : V ≤ M := hVN.trans hNM.le
  have hVH : V ≤ H := hVN.trans hNH.1
  refine ⟨⟨qimg_mono V hNH.1, qimg_le_normalizer hNH.2⟩,
    ⟨qimg_mono V hMH.1, qimg_le_normalizer hMH.2⟩, ?_, ?_⟩
  · refine lt_of_le_of_ne (qimg_mono V hNM.le) fun heq => hNM.ne ?_
    have := congrArg (qpre V) heq
    rwa [qpre_qimg hVN hNn, qpre_qimg hVM hMn] at this
  · intro K' hK' hNK hKM
    have hKH : qpre V K' ≤ H := by
      have := qpre_mono V hK'.1
      rwa [qpre_qimg hVH hH] at this
    have hKnorm : IsNormalIn (qpre V K') H :=
      ⟨hKH, fun x hx => mem_nrm_of_qmap_normalizer (hH hx) (hK'.2 (mem_qimg_of_mem hx (hH hx)))⟩
    have hNK' : N ≤ qpre V K' := by
      have := qpre_mono V hNK
      rwa [qpre_qimg hVN hNn] at this
    have hKM' : qpre V K' ≤ M := by
      have := qpre_mono V hKM
      rwa [qpre_qimg hVM hMn] at this
    rcases hmin _ hKnorm hNK' hKM' with h | h
    · left
      rw [← qimg_qpre V K', h]
    · right
      rw [← qimg_qpre V K', h]


section Orbit

variable [Finite Γ]

omit [Finite Γ] in
theorem orbitClosure_le_of_le_of_normalizes {J R X : Subgroup Γ} (hJ : J ≤ R)
    (hXR : X ≤ Subgroup.normalizer (R : Set Γ)) : orbitClosure J X ≤ R := by
  refine iSup₂_le fun x hx => ?_
  rintro _ ⟨j, hj, rfl⟩
  have := (Subgroup.mem_normalizer_iff.mp (hXR hx) j).mp (hJ hj)
  exact this

omit [Finite Γ] in
theorem orbitClosure_le_of_le {J X : Subgroup Γ} (hJ : J ≤ X) : orbitClosure J X ≤ X :=
  orbitClosure_le_of_le_of_normalizes hJ (fun x hx => Subgroup.mem_normalizer_iff.mpr fun y =>
    ⟨fun hy => mul_mem (mul_mem hx hy) (inv_mem hx), fun hy => by
      simpa [mul_assoc] using mul_mem (mul_mem (inv_mem hx) hy) hx⟩)


omit [Finite Γ] in
theorem centralizer_orbitClosure {A J : Subgroup Γ} (hA : IsMulCommutative A) {c : Γ} (hc : c ∈ A)
    (hcJ : c ∈ Subgroup.centralizer (J : Set Γ)) :
    c ∈ Subgroup.centralizer ((orbitClosure J A : Subgroup Γ) : Set Γ) := by
  have hle : orbitClosure J A ≤ Subgroup.centralizer ({c} : Set Γ) := by
    refine iSup₂_le fun a ha => ?_
    rintro _ ⟨j, hj, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hca : c * a = a * c := (commute_of_mem hA hc ha).eq
    have hcj : c * j = j * c := (Subgroup.mem_centralizer_iff.mp hcJ j hj).symm
    show (MulAut.conj a) j * c = c * (MulAut.conj a) j
    simp only [MulAut.conj_apply]
    calc a * j * a⁻¹ * c = a * j * (a⁻¹ * c) := by group
      _ = a * j * (c * a⁻¹) := by
        have : a⁻¹ * c = c * a⁻¹ := by
          have h2 := congrArg (fun z => a⁻¹ * z * a⁻¹) hca
          simpa [mul_assoc] using h2
        rw [this]
      _ = a * (j * c) * a⁻¹ := by group
      _ = a * (c * j) * a⁻¹ := by rw [hcj]
      _ = (a * c) * j * a⁻¹ := by group
      _ = (c * a) * j * a⁻¹ := by rw [hca]
      _ = c * (a * j * a⁻¹) := by group
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hk)

end Orbit

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27
