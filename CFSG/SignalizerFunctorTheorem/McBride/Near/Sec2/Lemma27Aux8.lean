module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief.Quotient
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux1

public section

open CFSG.Open
open scoped Pointwise
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27

variable {Γ : Type u} [Group Γ]

@[expose] def qpre (V : Subgroup Γ) (U : Subgroup (QG V)) : Subgroup Γ :=
  (U.comap (qmap V)).map (nrm V).subtype

theorem mem_qpre_iff {V : Subgroup Γ} {U : Subgroup (QG V)} {x : Γ} :
    x ∈ qpre V U ↔ ∃ h : x ∈ nrm V, qmap V ⟨x, h⟩ ∈ U := by
  unfold qpre
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem qpre_le_nrm (V : Subgroup Γ) (U : Subgroup (QG V)) : qpre V U ≤ nrm V := fun _ hx =>
  (mem_qpre_iff.mp hx).1

theorem le_qpre (V : Subgroup Γ) (U : Subgroup (QG V)) : V ≤ qpre V U := fun x hx =>
  mem_qpre_iff.mpr ⟨Subgroup.le_normalizer hx, by
    have : qmap V ⟨x, Subgroup.le_normalizer hx⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hx
    rw [this]; exact one_mem U⟩


theorem qimg_qpre (V : Subgroup Γ) (U : Subgroup (QG V)) : qimg V (qpre V U) = U := by
  ext u
  rw [mem_qimg_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h, hx⟩ := mem_qpre_iff.mp hy
    exact hx
  · intro hu
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective u
    exact ⟨y, mem_qpre_iff.mpr ⟨y.2, hu⟩, rfl⟩

theorem qpre_qimg {V U : Subgroup Γ} (hVU : V ≤ U) (hU : U ≤ nrm V) :
    qpre V (qimg V U) = U := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => mem_qpre_iff.mpr ⟨hU hx,
    (mem_qimg_iff V U _).mpr ⟨⟨x, hU hx⟩, hx, rfl⟩⟩)
  obtain ⟨h, hx⟩ := mem_qpre_iff.mp hx
  obtain ⟨y, hy, hyx⟩ := (mem_qimg_iff V U _).mp hx
  have : ((y : Γ))⁻¹ * x ∈ V := by
    have h1 : qmap V y = qmap V ⟨x, h⟩ := hyx
    have := (QuotientGroup.eq (s := V.subgroupOf (nrm V))).mp h1
    simpa [Subgroup.mem_subgroupOf] using this
  have : x = y * ((y : Γ)⁻¹ * x) := by group
  rw [this]
  exact mul_mem hy (hVU ‹((y : Γ))⁻¹ * x ∈ V›)

theorem qimg_mono (V : Subgroup Γ) {X Y : Subgroup Γ} (h : X ≤ Y) : qimg V X ≤ qimg V Y := by
  intro u hu
  obtain ⟨y, hy, rfl⟩ := (mem_qimg_iff V X u).mp hu
  exact (mem_qimg_iff V Y _).mpr ⟨y, h hy, rfl⟩

theorem mem_qimg_of_mem {V X : Subgroup Γ} {x : Γ} (hx : x ∈ X) (h : x ∈ nrm V) :
    qmap V ⟨x, h⟩ ∈ qimg V X := (mem_qimg_iff V X _).mpr ⟨⟨x, h⟩, hx, rfl⟩

theorem mem_nrm_of_qmap_normalizer {V : Subgroup Γ} {U : Subgroup (QG V)} {g : Γ}
    (hg : g ∈ nrm V) (h : qmap V ⟨g, hg⟩ ∈ Subgroup.normalizer (U : Set (QG V))) :
    g ∈ Subgroup.normalizer ((qpre V U : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ (x : Γ) (hxn : x ∈ nrm V) (hgxn : g * x * g⁻¹ ∈ nrm V),
      qmap V ⟨g * x * g⁻¹, hgxn⟩ =
        qmap V ⟨g, hg⟩ * qmap V ⟨x, hxn⟩ * (qmap V ⟨g, hg⟩)⁻¹ := by
    intro x hxn hgxn
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  constructor
  · intro hx
    obtain ⟨hxn, hxU⟩ := mem_qpre_iff.mp hx
    have hgxn : g * x * g⁻¹ ∈ nrm V := mul_mem (mul_mem hg hxn) (inv_mem hg)
    refine mem_qpre_iff.mpr ⟨hgxn, ?_⟩
    rw [key x hxn hgxn]
    exact (Subgroup.mem_normalizer_iff.mp h (qmap V ⟨x, hxn⟩)).mp hxU
  · intro hx
    obtain ⟨hgxn, hxU⟩ := mem_qpre_iff.mp hx
    have hxn : x ∈ nrm V := by
      have := mul_mem (mul_mem (inv_mem hg) hgxn) hg
      simpa [mul_assoc] using this
    refine mem_qpre_iff.mpr ⟨hxn, ?_⟩
    rw [key x hxn hgxn] at hxU
    exact (Subgroup.mem_normalizer_iff.mp h (qmap V ⟨x, hxn⟩)).mpr hxU

theorem inf_eq_bot_of_coprime {p : ℕ} {A V X : Subgroup Γ} (hA : IsElemAbelian p A)
    (hVX : V ≤ X) (hcop : Nat.Coprime p (Nat.card X)) : A ⊓ V = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxV⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_bot]
  have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hA.2 x hxA)
  have h2 : orderOf x ∣ Nat.card X := by
    have := Subgroup.orderOf_dvd_natCard X (hVX hxV)
    simpa using this
  have : orderOf x ∣ Nat.gcd p (Nat.card X) := Nat.dvd_gcd h1 h2
  rw [hcop] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)


variable [Finite Γ]

omit [Finite Γ] in
theorem isElemAbelian_of_le {p : ℕ} {A E : Subgroup Γ} (hA : IsElemAbelian p A) (hEA : E ≤ A) :
    IsElemAbelian p E := CFSG.Open.IsElemAbelian.mono hA hEA


end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27
