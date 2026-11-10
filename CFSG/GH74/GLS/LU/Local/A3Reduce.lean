module

public import CFSG.GH74.GLS.LU.Local.KStep
public import CFSG.GH74.GLS.LU.Local.A3
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.TwoThin
open scoped MatrixGroups

abbrev CY (G : Type) [Group G] (x : G) : Type := ↥(centralizer ({x} : Set G))

@[expose] def toCY {G : Type} [Group G] {x g : G} (hg : g * x = x * g) : CY G x :=
  ⟨g, mem_centralizer_singleton_iff.mpr hg⟩


variable {G : Type} [Group G]

theorem isKGroupNative_centralizer [Finite G] (hG : IsKProperSimple G) {x : G} (hx : x ≠ 1) :
    IsKGroupNative (CY G x) := by
  have hne : centralizer ({x} : Set G) ≠ ⊤ := by
    intro h
    have hz : x ∈ center G := by
      rw [mem_center_iff]
      intro g
      have : g ∈ centralizer ({x} : Set G) := by rw [h]; exact mem_top g
      exact ((mem_centralizer_iff.mp this) x (Set.mem_singleton x)).symm
    have hsimple : IsSimpleGroup G := hG.1
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h1 | h1
    · rw [h1, mem_bot] at hz
      exact hx hz
    · obtain ⟨a, b, hab⟩ := hG.2.1
      apply hab
      have : a ∈ center G := by rw [h1]; exact mem_top a
      exact (mem_center_iff.mp this b).symm
  exact isKGroupNative_of_kProper hG.2.2 hne

theorem card_inf_toCY {x : G} {K₁ : Subgroup G} (hK : K₁ ≤ centralizer ({x} : Set G)) {u' : G}
    (hxu : u' * x = x * u') :
    Nat.card ↥(K₁.subgroupOf (centralizer ({x} : Set G)) ⊓
        centralizer ({toCY hxu} : Set (CY G x))) = Nat.card ↥(K₁ ⊓ centralizer ({u'} : Set G)) := by
  let f : ↥(K₁.subgroupOf (centralizer ({x} : Set G)) ⊓ centralizer ({toCY hxu} : Set (CY G x))) →
      ↥(K₁ ⊓ centralizer ({u'} : Set G)) := fun k =>
    ⟨((k : CY G x) : G), Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp k.2).1,
        mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
          (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp k.2).2))⟩⟩
  refine Nat.card_eq_of_bijective f ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext; apply Subtype.ext
    have h1 := congrArg Subtype.val hab
    exact h1
  · rintro ⟨y, hy⟩
    obtain ⟨hyK, hyu⟩ := Subgroup.mem_inf.mp hy
    refine ⟨⟨⟨y, hK hyK⟩, Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hyK,
      mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp hyu))⟩⟩, rfl⟩

theorem map_subtype_sup_subgroupOf (C K₁ L : Subgroup G) (hK : K₁ ≤ C) (hL : L ≤ C) :
    (K₁.subgroupOf C ⊔ L.subgroupOf C).map C.subtype = K₁ ⊔ L := by
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hK, Subgroup.map_subgroupOf_eq_of_le hL]

theorem charP_of_card_eq_pow {K : Type} [Field K] [Finite K] {p m : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hK : Nat.card K = p ^ m) : CharP K p := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpr, hcard⟩ := FiniteField.card K (ringChar K)
  have h1 : p ^ m = (ringChar K) ^ (n : ℕ) := by
    rw [← hK, Nat.card_eq_fintype_card, hcard]
  have h2 : p ∣ (ringChar K) ^ (n : ℕ) := by rw [← h1]; exact dvd_pow_self p hm.ne'
  have h3 : p ∣ ringChar K := hp.dvd_of_dvd_pow h2
  have h4 : p = ringChar K := (Nat.prime_dvd_prime_iff_eq hp hpr).mp h3
  rw [h4]
  exact ringChar.charP K

theorem ker_le_center_of_range {S₀ : Type} [Group S₀] (hS : IsQuasisimple S₀) (α : S₀ →* G)
    {z : G} (hz1 : z ≠ 1) (hz : z ∈ α.range) : α.ker ≤ center S₀ := by
  obtain ⟨a, ha⟩ := hz
  exact CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hS ⟨a, by rw [ha]; exact hz1⟩


theorem range_comp_subtype_sup {x : G} {K₁ L : Subgroup G} (hK : K₁ ≤ centralizer ({x} : Set G))
    (hL : L ≤ centralizer ({x} : Set G)) {S₀ : Type} [Group S₀]
    (α₀ : S₀ →* ↥((K₁.subgroupOf (centralizer ({x} : Set G))) ⊔ (L.subgroupOf (centralizer ({x} : Set G)))))
    (hα₀ : Function.Surjective α₀) :
    ((centralizer ({x} : Set G)).subtype.comp
        ((K₁.subgroupOf (centralizer ({x} : Set G)) ⊔ L.subgroupOf (centralizer ({x} : Set G))).subtype.comp
          α₀)).range = K₁ ⊔ L := by
  rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hα₀, Subgroup.map_top,
    Subgroup.range_subtype, map_subtype_sup_subgroupOf _ _ _ hK hL]


end CFSG.GH74.GLS.LU.Local
