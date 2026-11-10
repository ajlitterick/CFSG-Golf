module

public import CFSG.GH74.GLS.LU.Local.A3Reduce
public import CFSG.GH74.GLS.LU.Local.KStep2

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.TwoThin
open scoped MatrixGroups

theorem subgroupOf_map_conj {G : Type} [Group G] (C K : Subgroup G) (g : G) (hg : g ∈ C) (hK : K ≤ C) :
    (K.subgroupOf C).map (MulAut.conj (⟨g, hg⟩ : C)).toMonoidHom =
      (K.map (MulAut.conj g).toMonoidHom).subgroupOf C := by
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨⟨k, hkC⟩, hk, hky⟩
    have h1 : g * k * g⁻¹ = y := by
      have := congrArg Subtype.val hky
      exact this
    exact ⟨k, hk, h1⟩
  · rintro ⟨k, hk, hky⟩
    have hkC : k ∈ C := hK hk
    refine ⟨⟨k, hkC⟩, hk, ?_⟩
    apply Subtype.ext
    exact hky

@[expose] def LUKStepLeaf₁ : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ p f : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ∀ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G), A3Hyp G p f z S K₁ K₂ t u →
    ∀ ε : ℤ, ¬ (p ^ f = 5 ∧ ε = 1) → LUEps G (p ^ f) ε z K₁ u →
      ∃ (u' h x : G) (hxz : z * x = x * z),
        h * x = x * h ∧ (u' = u ∨ u' = u * z) ∧ h⁻¹ * z * h = u' ∧
        t ∈ normalizer (cj K₁ h : Set G) ∧ x ≠ 1 ∧ K₁ ≤ centralizer ({x} : Set G) ∧
        KComp (CY G x) (toCY hxz) (K₁.subgroupOf (centralizer ({x} : Set G))) ∧
        (∀ T : Sylow 2 ↥(centralizer
            ((K₁.subgroupOf (centralizer ({x} : Set G)) : Subgroup (CY G x)) : Set (CY G x))),
          IsCyclic ↥T) ∧
        (∀ d ∈ pPrimeCore 2 (CY G x), (d : G) * z = z * (d : G) → u' * (d : G) = (d : G) * u') ∧
        ∃ g : G, g * x = x * g ∧ g * z * g⁻¹ = z * u'


end CFSG.GH74.GLS.LU.Local
