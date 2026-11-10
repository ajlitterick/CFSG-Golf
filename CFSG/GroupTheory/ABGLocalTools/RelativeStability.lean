module

public import CFSG.GroupTheory.ABGLocalTools.ZJFactorization

public section

open Subgroup
open scoped Pointwise commutatorElement

namespace CFSG.ABGLocalTools

variable {H : Type*} [Group H] {p : ℕ}

theorem map_pCore_le_of_surjective {K : Type*} [Group K] (f : H →* K)
    (hf : Function.Surjective f) : (pCore p H).map f ≤ pCore p K :=
  le_sSup ⟨(pCore_normal (G := H) (p := p)).map f hf, (pCore_isPGroup (G := H) (p := p)).map f⟩

theorem mem_normalizerPCoreModCentralizer_iff {P : Subgroup H} {x : H} :
    x ∈ normalizerPCoreModCentralizer p P ↔ ∃ hx : x ∈ normalizer (P : Set H),
      QuotientGroup.mk' ((centralizer (P : Set H)).subgroupOf (normalizer (P : Set H)))
        ⟨x, hx⟩ ∈ pCore p (normalizer (P : Set H) ⧸
          (centralizer (P : Set H)).subgroupOf (normalizer (P : Set H))) := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.2, hn⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩


end CFSG.ABGLocalTools
