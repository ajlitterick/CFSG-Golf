module

public import CFSG.ClassicalInvolution.Models.LinearFrames.Chart
public import CFSG.ClassicalInvolution.Models.LinearFrames.Generation

public section

namespace CFSG.ClassicalInvolution.Models

open CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

section Sets

variable (K : Type) [Field K] (n : ℕ)

variable {K n} in
@[expose] def longRootSet (hn : 2 ≤ n) : Set (Subgroup SL(n, K)) :=
  {L | ∃ i, IsLongRootSL2 hn L i}

abbrev coordSet : Set (Subgroup SL(n, K)) := Set.range (Lc K (n := n))

variable {K n}

theorem mem_coordSet {L : Subgroup SL(n, K)} : L ∈ coordSet K n ↔ ∃ T : Pair n, Lc K T = L :=
  Iff.rfl


theorem mem_longRootSet_iff (hn : 2 ≤ n) {L : Subgroup SL(n, K)} :
    L ∈ longRootSet hn ↔ ∃ g : SL(n, K), L = (rootSL2 K hn).map (MulAut.conj g).toMonoidHom := by
  constructor
  · rintro ⟨i, g, hL, -⟩
    exact ⟨g, hL⟩
  · rintro ⟨g, hL⟩
    exact ⟨g * rootInv K hn * g⁻¹, g, hL, rfl⟩

theorem longRootSet_conjInvariant (hn : 2 ≤ n) : ConjInvariant (longRootSet (K := K) hn) := by
  rintro g L ⟨i, hi⟩
  exact ⟨g * i * g⁻¹, hi.conj g⟩

theorem Lc_mem_longRootSet (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) (T : Pair n) :
    Lc K T ∈ longRootSet hn :=
  ⟨zElt K T, isLongRootSL2_Lc h2 hn T⟩


theorem Lc_injective (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) : Function.Injective (Lc K (n := n)) := by
  intro T T' h
  have h1 := isLongRootSL2_Lc h2 hn T
  have h1' : IsLongRootSL2 hn (Lc K T) (zElt K T') := h ▸ isLongRootSL2_Lc h2 hn T'
  exact zElt_injective h2 (h1.involution_unique h2 h1')

end Sets

section Generation

variable {K : Type} [Field K] {n : ℕ}

theorem zElt_ne_one (h2 : (2 : K) ≠ 0) (T : Pair n) : zElt K T ≠ 1 :=
  z_ne_one (mat := slMat K n) (z := zElt K (n := n)) h2 (fun _ => rfl) T

theorem isUniqueInvolution_Lc (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) (T : Pair n) :
    IsUniqueInvolution (Lc K T) (zElt K T) := by
  have hL := isLongRootSL2_Lc h2 hn T
  refine ⟨hL.mem, zElt_ne_one h2 T, zElt_mul_self T, fun y hy hy2 => ?_⟩
  by_cases h1 : y = 1
  · exact Or.inl h1
  · exact Or.inr (hL.eq_of_orderOf_eq_two h2 hy (orderOf_eq_prime (by rwa [pow_two]) h1))


theorem closure_range_zElt (h2 : (2 : K) ≠ 0) :
    Subgroup.closure (Set.range (zElt K (n := n))) = signGroup K n :=
  closure_range_z (mat := slMat K n) (z := zElt K (n := n)) h2 slMat_injective (fun x => x.2)
    (fun _ => rfl)


end Generation

section TheFrame


end TheFrame

end CFSG.ClassicalInvolution.Models
