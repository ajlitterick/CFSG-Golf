module

public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Chart
public import CFSG.ClassicalInvolution.Models.LinearFrames.Generation

public section

namespace CFSG.ClassicalInvolution.Models

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open scoped MatrixGroups

section SetsU

variable (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ)

variable {K p f n} in
@[expose] def longRootSetU (hn : 2 ≤ n) : Set (Subgroup (Su K p f n)) :=
  {L | ∃ i, IsLongRootSU2 K p f hn L i}


variable {K p f n}


theorem mem_longRootSetU_iff (hn : 2 ≤ n) {L : Subgroup (Su K p f n)} :
    L ∈ longRootSetU (K := K) (p := p) (f := f) hn ↔
      ∃ g : Su K p f n, L = (rootSU2 K p f hn).map (MulAut.conj g).toMonoidHom := by
  constructor
  · rintro ⟨i, g, hL, -⟩
    exact ⟨g, hL⟩
  · rintro ⟨g, hL⟩
    exact ⟨g * rootInvSU K p f hn * g⁻¹, g, hL, rfl⟩

theorem longRootSetU_conjInvariant (hn : 2 ≤ n) :
    ConjInvariant (longRootSetU (K := K) (p := p) (f := f) hn) := by
  rintro g L ⟨i, hi⟩
  exact ⟨g * i * g⁻¹, hi.conj g⟩

theorem LcU_mem_longRootSetU (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) (T : Pair n) :
    LcU K p f T ∈ longRootSetU hn :=
  ⟨zEltU K p f T, isLongRootSU2_LcU h2 hn T⟩


theorem LcU_injective (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 2 ≤ n) :
    Function.Injective (LcU K p f (n := n)) := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  intro T T' h
  have h1 := isLongRootSU2_LcU (p := p) (f := f) h2 hn T
  have h1' : IsLongRootSU2 K p f hn (LcU K p f T) (zEltU K p f T') := h ▸ isLongRootSU2_LcU h2 hn T'
  have := h1.involution_unique hK hp h1'
  exact Subtype.ext (zMat_inj h2 (congrArg suMat this))

end SetsU

section GenerationU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem zEltU_ne_one (h2 : (2 : K) ≠ 0) (T : Pair n) : zEltU K p f T ≠ 1 :=
  z_ne_one (mat := suMatHom K p f n) (z := zEltU K p f (n := n)) h2 (fun _ => rfl) T

theorem isUniqueInvolution_LcU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 2 ≤ n)
    (T : Pair n) : IsUniqueInvolution (LcU K p f T) (zEltU K p f T) := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hL := isLongRootSU2_LcU (p := p) (f := f) h2 hn T
  refine ⟨hL.mem, zEltU_ne_one h2 T, zEltU_mul_self T, fun y hy hy2 => ?_⟩
  by_cases h1 : y = 1
  · exact Or.inl h1
  · exact Or.inr (hL.eq_of_orderOf_eq_two hK hp hy (orderOf_eq_prime (by rwa [pow_two]) h1))


end GenerationU

section TheFrameU


end TheFrameU

end CFSG.ClassicalInvolution.Models
