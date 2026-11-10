module

public import CFSG.ClassicalInvolution.Q3.TL3T8

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G]


omit [Finite G] in
theorem comm_of_conj_mem_mul {L : Subgroup G} {u y : G} (hu : IsUniqueInvolution L u)
    {k : ℕ} (hy3 : y ^ 3 ^ k = 1) (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (h : ∀ l ∈ L, y * l * y⁻¹ = l ∨ y * l * y⁻¹ = l * u) : ∀ l ∈ L, y * l = l * y := by
  have hyu : y * u * y⁻¹ = u := by
    have hmem : y * u * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyL u).mp hu.mem
    have hsq : (y * u * y⁻¹) * (y * u * y⁻¹) = 1 := by
      calc (y * u * y⁻¹) * (y * u * y⁻¹) = y * (u * u) * y⁻¹ := by group
        _ = 1 := by rw [hu.sq]; group
    rcases hu.unique _ hmem hsq with h1 | h1
    · exfalso
      apply hu.ne_one
      calc u = y⁻¹ * (y * u * y⁻¹) * y := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  have key : ∀ c : G, (c = 1 ∨ c = u) → y * c * y⁻¹ = c := by
    rintro c (rfl | rfl)
    · group
    · exact hyu
  have hy2 : ∀ l ∈ L, (y * y) * l = l * (y * y) := by
    intro l hl
    obtain ⟨c, hc, hlc⟩ : ∃ c : G, (c = 1 ∨ c = u) ∧ y * l * y⁻¹ = l * c := by
      rcases h l hl with h1 | h1
      · exact ⟨1, Or.inl rfl, by rw [h1, mul_one]⟩
      · exact ⟨u, Or.inr rfl, h1⟩
    have hc2 : c * c = 1 := by
      rcases hc with rfl | rfl
      · group
      · exact hu.sq
    calc (y * y) * l = (y * (y * l * y⁻¹) * y⁻¹) * (y * y) := by group
      _ = (y * (l * c) * y⁻¹) * (y * y) := by rw [hlc]
      _ = ((y * l * y⁻¹) * (y * c * y⁻¹)) * (y * y) := by group
      _ = (l * c * c) * (y * y) := by rw [hlc, key c hc]
      _ = l * (y * y) := by rw [mul_assoc l c c, hc2, mul_one]
  intro l hl
  have hpow : ∀ m : ℕ, (y * y) ^ m * l = l * (y * y) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, mul_assoc, hy2 l hl, ← mul_assoc, ih, mul_assoc]
  have hodd : (3 ^ k) % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
  have h2 : 2 * ((3 ^ k + 1) / 2) = 3 ^ k + 1 := by omega
  have hym : y = (y * y) ^ ((3 ^ k + 1) / 2) := by
    calc y = y ^ (3 ^ k) * y := by rw [hy3, one_mul]
      _ = y ^ (3 ^ k + 1) := by rw [pow_succ]
      _ = y ^ (2 * ((3 ^ k + 1) / 2)) := by rw [h2]
      _ = (y * y) ^ ((3 ^ k + 1) / 2) := by rw [pow_mul, sq]
  rw [hym]
  exact hpow _

omit [Finite G] in
theorem comm_of_mem_pSpan {P : Set (Subgroup G)} {x y : G} (hy : y ∈ pSpan P)
    (h : ∀ L ∈ P, ∀ l ∈ L, x * l = l * x) : x * y = y * x := by
  have hle : pSpan P ≤ Subgroup.centralizer ({x} : Set G) :=
    pSpan_le fun L hL l hl => Subgroup.mem_centralizer_singleton_iff.mpr (h L hL l hl).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

variable {Ω : Set (Subgroup G)} {K : Subgroup G} (hS : ThinStd Ω K)
include hS

theorem ThinStd.maxAdj_symm {M N : Subgroup G} (h : MaxAdj (nbrAdj Ω) M N) :
    MaxAdj (nbrAdj Ω) N M :=
  ⟨hS.graphFam.graph.symm h.1, orbOf_mem_maxOrbs hS.graphFam h.1 h.2⟩


end CFSG.ClassicalInvolution.Q3.TC.Thin
