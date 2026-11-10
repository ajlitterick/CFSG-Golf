module

public import CFSG.ClassicalInvolution.Q3.TL3T12
public import CFSG.ClassicalInvolution.Q3.AE.Models

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G]

structure AEIdentOn (P : Set (Subgroup G)) (n : ℕ) (𝒜 : Set (Finset (Fin n)))
    (H : Subgroup (AE.AEQ n)) where
  φ : ↥(pSpan P) →* AE.AEQ n
  range_eq : φ.range = H
  ker_le : φ.ker ≤ Subgroup.center ↥(pSpan P)
  label : ∀ L ∈ P, ∃ α ∈ 𝒜, ∃ (h : α.card = 4) (b : Bool),
    (L.subgroupOf (pSpan P)).map φ = AE.memBar α h b
  label_surj : ∀ α ∈ 𝒜, ∀ (h : α.card = 4) (b : Bool), ∃ L ∈ P,
    (L.subgroupOf (pSpan P)).map φ = AE.memBar α h b

section Phi

variable [Finite G] {P : Set (Subgroup G)} {n : ℕ} (φ : ↥(pSpan P) →* AE.AEQ n)

theorem phi_injOn (hn : 5 ≤ n) {L : Subgroup G} (hL : L ∈ P) (h8 : Nat.card L = 8)
    {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map φ = AE.memBar α h b) {l₁ l₂ : G} (h₁ : l₁ ∈ L)
    (h₂ : l₂ ∈ L) (he : φ ⟨l₁, le_pSpan hL h₁⟩ = φ ⟨l₂, le_pSpan hL h₂⟩) : l₁ = l₂ := by
  let f : ↥(L.subgroupOf (pSpan P)) → ↥(AE.memBar α h b) := fun x =>
    ⟨φ x, by rw [← hlab]; exact ⟨x, x.2, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rw [← hlab] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨y, hy⟩, rfl⟩
  have hcard : Nat.card ↥(L.subgroupOf (pSpan P)) ≤ Nat.card ↥(AE.memBar α h b) := by
    rw [AE.natCard_memBar hn, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_pSpan hL)).toEquiv,
      h8]
  have hinj := (hf.bijective_of_nat_card_le hcard).1
  have := @hinj ⟨⟨l₁, le_pSpan hL h₁⟩, Subgroup.mem_subgroupOf.mpr h₁⟩
    ⟨⟨l₂, le_pSpan hL h₂⟩, Subgroup.mem_subgroupOf.mpr h₂⟩ (Subtype.ext he)
  exact congrArg (fun x : ↥(L.subgroupOf (pSpan P)) => ((x : ↥(pSpan P)) : G)) this

theorem phi_map_eq_zBar (hn : 5 ≤ n) {L : Subgroup G} (hL : L ∈ P) (h8 : Nat.card L = 8)
    {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map φ = AE.memBar α h b) {u : G}
    (hu : IsUniqueInvolution L u) : φ ⟨u, le_pSpan hL hu.mem⟩ = AE.zBar α h := by
  have hmem : φ ⟨u, le_pSpan hL hu.mem⟩ ∈ AE.memBar α h b := by
    rw [← hlab]
    exact ⟨⟨u, le_pSpan hL hu.mem⟩, Subgroup.mem_subgroupOf.mpr hu.mem, rfl⟩
  have hsq : φ ⟨u, le_pSpan hL hu.mem⟩ * φ ⟨u, le_pSpan hL hu.mem⟩ = 1 := by
    rw [← map_mul, ← map_one φ]
    congr 1
    exact Subtype.ext hu.sq
  rcases AE.eq_of_mem_memBar_mul_self hn hmem hsq with h1 | h1
  · exfalso
    apply hu.ne_one
    have : φ ⟨u, le_pSpan hL hu.mem⟩ = φ ⟨1, le_pSpan hL L.one_mem⟩ := by
      rw [h1]
      exact (map_one φ).symm
    exact phi_injOn φ hn hL h8 hlab hu.mem L.one_mem this
  · exact h1

theorem phi_twins (hn : 5 ≤ n) {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P)
    (h8 : Nat.card L = 8) (h8' : Nat.card L' = 8) {α : Finset (Fin n)} {h : α.card = 4}
    {b : Bool} (hlab : (L.subgroupOf (pSpan P)).map φ = AE.memBar α h b)
    (hlab' : (L'.subgroupOf (pSpan P)).map φ = AE.memBar α h (!b)) :
    L ≠ L' ∧ ∀ u u' : G, ∀ (hu : IsUniqueInvolution L u) (hu' : IsUniqueInvolution L' u'),
      (⟨u, le_pSpan hL hu.mem⟩ * ⟨u', le_pSpan hL' hu'.mem⟩ : ↥(pSpan P)) ∈ φ.ker := by
  refine ⟨fun heq => ?_, fun u u' hu hu' => ?_⟩
  · subst heq
    rw [hlab] at hlab'
    cases b
    · exact AE.memBar_true_ne_false hn α h hlab'.symm
    · exact AE.memBar_true_ne_false hn α h hlab'
  · rw [MonoidHom.mem_ker, map_mul, phi_map_eq_zBar φ hn hL h8 hlab hu,
      phi_map_eq_zBar φ hn hL' h8' hlab' hu']
    exact AE.zBar_mul_self α h

end Phi


theorem twins_of_phi {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {n : ℕ} (hn : 5 ≤ n)
    (φ : ↥(pSpan P) →* AE.AEQ n) (hker : φ.ker ≤ Subgroup.center ↥(pSpan P))
    (h8 : ∀ L ∈ P, Nat.card L = 8) {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P)
    {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map φ = AE.memBar α h b)
    (hlab' : (L'.subgroupOf (pSpan P)).map φ = AE.memBar α h (!b))
    (huniq : ∀ L ∈ P, ∃ u : G, IsUniqueInvolution L u) :
    ∃ L ∈ P, ∃ L' ∈ P, L ≠ L' ∧ ∃ u u' : G, IsUniqueInvolution L u ∧
      IsUniqueInvolution L' u' ∧ ∀ I ∈ P, ∀ x ∈ I, (u * u') * x = x * (u * u') := by
  obtain ⟨hne, hk⟩ := phi_twins φ hn hL hL' (h8 L hL) (h8 L' hL') hlab hlab'
  obtain ⟨u, hu⟩ := huniq L hL
  obtain ⟨u', hu'⟩ := huniq L' hL'
  refine ⟨L, hL, L', hL', hne, u, u', hu, hu', fun I hI x hx => ?_⟩
  have := Subgroup.mem_center_iff.mp (hker (hk u u' hu hu')) ⟨x, le_pSpan hI hx⟩
  exact (congrArg Subtype.val this).symm


end CFSG.ClassicalInvolution.Q3.TC.Thin

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Cit3


@[expose] def TightCaseE64Leaf (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHyp n Y R S t → TightOddCent t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      TC.SepHyp (CoreAssembly.conjClass (tightCore R)) →
      (∀ M N : Subgroup Y, MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) M N →
        TC.ThinAt (CoreAssembly.conjClass (tightCore R)) M N) →
      Nonempty (TC.Thin.AEIdentOn {L : Subgroup Y |
        MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) L} 7
          AE.e64Sets AE.e64Sub) → False

@[expose] def TightCase29Leaf (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHyp n Y R S t → TightOddCent t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      TC.SepHyp (CoreAssembly.conjClass (tightCore R)) →
      (∀ M N : Subgroup Y, MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) M N →
        TC.ThinAt (CoreAssembly.conjClass (tightCore R)) M N) →
      Nonempty (TC.Thin.AEIdentOn {L : Subgroup Y |
        MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) L} 8
          AE.e29Sets AE.e29Sub) → False


end Cit3

end CFSG.ClassicalInvolution.Q3
