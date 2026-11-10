module

public import CFSG.ClassicalInvolution.Asc77.AscT8T2
public import CFSG.ClassicalInvolution.Asc77.AscT7AAlphaTwin
public import CFSG.ClassicalInvolution.Asc77.AscT8Y1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance.Bootstrap

namespace T8T

section Alpha

variable {G : Type} [Group G] {B α₀ : Subgroup G}

theorem centralizer_le_normalizer_of_alphaOf_eq {A : Subgroup G} (h : alphaOf A = α₀) :
    Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (α₀ : Set G) := by
  intro c hc
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  have h1 : conjSub c A = A := T7A.conjSub_eq_self_of_mem_centralizer hc
  have h2 := alphaOf_conjSub c A
  rw [h1, h] at h2
  exact h2.symm

variable [Finite G]

theorem oddCoreOf_centralizer_le_normalizer {b : G} (hB : IsElemAbelian 2 B)
    (hB8 : Nat.card B = 8) (hbB : b ∈ B)
    (h3 : ∀ A : Subgroup G, A ≤ B → IsElemAbelian2 A 2 → alphaOf A = α₀) :
    oddCoreOf (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (α₀ : Set G) := by
  have hBC : B ≤ Subgroup.centralizer ({b} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact DeltaClosure.comm_of_mem_elemAbelian hB hy hbB
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two B (oddCoreOf (Subgroup.centralizer ({b} : Set G))) hB
    (by rw [hB8]; norm_num)
    (fun c hc => CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ (hBC hc))
    (Nat.coprime_two_left.mpr
      (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (Subgroup.centralizer ({b} : Set G))))
  conv_lhs => rw [← hgen]
  refine iSup₂_le fun E hE => inf_le_right.trans ?_
  have hE2 : IsElemAbelian2 E 2 :=
    ⟨hE.2, fun y hy => by rw [← pow_two]; exact hB.2 y (hE.1 hy)⟩
  exact centralizer_le_normalizer_of_alphaOf_eq (h3 E hE.1 hE2)

end Alpha

section Members

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {M : Fin 3 → Subgroup G} {x : Fin 3 → G} {R : Fin 3 → Subgroup G} {α₀ : Subgroup G}


end Members

section Layer

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem oddCoreOf_layerJoin_le_oddCoreOf_centralizer (hΩ : HypOmegaMod p f Ω) (a : G) :
    oddCoreOf (T8.layerJoin Ω a) ≤ oddCoreOf (Subgroup.centralizer ({a} : Set G)) := by
  have hYC : T8.layerJoin Ω a ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [← T8.cenZ_eq_centralizer]
    exact T8.layerJoin_le_cenZ _
  intro x hx
  exact T8.oddCoreOf_le_oddCoreOf_of_normalized hYC
    (fun c hc => T8.layerJoin_conjSub_eq hΩ (by rw [T8.cenZ_eq_centralizer]; exact hc)) hx

end Layer

end T8T

end CFSG.ClassicalInvolution.Asc77
