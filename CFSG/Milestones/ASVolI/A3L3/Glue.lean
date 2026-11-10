module

public import CFSG.Milestones.ASVolI.A3L3.Core
public import CFSG.Milestones.ASVolI.A3L3.Pull

public section

namespace CFSG.ASVolI

open Matrix CFSG.RankThree.SubgroupLists CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3
open scoped Pointwise


namespace burnsideA315y_Model

variable {F : Type} [Field F] {X : Type} [Group X] (M : burnsideA315y_Model F X)

theorem case3 [Finite F] [Finite X] (hsteps : burnsideA315y_StepsStatement)
    (hcartan : burnsideA315y_CartanStatement) {δ : Bool} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nonempty (↥M.K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
    (hΓscal : ∀ g : ↥M.Γ, (g : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g → ∀ μ : Fˣ,
      (μ : F) = ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 →
        Matrix.GeneralLinearGroup.scalar (Fin 3) μ ∈ M.Γ)
    (hΓdiag : ∀ g : ↥M.Γ, (g : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g →
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 → ∀ (n : ℕ) (s : Fˣ),
        (s : F) = (ulBlock ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).det ^ n →
          burnsideA315y_dgl s ∈ M.Γ)
    (hSK : Nat.card ↥(M.S ⊓ M.K) = 2 ^ (Nat.card ↥M.K).factorization 2)
    (hScard : Nat.card ↥M.S = 2 ^ (Nat.card (CFSG.GorensteinWalter.PGL2 (ZMod p))).factorization 2 *
      Nat.card ↥(M.S ⊓ Subgroup.centralizer (M.K : Set X)))
    {L' : Subgroup X} (hKL : M.K ≤ L') (hL'c : L' ≤ M.c.range)
    (hrel : ¬ p ∣ L'.relIndex M.c.range)
    (hD₀cyc : IsCyclic ↥(M.D₀.map M.c))
    (hD₀card : Nat.card ↥(M.D₀.map M.c) ∣ (if δ then p - 1 else p + 1))
    {U : Subgroup X} (hU : CFSG.Quasithin.A315.IsSylowOf p U L')
    (hUD : M.D₀.map M.c ≤ Subgroup.normalizer (U : Set X))
    {B : Subgroup X} (hBc : B ≤ M.c.range) (hBz : ∀ b ∈ B, b * M.z = M.z * b)
    (hab : IsMulCommutative ↥B) (hodd : Odd (Nat.card ↥B))
    (hperm : (B : Set X) * (M.S : Set X) = (M.S : Set X) * (B : Set X)) :
    ∃ K : Subgroup X, K ≤ L' ∧ CFSG.Quasithin.IsSL2 p ↥K ∧
      B = (B ⊓ K) ⊔ (B ⊓ Subgroup.centralizer (K : Set X)) ∧
      IsCyclic ↥(B ⊓ K) ∧ IsCyclic ↥(B ⊓ Subgroup.centralizer (K : Set X)) ∧
      (∃ H U : Subgroup X, CFSG.Quasithin.A315.IsSylowOf p U L' ∧
        CFSG.Quasithin.A315.IsCartan p U (L' ⊔ B) H ∧ B ⊓ Subgroup.centralizer (K : Set X) ≤ H) ∧
      Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) ∣ (if δ then p - 1 else p + 1) ∧
      (((∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ Int.ModEq 4 ε (p : ℤ) ∧
          ((Nat.card ↥(B ⊓ K) : ℕ) : ℤ) ∣ (p : ℤ) - ε) ∧
        CFSG.Quasithin.A315.InvertedIn (B ⊓ K) (M.S ⊓ K)) ∨
       ((p % 8 = 3 ∨ p % 8 = 5) ∧ Nat.card ↥(B ⊓ K) = 3 ∧
        CFSG.Quasithin.A315.InvertedIn (B ⊓ K) (M.S ⊓ Subgroup.normalizer (B : Set X) ⊓
          Subgroup.centralizer ((B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) : Set X)))) := by
  obtain ⟨hBeq, hcyc1, hlast⟩ :=
    M.steps hsteps hp2 hK hΓscal hΓdiag hBc hBz hab hodd hperm hSK hScard
  have hBM : B ≤ M.Mz := fun b hb =>
    ⟨hBc hb, Subgroup.mem_centralizer_singleton_iff.mpr (hBz b hb)⟩
  have hQD : B ⊓ Subgroup.centralizer (M.K : Set X) ≤ M.D₀.map M.c := by
    rw [← M.Mz_inf_centralizer]
    exact inf_le_inf_right _ hBM
  have hQcard : Nat.card ↥(B ⊓ Subgroup.centralizer (M.K : Set X)) ∣
      (if δ then p - 1 else p + 1) :=
    (Subgroup.card_dvd_of_le hQD).trans hD₀card
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpQ : ¬ p ∣ Nat.card ↥(B ⊓ Subgroup.centralizer (M.K : Set X)) := by
    intro hdvd
    have h1 := hdvd.trans hQcard
    cases δ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h1
      have h2 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp h1
      exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one h2)
    | true =>
      simp only [↓reduceIte] at h1
      have := Nat.le_of_dvd (by omega) h1
      omega
  refine ⟨M.K, hKL, hK, hBeq, hcyc1, burnsideA315x_cyclic_of_le hQD hD₀cyc, ?_, hQcard, ?_⟩
  · have hrel' : ¬ p ∣ L'.relIndex (L' ⊔ B) := by
      intro h
      apply hrel
      exact h.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex L' (L' ⊔ B) M.c.range
        le_sup_left (sup_le hL'c hBc)))
    obtain ⟨H, hH, hQH⟩ := hcartan X p hp L' (L' ⊔ B) U
      (B ⊓ Subgroup.centralizer (M.K : Set X)) le_sup_left hU hrel'
      (inf_le_left.trans le_sup_right) (hQD.trans hUD) hpQ
    exact ⟨H, U, hU, hH, hQH⟩
  · rcases hlast with ⟨hε, t, ht, hinv⟩ | ⟨h8, h3, t, ht, hinv⟩
    · exact Or.inl ⟨hε, t, ht, hinv⟩
    · have htC : t ∈ Subgroup.centralizer
          ((B ⊓ Subgroup.centralizer (M.K : Set X) : Subgroup X) : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        exact M.central c ⟨hBM hc.1, hc.2⟩ t (M.S_le_Mz ht.1)
      exact Or.inr ⟨h8, h3, t, ⟨ht, htC⟩, hinv⟩

end burnsideA315y_Model


end CFSG.ASVolI
