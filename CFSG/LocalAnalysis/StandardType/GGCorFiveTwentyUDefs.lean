module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestGen

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGTorusSelfCent (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) : Prop :=
  ∀ n : L', (∀ a ∈ A, a n = n) → n ^ p = 1 → MulAut.conj n ∈ A

@[expose] def GGTorusPseudoReflGenSC (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A ≤
        Subgroup.closure (ggTorusPseudoReflSet p A)

@[expose] def GGTorusSchurSC (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∃ W : Set L', (∀ n ∈ W, GGTorusWeylElt p A n) ∧
        ∀ f : MulAut L' → MulAut L', (∀ a ∈ A, f a ∈ A) →
          (∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b) →
          (∀ n ∈ W, ∀ a ∈ A, f (MulAut.conj n * a * (MulAut.conj n)⁻¹) =
            MulAut.conj n * f a * (MulAut.conj n)⁻¹) →
          ∃ c : ℕ, ∀ a ∈ A, f a = a ^ c

@[expose] def GGTorusWeylNormInnerSC (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∀ φ ∈ Subgroup.normalizer
        (ggAutomizer (MulAut.conj : L' →* MulAut L').range A : Set (MulAut ↥A)),
        ∃ w ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A,
          ∀ v ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, φ * v * φ⁻¹ = w * v * w⁻¹

section Transport

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggTorusSelfCent_ggGamma {p : ℕ} {Bs X : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) :
    GGTorusSelfCent p (ggGamma X hBsN).range := by
  intro n hn hnp
  have hnC : (n : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : b * (n : G) * b⁻¹ = n := by
      have := congrArg Subtype.val (hn (ggGamma X hBsN ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩)
      rw [ggGamma_coe] at this
      exact this
    calc b * (n : G) = b * n * b⁻¹ * b := by group
      _ = n * b := by rw [h1]
  have hnp' : (n : G) ^ p = 1 := by
    have := congrArg Subtype.val hnp
    simpa using this
  refine ⟨⟨n, hSC _ hnC hnp'⟩, ?_⟩
  ext l
  simp [ggGamma_coe, MulAut.conj_apply]


end Transport


end CFSG.StandardType

end
