module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRest

@[expose] public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


def GGTBTorRelD : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    ((lab.tag = .D ∧ p ∣ 2 ^ lab.n + 1 ∧ Odd lab.rank) ∨
      (lab.tag = .twD ∧ (p ∣ 2 ^ lab.n - 1 ∨ (p ∣ 2 ^ lab.n + 1 ∧ Even lab.rank)))) →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p (lab.rank - 1) (ggTorMpm p lab) (lab.rank - 1)
          (CartanMatrix.B (lab.rank - 1)) (CoxeterMatrix.B (lab.rank - 1)) R I

def GGTBTorRelE6 : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    ((lab.tag = .E6 ∧ p ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n - 1)) →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p 4 (ggTorMpm p lab) 4 CartanMatrix.F₄ CoxeterMatrix.F₄ R I

def GGTBTorRelE6Split : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    lab.tag = .E6 → p ∣ 2 ^ lab.n + 1 →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p 4 (ggTorMpm p lab) 4 CartanMatrix.F₄ CoxeterMatrix.F₄ R I

theorem GGTBTorRelE6.split (h : GGTBTorRelE6) : GGTBTorRelE6Split := by
  intro p hp hp2 hp3 lab hlab htag hpm
  exact h p hp hp2 hp3 lab hlab (Or.inl ⟨htag, hpm⟩)

def GGTBTorRelA5 : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.rank = 5 →
    ((lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1)) →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p 3 (ggTorMpm p lab) 3 (CartanMatrix.C 3) (CoxeterMatrix.B 3) R I

theorem ggCartanB_ker_zero {p n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n) :
    ∀ c : Fin n → ZMod p, (∀ j, ∑ k, (CartanMatrix.B n j k : ZMod p) * c k = 0) → c = 0 :=
  ggCartan_ker_zero_of_not_dvd_det _ (by
    rw [CartanMatrix.B_det hn]; exact ggTor_not_dvd_small hp.out hp2 (by norm_num))

end CFSG.StandardType
