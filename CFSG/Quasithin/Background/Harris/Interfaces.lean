module

public import CFSG.Quasithin.Background.G9Stmts

public section

namespace CFSG.Quasithin.G11.Harris

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

structure OneCompSetting (Γ A L : Subgroup (GLV V)) (m : ℕ) : Prop where
  quotient : IsQuotientOfSQTKTauCeti ↥Γ
  A_le : A ≤ Γ
  A_elem : IsElemAbelian 2 A
  A_card : Nat.card ↥A = 2 ^ m
  bound : Module.finrank (ZMod 2) V ≤ 2 * (m + 1)
  L_comp : IsComponentOf L Γ
  L_comm : ∃ a ∈ A, ∃ l ∈ L, a * l ≠ l * a
  L_normal : ∀ γ ∈ Γ, ∀ l ∈ L, γ * l * γ⁻¹ ∈ L
  L_irr : IsIrr L ⊤

theorem OneCompSetting.of_g93Hyp {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m) :
    OneCompSetting Γ A L m :=
  ⟨h.quotient, h.A_le, h.A_elem, h.A_card, h.bound, h.L_comp, h.L_comm, h.H_normal, h.H_irr⟩

@[expose] def CompType (X : Type) [Group X] : Prop :=
  (IsSimpleGroup X ∧ A23List X) ∨ (Nat.card (Subgroup.center X) = 3 ∧ A36Case2List X)

@[expose] def OneCompFor (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ A L : Subgroup (GLV V)) (m : ℕ),
    OneCompSetting Γ A L m → P ↥L → G93Concl Γ L m

@[expose] def DescentOne : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ A L : Subgroup (GLV V)) (m : ℕ),
    G93Hyp Γ A L L m → CompType ↥L

@[expose] def TwoComp : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Γ A L H : Subgroup (GLV V)) (m : ℕ), G93Hyp Γ A L H m →
    (∃ L₂ : Subgroup (GLV V), IsComponentOf L₂ Γ ∧ L₂ ≠ L ∧ H = L ⊔ L₂ ∧ QuasiEquivalent L L₂) →
    G93Case14 H m ∨ G93Case15 H m


theorem OneCompFor.mono {P Q : ∀ (X : Type) [Group X], Prop}
    (hPQ : ∀ (X : Type) [Group X], Q X → P X) (h : OneCompFor P) : OneCompFor Q :=
  fun V _ _ _ Γ A L m hs hQ => h V Γ A L m hs (hPQ ↥L hQ)

theorem OneCompFor.or {P Q : ∀ (X : Type) [Group X], Prop} (hP : OneCompFor P)
    (hQ : OneCompFor Q) : OneCompFor fun X _ => P X ∨ Q X :=
  fun V _ _ _ Γ A L m hs hPQ => hPQ.elim (hP V Γ A L m hs) (hQ V Γ A L m hs)

@[expose] def FamAlt (n : ℕ) (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ Nonempty (X ≃* alternatingGroup (Fin n))

@[expose] def FamOddL2 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ∃ f : ℕ, (f = 1 ∨ f = 2) ∧ StatedClassicalModel X .PSL 2 p f

@[expose] def FamOddL3 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ StatedClassicalModel X .PSL 3 p 1

@[expose] def FamOddU3 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ StatedClassicalModel X .PSU 3 p 1

@[expose] def FamL2 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel X .PSL 2 2 f

@[expose] def FamL3 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ f : ℕ, 1 ≤ f ∧ StatedClassicalModel X .PSL 3 2 f

@[expose] def FamU3 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel X .PSU 3 2 f

@[expose] def FamSp4 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel X .PSp 2 2 f

@[expose] def FamG2 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f

@[expose] def Fam3D4 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f

@[expose] def Fam2F4 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f

@[expose] def FamSz (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ SuzukiModel X 2 f

@[expose] def FamTits (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ReeTitsModel X .Tits 2 1

@[expose] def FamLn2 (n : ℕ) (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ StatedClassicalModel X .PSL n 2 1

@[expose] def FamSpor (s : TauCeti.SporadicName) (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ Nonempty (X ≃* NativeSporadic.Carrier s)

@[expose] def FamCoverSL3 (X : Type) [Group X] : Prop :=
  Nat.card (Subgroup.center X) = 3 ∧ ∃ (s : Bool) (p e : ℕ), p.Prime ∧ 1 ≤ e ∧
    ((p = 2 ∧ Int.ModEq 3 ((p ^ e : ℕ) : ℤ) (if s then 1 else -1)) ∨ (p ≠ 2 ∧ e = 1)) ∧
    IsSLEps3 s (p ^ e) X

@[expose] def FamHat (S : Type) [Group S] (X : Type) [Group X] : Prop :=
  Nat.card (Subgroup.center X) = 3 ∧ IsHat X S

@[expose] def FamOddL2Small (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ∃ f : ℕ, (f = 1 ∨ f = 2) ∧ (p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9) ∧
      StatedClassicalModel X .PSL 2 p f

@[expose] def FamOddL2Big (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ∃ f : ℕ, (f = 1 ∨ f = 2) ∧ p ^ f ≠ 5 ∧ p ^ f ≠ 7 ∧ p ^ f ≠ 9 ∧
      StatedClassicalModel X .PSL 2 p f

@[expose] def FamU33 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ StatedClassicalModel X .PSU 3 3 1

@[expose] def FamOddU3Big (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ StatedClassicalModel X .PSU 3 p 1

@[expose] def FamCoverSL3Two (X : Type) [Group X] : Prop :=
  Nat.card (Subgroup.center X) = 3 ∧ ∃ e : ℕ, 1 ≤ e ∧ Int.ModEq 3 ((2 ^ e : ℕ) : ℤ) 1 ∧
    IsSL3 (2 ^ e) X

@[expose] def FamCoverSU3Two (X : Type) [Group X] : Prop :=
  Nat.card (Subgroup.center X) = 3 ∧ ∃ e : ℕ, 1 ≤ e ∧ Int.ModEq 3 ((2 ^ e : ℕ) : ℤ) (-1) ∧
    IsSU3 (2 ^ e) X

@[expose] def FamCoverOdd (X : Type) [Group X] : Prop :=
  Nat.card (Subgroup.center X) = 3 ∧ ∃ (s : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ IsSLEps3 s p X

theorem oneCompFor_famOddL2 (hS : OneCompFor FamOddL2Small) (hB : OneCompFor FamOddL2Big) :
    OneCompFor FamOddL2 := by
  intro V _ _ _ Γ A L m hs ⟨hsimp, p, hp, hp2, f, hf, hm⟩
  by_cases h : p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9
  · exact hS V Γ A L m hs ⟨hsimp, p, hp, hp2, f, hf, h, hm⟩
  · push Not at h
    exact hB V Γ A L m hs ⟨hsimp, p, hp, hp2, f, hf, h.1, h.2.1, h.2.2, hm⟩

theorem oneCompFor_famOddU3 (h3 : OneCompFor FamU33) (hB : OneCompFor FamOddU3Big) :
    OneCompFor FamOddU3 := by
  intro V _ _ _ Γ A L m hs ⟨hsimp, p, hp, hp2, hm⟩
  by_cases h : p = 3
  · subst h
    exact h3 V Γ A L m hs ⟨hsimp, hm⟩
  · have h5 : 5 ≤ p := by
      have := hp.two_le
      rcases Nat.lt_or_ge p 5 with hlt | hge
      · interval_cases p <;> simp_all (config := { decide := true })
      · exact hge
    exact hB V Γ A L m hs ⟨hsimp, p, hp, h5, hm⟩

theorem oneCompFor_famCoverSL3 (h1 : OneCompFor FamCoverSL3Two) (h2 : OneCompFor FamCoverSU3Two)
    (h3 : OneCompFor FamCoverOdd) : OneCompFor FamCoverSL3 := by
  intro V _ _ _ Γ A L m hs ⟨hz, s, p, e, hp, he, hpe, hm⟩
  rcases hpe with ⟨rfl, hmod⟩ | ⟨hp2, rfl⟩
  · cases s
    · exact h2 V Γ A L m hs ⟨hz, e, he, by simpa using hmod, hm⟩
    · exact h1 V Γ A L m hs ⟨hz, e, he, by simpa using hmod, hm⟩
  · exact h3 V Γ A L m hs ⟨hz, s, p, hp, hp2, by simpa using hm⟩


end CFSG.Quasithin.G11.Harris
