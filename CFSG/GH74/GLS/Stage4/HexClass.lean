module

public import CFSG.GH74.GLS.Stage4.HexIdentify
public import CFSG.GH74.GLS.Stage4.HexRev
public import CFSG.GH74.GLS.Stage4.HexSL2Defs
public import CFSG.GH74.GLS.Stage4.Main

public noncomputable section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint
  CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank

namespace CFSG.GH74.GLS.Stage4.Hex

@[expose] def PStruct (p : ℕ) {G : Type} [Group G] (U : Subgroup G) (root : ℤ → Subgroup G) :
    Prop :=
  (∃ S : Sylow p G, (S : Subgroup G) = U) ∧
    ∀ i : ℤ, 1 ≤ i → i ≤ 6 → IsMulCommutative (root i) ∧ ∀ x ∈ root i, x ^ p = 1


@[expose] def HexMatchD4p :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (D : RankTwoSystem G 6) (p q : ℕ)
    (hq : 3 ≤ q), p.Prime → Odd q →
    (∀ i : ℤ, 1 ≤ i → i ≤ 6 → Nat.card (D.root i) = if i % 2 = 1 then q ^ 3 else q) →
      PStruct p D.U D.root →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K) (hK : Nat.card K = q ^ 3)
        (hσq : ∀ c, σ c = c ^ q), UMatch (d4ModelSystem σ (by omega) hK hσq) D


theorem lieModel_g2_of_match
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (D : RankTwoSystem G 6) {q : ℕ} (hq : 3 ≤ q)
    (h : ∃ (F : Type) (_ : Field F) (_ : Finite F) (hF : 3 ≤ Nat.card F),
      Nat.card F = q ∧ (UMatch (g2ModelSystem F hF) D ∨ UMatch (g2ModelSystem F hF) D.rev)) :
    ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f = q ∧ LieModel G .G2 0 p f := by
  obtain ⟨F, _, _, hF, hcard, hm⟩ := h
  have := Fintype.ofFinite F
  obtain ⟨p, -, n, hp, hpn⟩ := FiniteField.card' F
  have hcardp : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hpn]
  have hq' : q = p ^ (n : ℕ) := hcard.symm.trans hcardp
  have hmatch : G2RankTwoData F G hF := hm.elim (fun h => ⟨D, h⟩) (fun h => ⟨D.rev, h⟩)
  exact ⟨p, n, hp, n.pos, hq'.symm, lieModel_g2_of_rankTwoData hp n.pos (hq' ▸ hq) hcardp hmatch⟩

theorem lieModel_d4_of_match
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (D : RankTwoSystem G 6) {q : ℕ} (hq : 2 ≤ q)
    (h : ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K) (hK : Nat.card K = q ^ 3)
      (hσq : ∀ c, σ c = c ^ q), UMatch (d4ModelSystem σ hq hK hσq) D) :
    ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f = q ∧ LieModel G .trialityD4 0 p f := by
  obtain ⟨K, _, _, σ, hK, hσq, hm⟩ := h
  have := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hpn⟩ := FiniteField.card' K
  have hcardp : q ^ 3 = p ^ (n : ℕ) := by rw [← hK, Nat.card_eq_fintype_card, hpn]
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hp).1
    (show q ∣ p ^ (n : ℕ) from hcardp ▸ Dvd.intro_left _ (by ring : q * q * q = q ^ 3))
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hf
      omega
    · exact h
  exact ⟨p, f, hp, hf1, hf.symm, lieModel_d4_of_rankTwoData hp hf1 hf ⟨D, hm⟩⟩


@[expose] def HexMatchD4s :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (H : Subgroup G) (r₁ r₂ : G)
    (U : Subgroup G) (root : ℤ → Subgroup G) (R : RGD2 6 H r₁ r₂ U root)
    (hgen : (H ⊔ U) ⊔ R.N = ⊤) (p q : ℕ) (hq : 3 ≤ q), p.Prime → Odd q →
      RootOrdersD4 root q → PStruct p U root → SL2At H R.N root 1 → SL2At H R.N root 4 →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K) (hK : Nat.card K = q ^ 3)
        (hσq : ∀ c, σ c = c ^ q),
        UMatch (d4ModelSystem σ (by omega) hK hσq) (R.toPre hgen).toSystemOfSimple ∨
          UMatch (d4ModelSystem σ (by omega) hK hσq) (R.toPre hgen).toSystemOfSimple.rev

theorem lieModel_d4_of_match_or
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (D : RankTwoSystem G 6) {q : ℕ} (hq : 2 ≤ q)
    (h : ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K) (hK : Nat.card K = q ^ 3)
      (hσq : ∀ c, σ c = c ^ q), UMatch (d4ModelSystem σ hq hK hσq) D ∨
        UMatch (d4ModelSystem σ hq hK hσq) D.rev) :
    ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f = q ∧ LieModel G .trialityD4 0 p f := by
  obtain ⟨K, _, _, σ, hK, hσq, hm | hm⟩ := h
  · exact lieModel_d4_of_match D hq ⟨K, inferInstance, inferInstance, σ, hK, hσq, hm⟩
  · exact lieModel_d4_of_match D.rev hq ⟨K, inferInstance, inferInstance, σ, hK, hσq, hm⟩


end CFSG.GH74.GLS.Stage4.Hex
