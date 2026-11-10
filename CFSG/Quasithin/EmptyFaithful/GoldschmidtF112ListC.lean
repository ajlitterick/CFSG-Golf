module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112Slice

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Lists

variable {G : Type} [Group G]

@[expose] def F112ListC (L1 L2 S : Subgroup G) : Prop :=
  let α := RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)
  (∃ f : ℕ, 1 ≤ f ∧ IsAmalgamOfGroup α (IsLieOverTwo .PSL 3 f) ∧
      ((2 ≤ f ∧ IsBlock2 L1 L1 ∧ IsLin2Type L1 f ∧ IsBlock2 L2 L2 ∧ IsLin2Type L2 f) ∨
        (f = 1 ∧ Nonempty (↥(L1 ⊔ S) ≃* Equiv.Perm (Fin 4)) ∧
          Nonempty (↥(L2 ⊔ S) ≃* Equiv.Perm (Fin 4))))) ∨
  (∃ f : ℕ, 1 ≤ f ∧ IsAmalgamOfGroup α (IsSp4Over f) ∧
      ((2 ≤ f ∧ IsBlock2 L1 L1 ∧ IsLin2Type L1 f ∧ IsBlock2 L2 L2 ∧ IsLin2Type L2 f) ∨
        (f = 1 ∧ Nonempty (↥(L1 ⊔ S) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
          Nonempty (↥(L2 ⊔ S) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))))) ∨
  (∃ f : ℕ, 1 ≤ f ∧ IsAmalgamOfGroup α (IsG2Over f) ∧
      IsL2Quot f (oTwoQuot ↥L1) ∧ IsL2Quot f (oTwoQuot ↥L2) ∧
      IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ f) ^ 5) ∨
  (∃ f : ℕ, 1 ≤ f ∧ IsAmalgamOfGroup α (IsLieOverTwo .trialityD4 0 f) ∧
      IsL2Quot (3 * f) (oTwoQuot ↥L1) ∧
      IsSpecialPow 2 (2 ^ f) 4 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      IsL2Quot f (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ f) ^ 11) ∨
  (∃ a : ℕ, IsAmalgamOfGroup α (IsTwistedF4Over (2 * a + 1)) ∧
      (Nonempty (oTwoQuot ↥L1 ≃* Sz a) ∨ (a = 0 ∧ Nonempty (oTwoQuot ↥L1 ≃* DihedralGroup 5))) ∧
      Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ 10 ∧
      IsL2Quot (2 * a + 1) (oTwoQuot ↥L2) ∧
      Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ 11) ∨
  (∃ f : ℕ, 1 ≤ f ∧ (IsAmalgamOfGroup α (IsLieOverTwo .PSU 4 f) ∨ IsU4ExtTwo f α) ∧
      IsL2Quot f (oTwoQuot ↥L1) ∧ IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      IsBlock2 L2 L2 ∧ IsL2Quot (2 * f) (oTwoQuot ↥L2) ∧
      IsOmega4MinusType L2 f ∧ (f = 1 → IsAltType L2 5)) ∨
  (IsAmalgamOfGroup α (IsLieOverTwo .PSU 5 2) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ^ 2 ∧
        Nonempty (oTwoQuot ↥L1 ≃* CFSG.Open.StatedSU 3 4 F)) ∧
      IsSpecialPow 2 4 3 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧ IsL2Quot 4 (oTwoQuot ↥L2) ∧
      Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 16) ∨
  (IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* PSU3 3 1)) ∧
      IsL2Quot 1 (oTwoQuot ↥L1) ∧ IsL2Quot 1 (oTwoQuot ↥L2) ∧
      IsZ4StarQ8 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧ IsZ4Sq ↥(pCoreOf 2 (L2 ⊔ bigB L1 L2 S))) ∨
  (IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinTits)) ∧
      (Nonempty (oTwoQuot ↥L1 ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥L1 ≃* ↥(Sz 0))) ∧
      Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = 2 ^ 9 ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 10) ∨
  (IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinJ2)) ∧
      IsL2Quot 2 (oTwoQuot ↥L1) ∧ IsQ8D8 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 6) ∨
  (IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* MulAut quasithinJ2)) ∧
      Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* Equiv.Perm (Fin 5)) ∧
      IsQ8D8 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)) ∧
      Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 6) ∨
  (IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinM12)) ∧
      IsL2Quot 1 (oTwoQuot ↥L1) ∧ IsQ8Sq ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 5) ∨
  (IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* MulAut quasithinM12)) ∧
      IsL2Quot 1 (oTwoQuot ↥L1) ∧ IsAutM12Vertex (L1 ⊔ bigB L1 L2 S) ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 6)

@[expose] def F112ConclC (L1 L2 S : Subgroup G) : Prop :=
  ∃ L1' L2' : Subgroup G, ((L1' = L1 ∧ L2' = L2) ∨ (L1' = L2 ∧ L2' = L1)) ∧
    (centerOf S ≤ Subgroup.centralizer (L1 : Set G) ∨
        centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
      centerOf S ≤ Subgroup.centralizer (L1' : Set G)) ∧
    F112ListC L1' L2' S ∧ F112Second L1' L2' S

theorem F112ConclC.symm {L1 L2 S : Subgroup G} (h : F112ConclC L1 L2 S) : F112ConclC L2 L1 S := by
  obtain ⟨L1', L2', hsw, hZ, hl, h2⟩ := h
  exact ⟨L1', L2', hsw.symm, fun hc => hZ hc.symm, hl, h2⟩


end Lists

@[expose] def F112ConclPredC : F112Conc :=
  fun _ _ _ L1 L2 S => F112ConclC L1 L2 S


end CFSG.Quasithin
