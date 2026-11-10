module

public import CFSG.Milestones.ASVolI.C137.SOff
public import CFSG.Milestones.ASVolI.C137.SFin
public import CFSG.Quasithin.H13.GoldschmidtC137L32Off

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.ASVolI.ChC
open CFSG.Quasithin.L3 CFSG.Quasithin.H13.U3 CFSG.Quasithin.H13.U3.GC137
open scoped commutatorElement

variable {G : Type} [Group G]

structure burnsideC137_SCtx (X T L P U : Subgroup G) (α : ↥L →* Γ) (U₁ U₂ : Subgroup G)
    (β₁ : ↥U₁ →* Multiplicative Vec) (β₂ : ↥U₂ →* Multiplicative Vec) : Prop where
  hT : IsSylowTwoOf T X
  hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t
  hL : L ∈ cComp X
  lie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1
  hTP : T ≤ P
  hPX : P < X
  hmax : ∀ H : Subgroup G, P ≤ H → H ≤ X → H = P ∨ H = X
  hred : IsTwoReducedIn X U
  hUL : ⁅U, L⁆ = U
  hs : SumOfTwoNat L U α U₁ U₂ β₁ β₂
  hdyn : ∀ t ∈ T, ∃ l : ↥L, ∀ x y : ↥L, (y : G) = t * x * t⁻¹ →
      (QuotientGroup.mk y : ↥L ⧸ CFSG.pCore 2 ↥L) = QuotientGroup.mk (l * x * l⁻¹)

namespace burnsideC137_SCtx

variable [Finite G] {X T L P U U₁ U₂ : Subgroup G} {α : ↥L →* Γ}
  {β₁ : ↥U₁ →* Multiplicative Vec} {β₂ : ↥U₂ →* Multiplicative Vec}
  (h : burnsideC137_SCtx X T L P U α U₁ U₂ β₁ β₂)
include h

omit [Finite G] in
theorem hLX : L ≤ X := le_of_mem_cComp h.hL

theorem hn : X ≤ normalizer (L : Set G) := C124.le_normalizer_of_prod h.hT h.hprod h.hL


omit [Finite G] in
theorem hU : IsElemAbelian 2 U := h.hred.2.2.1


omit [Finite G] in
theorem hTodd : ¬ 2 ∣ T.relIndex P := fun h2 => by
  have h3 := Subgroup.relIndex_mul_relIndex T P X h.hTP h.hPX.le
  have h4 : 2 ∣ T.relIndex X := by
    rw [← h3]
    exact Dvd.dvd.mul_right h2 _
  exact h.hT.2.2 h4

theorem hRT : pCoreOf 2 P ≤ T :=
  pCoreOf_two_le_of_sylowIn h.hTP h.hT.2.1 h.hTodd

theorem hQR : pCoreOf 2 X ≤ pCoreOf 2 P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQT : pCoreOf 2 X ≤ T := pCoreOf_two_le_of_sylowIn h.hT.1 h.hT.2.1 h.hT.2.2
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans h.hTP)
    (h.hPX.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)


theorem hR2 : IsPGroup 2 (pCoreOf 2 P) := isPGroup_pCoreOf_two_gc P


theorem card_U : Nat.card U = 64 := burnsideC137_card_U h.hs h.hU

theorem hU1 : U ≠ ⊥ := by
  intro hb
  have h1 := h.card_U
  rw [hb, Subgroup.card_bot] at h1
  omega

theorem hVL : ⁅U, L⁆ ≠ ⊥ := by
  rw [h.hUL]
  exact h.hU1

theorem hb2102 :
    (IsSylowTwoOf (pCoreOf 2 (X ⊓ centralizer (U : Set G))) (X ⊓ centralizer (U : Set G)) ∧
      pCoreOf 2 X = pCoreOf 2 P ⊓ centralizer (U : Set G)) ∧
    (CFSG.IsQuasisimple ↥(autI h.hU L) ∨ Nat.card ↥(autI h.hU L) = 3) ∧
    quasithinGenFitting (autI h.hU X) = autI h.hU L ∧
    (baum (pCoreOf 2 P) = baum (pCoreOf 2 X) ∨
      (IsStableFF (autI h.hU X) (C124.offenderImagesConjIn h.hU X (pCoreOf 2 P)) ∧
        ffJP (C124.offenderImagesConjIn h.hU X (pCoreOf 2 P)) (autI h.hU X) ≤
          ffJ (autI h.hU X) ∧
        quasithinGenFitting (ffJP (C124.offenderImagesConjIn h.hU X (pCoreOf 2 P))
          (autI h.hU X)) = autI h.hU L)) :=
  C124.B2_10_2 h.hU h.hred h.hQR h.hRT h.hT h.hLX h.hn h.hprod h.hVL
    (Or.inl (isQuasisimple_L32 h.lie))


end burnsideC137_SCtx

end CFSG.ASVolI
