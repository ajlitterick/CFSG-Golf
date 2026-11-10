module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBOrbit
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
import all CFSG.LieType.Universal.SymplecticRoots

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CoxeterSystem CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras TauCeti.GLSymplecticFin

section Standard

variable {n : ℕ} {F : Type} [Field F] {X : Type*} [Group X]


end Standard

section Data

theorem spFrameLift_range_le {n : ℕ} {F : Type} [Field F] {X : Type*} [Group X]
    (h2 : (2 : F) = 0) (hn : 2 ≤ n) {φ₁ : StatedSp n F →* X} {T : X} (h : GGSpEndNode φ₁ T)
    {H : Subgroup X} (hφ : φ₁.range ≤ H) (hT : T ∈ H) : (spFrameLift h2 hn h).range ≤ H := by
  rintro _ ⟨w, rfl⟩
  induction w using
    (coxeterMatrix (isFiniteType_cartanC (n + 1))).toCoxeterSystem.simple_induction_left with
  | one => rw [map_one]; exact one_mem H
  | mul_simple_left w j ih =>
    rw [map_mul, spFrameLift_simple]
    refine mul_mem ?_ ih
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · rw [spSpecial_zero]
      exact hT
    · rw [spSpecial_succ]
      exact hφ ⟨_, rfl⟩

theorem ggStandardCopy_PSp (n f : ℕ) (hadm : StatedLieAdmissible .PSp n 2 f) :
    ∃ ν, GGStandardCopy (lieUniversal .PSp n 2 f hadm.1).D ν := by
  have h2 : (2 : GaloisField 2 f) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (GaloisField 2 f) 2
  exact ⟨spWeylLift n h2, spWeylLift_standardCopy h2⟩

variable {G : Type} [Group G] [Finite G]

theorem ggSecFiveLocal_of_spEndNode {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) (φ₁ : StatedSp n (GaloisField 2 f) →* G)
    (hφ : Function.Injective φ₁) (hφL : φ₁.range = L) {T : G} (hT : GGSpEndNode φ₁ T)
    (hTG : T ∈ ggG0 p B x L D J)
    (hnbr : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      K ≤ L ⊔ L.map (MulAut.conj T).toMonoidHom) :
    GGSecFiveLocal p B x L D J .PSp (n + 1) f := by
  have h2 : (2 : GaloisField 2 f) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (GaloisField 2 f) 2
  have hn2 : 2 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hadm : StatedLieAdmissible .PSp (n + 1) 2 f :=
    ⟨Nat.prime_two, hf, by omega, fun h => by simp at h; omega⟩
  have hLG := le_ggG0_left p B x L D J
  have hTR : T ∈ (spFrameLift h2 hn2 hT).range := ⟨_, by rw [spFrameLift_simple, spSpecial_zero]⟩
  have hLcl : L ≤ ggClosure (Symplectic.rootDatum (n + 1) (GaloisField 2 f))
      (fun _ : Unit => ggSupp (Symplectic.rootDatum (n + 1) (GaloisField 2 f)) (spLeviJ n))
      (fun _ => spLeviHom φ₁) (spFrameLift h2 hn2 hT).range := by
    rw [← hφL, ← range_spLeviHom φ₁]
    exact range_le_ggClosure (Δ := Symplectic.rootDatum (n + 1) (GaloisField 2 f))
      (S := fun _ : Unit =>
        ggSupp (Symplectic.rootDatum (n + 1) (GaloisField 2 f)) (spLeviJ n))
      (φ := fun _ => spLeviHom φ₁) (R := (spFrameLift h2 hn2 hT).range) ()
  refine ⟨⟨hadm, by simp only [bnRank]; omega, by change 2 ≤ n + 1; omega⟩,
    spWeylLift (n + 1) h2, Unit,
    fun _ => ggSupp (Symplectic.rootDatum (n + 1) (GaloisField 2 f)) (spLeviJ n),
    fun _ => spLeviHom φ₁, spFrameLift h2 hn2 hT, fun _ => spLeviWeyl n,
    spWeylLift_standardCopy h2, fun _ γ hγ => hγ.1, spFrameLift_injective h2 hn2 hT hφ hn3,
    fun _ _ _ _ _ _ _ => rfl, fun _ v hv => spWeylLift_mem_levi h2 hv,
    fun _ v hv => spFrame_eq_ggExt h2 hn2 hT hv,
    fun _ w j hj => spLevi_refl_mem (by omega) w j hj, ?_,
    fun w _ α hα hfix z hz => spFrame_hcent h2 hn2 hT hn3 w α hα hfix z hz,
    spLevi_orbit _ hn, ⟨(), spLevi_hnt hφ (by omega)⟩, fun _ => ?_,
    spFrameLift_range_le h2 hn2 hT (hφL ▸ hLG) hTG, hLcl, fun y K hK => ?_⟩
  · intro w _ _ α hα hwα
    obtain ⟨v, hv, hvα⟩ := spLevi_transitive (by omega) w hα hwα
    exact ⟨α, hα, hα, 1, one_mem _, v, hv, by rw [map_one, Module.End.one_apply], hvα⟩
  · exact ((range_spLeviHom φ₁).trans hφL).le.trans hLG
  · refine (hnbr y K hK).trans (sup_le hLcl ?_)
    rw [← hφL, ← range_spLeviHom φ₁]
    exact le_iSup_of_le ⟨T, hTR⟩ (le_iSup_of_le () le_rfl)

end Data

section Config

variable {G : Type} [Group G] [Finite G]

@[expose] def GGTypeCNbr (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (n f : ℕ)
    (y : G) (K : Subgroup G) : Prop :=
  StatedClassicalModel (L ⧸ Subgroup.center L) .PSp n 2 f ∧ 4 ≤ n ∧ GGScalarsPmOne Bs ∧
    GGNbr p B x D J y K ∧ StatedClassicalModel (K ⧸ Subgroup.center K) .PSp n 2 f ∧
    GGWeylOfType p (CoxeterMatrix.B (n + 1)) (ggAutomizer L Bs ⊔ ggAutomizer K Bs)

end Config

@[expose] def GGSpLiftInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (n f : ℕ), 4 ≤ n → commutator L = ⊤ →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSp n 2 f →
      ∃ φ₁ : StatedSp n (GaloisField 2 f) →* G, Function.Injective φ₁ ∧ φ₁.range = L

@[expose] def GGSpJoinEndNodeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGOpAutTrivial p Bs →
    GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → GGTypeCNbr p B Bs x L D J n f y K →
    ∀ φ₁ : StatedSp n (GaloisField 2 f) →* G, Function.Injective φ₁ → φ₁.range = L →
      ∃ T : G, T ∈ L ⊔ K ∧ GGSpEndNode φ₁ T ∧ K ≤ L ⊔ L.map (MulAut.conj T).toMonoidHom

@[expose] def GGSpJoinInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGOpAutTrivial p Bs →
    GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → GGTypeCNbr p B Bs x L D J n f y K →
      ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' → K' ≤ L ⊔ K

section Rest

@[expose] def GGSecFiveWeylBRestInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
      (∃ n, 2 ≤ n ∧ GGSecFiveWeylAt p B Bs x L D J (CoxeterMatrix.B n)) →
      (¬ ∃ (n : ℕ) (y : G) (K : Subgroup G), GGTypeAHalfNbr p B Bs x L D J n y K) →
      (¬ ∃ (n f : ℕ) (y : G) (K : Subgroup G), GGTypeCNbr p B Bs x L D J n f y K) →
      GGSecFiveData p B x L D J

theorem ggSecFiveWeylBInput_of_typeC (hL : GGSpLiftInput) (hE : GGSpJoinEndNodeInput)
    (hJ : GGSpJoinInput) (hR : GGSecFiveWeylBRestInput) : GGSecFiveWeylBInput := by
  intro G _ _ p B Bs x L D J hR' hWC hB hH
  by_cases hC : ∃ (n f : ℕ) (y : G) (K : Subgroup G), GGTypeCNbr p B Bs x L D J n f y K
  · obtain ⟨n, f, y, K, hN⟩ := hC
    obtain ⟨hcfg, hOp, hInn, hNoTr, -, -⟩ := hR'
    have hperf : commutator L = ⊤ := hcfg.1.2.2.2.2.2.2.2.1.1
    have hf : 1 ≤ f := hN.1.1.2.1
    obtain ⟨φ₁, hφ, hφL⟩ := hL G L n f hN.2.1 hperf hN.1
    obtain ⟨T, hTLK, hT, hKle⟩ := hE G p B Bs x L D J n f y K hcfg hOp hInn hNoTr hN φ₁ hφ hφL
    have hTG : T ∈ ggG0 p B x L D J :=
      (sup_le (le_ggG0_left p B x L D J) (le_ggG0_of_ggNbr hN.2.2.2.1)) hTLK
    exact Or.inr (Or.inl ⟨.PSp, n + 1, f, ggSecFiveLocal_of_spEndNode hN.2.1 hf φ₁ hφ hφL hT hTG
      fun y' K' hK' => (hJ G p B Bs x L D J n f y K hcfg hOp hInn hNoTr hN y' K' hK').trans
        (sup_le le_sup_left hKle)⟩)
  · exact hR G p B Bs x L D J hR' hWC hB hH hC

end Rest

section Assembly

open CFSG.Blueprint CFSG.RankThree.PartTwo.Sec21


end Assembly

end CFSG.StandardType
