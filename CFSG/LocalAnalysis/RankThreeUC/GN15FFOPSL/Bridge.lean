module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOVacuity
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Bridge.Rep
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL

open CFSG.Assembly.LowTwoRank CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups Matrix

theorem exists_cover_of_psl_model
    {L : Type} [Group L] [Finite L]
    (hperf : Group.IsPerfect L) (hodd : Odd (Nat.card (Subgroup.center L)))
    {m f : ℕ} (hf : 1 ≤ f)
    (hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL m 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 2 ^ f ∧ CharP K 2 ∧ 2 ≤ m ∧
      ∃ φ' : Matrix.SpecialLinearGroup (Fin m) K →* L,
        Function.Surjective φ' ∧ φ'.ker ≤ LinearFlag.scalars m K ∧
        (LinearFlag.scalars m K).map φ' = Subgroup.center L := by
  classical
  obtain ⟨hadm, K, iK, iKfin, hKcard, ⟨eP⟩⟩ := hmodel
  have hPerf : Group.IsPerfect L := hperf
  have hm2 : 2 ≤ m := hadm.2.2.1
  have hchar : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hKcard
  obtain ⟨φ, hφs, hker, hmap⟩ :=
    CFSG.SectionRank.EvenCover.even_linear_perfect_odd_cover_map (K := K) (n := m) hm2
      hodd eP
  let ε := specialLinearGroupEquivStatedSL m K
  let φ' : Matrix.SpecialLinearGroup (Fin m) K →* L := φ.comp ε.toMonoidHom
  refine ⟨K, iK, iKfin, hKcard, hchar, hm2, φ', ?_, ?_, ?_⟩
  · exact hφs.comp ε.surjective
  · intro x hx
    have h1 : ε x ∈ φ.ker := hx
    have h2 : ε x ∈ (StatedScalars (Fin m) K).subgroupOf (StatedSL m K) := hker h1
    rw [← map_center_eq_statedScalars m K] at h2
    obtain ⟨y, hy, hyx⟩ := h2
    have hxy : y = x := ε.injective hyx
    rw [LinearFlag.scalars_eq_center]
    exact hxy ▸ hy
  · rw [LinearFlag.scalars_eq_center, ← Subgroup.map_map]
    have hc := map_center_eq_statedScalars m K
    exact (congrArg (Subgroup.map φ) hc).trans hmap

theorem scalarElement_pow_eq_one {K : Type} [Field K] {m k : ℕ} (c : Kˣ)
    (hc : c ^ m = 1) (hck : c ^ k = 1) :
    LinearFlag.scalarElement c hc ^ k = 1 := by
  apply Subtype.ext
  calc ((LinearFlag.scalarElement c hc ^ k : Matrix.SpecialLinearGroup (Fin m) K) :
        Matrix (Fin m) (Fin m) K)
      = (Matrix.scalar (Fin m) (c : K)) ^ k := by
        rw [Matrix.SpecialLinearGroup.coe_pow, LinearFlag.coe_scalarElement]
    _ = Matrix.scalar (Fin m) ((c : K) ^ k) :=
        (map_pow (Matrix.scalar (Fin m)) (c : K) k).symm
    _ = 1 := by rw [← Units.val_pow_eq_pow_val, hck, Units.val_one, map_one]

theorem scalarElement_map_eq_one {L : Type} [Group L] [Finite L]
    {K : Type} [Field K] [Finite K] {m r : ℕ}
    (φ' : Matrix.SpecialLinearGroup (Fin m) K →* L)
    (hmap : (LinearFlag.scalars m K).map φ' = Subgroup.center L)
    (hr : r.Prime) (hZ : ¬ r ∣ Nat.card (Subgroup.center L))
    (c : Kˣ) (hc : c ^ m = 1) (hcr : c ^ r = 1) :
    φ' (LinearFlag.scalarElement c hc) = 1 := by
  classical
  let s : Matrix.SpecialLinearGroup (Fin m) K := LinearFlag.scalarElement c hc
  have hmem : φ' s ∈ Subgroup.center L := by
    have hs : φ' s ∈ (LinearFlag.scalars m K).map φ' :=
      Subgroup.mem_map_of_mem φ' (LinearFlag.scalarElement_mem_scalars c hc)
    rwa [hmap] at hs
  have hpm : (φ' s) ^ m = 1 := by
    rw [← map_pow, scalarElement_pow_eq_one c hc hc, map_one]
  have hpr : (φ' s) ^ r = 1 := by
    rw [← map_pow, scalarElement_pow_eq_one c hc hcr, map_one]
  have hdm : orderOf (φ' s) ∣ m := orderOf_dvd_of_pow_eq_one hpm
  have hdr : orderOf (φ' s) ∣ r := orderOf_dvd_of_pow_eq_one hpr
  have hdZ : orderOf (φ' s) ∣ Nat.card (Subgroup.center L) := by
    have := orderOf_dvd_natCard (⟨φ' s, hmem⟩ : Subgroup.center L)
    simpa [Subgroup.orderOf_mk] using this
  rcases (Nat.dvd_prime hr).1 hdr with h1 | hr'
  · exact orderOf_eq_one_iff.1 h1
  · exact absurd (hr' ▸ hdZ) hZ

theorem pslNoOffenderAt_of_linear
    {m f r : ℕ} (hm : 3 ≤ m) (hf : 1 ≤ f) (hr : r.Prime)
    (hcore : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
      ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
        (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin m) K) W),
        ρ.IsIrreducible →
        (∀ g, ρ g = 1 → g ∈ LinearFlag.scalars m K) →
        (∀ (c : Kˣ) (hc : c ^ m = 1), c ^ r = 1 →
          ρ (LinearFlag.scalarElement c hc) = 1) →
        ∀ A : Subgroup (W ≃ₗ[ZMod 2] W), A ≠ ⊥ → CFSG.IsElementaryAbelian 2 ↥A →
          (∀ a ∈ A, ∀ b ∈ A, ∀ w, b (a w - w) = a w - w) →
          (∀ a ∈ A, ∀ x, ∃ y, ∀ w, a (ρ x w) = ρ y (a w)) →
          Nat.card ↥A * Nat.card {w : W // ∀ a ∈ A, a w = w} < Nat.card W) :
    FFO.PSLNoOffenderAt m f r := by
  intro V _ _ hV L E hirr hperf hZ hmodel hEN hE1 hEel hEq
  classical
  have _hm : 3 ≤ m := hm
  have hNontriv : Nontrivial V := hirr.1
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) :=
    CFSG.QuasithinUnique.Setup.Family.odd_card_center_of_irreducible hV hirr.2
  obtain ⟨K, iK, iKfin, hKcard, hchar, hm2, φ', hφ', hker, hmap⟩ :=
    exists_cover_of_psl_model hperf hodd hf hmodel
  have : Fintype K := Fintype.ofFinite K
  have hKF : Fintype.card K = 2 ^ f := by
    rw [Fintype.card_eq_nat_card]; exact hKcard
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hV
  have hntW : Nontrivial W := by
    obtain ⟨v, hv⟩ := exists_ne (1 : V)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  let ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin m) K) W := repOf θ φ'
  have hirrρ : ρ.IsIrreducible := repOf_irreducible θ hirr.2 hφ'
  have hkerρ : ∀ g, ρ g = 1 → g ∈ LinearFlag.scalars m K := fun g hg =>
    hker (repOf_ker θ φ' g hg)
  have hscalar : ∀ (c : Kˣ) (hc : c ^ m = 1), c ^ r = 1 →
      ρ (LinearFlag.scalarElement c hc) = 1 := by
    intro c hc hcr
    have h1 : φ' (LinearFlag.scalarElement c hc) = 1 :=
      scalarElement_map_eq_one φ' hmap hr hZ c hc hcr
    refine LinearMap.ext fun w => ?_
    rw [repOf_apply, h1]
    simp
  have hA1 : E.map (binPsi θ).toMonoidHom ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective E (binPsi θ).injective]
    exact hE1
  have hAel : CFSG.IsElementaryAbelian 2 ↥(E.map (binPsi θ).toMonoidHom) :=
    (isElemAbelian2_iff_map θ E).1 hEel
  have hquad : ∀ a ∈ E.map (binPsi θ).toMonoidHom, ∀ b ∈ E.map (binPsi θ).toMonoidHom,
      ∀ w, b (a w - w) = a w - w := B42SL3.quad_map θ hEq
  have hint : ∀ a ∈ E.map (binPsi θ).toMonoidHom,
      ∀ x, ∃ y, ∀ w, a (ρ x w) = ρ y (a w) := intertwines_map θ hφ' hEN
  have hlt := hcore K hKcard W ρ hirrρ hkerρ hscalar
    (E.map (binPsi θ).toMonoidHom) hA1 hAel hquad hint
  rw [Subgroup.card_map_of_injective (binPsi θ).injective, B42SL3.card_fix_map,
    ← natCard_eq θ] at hlt
  exact hlt


end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL
