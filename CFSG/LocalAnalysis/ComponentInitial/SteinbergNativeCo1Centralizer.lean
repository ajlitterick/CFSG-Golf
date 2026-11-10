module

public import CFSG.Monster.Visible.Irreducible
public import CFSG.Monster.VisQuot.Simple
public import CFSG.LinearAlgebra.IrreducibleBinaryCentralizerField

public section

namespace CFSG.LocalAnalysis.ComponentInitial.NativeCo1Centralizer

open CFSG.Monster CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.LinearAlgebra

open scoped IsMulCommutative

@[expose] noncomputable def visImage :
    Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod)) :=
  repQuot.range

noncomputable abbrev linCentralizer :
    Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod)) :=
  Subgroup.centralizer (visImage : Set (LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod)))

theorem natCard_visImage : Nat.card visImage = 4157776806543360000 := by
  rw [visImage, ← natCard_visQuot]
  exact Nat.card_congr (MonoidHom.ofInjective repQuot_injective).toEquiv.symm

theorem visImage_irreducible (W : Submodule (ZMod 2) (Additive VisMod))
    (hW : ∀ h ∈ visImage, ∀ w ∈ W, (h : Additive VisMod →ₗ[ZMod 2] Additive VisMod) w ∈ W) :
    W = ⊥ ∨ W = ⊤ :=
  visible_quotient_irreducible_action.1 W fun g w hw => hW _ ⟨g, rfl⟩ w hw

theorem eq_of_dvd_24 {d : ℕ} (hd : 0 < d) (hdvd : d ∣ 24) :
    d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 6 ∨ d = 8 ∨ d = 12 ∨ d = 24 := by
  have hle : d ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases d <;> simp_all

theorem not_dvd_natCard_GL {F : Type*} [Field F] [Finite F] {d : ℕ} (hF : Nat.card F = 2 ^ d)
    (hd0 : 0 < d) (hdvd : d ∣ 24) (hd : 3 ≤ d) : ¬ 23 ∣ Nat.card (GL (Fin (24 / d)) F) := by
  have := Fintype.ofFinite F
  rw [Matrix.card_GL_field, Fintype.card_eq_nat_card, hF,
    Prime.dvd_finsetProd_iff (Nat.prime_iff.1 (by norm_num : Nat.Prime 23))]
  rcases eq_of_dvd_24 hd0 hdvd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | omega | decide

theorem finite_gl : Finite (LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod)) := by
  have : Module.Finite (ZMod 2) (Additive VisMod) := Module.finite_of_finrank_eq_succ finrank_visMod
  have : Finite (Additive VisMod) := Module.finite_of_finite (ZMod 2)
  have : Finite (Module.End (ZMod 2) (Additive VisMod)) := Module.finite_of_finite (ZMod 2)
  exact Finite.of_injective (Units.val : (Module.End (ZMod 2) (Additive VisMod))ˣ → _)
    Units.val_injective

theorem pow_three_eq_one (a : LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod))
    (ha : a ∈ linCentralizer) : a ^ 3 = 1 := by
  have : FiniteDimensional (ZMod 2) (Additive VisMod) :=
    Module.finite_of_finrank_eq_succ finrank_visMod
  obtain ⟨hR, d, hd0, hdvd, hcard, hord, hφ, -⟩ :=
    irreducible_binary_linear_centralizer_field_degree_bound (by norm_num) finrank_visMod visImage
      visImage_irreducible a ha
  by_cases hd : 3 ≤ d
  · exfalso
    let : Field (Algebra.adjoin (ZMod 2) {(a : Module.End (ZMod 2) (Additive VisMod))}) :=
      hR.toField
    obtain ⟨φ, hφ⟩ := hφ
    have : Finite (Algebra.adjoin (ZMod 2) {(a : Module.End (ZMod 2) (Additive VisMod))}) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    exact not_dvd_natCard_GL hcard hd0 hdvd hd
      ((show 23 ∣ Nat.card visImage by rw [natCard_visImage]; norm_num).trans
        (Subgroup.card_dvd_of_injective φ hφ))
  · rw [not_le] at hd
    interval_cases d
    · have ha1 : a = 1 := by simpa using orderOf_dvd_iff_pow_eq_one.1 hord
      rw [ha1, one_pow]
    · exact orderOf_dvd_iff_pow_eq_one.1 hord


theorem pow_three_of_mem (g : linCentralizer) : g ^ 3 = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact pow_three_eq_one g g.2)


end CFSG.LocalAnalysis.ComponentInitial.NativeCo1Centralizer
