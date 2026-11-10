module

public import CFSG.LocalAnalysis.GLTheoremB.BaseCase
public import CFSG.LocalAnalysis.GLTheoremB.LayerTools
public import CFSG.Quasithin.Background.F918V5GComp

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem i116n_isComponentOf_of_glaPComponent {X : Type} [Group X] {p : ℕ} (hO : GLAPPrimeCore p X = ⊥)
    {L : Subgroup X} (hL : GLAPComponent p ⊤ L) : IsComponentOf L ⊤ := by
  have hcore : GLAPPrimeCore p ↥(⊤ : Subgroup X) = ⊥ := by
    have h := glaPPrimeCore_map_iso p (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X)
    rw [hO] at h
    exact Subgroup.map_injective (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X).injective
      (by simpa using h)
  have hker : GLAPPrimeCore p ↥(⊤ : Subgroup X) ≤ (⊤ : Subgroup X).subtype.ker := by
    rw [hcore]; exact bot_le
  let ψ : (↥(⊤ : Subgroup X) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup X)) →* X :=
    QuotientGroup.lift _ (⊤ : Subgroup X).subtype hker
  have hψc : ψ.comp (QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup X))) =
      (⊤ : Subgroup X).subtype := by
    ext t; simp [ψ]
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have ht : (t : X) = 1 := by
      have := congrArg (fun f => f t) hψc
      simp only [MonoidHom.comp_apply] at this
      rw [MonoidHom.mem_ker] at hq
      exact this.symm.trans hq
    have : t = 1 := Subtype.ext ht
    simp [this]
  have hsurj : Function.Surjective ψ := by
    intro x
    exact ⟨QuotientGroup.mk' _ ⟨x, trivial⟩, by
      have := congrArg (fun f => f ⟨x, trivial⟩) hψc
      simpa using this⟩
  let e := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hL.2.2.1
  have htop : (⊤ : Subgroup (↥(⊤ : Subgroup X) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup X))).map
      (e : _ →* X) = ⊤ := Subgroup.map_top_of_surjective _ e.surjective
  rw [htop, Subgroup.map_map] at h1
  have h2 : (e : _ →* X).comp (QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup X))) =
      (⊤ : Subgroup X).subtype := hψc
  rw [h2, Subgroup.subgroupOf_map_subtype, inf_top_eq] at h1
  exact h1


end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
