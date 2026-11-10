module

public import CFSG.ClassicalInvolution.RouteD.GapsMoved
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpinOdd
public import CFSG.ClassicalInvolution.RouteD.GapsPatternDMain
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBAdapt
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpin
public import CFSG.ClassicalInvolution.RouteD.GapsScenario
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBWeakNodes

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups modelUniv InClass
  IsClassicalMember LocalOddCentral ExactMembers centralizingMembers ConjInvariant LieSystemData
  centralizingLayer_le_centralizer)
open CFSG.ClassicalInvolution.Balance (iSup_rankOneImage_eq_range rankOneImage)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

theorem exists_adapted_y_normal' {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G}
    (hΩ : ConjInvariant Ω) {Y : LieUniversal} (ψ : Y.K →* locQuot Ω z)
    {n : Fin Y.D.rank → Y.K} {H : Fin Y.D.rank → Subgroup Y.K}
    (hct : IsCTGroupDatum (coxeterMatrix Y.D.isFiniteType).toCoxeterSystem
      (weylAction Y.D.isFiniteType) Y.D.roots Y.D.rootGroup n H)
    (hPat : PatternLemma Y.D.cartan) {t : G} (ht : t * z * t⁻¹ = z)
    (v : Fin Y.D.rank → ZMod 2) (hv : v ≠ 0) (k₀ : Y.K)
    (hT : ∀ γ ∈ Y.D.roots,
      ((conjSub k₀ (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ))).map ψ).map
          (locAut hΩ ht).toMonoidHom = (conjSub k₀ (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ))).map ψ ∧
        ((∀ x ∈ (conjSub k₀ (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ))).map ψ, locAut hΩ ht x = x) ↔
          charOf v γ = 0))
    {j : Fin Y.D.rank → Subgroup G}
    (hjimg : ∀ a, locImg Ω z (j a) = (rankOne Y.D.rootGroup a).map ψ) :
    ∃ y ∈ locLayer Ω z, ∃ p₀ : Fin Y.D.rank, CharReach Y.D.cartan v (Pi.single p₀ 1) ∧ ∀ a,
      ((∀ x ∈ locImg Ω z (conjSub y (j a)), locAut hΩ ht x = x) ↔ a ≠ p₀) ∧
      (locImg Ω z (conjSub y (j a))).map (locAut hΩ ht).toMonoidHom =
        locImg Ω z (conjSub y (j a)) := by
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk_surjective (ψ k₀)
  let ψ₀ : Y.K →* locQuot Ω z := ψ.comp (MulAut.conj k₀).toMonoidHom
  have hmap : ∀ S : Subgroup Y.K, (conjSub k₀ S).map ψ = S.map ψ₀ := fun S => by
    unfold conjSub
    rw [Subgroup.map_map]
  have hT₀ : ∀ γ ∈ Y.D.roots,
      ((Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ)).map ψ₀).map (locAut hΩ ht).toMonoidHom =
          (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ)).map ψ₀ ∧
        ((∀ x ∈ (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ)).map ψ₀, locAut hΩ ht x = x) ↔
          charOf v γ = 0) := fun γ hγ => by
    rw [← hmap]
    exact hT γ hγ
  have hjimg₀ : ∀ a, locImg Ω z (conjSub (y₀ : G) (j a)) =
      (rankOne Y.D.rootGroup a).map ψ₀ := fun a => by
    rw [locImg_conjSub_layer, hjimg a, show locMk Ω z y₀ = ψ k₀ from hy₀,
      map_conj_map_hom, hmap]
  obtain ⟨w, hw, p₀, rfl⟩ := hPat v hv
  obtain ⟨W₀, k, hk, hW₀⟩ := exists_actsAs_of_charReach hct hw
  obtain ⟨y₁, hy₁⟩ := QuotientGroup.mk_surjective (ψ₀ k)
  refine ⟨(y₁ : G) * (y₀ : G), (locLayer Ω z).mul_mem y₁.2 y₀.2, p₀, hw, fun a => ?_⟩
  have hroot : weylAction Y.D.isFiniteType W₀ (Pi.single a 1) ∈ Y.D.roots :=
    weylAction_mem_roots _ W₀ (single_mem_roots _ a)
  have himg : locImg Ω z (conjSub ((y₁ : G) * (y₀ : G)) (j a)) =
      (Y.D.rootGroup (weylAction Y.D.isFiniteType W₀ (Pi.single a 1)) ⊔
        Y.D.rootGroup (-weylAction Y.D.isFiniteType W₀ (Pi.single a 1))).map ψ₀ := by
    rw [CFSG.ClassicalInvolution.Generic.conjSub_mul, locImg_conjSub_layer, hjimg₀ a,
      show locMk Ω z y₁ = ψ₀ k from hy₁, map_conj_map_hom]
    congr 1
    exact conjSub_rankOne_of_actsAs hk (single_mem_roots _ a)
      (CFSG.Timmesfeld.LevisExtras.neg_mem_roots (single_mem_roots _ a))
  obtain ⟨hstab, hfixiff⟩ := hT₀ _ hroot
  rw [himg]
  refine ⟨?_, hstab⟩
  rw [hfixiff, hW₀ a, Pi.single_apply]
  by_cases hap : a = p₀
  · simp [hap]
  · simp [hap]

section Path

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
  {tY : StatedLieTag} {nY : ℕ}

@[expose] def adjPath (n : ℕ) (a b : Fin n) : Prop := a.val + 1 = b.val

local macro "pidx_tac" : tactic =>
  `(tactic| first
    | (simp [LNodes.Adj, adjPath]; done)
    | (simp [LNodes.Adj, adjPath]; omega)
    | (apply fin_ne_of_val_ne; simp only; omega)
    | (left; apply Fin.ext; simp only; omega)
    | (right; apply Fin.ext; simp only; omega))

theorem path_interior_false {n : ℕ} (hn : 7 ≤ n)
    (hF : OrthGeom (Subgroup.center (modelUniv tY nY p f Fact.out).K)
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) (GaloisField p f))
    (c : TCtx p f tY nY Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 tY nY Ω z) (nd : LNodes p f (adjPath n) Ω K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    {pp : Fin n} (hfix : ∀ a, a ≠ pp → Commutes β (nd.J a))
    (hmov : ¬ Commutes β (nd.J pp)) (hnorm : conjSub t (nd.J pp) = nd.J pp)
    (h1 : 1 ≤ pp.val) (h2 : pp.val + 2 ≤ n) : False := by
  have hpt : pp.val < n := pp.isLt
  have hcases : pp.val = 1 ∨ (2 ≤ pp.val ∧ pp.val ≤ 3) ∨ 4 ≤ pp.val := by omega
  rcases hcases with h | h | h
  ·
    refine scenarioA hF c hsingle hshape nd hβ ht hKβ (pp := pp) (a₀ := ⟨0, by omega⟩)
      (a₁ := ⟨2, by omega⟩) (e := ⟨3, by omega⟩) (b := ⟨n - 1, by omega⟩) hfix hmov hnorm
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    pidx_tac
  ·
    refine scenarioA hF c hsingle hshape nd hβ ht hKβ (pp := pp)
      (a₀ := ⟨pp.val - 1, by omega⟩) (a₁ := ⟨pp.val + 1, by omega⟩)
      (e := ⟨pp.val - 2, by omega⟩) (b := ⟨n - 1, by omega⟩) hfix hmov hnorm
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    pidx_tac
  ·
    refine scenarioA hF c hsingle hshape nd hβ ht hKβ (pp := pp)
      (a₀ := ⟨pp.val - 1, by omega⟩) (a₁ := ⟨pp.val + 1, by omega⟩)
      (e := ⟨pp.val - 2, by omega⟩) (b := ⟨0, by omega⟩) hfix hmov hnorm
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    pidx_tac

end Path

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G} {m : ℕ}

@[expose] def ToralPropB (c : TCtx p f .POmegaOdd m Ω K z) {t : G} (ht : t * z * t⁻¹ = z)
    (k₀ : (modelUniv .POmegaOdd m p f Fact.out).K)
    (v : Fin (modelUniv .POmegaOdd m p f Fact.out).D.rank → ZMod 2) : Prop :=
  ∀ γ ∈ (modelUniv .POmegaOdd m p f Fact.out).D.roots,
    ((conjSub k₀ ((modelUniv .POmegaOdd m p f Fact.out).D.rootGroup γ ⊔
        (modelUniv .POmegaOdd m p f Fact.out).D.rootGroup (-γ))).map c.d.ψ).map
        (locAut c.hΩ.conjInvariant ht).toMonoidHom =
      (conjSub k₀ ((modelUniv .POmegaOdd m p f Fact.out).D.rootGroup γ ⊔
        (modelUniv .POmegaOdd m p f Fact.out).D.rootGroup (-γ))).map c.d.ψ ∧
    ((∀ x ∈ (conjSub k₀ ((modelUniv .POmegaOdd m p f Fact.out).D.rootGroup γ ⊔
        (modelUniv .POmegaOdd m p f Fact.out).D.rootGroup (-γ))).map c.d.ψ,
      locAut c.hΩ.conjInvariant ht x = x) ↔ charOf v γ = 0)

@[expose] def ToralNormalB (c : TCtx p f .POmegaOdd m Ω K z) {t : G} (ht : t * z * t⁻¹ = z) :
    Prop :=
  ∃ (k₀ : (modelUniv .POmegaOdd m p f Fact.out).K)
    (v : Fin (modelUniv .POmegaOdd m p f Fact.out).D.rank → ZMod 2), ToralPropB c ht k₀ v


end Main

end CFSG.ClassicalInvolution.RouteD.Gaps
