module

public import CFSG.CharacterTheory.Wreathed.ActualCentralizerSemilinear
public import CFSG.CharacterTheory.Wreathed.WreathedCentralCover
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

public noncomputable section
namespace CFSG.Wreathed.FullCentralizerFromProjectiveModel

universe u v
open Matrix
open CFSG.Wreathed.ActualProjectiveLayer
open CFSG.Wreathed.ActualCentralizerSemilinear
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.SemilinearOddExtensions
open CFSG.Semidihedral.OddFieldLift
open CFSG.Semidihedral.MatrixCover
open CFSG.Semidihedral.MatrixCoverData
open CFSG.Wreathed.WreathedCentralCover

variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]


omit [IsSimpleGroup G] in
theorem original_phi_kernel_central
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {F : Type v} [Field F] [Finite F]
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrho : Function.Injective rho)
    (hlinear : LinearExtension F rho.range (actualField n hn S e rho)) :
    (actualPhi n hn S e rho hlinear).ker ≤
      Subgroup.center (centralizerOddCoreQuotient n S e) := by
  rw [actualPhi_ker n hn S e rho hrho hlinear,
    centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e]

theorem original_phi_layer_action
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ)
    (theta : centralizerSimpleLayer n hn S e ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      SpecialLinearGroup (Fin 2) F)
    (hin : ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta)
    (v : CFSG.layer (centralizerOddCoreQuotient n S e)) :
    slCoordinateAction F (eta v) = coordinateProjection F (actualField n hn S e rho)
      (actualPhi n hn S e rho hin.linear_extension) v := hin.action_values v


section OriginalFixedCentralizer

variable
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hcard : Nat.card F = p ^ f)
    (theta : centralizerSimpleLayer n hn S e ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrho : Function.Injective rho)
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      SpecialLinearGroup (Fin 2) F)
    (hin : ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta)

include hnonab n hn S e hfour p f theta rho hrho eta hin

local notation "H₀" => centralizerOddCoreQuotient n S e
local notation "M₀" => CFSG.layer H₀
local notation "Σ₀" => actualField n hn S e rho
local notation "φ₀" => actualPhi n hn S e rho hin.linear_extension
local notation "hc₀" => original_phi_kernel_central n hn S e rho hrho hin.linear_extension
local notation "E₀" => CFSG.Wreathed.CentralTwoPowerFieldLift.E F Σ₀ φ₀ hc₀

theorem actual_kernel_isPGroup
    : IsPGroup 2 (φ₀).ker :=
  CFSG.Wreathed.CentralTwoPowerFieldLift.kernel_isPGroup_of_card φ₀
    ⟨n, (actualPhi_kernel_center_data n hn S e rho hrho hin.linear_extension).2.2.2.2⟩

local notation "hK₀" => actual_kernel_isPGroup hnonab n hn S e hfour p f theta rho hrho eta hin
local notation "hsurj₀" => actualPhi_surjective n hn S e rho hin.linear_extension
local notation "e₀" => CFSG.Wreathed.CentralTwoPowerFieldLift.eSigma F Σ₀ φ₀
  hsurj₀ hc₀ hK₀ hin.field_odd


end OriginalFixedCentralizer

structure ActualProjectiveCentralizerData
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ)
    (theta : centralizerSimpleLayer n hn S e ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      SpecialLinearGroup (Fin 2) F) : Prop where
  field_card : Nat.card F = p ^ f
  rho_injective : Function.Injective rho
  field_odd : Odd (Nat.card (actualField n hn S e rho))
  field_order_dvd : Nat.card (actualField n hn S e rho) ∣ f
  rho_layer : (centralizerSimpleLayer n hn S e).map rho = specialLayer F
  rho_range : rho.range = linearLayer F ⊔ liftedField F (actualField n hn S e rho)
  component : CFSG.IsComponent (CFSG.layer (centralizerOddCoreQuotient n S e))
  only_component : ∀ D : Subgroup (centralizerOddCoreQuotient n S e),
    CFSG.IsComponent D → D = CFSG.layer (centralizerOddCoreQuotient n S e)
  characteristic : (CFSG.layer (centralizerOddCoreQuotient n S e)).Characteristic
  full_center : centralizerFullCenterImage n hn S e =
    Subgroup.center (centralizerOddCoreQuotient n S e)
  full_centralizer : centralizerFullCenterImage n hn S e =
    Subgroup.centralizer (CFSG.layer (centralizerOddCoreQuotient n S e) :
      Set (centralizerOddCoreQuotient n S e))
  center_cyclic : IsCyclic (centralizerFullCenterImage n hn S e)
  center_card : Nat.card (centralizerFullCenterImage n hn S e) = 2 ^ n
  center_generator : centralizerFullCenterImage n hn S e = Subgroup.zpowers
    (centralizerOddCoreMap n S e
      (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
        (Original.a (2 ^ n))))
  layer_center : Subgroup.center (CFSG.layer (centralizerOddCoreQuotient n S e)) =
    (Subgroup.zpowers (centralizerOddCoreMap n S e (centralInvolution n S e))).subgroupOf
      (CFSG.layer (centralizerOddCoreQuotient n S e))
  involution : eta (centralizerActualLayerInvolution hnonab n hn S e hfour) =
    CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F
  projective : (CFSG.Semidihedral.ProjectiveSL2Cover.nativeQuotient F).comp eta.toMonoidHom =
    theta.toMonoidHom.comp (centralizerActualLayerMap hnonab n hn S e hfour)
  action_values : ∀ v : CFSG.layer (centralizerOddCoreQuotient n S e),
    slCoordinateAction F (eta v) = (rho (centralizerFullQuotientMap n hn S e v)).val
  q_two_part : 2 ^ (Nat.card F ^ 2 - 1).factorization 2 = 2 * 2 ^ n

theorem actual_projective_centralizer_data
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ) (hcard : Nat.card F = p ^ f)
    (theta : centralizerSimpleLayer n hn S e ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrho : Function.Injective rho)
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      SpecialLinearGroup (Fin 2) F)
    (hin : ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta) :
    ActualProjectiveCentralizerData hnonab n hn S e hfour p f theta rho eta := by
  have hM := actual_layer_component_data hnonab n hn S e hfour
  refine ⟨hcard, hrho, hin.field_odd, hin.field_order_dvd, hin.rho_layer,
    hin.linear_extension.1.2.2.1, hM.1, hM.2.1, hM.2.2.1,
    (centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e).symm,
    hM.2.2.2.1.symm, inferInstance, centralizerFullCenterImage_card n hn S e,
    centralizerFullCenterImage_eq_zpowers n hn S e, hM.2.2.2.2,
    hin.involution, hin.projective, hin.action_values, hin.q_two_part⟩

theorem actual_projective_model_centralizer_data
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      ringChar F = p ∧ 1 < Nat.card F ∧
      ∃ (theta : centralizerSimpleLayer n hn S e ≃*
          ProjectiveSpecialLinearGroup (Fin 2) F)
        (rho : centralizerFullQuotient n hn S e →* coordinateE F)
        (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
          SpecialLinearGroup (Fin 2) F),
        ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta ∧
        ActualProjectiveCentralizerData hnonab n hn S e hfour p f theta rho eta := by
  obtain ⟨F, hfield, hfinite, hcard, hchar, hq, theta, rho, eta, hrho, _, hin⟩ :=
    actual_projective_model_cover_inputs hnonab n hn S e hfour p f hp hpodd hf hmodel
  let : Field F := hfield
  let : Finite F := hfinite
  exact ⟨F, hfield, hfinite, hcard, hchar, hq, theta, rho, eta, hin,
    actual_projective_centralizer_data hnonab n hn S e hfour p f hcard
      theta rho hrho eta hin⟩

open CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.Semidihedral.ProjectiveNonsquareInvolutions

structure ActualFullCentralizerData
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ)
    (theta : centralizerSimpleLayer n hn S e ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      SpecialLinearGroup (Fin 2) F)
    (hin : ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta)
    (hrho : Function.Injective rho) : Prop where
  structural : ActualProjectiveCentralizerData hnonab n hn S e hfour p f theta rho eta
  phi_values : ∀ v : centralizerOddCoreQuotient n S e,
    (actualPhi n hn S e rho hin.linear_extension v : coordinateE F) =
      rho (centralizerFullQuotientMap n hn S e v)
  fixed_field_card : Nat.card (FixedField F (actualField n hn S e rho)) =
    p ^ (f / Nat.card (actualField n hn S e rho))
  quotient_cyclic :
    let := hin.layer_normal
    IsCyclic (centralizerOddCoreQuotient n S e ⧸ CFSG.layer (centralizerOddCoreQuotient n S e))
  quotient_card :
    let := hin.layer_normal
    Nat.card (centralizerOddCoreQuotient n S e ⧸
      CFSG.layer (centralizerOddCoreQuotient n S e)) =
        2 ^ n * Nat.card (actualField n hn S e rho)
  group_card : Nat.card (centralizerOddCoreQuotient n S e) =
    2 ^ n * Nat.card (actualField n hn S e rho) * Nat.card F * (Nat.card F ^ 2 - 1)
  complement_membership :
    let phi := actualPhi n hn S e rho hin.linear_extension
    let hc := original_phi_kernel_central n hn S e rho hrho hin.linear_extension
    ∀ t : centralizerOddCoreQuotient n S e,
      t ∈ CFSG.Wreathed.CentralTwoPowerFieldLift.E F (actualField n hn S e rho) phi hc ↔
        t ∈ B F (actualField n hn S e rho) phi ∧
          t ^ Nat.card (actualField n hn S e rho) = 1
  field_unique :
    let Sigma := actualField n hn S e rho
    let phi := actualPhi n hn S e rho hin.linear_extension
    let hc := original_phi_kernel_central n hn S e rho hrho hin.linear_extension
    ∀ sigma : Sigma, ∃! t : CFSG.Wreathed.CentralTwoPowerFieldLift.E F Sigma phi hc,
      coordinateProjection F Sigma phi t = fieldExtension F sigma
  field_entrywise :
    let := hin.layer_normal
    let Sigma := actualField n hn S e rho
    let phi := actualPhi n hn S e rho hin.linear_extension
    let hc := original_phi_kernel_central n hn S e rho hrho hin.linear_extension
    let hK := actual_kernel_isPGroup hnonab n hn S e hfour p f theta rho hrho eta hin
    ∀ sigma : Sigma, ∀ v : CFSG.layer (centralizerOddCoreQuotient n S e), ∀ i j : Fin 2,
      eta (conjugateIn (CFSG.layer (centralizerOddCoreQuotient n S e))
        (originalFieldLift F Sigma phi
          (actualPhi_surjective n hn S e rho hin.linear_extension) hc hK hin.field_odd sigma) v)
          i j = sigma.val (eta v i j)
  fixed_centralizer :
    let phi := actualPhi n hn S e rho hin.linear_extension
    let hc := original_phi_kernel_central n hn S e rho hrho hin.linear_extension
    let E0 := CFSG.Wreathed.CentralTwoPowerFieldLift.E F (actualField n hn S e rho) phi hc
    ((Subgroup.centralizer (E0 : Set (centralizerOddCoreQuotient n S e))).subgroupOf
      (CFSG.layer (centralizerOddCoreQuotient n S e))).map eta.toMonoidHom =
        (fixedSL2Inclusion F (actualField n hn S e rho)).range
  fixed_centralizer_equiv :
    let Sigma := actualField n hn S e rho
    let phi := actualPhi n hn S e rho hin.linear_extension
    let hc := original_phi_kernel_central n hn S e rho hrho hin.linear_extension
    let E0 := CFSG.Wreathed.CentralTwoPowerFieldLift.E F Sigma phi hc
    ∃ eps : (Subgroup.centralizer (E0 : Set (centralizerOddCoreQuotient n S e))).subgroupOf
      (CFSG.layer (centralizerOddCoreQuotient n S e)) ≃*
        SpecialLinearGroup (Fin 2) (FixedField F Sigma),
      ∀ v, fixedSL2Inclusion F Sigma (eps v) = eta v
  every_nonsquare : ∀ (b : (FixedField F (actualField n hn S e rho))ˣ), ¬IsSquare b →
    let Sigma := actualField n hn S e rho
    let phi := actualPhi n hn S e rho hin.linear_extension
    let hc := original_phi_kernel_central n hn S e rho hrho hin.linear_extension
    let E0 := CFSG.Wreathed.CentralTwoPowerFieldLift.E F Sigma phi hc
    let hK := actual_kernel_isPGroup hnonab n hn S e hfour p f theta rho hrho eta hin
    let eField := originalFieldLift F Sigma phi
      (actualPhi_surjective n hn S e rho hin.linear_extension) hc hK hin.field_odd
    let m := 2 ^ n
    let hm : 0 < m := by positivity
    let heven : Even m := even_two.pow_of_ne_zero (by omega)
    let hfix := original_fixed_parameter F Sigma b
    ¬IsSquare (fixedUnit F Sigma b) ∧
      ∃ tau : centralizerOddCoreQuotient n S e,
        tau ∈ Subgroup.centralizer (E0 : Set (centralizerOddCoreQuotient n S e)) ∧
        tau ^ 2 = centralizerOddCoreMap n S e
          (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
            (Original.a m)) ∧
        tau ^ m = centralizerOddCoreMap n S e (centralInvolution n S e) ∧
        orderOf tau = 2 * m ∧
        coordinateProjection F Sigma phi tau =
          (jProjective F (fixedUnit F Sigma b) : Equiv.Perm (Omega F)) ∧
        ∃ Phi : SemilinearExtension F (fixedUnit F Sigma b) m hm heven Sigma hfix ≃*
            centralizerOddCoreQuotient n S e,
          (∀ X j sigma, Phi ⟨quotientClass F (fixedUnit F Sigma b) m hm heven X j, sigma⟩ =
            (eta.symm X : centralizerOddCoreQuotient n S e) * tau ^ j.val * eField sigma) ∧
          (∀ X : SpecialLinearGroup (Fin 2) F,
            Phi ⟨specialInclusion F (fixedUnit F Sigma b) m hm heven X, 1⟩ =
              (eta.symm X : centralizerOddCoreQuotient n S e)) ∧
          Phi ⟨cyclicGenerator F (fixedUnit F Sigma b) m hm heven, 1⟩ = tau ∧
          Phi (⟨cyclicGenerator F (fixedUnit F Sigma b) m hm heven, 1⟩ ^ 2) =
            centralizerOddCoreMap n S e
              (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
                (Original.a m)) ∧
          (∀ sigma : Sigma, Phi ⟨1, sigma⟩ = eField sigma) ∧
          (∀ sigma : Sigma, ∃! v : E0,
            coordinateProjection F Sigma phi v = fieldExtension F sigma ∧
              Phi ⟨1, sigma⟩ = (v : centralizerOddCoreQuotient n S e)) ∧
          (∀ (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) (sigma : Sigma),
            coordinateProjection F Sigma phi
              (Phi ⟨quotientClass F (fixedUnit F Sigma b) m hm heven X j, sigma⟩) =
                coordinatePGLAction F (ProjGenLinGroup.mk (SpecialLinearGroup.toGL X *
                  nonsquareMatrix F (fixedUnit F Sigma b) ^ j.val)) * fieldExtension F sigma) ∧
          (CFSG.Wreathed.CentralSL2Abelianization.matrixLayer F (fixedUnit F Sigma b) m hm heven
            Sigma hfix).map Phi.toMonoidHom = CFSG.layer (centralizerOddCoreQuotient n S e)


theorem actual_originalLayerX_eta
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ)
    (theta : centralizerSimpleLayer n hn S e ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      SpecialLinearGroup (Fin 2) F)
    (hin : ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta) :
    eta (originalLayerX n hn (centralizerOddCoreSylow n hn S e)
      (centralizerOddCoreCoordinates n hn S e) (CFSG.layer (centralizerOddCoreQuotient n S e))
      hin.sylow_intersection) = CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F := by
  have hx : originalLayerX n hn (centralizerOddCoreSylow n hn S e)
      (centralizerOddCoreCoordinates n hn S e) (CFSG.layer (centralizerOddCoreQuotient n S e))
      hin.sylow_intersection = centralizerActualLayerInvolution hnonab n hn S e hfour :=
    Subtype.ext (actual_quotient_involution_value n hn S e)
  rw [hx]
  exact hin.involution


theorem actual_full_centralizer_data
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f)
    (theta : centralizerSimpleLayer n hn S e ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrho : Function.Injective rho)
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      SpecialLinearGroup (Fin 2) F)
    (hin : ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta) :
    ActualFullCentralizerData hnonab n hn S e hfour p f theta rho eta hin hrho := by
  let := hin.layer_normal
  let Sigma := actualField n hn S e rho
  let phi := actualPhi n hn S e rho hin.linear_extension
  let hc := original_phi_kernel_central n hn S e rho hrho hin.linear_extension
  have hker := (actualPhi_kernel_center_data n hn S e rho hrho hin.linear_extension).1
  have hminus := actual_originalLayerX_eta hnonab n hn S e hfour p f theta rho eta hin
  obtain ⟨_, hfixed, hEmem, hEunique, hmodels, hcardH, hcyclic, hcardQ, hentry,
    hcentral, hequiv⟩ :=
    wreathed_central_cover_exact_matrix_field_model_of_finite F p f hp
      (hp.odd_of_ne_two hpodd) hf hcard Sigma hin.field_odd n hn
      (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e)
      phi (actualPhi_surjective n hn S e rho hin.linear_extension) hker hc
      (CFSG.layer (centralizerOddCoreQuotient n S e)) hin.sylow_intersection eta
      (original_phi_layer_action hnonab n hn S e hfour p f theta rho eta hin) hminus
  refine ⟨actual_projective_centralizer_data hnonab n hn S e hfour p f hcard
      theta rho hrho eta hin, actualPhi_coe n hn S e rho hin.linear_extension,
    hfixed, hcyclic, hcardQ, hcardH, hEmem, hEunique, hentry, hcentral, hequiv, ?_⟩
  intro b hb
  obtain ⟨hbF, tau, hctau, hsq, hpow, horder, hproj, Phi, hformula,
    hspecial, hgen, hgensq, hfield, hprojPhi, hmatrix⟩ := hmodels b hb
  refine ⟨hbF, tau, hctau, ?_, ?_, horder, hproj, Phi,
    hformula, hspecial, hgen, ?_, hfield, ?_, hprojPhi, hmatrix⟩
  · exact hsq.trans (actual_quotient_wreath_value n hn S e (Original.a (2 ^ n)))
  · exact hpow.trans (actual_quotient_involution_value n hn S e)
  · exact hgensq.trans (actual_quotient_wreath_value n hn S e (Original.a (2 ^ n)))
  · intro sigma
    obtain ⟨v, hv, huniq⟩ := hEunique sigma
    refine ⟨v, ⟨hv, ?_⟩, ?_⟩
    · rw [hfield]
      have he := CFSG.Wreathed.CentralTwoPowerFieldLift.eSigma_projective F Sigma phi
        (actualPhi_surjective n hn S e rho hin.linear_extension) hc
        (actual_kernel_isPGroup hnonab n hn S e hfour p f theta rho hrho eta hin)
        hin.field_odd sigma
      have heq := huniq _ he
      exact congrArg Subtype.val heq
    · intro w hw
      exact huniq w hw.1


theorem actual_projective_model_determines_full_centralizer
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      ringChar F = p ∧ 1 < Nat.card F ∧
      ∃ (theta : centralizerSimpleLayer n hn S e ≃*
          ProjectiveSpecialLinearGroup (Fin 2) F)
        (rho : centralizerFullQuotient n hn S e →* coordinateE F)
        (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
          SpecialLinearGroup (Fin 2) F)
        (hin : ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta)
        (hrho : Function.Injective rho),
        (∀ l : centralizerSimpleLayer n hn S e,
          (rho l.val).val = ((pslEquivCoordinateG F) (theta l)).val) ∧
        ActualFullCentralizerData hnonab n hn S e hfour p f theta rho eta hin hrho := by
  obtain ⟨F, hfield, hfinite, hcard, hchar, hq, theta, rho, eta, hrho, hextends, hin⟩ :=
    actual_projective_model_cover_inputs hnonab n hn S e hfour p f hp hpodd hf hmodel
  let : Field F := hfield
  let : Finite F := hfinite
  exact ⟨F, hfield, hfinite, hcard, hchar, hq, theta, rho, eta, hin, hrho,
    hextends, actual_full_centralizer_data hnonab n hn S e hfour p f hp hpodd hf hcard
      theta rho hrho eta hin⟩

theorem actual_projective_layer_model_determines_full_centralizer
    {G₀ : Type} [Group G₀] [Finite G₀] [IsSimpleGroup G₀]
    (hnonab : ∃ a b : G₀, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G₀) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      ringChar F = p ∧ 1 < Nat.card F ∧
      ∃ (theta : centralizerSimpleLayer n hn S e ≃*
          ProjectiveSpecialLinearGroup (Fin 2) F)
        (rho : centralizerFullQuotient n hn S e →* coordinateE F)
        (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
          SpecialLinearGroup (Fin 2) F)
        (hin : ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta)
        (hrho : Function.Injective rho),
        (∀ l : centralizerSimpleLayer n hn S e,
          (rho l.val).val = ((pslEquivCoordinateG F) (theta l)).val) ∧
        ActualFullCentralizerData hnonab n hn S e hfour p f theta rho eta hin hrho := by
  obtain ⟨F, hfield, hfinite, hcard, hchar, hq, theta, rho, eta, hrho, hextends, hin⟩ :=
    actual_stated_projective_model_cover_inputs hnonab n hn S e hfour p f hp hpodd hf hmodel
  let : Field F := hfield
  let : Finite F := hfinite
  exact ⟨F, hfield, hfinite, hcard, hchar, hq, theta, rho, eta, hin, hrho,
    hextends, actual_full_centralizer_data hnonab n hn S e hfour p f hp hpodd hf hcard
      theta rho hrho eta hin⟩

end CFSG.Wreathed.FullCentralizerFromProjectiveModel
