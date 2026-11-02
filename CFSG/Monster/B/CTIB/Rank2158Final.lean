module

public import CFSG.Monster.B.CTIB.Rank2158
public import CFSG.Monster.B.CTIB.DistThreeProductCent
public import CFSG.Monster.B.TwoA.Fischer.AmbientRootNative

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Amalgam

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem commutator_self_le {G : Type*} [Group G] (R : Subgroup G) : ⁅R, R⁆ ≤ R :=
  Subgroup.commutator_le.2 fun _ hg _ hh =>
    R.mul_mem (R.mul_mem (R.mul_mem hg hh) (R.inv_mem hg)) (R.inv_mem hh)

theorem distThreeProduct_of_pair
    {v w : CVert} (hvw : cgraph.dist v w = 3)
    {R F C : Subgroup Shat} (hR : R = Subgroup.centralizer {clabelS v, clabelS w})
    (hF : F = ⁅R, R⁆) (hC : C = Subgroup.centralizer {clabelS v * clabelS w}) :
    ∃ F' : Subgroup C, CFSG.IsComponent F' ∧ (∀ K : Subgroup C, CFSG.IsComponent K → K = F') ∧
      IsSimpleGroup F' ∧ Nonempty (F' ≃* adjointGroup Tag.F4 (ZMod 2)) ∧
      Nat.card F' = 3311126603366400 := by
  have hL := labelsInput_of_ambient ambientRootOrbitsHyp
  have hO := outerInput_of_ambient ambientRootOrbitsHyp
  have hP := pathInput_of_ambient ambientRootOrbitsHyp
  have hT := typeThreeBoundInput_of_ambient ambientRootOrbitsHyp
  obtain ⟨-, -, hRC, -, -, -, -, -, hFcard, hcomp, huniq, -, hFsimple, -, ⟨Ψ, -, hiso⟩, -⟩ :=
    distance_three_product_full_centralizer hL hO hP hT hvw hR hF hC
  have hsv : clabelS w ∈ vStab v := (hL v w hvw).1
  obtain ⟨ρ, iv, hρ, hρs⟩ := exists_compat_beta hO hP hT hvw ⟨clabelS w, hsv⟩ rfl
  obtain ⟨φ, -, e, -⟩ := hiso ρ hρ.1 hρ.2.1 ⟨clabelS w, hsv⟩ rfl hρs
  have hFC : F ≤ C := hF ▸ (commutator_self_le R).trans hRC
  refine ⟨F.subgroupOf C, hcomp, huniq,
    @MulEquiv.isSimpleGroup _ _ _ _ hFsimple (Subgroup.subgroupOfEquivOfLe hFC),
    ⟨(Subgroup.subgroupOfEquivOfLe hFC).trans e⟩, ?_⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv, hFcard]

theorem distThreeProductInput_holds :
    DistThreeProductInput :=
  fun _ _ hvw => distThreeProduct_of_pair hvw rfl rfl rfl

theorem native_rank_2158_distance_three_product_final :
    (∃ v u : CVert, cgraph.dist v u = 3 ∧ IsConj (sEquiv (rs 5)) (clabelS v * clabelS u)) ∧
    (∀ s : Sbp, orderOf s = 2 → ((βr s) - 1).rank = 2158 →
      ∃ K : Subgroup (Subgroup.centralizer {s}), CFSG.IsComponent K ∧
        (∀ K' : Subgroup (Subgroup.centralizer {s}), CFSG.IsComponent K' → K' = K) ∧
        IsSimpleGroup K ∧ Nonempty (K ≃* adjointGroup Tag.F4 (ZMod 2)) ∧
        Nat.card K = 3311126603366400 ∧ 17 ∣ Nat.card K) ∧
    ∀ X : NativeSporadic.B, orderOf X = 2 → (X.val.val - 1).rank = 2158 →
      ∃ K : Subgroup (Subgroup.centralizer {X}), CFSG.IsComponent K ∧
        (∀ K' : Subgroup (Subgroup.centralizer {X}), CFSG.IsComponent K' → K' = K) ∧
        IsSimpleGroup K ∧ Nonempty (K ≃* adjointGroup Tag.F4 (ZMod 2)) ∧
        Nat.card K = 3311126603366400 ∧ 17 ∣ Nat.card K :=
  native_rank_2158_distance_three_product_of ambientRootOrbitsHyp distThreeProductInput_holds

end CFSG.Monster.B.CTIB
