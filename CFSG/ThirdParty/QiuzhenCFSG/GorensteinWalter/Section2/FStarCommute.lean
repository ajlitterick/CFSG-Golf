module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal

namespace CFSG
end CFSG
open CFSG

/-!
# Bender (1970) Statement 1.7 — centralizer and F\*-commutation helpers

This module closes the two gaps named by the `gw-bender1970-17` owner:

1. `fstar_normalizer_center_qCoreOf_fitting_eq_A` — for `p ∈ π(F(A))`,
   `N_G(Z(O_p(F(A)))) = A`.  The proof is the characteristic-chain
   argument: `O_p(F(A))` is characteristic in `F(A)`, `F(A) ⊴ A`, the
   center of `O_p(F(A))` is characteristic in `O_p(F(A))`, so
   `Z(O_p(F(A))) ⊴ A`; the normalizer contains `A`, is not `G` by
   simplicity (the center is nontrivial), and is not larger than `A` by
   maximality.
2. `centralizer_qCoreOf_S_le_A` — for the 1.7 hypotheses and
   `p ∈ π(F(A))`, the centralizer of `O_p(S)` lies in `A`.  This is the
   exact statement imported by `Bender1970_17i` under the name
   `bender1970_1_7_centralizer_qCoreOf_S_le_A`.

The residual Thompson-lemma assembly (paper 1.7 proof steps 3–4) is **not**
landed here: the unconditional three-conjunct bridge
`bender1970_1_7_residual_commutator_assembly` declared in
`Bender1970_17i.lean` is mathematically false (explicit counterexample in
`A₅`: `A = S₃`, `S = C₃ = F*(A)`, `B = A₄` satisfies all 1.7 hypotheses
but `F*(B) = V₄ ⊄ A`), and the honest two-conjunct statement
`[O_p(B) ⊓ A, O^p(F*(A))] = ⊥ ∧ (p ∈ π(F(A)) → [O_p(B), O^p(F*(A))] = ⊥)`
requires the paper's "obvious" step `[O_p(B) ⊓ A, O^p(S)] = 1` (equivalently
`O_p(B) ⊓ A ≤ O_p(A)`) and the p-residual generation lemma
`O^p(F*(A)) = ⟨O^p(S), O_q(A) (q ≠ p)⟩`, neither of which exists in the
allowed module graph.  See the task card for the exact gap list.
-/

noncomputable section

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

universe u

/-! ## Characteristic transport through a normal intermediate subgroup -/

/-- The image of a characteristic subgroup of a subgroup normal in `A` is
normal in `A`. -/
public theorem fstar_characteristic_subgroupOf_map_normal_in
    {G : Type u} [Group G] {A F : Subgroup G} {K : Subgroup (↥F)}
    (hK : K.Characteristic) (hF : IsNormalIn F A) :
    IsNormalIn (K.map F.subtype) A := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, _hy, rfl⟩
    exact hF.1 y.2
  · intro a ha z hz
    rcases (Subgroup.mem_map).1 hz with ⟨y, hy, rfl⟩
    let α : ↥F ≃* ↥F :=
      { toFun := fun y => ⟨a * (y : G) * a⁻¹, hF.2 a ha (y : G) y.2⟩
        invFun := fun y =>
          ⟨a⁻¹ * (y : G) * a, by
            have h := hF.2 a⁻¹ (A.inv_mem ha) (y : G) y.2
            simpa [mul_assoc] using h⟩
        left_inv := by intro y; ext; group
        right_inv := by intro y; ext; group
        map_mul' := by
          intro x y
          ext
          change a * ((x * y : ↥F) : G) * a⁻¹ =
            (a * (x : G) * a⁻¹) * (a * (y : G) * a⁻¹)
          rw [Subgroup.coe_mul]
          group }
    have hmap : K.map α.toMonoidHom = K :=
      (Subgroup.characteristic_iff_map_eq.mp hK) α
    have hαy : α y ∈ K := by
      rw [← hmap]
      exact (Subgroup.mem_map).mpr ⟨y, hy, rfl⟩
    refine (Subgroup.mem_map).mpr ⟨α y, hαy, ?_⟩
    change (α y).1 = a * (y : G) * a⁻¹
    rfl

/-! ## Normalizer of `Z(O_p(F(A)))` -/

/-- The normalizer of `Z(O_p(F(A)))` is the maximal subgroup `A` when
`p ∈ π(F(A))`. -/
public theorem fstar_normalizer_center_qCoreOf_fitting_eq_A
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    {p : ℕ} (hp : p.Prime)
    (hpF : p ∈ primesOfOrder (fittingSubgroupOf A)) :
    Subgroup.normalizer
      ((Subgroup.center (↥(qCoreOf (fittingSubgroupOf A) p))).map
        (qCoreOf (fittingSubgroupOf A) p).subtype : Set G) = A := by
  classical
  let F : Subgroup G := fittingSubgroupOf A
  let P : Subgroup G := qCoreOf F p
  let Z : Subgroup G := (Subgroup.center (↥P)).map P.subtype
  have hFleA : F ≤ A := by
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, rfl⟩
    exact f.2
  have hPleF : P ≤ F := qCoreOf_le F p
  have hPleA : P ≤ A := hPleF.trans hFleA
  have hZleP : Z ≤ P := Subgroup.map_subtype_le (H := P) (Subgroup.center (↥P))
  have hZleA : Z ≤ A := hZleP.trans hPleA
  have hPnormalA : IsNormalIn P A := by
    simpa [P, qCoreOf] using
      (fstar_characteristic_subgroupOf_map_normal_in (F := fittingSubgroupOf A)
        (K := pCore p (↥(fittingSubgroupOf A)))
        (pCore_characteristic (p := p)) (fittingSubgroupOf_isNormalIn A))
  have hZnormalA : IsNormalIn Z A := by
    simpa [Z] using
      (fstar_characteristic_subgroupOf_map_normal_in (F := P)
        (K := Subgroup.center (↥P)) (Subgroup.centerCharacteristic) hPnormalA)
  have hAleN : A ≤ Subgroup.normalizer (Z : Set G) := by
    refine (Subgroup.le_normalizer_iff).mpr ?_
    intro a ha z hz
    exact hZnormalA.2 a ha z hz
  have hPne : P ≠ ⊥ := by
    simpa [P, F] using
      (fstar_qCoreOf_fitting_ne_bot_of_mem_primesOfOrder A p hp hpF)
  have hPnt : Nontrivial (↥P) := (Subgroup.nontrivial_iff_ne_bot P).2 hPne
  have : Fact p.Prime := ⟨hp⟩
  have hCne : (Subgroup.center (↥P)) ≠ ⊥ := by
    intro hbot
    have hnt : Nontrivial (Subgroup.center (↥P)) :=
      IsPGroup.center_nontrivial (qCoreOf_isPGroup F p)
    exact (Subgroup.nontrivial_iff_ne_bot (Subgroup.center (↥P))).1 hnt hbot
  have hZne : Z ≠ ⊥ := by
    intro hZbot
    have hcbot :=
      (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center (↥P))
        (f := P.subtype) P.subtype_injective).1 hZbot
    exact hCne hcbot
  have hNne_top : Subgroup.normalizer (Z : Set G) ≠ ⊤ := by
    intro htop
    have hZnormalG : Z.Normal := (Subgroup.normalizer_eq_top_iff).mp htop
    rcases (haveI := hZnormalG; hsimple.eq_bot_or_eq_top_of_normal Z) with hbot | htopZ
    · exact hZne hbot
    · have hAtop : A = ⊤ := by
        have htopLeA : (⊤ : Subgroup G) ≤ A := by
          intro x hx
          exact hZleA (htopZ ▸ hx)
        exact le_antisymm le_top htopLeA
      exact hA.1 hAtop
  have hNleA : Subgroup.normalizer (Z : Set G) ≤ A := by
    by_cases hEq : A = Subgroup.normalizer (Z : Set G)
    · rw [hEq]
    · have hlt : A < Subgroup.normalizer (Z : Set G) :=
        lt_of_le_of_ne hAleN (by
          intro h
          exact hEq h)
      have htop := hA.2 (Subgroup.normalizer (Z : Set G)) hlt
      exact False.elim (hNne_top htop)
  exact le_antisymm hNleA hAleN

/-! ## Centralizer of `O_p(S)` for the 1.7 hypotheses -/

/-- For the 1.7 hypotheses with `p ∈ π(F(A))`, the centralizer of
`O_p(S)` lies in the maximal subgroup `A`. -/
public theorem centralizer_qCoreOf_S_le_A
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A S : Subgroup G) (hA : IsCoatom A)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {p : ℕ} (hp : p.Prime)
    (hpF : p ∈ primesOfOrder (fittingSubgroupOf A)) :
    Subgroup.centralizer ((qCoreOf S p : Subgroup G) : Set G) ≤ A := by
  let F : Subgroup G := fittingSubgroupOf A
  let P : Subgroup G := qCoreOf F p
  let Z : Subgroup G := (Subgroup.center (↥P)).map P.subtype
  have hZleQ : Z ≤ qCoreOf S p := by
    simpa [Z, P] using (fstar_center_qCoreOf_fitting_le_qCoreOf_S A S
      hSF hSsub hCS p hp hpF)
  have hNZ : Subgroup.normalizer (Z : Set G) = A := by
    simpa [Z, P] using (fstar_normalizer_center_qCoreOf_fitting_eq_A
      hsimple A hA hp hpF)
  calc
    Subgroup.centralizer ((qCoreOf S p : Subgroup G) : Set G)
        ≤ Subgroup.centralizer (Z : Set G) :=
      Subgroup.centralizer_le (show (Z : Set G) ⊆ (qCoreOf S p : Set G) from hZleQ)
    _ ≤ Subgroup.normalizer (Z : Set G) := Subgroup.centralizer_le_normalizer (Z : Set G)
    _ = A := hNZ

/-- The exact centralizer statement imported by `Bender1970_17i`. -/
public theorem bender1970_1_7_centralizer_qCoreOf_S_le_A
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    (p : ℕ) (hp : p.Prime) (hpF : p ∈ primesOfOrder (fittingSubgroupOf A)) :
    Subgroup.centralizer ((qCoreOf S p : Subgroup G) : Set G) ≤ A := by
  exact centralizer_qCoreOf_S_le_A hsimple A S hA hSF hSsub hCS hp hpF

/-! ## `O^p(F*(A))` centralizes `O_p(A)` -/


/-!
## Residual Thompson-lemma assembly — status

The paper's step `[O_p(B) ∩ A, O^p(F*(A))] = 1` (all primes) and the
`p ∈ π(F(A))` step `[O_p(B), O^p(F*(A))] = 1` are **not** declared here.
The earlier bridge `residual_commutator_assembly` was
removed rather than left as a `sorry`: its proof requires the two missing
facts listed in the module header, and the 17i three-conjunct bridge is
false as stated.  `Bender1970_17ii` currently imports this module for
`residual_commutator_assembly`; that import must be re-routed to a future
assembly lemma (see `tasks/gw-bender1970-17.md` Route Ledger).
-/

end CFSG.GorensteinWalter
