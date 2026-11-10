module

public import CFSG.Milestones.ASVolI.C135.NB
public import CFSG.Milestones.ASVolI.C135.Cent
public import CFSG.Milestones.ASVolI.C135.Coords

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open CFSG.ASVolI.ChC
open CFSG.Quasithin.H13.Ch4 (le_normalizer_c134Q c134Q_le mem_normalizer_centralizer_of_mem)
open CFSG.Quasithin.H13.Ch4.C135 (cnj coe_cnj slNat slNat_surjective dualHom coe_dualHom
  dualHom_dualHom moduleAct_true_eq le_normalizer_centerOf mix mix_apply commutator_mem_Q
  commute_of_mem_pCoreOf)
open scoped Matrix commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure burnsideC135_H1 (X R L : Subgroup G) {F : Type} [Field F] [Fintype F]
    (α : ↥L →* ↥(StatedSL 3 F))
    (β : ↥(c134Q X L) →* Multiplicative (Fin 2 → Fin 3 → F))
    (βU : ↥(centerOf (c134Q X L)) →* Multiplicative (Fin 3 → F)) : Prop where
  card : Fintype.card F = 2
  ms : IsMSPair X R
  comp : L ∈ cComp X
  prod : (X : Set G) = (L : Set G) * (R : Set G)
  normL : X ≤ Subgroup.normalizer (L : Set G)
  surj : IsModO2Surj L α
  cent : X ⊓ Subgroup.centralizer (L : Set G) = ⊥
  nat : IsSumOfNaturalModulesVia L (centerOf (c134Q X L)) ⊥ α false 1
  βs : Function.Surjective β
  βk : β.ker = (centerOf (c134Q X L)).subgroupOf (c134Q X L)
  βeq : ∀ (a : ↥L) (u v : ↥(c134Q X L)), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
    Multiplicative.toAdd (β v) i =
      (moduleAct true (α a : GL (Fin 3) F)).mulVec (Multiplicative.toAdd (β u) i)
  dsg : burnsideC135_DSG (c134Q X L) L (burnsideC135_Wc β 1) (burnsideC135_Wc β 0) (slNat α) βU
    (burnsideC135_βc β 1) (burnsideC135_βc β 0)
  normW : X ≤ Subgroup.normalizer (burnsideC135_Wc β 1 : Set G)

namespace burnsideC135_H1


end burnsideC135_H1

section Coords


end Coords

namespace burnsideC135_H1


end burnsideC135_H1

end CFSG.ASVolI

end
