module

public import CFSG.Walter.Bender1970
public import CFSG.Walter.W67.Corollary
public import CFSG.Walter.Models
public import CFSG.Walter.ReeOrder.JTFinal
public import CFSG.Walter.Statement
public import CFSG.Walter.J1Recog.Main

public section

namespace CFSG.Walter

open scoped MatrixGroups


theorem walter_structure
    (hJ : JRStrongHyp) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) (hP : IsMulCommutative (P : Subgroup G)) :
    IsTypeL2 G ∨ Nonempty (Ward.ReeTypeHyp G) ∨ Nonempty (G ≃* CFSG.Open.walterJ1) := by
  have hab : HasAbelianSylowTwo G := hasAbelianSylowTwo_of_sylow P hP
  have hSC := simpleCaseHyp_of_benderHyp benderHyp
  rcases hSC G inferInstance hnonab hab
      (fun H _ => isAStar_of_hasAbelianSylowTwo hSC (hab.subgroup H)) with hL2 | hJR
  · exact Or.inl hL2
  · exact Or.inr (hJ G hJR hnonab)

theorem j1RecogHyp : J1RecogHyp := fun _ _ _ h => J1Recog.nonempty_mulEquiv_walterJ1 h

theorem jrStrongHyp_of_open
    (hT : W67.Theorem) (hJ1 : J1RecogHyp) (hJT : JTThreeHyp) :
    JRStrongHyp :=
  jrStrongHyp_of (W67.walter67Hyp_of_theorem hT) hJ1 hJT

theorem walter_order_form_of
    (hT : W67.Theorem) (hJ1 : J1RecogHyp) (hJT : JTThreeHyp) :
    WalterOrderForm :=
  walter_order_form benderHyp (jrHyp_of_jrStrongHyp (jrStrongHyp_of_open hT hJ1 hJT))


theorem walter_order_form_of'
    (hT : W67.Theorem) (hJT : JTThreeHyp) :
    WalterOrderForm :=
  walter_order_form_of hT j1RecogHyp hJT


theorem walter_order_form_of_W67
    (hT : W67.Theorem) :
    WalterOrderForm :=
  walter_order_form_of' hT jtThreeHyp


end CFSG.Walter
