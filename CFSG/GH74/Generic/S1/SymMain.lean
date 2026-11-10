module

public import CFSG.GH74.Generic.S1.SymFrame
public import CFSG.GH74.Generic.S1.SymOpsLin
public import CFSG.GH74.Generic.S1.SymOpsUni
public import CFSG.GH74.Generic.S1.SymClass
public import CFSG.GH74.Generic.S1.SymProd

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sym_hyps {x : G} {K : Subgroup (CentralizerBar x)} (hxK : xbar x ∈ K) (hx : orderOf x = 2)
    {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu)
    (i : Fin 5) :
    IsConj x (symX x u i) ∧
      (∀ j, symX x u (i.succAbove j) ∈ centralizer ({symX x u i} : Set G)) ∧
        (∀ j, symX x u (i.succAbove j) * symX x u (i.succAbove j) = 1) ∧
          (∀ j k, symX x u (i.succAbove j) * symX x u (i.succAbove k) =
            symX x u (i.succAbove k) * symX x u (i.succAbove j)) ∧
            (∀ j, IsConj (symX x u i) (symX x u (i.succAbove j))) ∧
              (∀ j, symX x u (i.succAbove j) ≠ symX x u i) ∧
                (∀ j k, j ≠ k → symX x u (i.succAbove j) * symX x u (i.succAbove k) ≠ 1) ∧
                  (∀ j k, j ≠ k → symX x u (i.succAbove j) * symX x u (i.succAbove k) *
                    symX x u i ≠ 1) ∧
                    symX x u (i.succAbove 0) * symX x u (i.succAbove 1) * symX x u (i.succAbove 2) *
                      symX x u (i.succAbove 3) = symX x u i := by
  obtain ⟨hconj, hX2, hXc, hX1, hXd⟩ := symX_facts hxK hx hf
  refine ⟨hconj i, fun j => mem_centralizer_singleton_iff.2 (hXc _ _), fun j => hX2 _,
    fun j k => hXc _ _, fun j => (hconj i).symm.trans (hconj _),
    fun j => hXd _ _ (Fin.succAbove_ne i j), ?_, ?_, five_prod_succAbove _ hXc hX2 hX1 i⟩
  · intro j k hjk h1
    apply hXd _ _ (fun h => hjk (Fin.succAbove_right_injective h))
    calc symX x u (i.succAbove j) = symX x u (i.succAbove j) * (symX x u (i.succAbove k) *
          symX x u (i.succAbove k)) := by rw [hX2, mul_one]
      _ = (symX x u (i.succAbove j) * symX x u (i.succAbove k)) * symX x u (i.succAbove k) :=
          (mul_assoc _ _ _).symm
      _ = symX x u (i.succAbove k) := by rw [h1, one_mul]
  · intro j k hjk
    exact five_triple_ne_one _ hXc hX2 hX1 hXd
      (fun h => hjk (Fin.succAbove_right_injective h)) (Fin.succAbove_ne i j).symm.symm
      (Fin.succAbove_ne i k).symm.symm


@[expose] def S1NbhdSym : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
      S1Frame x K u hu → S1SymFrame x u → ∃ J : Fin 4 → Subgroup G, IsS1A4 x K J


end CFSG.GH74.Generic.S1
