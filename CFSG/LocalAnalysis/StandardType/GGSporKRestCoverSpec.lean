module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import CFSG.LocalAnalysis.StandardType.GGSporKRestEval

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

theorem sporKRest_mem_closure_iff_mem_table {K : Type} [Group K] (sg T : List K)
    (h1 : (1 : K) ∈ T) (hcl : ∀ t ∈ T, ∀ g ∈ sg, t * g ∈ T ∧ t * g⁻¹ ∈ T)
    (hgen : ∀ t ∈ T, t ∈ Subgroup.closure {g | g ∈ sg}) (x : K) :
    x ∈ Subgroup.closure {g | g ∈ sg} ↔ x ∈ T := by
  constructor
  · intro hx
    have hmul : ∀ t ∈ T, t * x ∈ T :=
      Subgroup.closure_induction'' (s := {g | g ∈ sg}) (p := fun y _ => ∀ t ∈ T, t * y ∈ T)
        (fun y hy t ht => (hcl t ht y hy).1)
        (fun y hy t ht => (hcl t ht y hy).2)
        (fun t ht => by simpa using ht)
        (fun y₁ y₂ _ _ ih₁ ih₂ t ht => by
          have h1' : t * y₁ ∈ T := ih₁ t ht
          have h2' : (t * y₁) * y₂ ∈ T := ih₂ (t * y₁) h1'
          rw [← mul_assoc]
          exact h2')
        hx
    simpa using hmul 1 h1
  · intro hx
    exact hgen x hx

theorem sporKRest_card_closure_of_table {K : Type} [Group K] (sg T : List K)
    (h1 : (1 : K) ∈ T) (hcl : ∀ t ∈ T, ∀ g ∈ sg, t * g ∈ T ∧ t * g⁻¹ ∈ T)
    (hgen : ∀ t ∈ T, t ∈ Subgroup.closure {g | g ∈ sg}) (hnd : T.Nodup) :
    Nat.card (Subgroup.closure {g | g ∈ sg}) = T.length := by
  classical
  have hiff : ∀ x : K, x ∈ Subgroup.closure {g | g ∈ sg} ↔ x ∈ T :=
    fun x => sporKRest_mem_closure_iff_mem_table sg T h1 hcl hgen x
  have h1' : Nat.card (Subgroup.closure {g | g ∈ sg}) = Nat.card {x : K // x ∈ T} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  have h2' : Nat.card {x : K // x ∈ T} = T.toFinset.card :=
    calc Nat.card {x : K // x ∈ T}
        = Nat.card ↥(T.toFinset) :=
          Nat.card_congr (Equiv.subtypeEquivRight (fun x => (List.mem_toFinset).symm))
      _ = T.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have h3' : T.toFinset.card = T.length := List.toFinset_card_of_nodup hnd
  exact h1'.trans (h2'.trans h3')


end CFSG.StandardType.SporadicShape
