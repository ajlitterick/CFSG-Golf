module

public import CFSG.Milestones.ASVolI.C135.P1

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL specialLinearGroupEquivStatedSL_coe)
open CFSG.Quasithin.H13.Ch4.C135 (slNat dualHom coe_dualHom coe_slNat moduleAct_false_eq
  moduleAct_true_eq)
open scoped Matrix commutatorElement

variable {G : Type} [Group G]

section Coords

variable {F : Type} [Field F]

@[expose] def burnsideC135_Kc (F : Type) [Field F] (i : Fin 2) :
    Subgroup (Multiplicative (Fin 2 → Fin 3 → F)) where
  carrier := {v | Multiplicative.toAdd v i = 0}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [toAdd_mul, Pi.add_apply, ha, hb, add_zero]
  one_mem' := rfl
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [toAdd_inv, Pi.neg_apply, ha, neg_zero]

@[expose] def burnsideC135_Wc {Q : Subgroup G} (β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F))
    (i : Fin 2) : Subgroup G :=
  ((burnsideC135_Kc F i).comap β).map Q.subtype

variable {Q : Subgroup G} {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)}

theorem burnsideC135_mem_Wc {i : Fin 2} {g : G} :
    g ∈ burnsideC135_Wc β i ↔ ∃ h : g ∈ Q, Multiplicative.toAdd (β ⟨g, h⟩) i = 0 := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.2, hq⟩
  · rintro ⟨h, hq⟩
    exact ⟨⟨g, h⟩, hq, rfl⟩

theorem burnsideC135_Wc_le (i : Fin 2) : burnsideC135_Wc β i ≤ Q := fun _ hg =>
  (burnsideC135_mem_Wc.mp hg).1

@[expose] noncomputable def burnsideC135_βc (β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F))
    (i : Fin 2) : ↥(burnsideC135_Wc β i) →* Multiplicative (Fin 3 → F) :=
  (burnsideC135_proj F (1 - i)).comp (β.comp (Subgroup.inclusion (burnsideC135_Wc_le i)))


end Coords

section Twist


end Twist

end CFSG.ASVolI

end
