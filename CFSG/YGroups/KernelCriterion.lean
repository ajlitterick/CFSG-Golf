module

public import CFSG.YGroups.MarkedWalks
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.YGroups

open SimpleGraph CFSG.Monster.B.Recog

section RightCosetGraph

variable {G : Type*} [Group G]

@[expose] def rcGraph (L : Subgroup G) (x : G) :
    SimpleGraph (Quotient (QuotientGroup.rightRel L)) :=
  SimpleGraph.fromRel fun u v => ∃ g : G, u = Quotient.mk'' g ∧ v = Quotient.mk'' (x * g)

@[expose] def yTri (L : Subgroup G) (x y : G) (u v w : Quotient (QuotientGroup.rightRel L)) :
    Prop :=
  ∃ g : G, u = Quotient.mk'' g ∧ v = Quotient.mk'' (x * g) ∧ w = Quotient.mk'' (x * y * g) ∧
    u ≠ v ∧ v ≠ w ∧ u ≠ w

variable {L : Subgroup G} {x y : G}

theorem rc_mk_eq_mk_iff {g h : G} :
    (Quotient.mk'' g : Quotient (QuotientGroup.rightRel L)) = Quotient.mk'' h ↔ h * g⁻¹ ∈ L :=
  Quotient.eq''.trans QuotientGroup.rightRel_apply

theorem rc_mk_mul_left_of_mem {k : G} (hk : k ∈ L) (g : G) :
    (Quotient.mk'' (k * g) : Quotient (QuotientGroup.rightRel L)) = Quotient.mk'' g := by
  rw [rc_mk_eq_mk_iff]
  simpa using L.inv_mem hk

theorem rcGraph_adj_iff {u v : Quotient (QuotientGroup.rightRel L)} :
    (rcGraph L x).Adj u v ↔ u ≠ v ∧ ((∃ g : G, u = Quotient.mk'' g ∧ v = Quotient.mk'' (x * g)) ∨
      ∃ g : G, v = Quotient.mk'' g ∧ u = Quotient.mk'' (x * g)) :=
  SimpleGraph.fromRel_adj _ u v

theorem rcGraph_adj_mk_iff (hx : x * x = 1) (hxL : x ∉ L) (g : G)
    (v : Quotient (QuotientGroup.rightRel L)) :
    (rcGraph L x).Adj (Quotient.mk'' g) v ↔ ∃ k ∈ L, v = Quotient.mk'' (x * k * g) := by
  induction v using Quotient.inductionOn' with | _ h => ?_
  rw [rcGraph_adj_iff]
  constructor
  · rintro ⟨-, ⟨a, ha, hb⟩ | ⟨a, ha, hb⟩⟩
    · rw [rc_mk_eq_mk_iff] at ha
      refine ⟨a * g⁻¹, ha, ?_⟩
      rw [hb, mul_assoc, inv_mul_cancel_right]
    · rw [rc_mk_eq_mk_iff] at hb
      refine ⟨x * a * g⁻¹, hb, ?_⟩
      rw [ha]
      congr 1
      calc a = (x * x) * a := by rw [hx, one_mul]
        _ = x * (x * a * g⁻¹) * g := by group
  · rintro ⟨k, hk, hv⟩
    rw [hv]
    refine ⟨fun h => hxL ?_, Or.inl ⟨k * g, (rc_mk_mul_left_of_mem hk g).symm, by rw [mul_assoc]⟩⟩
    rw [rc_mk_eq_mk_iff] at h
    simpa using L.mul_mem h (L.inv_mem hk)


theorem rc_mk_mul_right_iff (c g h : G) :
    (Quotient.mk'' (g * c) : Quotient (QuotientGroup.rightRel L)) = Quotient.mk'' (h * c) ↔
      (Quotient.mk'' g : Quotient (QuotientGroup.rightRel L)) = Quotient.mk'' h := by
  rw [rc_mk_eq_mk_iff, rc_mk_eq_mk_iff]
  have : h * c * (g * c)⁻¹ = h * g⁻¹ := by group
  rw [this]

@[expose] def rcRmul (L : Subgroup G) (x c : G) : rcGraph L x →g rcGraph L x where
  toFun := Quotient.map' (· * c) fun a b h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa [mul_assoc] using h
  map_rel' {a b} h := by
    induction a using Quotient.inductionOn' with | _ g => ?_
    induction b using Quotient.inductionOn' with | _ g' => ?_
    rw [rcGraph_adj_iff] at h
    obtain ⟨hne, ⟨a, ha, hb⟩ | ⟨a, ha, hb⟩⟩ := h
    · refine rcGraph_adj_iff.2 ⟨fun e => hne ((rc_mk_mul_right_iff c g g').1 e),
        Or.inl ⟨a * c, (rc_mk_mul_right_iff c g a).2 ha, ?_⟩⟩
      rw [← mul_assoc]
      exact (rc_mk_mul_right_iff c g' (x * a)).2 hb
    · refine rcGraph_adj_iff.2 ⟨fun e => hne ((rc_mk_mul_right_iff c g g').1 e),
        Or.inr ⟨a * c, (rc_mk_mul_right_iff c g' a).2 ha, ?_⟩⟩
      rw [← mul_assoc]
      exact (rc_mk_mul_right_iff c g (x * a)).2 hb

@[simp] theorem rcRmul_mk (L : Subgroup G) (x c g : G) :
    rcRmul L x c (Quotient.mk'' g) = Quotient.mk'' (g * c) := rfl


theorem yTri.adj {u v w : Quotient (QuotientGroup.rightRel L)} (h : yTri L x y u v w) :
    (rcGraph L x).Adj u v := by
  obtain ⟨g, rfl, rfl, -, h₁, -⟩ := h
  exact rcGraph_adj_iff.2 ⟨h₁, Or.inl ⟨g, rfl, rfl⟩⟩


end RightCosetGraph

section Covering

variable {G : Type*} [Group G] {E : Type*} [Group E] (f : E →* G)

@[expose] def rcMap (L : Subgroup E) :
    Quotient (QuotientGroup.rightRel L) → Quotient (QuotientGroup.rightRel (L.map f)) :=
  Quotient.map' f fun a b h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa using Subgroup.mem_map_of_mem f h

@[simp] theorem rcMap_mk (L : Subgroup E) (g : E) :
    rcMap f L (Quotient.mk'' g) = Quotient.mk'' (f g) := rfl

variable {L : Subgroup E} {x y : E}

@[expose] def rcHom (f : E →* G) (L : Subgroup E) (x : E) (hx : x * x = 1) (hxL : f x ∉ L.map f) :
    rcGraph L x →g rcGraph (L.map f) (f x) where
  toFun := rcMap f L
  map_rel' {a b} h := by
    induction a using Quotient.inductionOn' with | _ g => ?_
    have hxL' : x ∉ L := fun h => hxL (Subgroup.mem_map_of_mem f h)
    obtain ⟨k, hk, rfl⟩ := (rcGraph_adj_mk_iff hx hxL' g b).1 h
    refine (rcGraph_adj_mk_iff (by rw [← map_mul, hx, map_one]) hxL (f g) _).2
      ⟨f k, Subgroup.mem_map_of_mem f hk, ?_⟩
    rw [rcMap_mk, map_mul, map_mul]

@[simp] theorem rcHom_mk (hx : x * x = 1) (hxL : f x ∉ L.map f) (g : E) :
    rcHom f L x hx hxL (Quotient.mk'' g) = Quotient.mk'' (f g) := rfl


end Covering


end CFSG.YGroups
