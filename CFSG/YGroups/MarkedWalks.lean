module

public import CFSG.Monster.B.Recog.GenericCovering

public section

namespace CFSG.YGroups

open SimpleGraph CFSG.Monster.B.Recog

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

@[expose] def permClosure (T : V → V → V → Prop) (a b c : V) : Prop :=
  T a b c ∨ T a c b ∨ T b a c ∨ T b c a ∨ T c a b ∨ T c b a

theorem permClosure_swap {T : V → V → V → Prop} {a b c : V} (h : permClosure T a b c) :
    permClosure T a c b := by
  unfold permClosure at h ⊢
  tauto

inductive MarkedMove (T : V → V → V → Prop) {u v : V} : G.Walk u v → G.Walk u v → Prop
  | backtrack {x y : V} (p : G.Walk u x) (q : G.Walk x v) (h : G.Adj x y) :
      MarkedMove T (p.append q) (p.append (.cons h (.cons h.symm q)))
  | triangle {x y z : V} (p : G.Walk u x) (q : G.Walk x v) (hxy : G.Adj x y) (hyz : G.Adj y z)
      (hzx : G.Adj z x) (hT : permClosure T x y z) :
      MarkedMove T (p.append q) (p.append (.cons hxy (.cons hyz (.cons hzx q))))

@[expose] def MarkedHomotopic (T : V → V → V → Prop) {u v : V} (p q : G.Walk u v) : Prop :=
  Relation.EqvGen (MarkedMove T) p q

namespace MarkedHomotopic

variable {T : V → V → V → Prop} {u v w : V} {p q r : G.Walk u v}

@[refl] theorem refl (p : G.Walk u v) : MarkedHomotopic T p p := Relation.EqvGen.refl p

@[symm] theorem symm (h : MarkedHomotopic T p q) : MarkedHomotopic T q p :=
  Relation.EqvGen.symm _ _ h

@[trans] theorem trans (h₁ : MarkedHomotopic T p q) (h₂ : MarkedHomotopic T q r) :
    MarkedHomotopic T p r :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

end MarkedHomotopic

theorem MarkedMove.markedHomotopic {T : V → V → V → Prop} {u v : V} {p q : G.Walk u v}
    (h : MarkedMove T p q) : MarkedHomotopic T p q :=
  Relation.EqvGen.rel _ _ h

theorem markedHomotopic_backtrack (T : V → V → V → Prop) {u x y v : V} (p : G.Walk u x)
    (q : G.Walk x v) (h : G.Adj x y) :
    MarkedHomotopic T (p.append q) (p.append (.cons h (.cons h.symm q))) :=
  (MarkedMove.backtrack p q h).markedHomotopic

theorem markedHomotopic_triangle {T : V → V → V → Prop} {u x y z v : V} (p : G.Walk u x)
    (q : G.Walk x v) (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x)
    (hT : permClosure T x y z) :
    MarkedHomotopic T (p.append q) (p.append (.cons hxy (.cons hyz (.cons hzx q)))) :=
  (MarkedMove.triangle p q hxy hyz hzx hT).markedHomotopic

theorem MarkedMove.append_left {T : V → V → V → Prop} {w u v : V} (r : G.Walk w u)
    {p q : G.Walk u v} (h : MarkedMove T p q) : MarkedMove T (r.append p) (r.append q) := by
  cases h with
  | backtrack p q h =>
    rw [Walk.append_assoc, Walk.append_assoc]
    exact .backtrack _ q h
  | triangle p q hxy hyz hzx hT =>
    rw [Walk.append_assoc, Walk.append_assoc]
    exact .triangle _ q hxy hyz hzx hT

theorem MarkedMove.append_right {T : V → V → V → Prop} {u v w : V} {p q : G.Walk u v}
    (h : MarkedMove T p q) (r : G.Walk v w) : MarkedMove T (p.append r) (q.append r) := by
  cases h with
  | backtrack p q h =>
    rw [← Walk.append_assoc, ← Walk.append_assoc, Walk.cons_append, Walk.cons_append]
    exact .backtrack p _ h
  | triangle p q hxy hyz hzx hT =>
    rw [← Walk.append_assoc, ← Walk.append_assoc, Walk.cons_append, Walk.cons_append,
      Walk.cons_append]
    exact .triangle p _ hxy hyz hzx hT

theorem MarkedMove.reverse {T : V → V → V → Prop} {u v : V} {p q : G.Walk u v}
    (h : MarkedMove T p q) : MarkedMove T p.reverse q.reverse := by
  cases h with
  | backtrack p q h =>
    simp only [Walk.reverse_append, Walk.reverse_cons, ← Walk.append_assoc, Walk.cons_append,
      Walk.nil_append]
    exact .backtrack q.reverse p.reverse h
  | triangle p q hxy hyz hzx hT =>
    simp only [Walk.reverse_append, Walk.reverse_cons, ← Walk.append_assoc, Walk.cons_append,
      Walk.nil_append]
    exact .triangle q.reverse p.reverse hzx.symm hyz.symm hxy.symm (permClosure_swap hT)

namespace MarkedHomotopic

variable {T : V → V → V → Prop} {u v w : V}

theorem append_left (r : G.Walk w u) {p q : G.Walk u v} (h : MarkedHomotopic T p q) :
    MarkedHomotopic T (r.append p) (r.append q) := by
  induction h with
  | rel p q h => exact (h.append_left r).markedHomotopic
  | refl p => exact refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem append_right {p q : G.Walk u v} (h : MarkedHomotopic T p q) (r : G.Walk v w) :
    MarkedHomotopic T (p.append r) (q.append r) := by
  induction h with
  | rel p q h => exact (h.append_right r).markedHomotopic
  | refl p => exact refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem append {p p' : G.Walk u v} {q q' : G.Walk v w} (hp : MarkedHomotopic T p p')
    (hq : MarkedHomotopic T q q') : MarkedHomotopic T (p.append q) (p'.append q') :=
  (hp.append_right q).trans (hq.append_left p')

theorem cons (h : G.Adj w u) {p q : G.Walk u v} (hpq : MarkedHomotopic T p q) :
    MarkedHomotopic T (.cons h p) (.cons h q) := by
  simpa using hpq.append_left (.cons h .nil)

theorem reverse {p q : G.Walk u v} (h : MarkedHomotopic T p q) :
    MarkedHomotopic T p.reverse q.reverse := by
  induction h with
  | rel p q h => exact h.reverse.markedHomotopic
  | refl p => exact refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end MarkedHomotopic

theorem markedHomotopic_cons_cons_nil (T : V → V → V → Prop) {x y : V} (h : G.Adj x y) :
    MarkedHomotopic T (.cons h (.cons h.symm .nil) : G.Walk x x) .nil :=
  (markedHomotopic_backtrack T (.nil : G.Walk x x) .nil h).symm

theorem markedHomotopic_append_reverse (T : V → V → V → Prop) {u v : V} (p : G.Walk u v) :
    MarkedHomotopic T (p.append p.reverse) .nil := by
  induction p with
  | nil => exact MarkedHomotopic.refl _
  | @cons a b c h p ih =>
    rw [Walk.reverse_cons, Walk.cons_append, Walk.append_assoc]
    refine (MarkedHomotopic.cons h (ih.append_right (.cons h.symm .nil))).trans ?_
    exact markedHomotopic_cons_cons_nil T h

theorem markedHomotopic_reverse_append (T : V → V → V → Prop) {u v : V} (p : G.Walk u v) :
    MarkedHomotopic T (p.reverse.append p) .nil := by
  simpa using markedHomotopic_append_reverse T p.reverse


theorem MarkedMove.elemMove {T : V → V → V → Prop} {u v : V} {p q : G.Walk u v}
    (h : MarkedMove T p q) : ElemMove p q := by
  cases h with
  | backtrack p q h => exact .backtrack p q h
  | triangle p q hxy hyz hzx _ => exact .triangle p q hxy hyz hzx


theorem MarkedHomotopic.homotopic {T : V → V → V → Prop} {u v : V} {p q : G.Walk u v}
    (h : MarkedHomotopic T p q) : Homotopic p q := by
  induction h with
  | rel p q h => exact h.elemMove.homotopic
  | refl p => exact Homotopic.refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂


@[expose] def LiftsMarked (f : H →g G) (T : V → V → V → Prop) : Prop :=
  ∀ a y z, G.Adj (f a) y → G.Adj y z → G.Adj z (f a) → permClosure T (f a) y z →
    ∃ b c, H.Adj a b ∧ H.Adj b c ∧ H.Adj c a ∧ f b = y ∧ f c = z


section Lifting

variable {f : H →g G} {T : V → V → V → Prop}

theorem liftEnd_nil_eq (hf : IsCovering f) {u : V} (a : W) (ha : f a = u) :
    hf.liftEnd (.nil : G.Walk u u) a ha = a := by
  subst ha
  simpa using hf.liftEnd_map (.nil : H.Walk a a) rfl

theorem liftEnd_marked_triangle (hf : IsCovering f) (ht : LiftsMarked f T) {x y z v : V}
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x) (hT : permClosure T x y z)
    (q : G.Walk x v) (a : W) (ha : f a = x) :
    hf.liftEnd (.cons hxy (.cons hyz (.cons hzx q))) a ha = hf.liftEnd q a ha := by
  subst ha
  obtain ⟨b, c, hab, hbc, hca, rfl, rfl⟩ := ht a y z hxy hyz hzx hT
  have h₁ := hf.liftEnd_map (.cons hab (.cons hbc (.cons hca .nil)) : H.Walk a a) rfl
  have h₂ : ((Walk.cons hab (.cons hbc (.cons hca .nil)) : H.Walk a a).map f).append q =
      .cons hxy (.cons hyz (.cons hzx q)) := by
    simp only [Walk.map_cons, Walk.map_nil, Walk.cons_append, Walk.nil_append]
  rw [← h₂, hf.liftEnd_append]
  exact hf.liftEnd_congr q h₁ _ _

theorem MarkedMove.liftEnd_eq (hf : IsCovering f) (ht : LiftsMarked f T) {u v : V}
    {p q : G.Walk u v} (hpq : MarkedMove T p q) (a : W) (ha : f a = u) :
    hf.liftEnd p a ha = hf.liftEnd q a ha := by
  cases hpq with
  | backtrack p q h => rw [hf.liftEnd_append, hf.liftEnd_append, hf.liftEnd_backtrack]
  | triangle p q hxy hyz hzx hT =>
    rw [hf.liftEnd_append, hf.liftEnd_append, liftEnd_marked_triangle hf ht hxy hyz hzx hT]

theorem MarkedHomotopic.liftEnd_eq (hf : IsCovering f) (ht : LiftsMarked f T) {u v : V}
    {p q : G.Walk u v} (hpq : MarkedHomotopic T p q) (a : W) (ha : f a = u) :
    hf.liftEnd p a ha = hf.liftEnd q a ha := by
  induction hpq with
  | rel p q h => exact h.liftEnd_eq hf ht a ha
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂


end Lifting

inductive ClosedMove (C : ∀ {a : V}, G.Walk a a → Prop) {u v : V} :
    G.Walk u v → G.Walk u v → Prop
  | backtrack {x y : V} (p : G.Walk u x) (q : G.Walk x v) (h : G.Adj x y) :
      ClosedMove C (p.append q) (p.append (.cons h (.cons h.symm q)))
  | closed {x : V} (p : G.Walk u x) (r : G.Walk x x) (q : G.Walk x v) (hr : C r) :
      ClosedMove C (p.append q) (p.append (r.append q))

@[expose] def ClosedHomotopic (C : ∀ {a : V}, G.Walk a a → Prop) {u v : V} (p q : G.Walk u v) :
    Prop :=
  Relation.EqvGen (ClosedMove C) p q


section ClosedLifting

variable {f : H →g G} {C : ∀ {a : V}, G.Walk a a → Prop}

@[expose] def ClosedLifts (hf : IsCovering f) (C : ∀ {a : V}, G.Walk a a → Prop) : Prop :=
  ∀ {x : V} (r : G.Walk x x), C r → ∀ (a : W) (ha : f a = x), hf.liftEnd r a ha = a


namespace ClosedHomotopic

variable {u v : V} {p q r : G.Walk u v}

@[refl] theorem refl (p : G.Walk u v) : ClosedHomotopic C p p := Relation.EqvGen.refl p

@[symm] theorem symm (h : ClosedHomotopic C p q) : ClosedHomotopic C q p :=
  Relation.EqvGen.symm _ _ h

@[trans] theorem trans (h₁ : ClosedHomotopic C p q) (h₂ : ClosedHomotopic C q r) :
    ClosedHomotopic C p r :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

end ClosedHomotopic


theorem ClosedMove.liftEnd_eq {hf : IsCovering f} (hC : ClosedLifts hf C) {u v : V}
    {p q : G.Walk u v} (hpq : ClosedMove C p q) (a : W) (ha : f a = u) :
    hf.liftEnd p a ha = hf.liftEnd q a ha := by
  cases hpq with
  | backtrack p q h => rw [hf.liftEnd_append, hf.liftEnd_append, hf.liftEnd_backtrack]
  | closed p r q hr =>
    rw [hf.liftEnd_append, hf.liftEnd_append, hf.liftEnd_append]
    exact hf.liftEnd_congr q (hC r hr _ _).symm _ _

theorem ClosedHomotopic.liftEnd_eq {hf : IsCovering f} (hC : ClosedLifts hf C) {u v : V}
    {p q : G.Walk u v} (hpq : ClosedHomotopic C p q) (a : W) (ha : f a = u) :
    hf.liftEnd p a ha = hf.liftEnd q a ha := by
  induction hpq with
  | rel p q h => exact h.liftEnd_eq hC a ha
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂


end ClosedLifting

end CFSG.YGroups
