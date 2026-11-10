
module

public import CFSG.Sporadic.Schreier.PairClasses
public import CFSG.Quasithin.Vol2.KGFactC31Orb

public section

namespace CFSG.Quasithin.KGC31.Native

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative


@[expose] def orbW (t0 : Array Nat) (w wi : List (Array Nat)) : Nat → List (List (Array Nat))
  | 0 => []
  | m + 1 => [t0] :: (orbW t0 w wi m).map fun o => wi ++ o ++ w

@[expose] def commW (bs : List Nat) (t0 : Array Nat) (o : List (Array Nat)) : Bool :=
  baseImgs bs (o ++ [t0]) == baseImgs bs (t0 :: o)

@[expose] def spanAddW (bs : List Nat) (sp : List (List (Array Nat))) (o : List (Array Nat)) :
    List (List (Array Nat)) :=
  if sp.any (fun e => baseImgs bs e == baseImgs bs o) then sp else sp ++ sp.map (· ++ o)

@[expose] def spanW (bs : List Nat) (os : List (List (Array Nat))) : List (List (Array Nat)) :=
  os.foldl (spanAddW bs) [[]]

@[expose] def inSpanW (bs : List Nat) (sp cand : List (List (Array Nat))) : Bool :=
  cand.all fun x => sp.any fun e => baseImgs bs e == baseImgs bs x

@[expose] def normW (bs : List Nat) (w wi : List (Array Nat)) (cand : List (List (Array Nat))) :
    Bool :=
  inSpanW bs (spanW bs cand) (cand.map fun x => wi ++ x ++ w)


end CFSG.Quasithin.KGC31.Native

namespace CFSG.Quasithin.KGC31

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.Certificates CFSG.Certificates.Native
  CFSG.Quasithin.KGC31.Native

variable {n : ℕ}


theorem sum_eq_zero_iff {α : Type*} {F : α → ℕ} {l : List α} :
    (l.map F).sum = 0 ↔ ∀ a ∈ l, F a = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem exists_left_of_forall₂ {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => exact absurd hb List.not_mem_nil
  | cons hab _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, h⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

theorem exists_right_of_forall₂ {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {a : α} (ha : a ∈ l₁) : ∃ b ∈ l₂, R a b := by
  induction h with
  | nil => exact absurd ha List.not_mem_nil
  | cons hab _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, h⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩


section Chain

variable {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)}
  {chunks : ℕ}


theorem mem_products_of_mem (hA : ChainArrays Q O S base W) (hc : 0 < chunks)
    (h : rawChainOK n O S base W chunks = true) {c : Equiv.Perm (Fin n)}
    (hcQ : c ∈ Q.originalSubgroup) :
    c ∈ products ((List.range Q.baseCount).map (levList n S base)) := by
  have hF := chainCheckFacts h
  have hQ := (validSchreier_of_chainOK hA hc h).1
  rw [← enumeration_eq hA hF]
  exact (mem_enumeration_iff Q hQ c).2 hcQ

end Chain

section Tests

variable {H : Subgroup (Equiv.Perm (Fin n))} {bs : List ℕ}


theorem foldl_spanAddW_mem (K : Subgroup (Equiv.Perm (Fin n))) :
    ∀ {os : List (List (Array ℕ))} {osG : List (Equiv.Perm (Fin n))},
      List.Forall₂ (RepW n) os osG → (∀ g ∈ osG, g ∈ K) →
      ∀ {sp : List (List (Array ℕ))}, (∀ e ∈ sp, ∃ g ∈ K, RepW n e g) →
        ∀ e ∈ os.foldl (spanAddW bs) sp, ∃ g ∈ K, RepW n e g
  | [], [], .nil, _, sp, hsp => hsp
  | o :: os, g :: osG, .cons hog hos, hK, sp, hsp => by
    rw [List.foldl_cons]
    refine foldl_spanAddW_mem K hos (fun x hx => hK x (List.mem_cons_of_mem _ hx)) ?_
    intro e he
    rw [spanAddW] at he
    split_ifs at he with hany
    · exact hsp e he
    · rcases List.mem_append.mp he with he | he
      · exact hsp e he
      · obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        obtain ⟨g', hg'K, hg'⟩ := hsp e' he'
        exact ⟨g * g', K.mul_mem (hK g List.mem_cons_self) hg'K, hg'.append hog⟩

theorem spanW_mem {os : List (List (Array ℕ))} {osG : List (Equiv.Perm (Fin n))}
    (hos : List.Forall₂ (RepW n) os osG) :
    ∀ e ∈ spanW bs os, ∃ g ∈ Subgroup.closure {x | x ∈ osG}, RepW n e g :=
  foldl_spanAddW_mem _ hos (fun g hg => Subgroup.subset_closure hg) fun e he => by
    rw [List.mem_singleton] at he
    exact ⟨1, Subgroup.one_mem _, he ▸ repW_nil⟩

theorem mem_of_inSpanW (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n)
    {K : Subgroup (Equiv.Perm (Fin n))} (hKH : K ≤ H) {sp : List (List (Array ℕ))}
    (hsp : ∀ e ∈ sp, ∃ g ∈ K, RepW n e g) {cand : List (List (Array ℕ))}
    {candG : List (Equiv.Perm (Fin n))} (hc : List.Forall₂ (RepW n) cand candG)
    (hcH : ∀ x ∈ candG, x ∈ H) (h : inSpanW bs sp cand = true) : ∀ x ∈ candG, x ∈ K := by
  intro x hx
  obtain ⟨xw, hxw, hxwx⟩ := exists_left_of_forall₂ hc hx
  rw [inSpanW, List.all_eq_true] at h
  obtain ⟨e, he, heq⟩ := List.any_eq_true.mp (h xw hxw)
  obtain ⟨g, hgK, heg⟩ := hsp e he
  rw [beq_iff_eq] at heq
  rw [← eq_of_baseImgs_eq hH hbs heg hxwx (hKH hgK) (hcH x hx) heq]
  exact hgK


end Tests

section Scan


end Scan

end CFSG.Quasithin.KGC31

end
