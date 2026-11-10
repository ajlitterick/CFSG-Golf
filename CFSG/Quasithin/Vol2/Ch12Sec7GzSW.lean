module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzSBrS
public import Certificates.Data.S1277Surv

public section

namespace CFSG.Quasithin.H13.I1277

open Certificates.Data.S1277Struct Certificates.Data.S1277Sig Certificates.Data.S1277Surv
  Certificates.Data.S1277Bfs Std

theorem unpackC_packC (cols : List Nat) (hlen : cols.length = 6) (hlt : ∀ c ∈ cols, c < 64) :
    unpackC 6 (packC cols) = cols := by
  match cols, hlen with
  | [a, b, c, d, e, f], _ =>
    have ha : a < 64 := hlt a (by simp)
    have hb : b < 64 := hlt b (by simp)
    have hc : c < 64 := hlt c (by simp)
    have hd : d < 64 := hlt d (by simp)
    have he : e < 64 := hlt e (by simp)
    have hf : f < 64 := hlt f (by simp)
    simp [unpackC, packC, List.range_succ]
    omega

theorem packC_injective (c₁ c₂ : List Nat) (h1 : c₁.length = 6) (h2 : c₂.length = 6)
    (hl1 : ∀ c ∈ c₁, c < 64) (hl2 : ∀ c ∈ c₂, c < 64) (h : packC c₁ = packC c₂) : c₁ = c₂ := by
  rw [← unpackC_packC c₁ h1 hl1, ← unpackC_packC c₂ h2 hl2, h]

theorem app6_eq (x v : Nat) : app6 x v = applyCols (unpackC 6 x) v := by
  simp [app6, unpackC, List.range_succ, applyCols, Nat.div_div_eq_div_mul]

theorem mulS_eq (x y : Nat) : mulS x y = mulSSpec x y := by
  unfold mulS mulSSpec packC compCols
  simp only [app6_eq]
  simp [unpackC, List.range_succ, Nat.div_div_eq_div_mul]

@[expose] noncomputable def pk (σ : Equiv.Perm (Fin (2 ^ 6))) : Nat := packC (colsOf σ)

theorem pk_def (σ : Equiv.Perm (Fin (2 ^ 6))) : pk σ = packC (colsOf σ) := rfl

theorem colsOf_lt (σ : Equiv.Perm (Fin (2 ^ 6))) : ∀ c ∈ colsOf σ, c < 64 := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hi' : i < 6 := by simpa [length_colsOf] using hi
  rw [getElem_colsOf σ i hi']
  exact (σ _).2

theorem unpackC_pk (σ : Equiv.Perm (Fin (2 ^ 6))) : unpackC 6 (pk σ) = colsOf σ :=
  unpackC_packC _ (length_colsOf σ) (colsOf_lt σ)

theorem pk_mul {σ : Equiv.Perm (Fin (2 ^ 6))}
    (hσ : ∀ a b c : Fin (2 ^ 6), a.1 ^^^ b.1 = c.1 → (σ a).1 ^^^ (σ b).1 = (σ c).1)
    (τ : Equiv.Perm (Fin (2 ^ 6))) : pk (σ * τ) = mulS (pk σ) (pk τ) := by
  rw [mulS_eq]
  unfold mulSSpec
  rw [unpackC_pk, unpackC_pk]
  show packC (colsOf (σ * τ)) = packC (compCols (colsOf σ) (colsOf τ))
  rw [colsOf_mul hσ]

theorem pk_one : pk (1 : Equiv.Perm (Fin (2 ^ 6))) = oneS := by
  unfold pk
  rw [colsOf_one]
  rfl

theorem pk_injective {φ : Nat → Nat} {σ τ : Equiv.Perm (Fin (2 ^ 6))} (hσ : σ ∈ Sig 6 φ)
    (hτ : τ ∈ Sig 6 φ) (h : pk σ = pk τ) : σ = τ :=
  colsOf_injective hσ hτ (packC_injective _ _ (length_colsOf σ) (length_colsOf τ)
    (colsOf_lt σ) (colsOf_lt τ) h)


section Lattice

variable {φ : Nat → Nat}

abbrev pkSet (R : Subgroup (Equiv.Perm (Fin (2 ^ 6)))) (y : Nat) : Prop := ∃ r ∈ R, pk r = y

theorem pkSet_mul {R : Subgroup (Equiv.Perm (Fin (2 ^ 6)))} (hR : R ≤ Sig 6 φ) {x y : Nat}
    (hx : pkSet R x) (hy : pkSet R y) : pkSet R (mulS x y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨r', hr', rfl⟩ := hy
  exact ⟨r * r', R.mul_mem hr hr', pk_mul (hR hr).1 r'⟩

theorem pkSet_one {R : Subgroup (Equiv.Perm (Fin (2 ^ 6)))} : pkSet R oneS :=
  ⟨1, R.one_mem, pk_one⟩

theorem card_le_of_pkSet {R : Subgroup (Equiv.Perm (Fin (2 ^ 6)))} (hR : R ≤ Sig 6 φ)
    (l : List Nat) (hnd : l.Nodup) (hl : ∀ y ∈ l, pkSet R y) : l.length ≤ Nat.card R := by
  classical
  let f : {y // y ∈ l} → R := fun y => ⟨(hl y.1 y.2).choose, (hl y.1 y.2).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have := congrArg (fun r : R => pk r.1) hab
    simp only [f] at this
    rw [(hl a.1 a.2).choose_spec.2, (hl b.1 b.2).choose_spec.2] at this
    exact this
  have h1 := Nat.card_le_card_of_injective f hf
  have e2 : {y // y ∈ l} ≃ ↥l.toFinset := Equiv.subtypeEquivRight fun c => by simp
  rwa [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hnd] at h1


end Lattice

end CFSG.Quasithin.H13.I1277

end
