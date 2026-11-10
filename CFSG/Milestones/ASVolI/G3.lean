module

public import CFSG.Quasithin.Vol2.Ch10SecG31L

public section

namespace CFSG.ASVolI.ChG

open CFSG.Open

variable {V : Type*} [CommGroup V]

@[expose] def transvGroup (Gm : Subgroup (MulAut V)) (X : Subgroup V) : Subgroup (MulAut V) :=
  Subgroup.closure {g | g ∈ Gm ∧ ∀ v : V, g v * v⁻¹ ∈ X}

@[expose] def spanPts (Δ : Set (Subgroup V)) : Subgroup V := ⨆ X ∈ Δ, X

@[expose] def transvSpan (Gm : Subgroup (MulAut V)) (Δ : Set (Subgroup V)) :
    Subgroup (MulAut V) :=
  ⨆ X ∈ Δ, transvGroup Gm X

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChG

@[expose] def G_3_1 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (Gm : Subgroup (MulAut V)), pCoreOf 2 Gm = ⊥ → ∀ (Δ₀ : Set (Subgroup V)), Δ₀.Nonempty →
    (∀ X ∈ Δ₀, Nat.card X = 2) →
    (∀ X ∈ Δ₀, ∀ g ∈ Gm, X.map (g : MulAut V).toMonoidHom ∈ Δ₀) →
    (∀ X ∈ Δ₀, ∀ Y ∈ Δ₀, ∃ g ∈ Gm, X.map (g : MulAut V).toMonoidHom = Y) →
    (∀ X ∈ Δ₀, 4 ≤ (transvGroup Gm X ⊓ pCoreOf 2 Gm).relIndex (transvGroup Gm X)) →
    ∀ (s : ℕ) (hs : 0 < s) (Δ : Fin s → Set (Subgroup V)),
      (∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)) → (⋃ i, Δ i) = Δ₀ → (∀ i, (Δ i).Nonempty) →
      (∀ i, ∀ X ∈ Δ i, ∀ g ∈ transvSpan Gm Δ₀, X.map (g : MulAut V).toMonoidHom ∈ Δ i) →
      (∀ i, ∀ X ∈ Δ i, ∀ Y ∈ Δ i, ∃ g ∈ transvSpan Gm Δ₀,
        X.map (g : MulAut V).toMonoidHom = Y) →
        (iSupIndep (fun i => spanPts (Δ i)) ∧ (⨆ i, spanPts (Δ i)) = spanPts Δ₀ ∧
          iSupIndep (fun i => transvSpan Gm (Δ i)) ∧
          (⨆ i, transvSpan Gm (Δ i)) = transvSpan Gm Δ₀ ∧
          (∀ i j, i ≠ j → ∀ a ∈ transvSpan Gm (Δ i), ∀ b ∈ transvSpan Gm (Δ j), a * b = b * a) ∧
          (∀ i j, i ≠ j → ∀ a ∈ transvSpan Gm (Δ i), ∀ v ∈ spanPts (Δ j), a v = v) ∧
          (∀ i j, ∃ g ∈ Gm, (transvSpan Gm (Δ i)).map (MulAut.conj g).toMonoidHom =
            transvSpan Gm (Δ j)) ∧
          (∀ i j, ∃ g ∈ Gm, (spanPts (Δ i)).map (g : MulAut V).toMonoidHom = spanPts (Δ j))) ∧
        ((∀ φ : ↥(spanPts (Δ ⟨0, hs⟩)) ≃* ↥(spanPts (Δ ⟨0, hs⟩)),
            ∃ g ∈ transvSpan Gm (Δ ⟨0, hs⟩),
              ∀ v : ↥(spanPts (Δ ⟨0, hs⟩)), g (v : V) = ((φ v : ↥(spanPts (Δ ⟨0, hs⟩))) : V)) ∧
          Δ ⟨0, hs⟩ = {X | X ≤ spanPts (Δ ⟨0, hs⟩) ∧ Nat.card X = 2} ∧
          IsElemAbelian 2 (transvSpan Gm (Δ ⟨0, hs⟩) ⊓
            fixingSubgroup (MulAut V) (spanPts (Δ ⟨0, hs⟩) : Set V)) ∧
          ∀ d : ℕ, Nat.card (spanPts (Δ ⟨0, hs⟩)) = 2 ^ d → ∀ X ∈ Δ ⟨0, hs⟩,
            Nat.card (transvGroup Gm X) = 2 ^ (d - 1) * Nat.card ↥(transvGroup Gm X ⊓
              fixingSubgroup (MulAut V) (spanPts (Δ ⟨0, hs⟩) : Set V))) ∧
        8 ≤ Nat.card (spanPts (Δ ⟨0, hs⟩))


end CFSG.ASVolI
