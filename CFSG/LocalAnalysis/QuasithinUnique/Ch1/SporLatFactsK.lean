module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatOfFacts

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat

open CFSG.QuasithinUnique.K1.SporadicPerm

variable {Γ : Type} [Group Γ] [Finite Γ] {Lab : Type} [DecidableEq Lab] [Hashable Lab]
  [Inhabited Lab]

@[expose] def LatFactsK (A : LabAct Lab) (n : ℕ) [MulAction Γ (Fin n)] (ta tb : Array ℕ) (Δ : Lab)
    (a b : Γ) (sg : List Γ) (sT : List (Array ℕ)) (D : LatData Lab) : Prop :=
  D.sTabs = sT ∧ MembersOK A.act n ta tb Δ D ∧
    (∀ g : Γ, lab n A Δ g = Δ ↔ g ∈ Subgroup.closure {x | x ∈ sg}) ∧
    ∀ Z : Subgroup Γ, Subgroup.closure {x | x ∈ sg} ≤ Z → ∃ j ≤ D.mw.size,
      Z = memberOrTop D.mw.size
        (fun j => Subgroup.closure {x | x ∈ sg ++ (D.mw[j]!).map (wordElt a b)}) j

namespace LatFactsK

variable {n : ℕ} [MulAction Γ (Fin n)] {A : LabAct Lab} {valid : Lab → Prop}
  (hlaw : LabLawful Γ n A valid) {Δ : Lab} (hΔ : valid Δ) {a b : Γ} {ta tb : Array ℕ}
  (ha : (tab n a).toArray = ta) (hb : (tab n b).toArray = tb)
  (gen : Subgroup.closure ({a, b} : Set Γ) = ⊤) {sg : List Γ} {sT : List (Array ℕ)} {k : ℕ}
  (hsg : genTabs n sg = sT) (hSk : Nat.card (Subgroup.closure {x | x ∈ sg}) = 2 ^ k) (N : ℕ)
  (hΓ : Nat.card Γ = N * 2 ^ k) {D : LatData Lab} (h : LatFactsK A n ta tb Δ a b sg sT D)

@[expose] noncomputable def ctx : LatCtx Γ n Lab :=
  LatCtx.ofFacts A valid hlaw Δ hΔ a b ta tb ha hb gen D sg k (hsg.trans h.1.symm) hSk N hΓ h.2.1
    h.2.2.1 h.2.2.2


theorem ctx_O_size : (ctx hlaw hΔ ha hb gen hsg hSk N hΓ h).D.O.lbl.size = N :=
  LatCtx.ofFacts_O_size ..

end LatFactsK

end CFSG.QuasithinUnique.Ch1.SporLat

end
