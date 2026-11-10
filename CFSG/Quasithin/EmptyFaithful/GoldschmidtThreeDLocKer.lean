module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatQuot
import all Mathlib.Data.List.Sort

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm

namespace GoldD3


section Omega

variable {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

omit [Inhabited Lab] in
theorem distinctB_of_nodup {a : Array Lab} (h : a.toList.Nodup) : distinctB a = true := by
  have key : ∀ (l : List Lab) (f : Bool) (S : Std.HashSet Lab), f = true → l.Nodup →
      (∀ x ∈ l, S.contains x = false) → (l.foldl distinctStep (f, S)).1 = true := by
    intro l
    induction l with
    | nil => intro f S hf _ _; simpa using hf
    | cons x l ih =>
      intro f S hf hnd hS
      have hx : S.contains x = false := hS x List.mem_cons_self
      simp only [List.foldl_cons, distinctStep, hx]
      refine ih f _ hf (List.nodup_cons.1 hnd).2 fun y hy => ?_
      rw [Std.HashSet.contains_insert, hS y (List.mem_cons_of_mem _ hy)]
      have : y ≠ x := fun h => (List.nodup_cons.1 hnd).1 (h ▸ hy)
      simp [Ne.symm this]
  unfold distinctB
  rw [← Array.foldl_toList]
  exact key a.toList true ∅ rfl h fun x _ => by simp

@[expose] def OmegaSpecK (act : Array ℕ → Lab → Lab) (letters : Array (Array ℕ)) (Δ : Lab)
    (O : OmegaData Lab) : Prop :=
  O.lbl[0]! = Δ ∧ 0 < O.lbl.size ∧
  (∀ l < letters.size, ∀ i < O.lbl.size,
    (O.pn[l]!)[i]! < O.lbl.size ∧ O.lbl[(O.pn[l]!)[i]!]! = act letters[l]! O.lbl[i]!) ∧
  (∀ i < O.lbl.size, 0 < i → O.par[i]! < i ∧ O.via[i]! < letters.size ∧
    (O.pn[O.via[i]!]!)[O.par[i]!]! = i) ∧
  O.lbl.toList.Nodup

instance (act : Array ℕ → Lab → Lab) (letters : Array (Array ℕ)) (Δ : Lab) (O : OmegaData Lab) :
    Decidable (OmegaSpecK act letters Δ O) := by
  unfold OmegaSpecK; infer_instance

theorem OmegaSpecK.spec {act : Array ℕ → Lab → Lab} {letters : Array (Array ℕ)} {Δ : Lab}
    {O : OmegaData Lab} (h : OmegaSpecK act letters Δ O) : OmegaSpec act letters Δ O :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, distinctB_of_nodup h.2.2.2.2⟩

end Omega

end GoldD3

end CFSG.Quasithin
