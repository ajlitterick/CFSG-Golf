module

public import CFSG.Quasithin.AppendixH.H12.ModelPlane
public import CFSG.Quasithin.AppendixH.H12.GroupPerm
public import CFSG.Certificates.Kernel.J4.ModelsSound

public section

namespace CFSG.Quasithin.AppendixH.H12.Model

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H12Cert
  CFSG.Quasithin.H13.MatNCert CFSG.Open
open CFSG.ASVolI.ChH (cenIn ptStab)

@[expose] def sigOf (Pg : ℕ → List ℕ) (n : ℕ) (w : List ℕ) : List ℕ :=
  (List.range n).map fun i => spanMask ((Pg i).map (mvN (tW w)))

theorem spanMask_eq_iff {b b' : List ℕ} (hb : ∀ c ∈ b, c < 4096) (hb' : ∀ c ∈ b', c < 4096) :
    spanMask b = spanMask b' ↔ spanSub b = spanSub b' := by
  constructor
  · intro h
    exact (spanSub_eq_iff hb hb').mpr fun c hc => mem_iff_of_maskOf_eq h c
  · intro h
    apply Nat.eq_of_testBit_eq
    intro c
    rw [spanMask, spanMask, testBit_maskOf, testBit_maskOf]
    by_cases hc : c < 4096
    · rw [decide_eq_decide]
      exact (spanSub_eq_iff hb hb').mp h c hc
    · have hcb : ¬ c ∈ spanN b := fun hmem => hc (spanN_lt hb c hmem)
      have hcb' : ¬ c ∈ spanN b' := fun hmem => hc (spanN_lt hb' c hmem)
      simp [hcb, hcb']


theorem exists_actHom {n : ℕ} (H : Subgroup Γ12) (Pg : ℕ → List ℕ)
    (hinj : ∀ i < n, ∀ j < n, spanSub (Pg i) = spanSub (Pg j) → i = j)
    (hclosed : ∀ g ∈ H, ∀ i < n, ∃ j < n, smulSub g (spanSub (Pg i)) = spanSub (Pg j)) :
    ∃ π : ↥H →* Equiv.Perm (Fin n), ∀ (g : ↥H) (i : Fin n),
      smulSub (g : Γ12) (spanSub (Pg i)) = spanSub (Pg (π g i)) := by
  obtain ⟨π, hπ⟩ := exists_permHom (H := ↥H) (X := Subgroup Vec12)
    (fun (g : ↥H) (P : Subgroup Vec12) => smulSub (g : Γ12) P)
    (fun P => by simp only [Subgroup.coe_one, smulSub_one])
    (fun g h P => by simp only [Subgroup.coe_mul, smulSub_mul])
    (fun i : Fin n => spanSub (Pg i))
    (fun i j hij => Fin.ext (hinj i.1 i.2 j.1 j.2 hij))
    (fun g i => by
      obtain ⟨j, hj, hje⟩ := hclosed (g : Γ12) g.2 i.1 i.2
      exact ⟨⟨j, hj⟩, hje⟩)
  exact ⟨π, hπ⟩


end CFSG.Quasithin.AppendixH.H12.Model
