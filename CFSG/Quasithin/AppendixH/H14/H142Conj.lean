module

public import CFSG.Quasithin.AppendixH.H14.Vocab

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI.ChH CFSG.Open

variable {X : Type*} [Group X]


theorem exists_mul_of_card_le [Finite X] {M E : Subgroup X} {N : ℕ} (g : Fin N → X) {Y : Type*}
    (act : X → Y) (hgM : ∀ k, g k ∈ M) (hE : E ≤ M)
    (hact : ∀ k, ∀ e ∈ E, act (g k * e) = act (g k))
    (hinj : Function.Injective (fun k => act (g k))) (hcard : Nat.card ↥M ≤ N * Nat.card ↥E) :
    ∀ x ∈ M, ∃ k, ∃ e ∈ E, x = g k * e := by
  intro x hx
  let F : Fin N × ↥E → ↥M :=
    fun ke => ⟨g ke.1 * (ke.2 : X), mul_mem (hgM ke.1) (hE ke.2.2)⟩
  have hF_inj : Function.Injective F := by
    rintro ⟨k, e⟩ ⟨k', e'⟩ h
    have h1 : g k * (e : X) = g k' * (e' : X) := by
      simpa [F] using congrArg Subtype.val h
    have h2 : act (g k) = act (g k') := by
      calc act (g k) = act (g k * (e : X)) := (hact k e e.2).symm
        _ = act (g k' * (e' : X)) := by rw [h1]
        _ = act (g k') := hact k' e' e'.2
    have hk : k = k' := hinj h2
    subst hk
    have he : e = e' := Subtype.ext (mul_left_cancel h1)
    subst he
    rfl
  have hcard' : Nat.card ↥M ≤ Nat.card (Fin N × ↥E) := by
    rw [Nat.card_prod, Nat.card_fin]
    exact hcard
  have hbij : Function.Bijective F := hF_inj.bijective_of_nat_card_le hcard'
  obtain ⟨ke, hke⟩ := hbij.2 ⟨x, hx⟩
  exact ⟨ke.1, ke.2, by simpa [F] using (congrArg Subtype.val hke).symm⟩

end CFSG.Quasithin.AppendixH.H14