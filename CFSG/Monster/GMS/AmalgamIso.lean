module

public import CFSG.Monster.B.Recog.GenericTits

public section

namespace CFSG.Monster.GMS

open CFSG.Monster.B.Recog

structure TitsData {V : Type*} (Γ : SimpleGraph V) (X : Type*) [Group X] [MulAction X V]
    (ι : Type*) where
  v : V
  w : V
  u : ι → V
  Xv : Subgroup X
  Xe : Subgroup X
  Xt : ι → Subgroup X
  hadj : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b)
  hconn : Γ.Preconnected
  hΓ : Triangulable Γ
  hvw : Γ.Adj v w
  hloc : ∀ y, Γ.Adj v y → ∃ g : X, g • v = v ∧ g • w = y
  hswap : ∃ g : X, g • v = w ∧ g • w = v
  hXv : ∀ g, g ∈ Xv ↔ g • v = v
  hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • w = w) ∨ (g • v = w ∧ g • w = v)
  hXt : ∀ j, ∀ g ∈ Xt j, g • v = v ∨ g • v = w ∨ g • v = u j
  hτ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = v
  hρ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = u j ∧ g • u j = v
  htri : ∀ y₁ y₂, Γ.Adj v y₁ → Γ.Adj y₁ y₂ → Γ.Adj y₂ v →
    ∃ j, ∃ g : X, g • v = v ∧ g • w = y₁ ∧ g • u j = y₂

namespace TitsData

variable {V : Type*} {Γ : SimpleGraph V} {X : Type*} [Group X] [MulAction X V] {ι : Type*}

theorem existsUnique_hom (D : TitsData Γ X ι) {Y : Type*} [Group Y] (φv : D.Xv →* Y)
    (φe : D.Xe →* Y) (φt : ∀ j, D.Xt j →* Y)
    (hve : ∀ a (ha : a ∈ D.Xv) (hb : a ∈ D.Xe), φv ⟨a, ha⟩ = φe ⟨a, hb⟩)
    (hvt : ∀ j a (ha : a ∈ D.Xv) (hb : a ∈ D.Xt j), φv ⟨a, ha⟩ = φt j ⟨a, hb⟩)
    (het : ∀ j a (ha : a ∈ D.Xe) (hb : a ∈ D.Xt j), φe ⟨a, ha⟩ = φt j ⟨a, hb⟩) :
    ∃! Φ : X →* Y, (∀ a : D.Xv, Φ a = φv a) ∧ (∀ a : D.Xe, Φ a = φe a) ∧
      ∀ j (a : D.Xt j), Φ a = φt j a :=
  tits_universal_completion D.hadj D.hconn D.hΓ D.hvw D.hloc D.hswap D.Xv D.Xe D.hXv D.hXe D.u
    D.Xt D.hXt D.hτ D.hρ D.htri φv φe φt hve hvt het

theorem hom_eq_id (D : TitsData Γ X ι) (Φ : X →* X) (hv : ∀ a : D.Xv, Φ a = a)
    (he : ∀ a : D.Xe, Φ a = a) (ht : ∀ j (a : D.Xt j), Φ a = a) : Φ = MonoidHom.id X := by
  obtain ⟨Ψ, -, hΨ⟩ := D.existsUnique_hom D.Xv.subtype D.Xe.subtype (fun j => (D.Xt j).subtype)
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  rw [hΨ Φ ⟨hv, he, ht⟩, hΨ (MonoidHom.id X) ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩]

end TitsData


end CFSG.Monster.GMS
