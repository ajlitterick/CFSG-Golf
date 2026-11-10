module

public import CFSG.Quasithin.Background.JonesParshallWedgeH1

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Assembly.LowTwoRank

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def repOfEnd {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (μ : G →* AddMonoid.End V) : Representation (ZMod 2) G V where
  toFun g := (μ g : V →+ V).toZModLinearMap 2
  map_one' := LinearMap.ext fun v => by
    change μ 1 v = v
    rw [map_one]
    rfl
  map_mul' g h := LinearMap.ext fun v => by
    change μ (g * h) v = μ g (μ h v)
    rw [map_mul]
    rfl

@[expose] def wedgeRep : Representation (ZMod 2) (SpecialLinearGroup (Fin 5) (ZMod 2))
    (Fin 10 → ZMod 2) :=
  repOfEnd (muW (ZMod 2))

theorem card_Z1A_wedge
    : Nat.card (Z1A (muW (ZMod 2))) = 1 * Nat.card (B1A (muW (ZMod 2))) := by
  rw [Z1A_eq_B1A_wedge, one_mul]


end CFSG.Quasithin.JonesParshall
