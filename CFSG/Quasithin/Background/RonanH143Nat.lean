module

public import CFSG.Quasithin.Background.RonanH143QH

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin

@[expose] def betaNatT (a₁ a₂ a₃ a₄ a₅ : ZMod 2) : ℕ :=
  (if a₁ = 1 then 1 else 0) ^^^ (if a₂ = 1 then 15 else 0) ^^^ (if a₃ = 1 then 12 else 0) ^^^
    (if a₄ = 1 then 8 else 0) ^^^ (if a₅ = 1 then 10 else 0)

@[expose] def betaIdx (v : Fin 6 → ZMod 2) : Fin 16 :=
  ⟨betaNatT (v 1) (v 2) (v 3) (v 4) (v 5) % 16, Nat.mod_lt _ (by norm_num)⟩

theorem betaIdx_zero : betaIdx 0 = 0 := by decide +kernel

theorem betaNatT_add : ∀ a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ : ZMod 2,
    betaNatT (a₁ + b₁) (a₂ + b₂) (a₃ + b₃) (a₄ + b₄) (a₅ + b₅) % 16 =
      ((betaNatT a₁ a₂ a₃ a₄ a₅ % 16) ^^^ (betaNatT b₁ b₂ b₃ b₄ b₅ % 16)) % 16 := by
  decide +kernel

theorem betaIdx_add (v w : Fin 6 → ZMod 2) :
    betaIdx (v + w) = xorF (betaIdx v) (betaIdx w) := by
  apply Fin.ext
  exact betaNatT_add (v 1) (v 2) (v 3) (v 4) (v 5) (w 1) (w 2) (w 3) (w 4) (w 5)

@[expose] def beta6Full : G6.PermMod 6 →* P24 where
  toFun v := koPerm (betaIdx (Multiplicative.toAdd v))
  map_one' := by
    show koPerm (betaIdx 0) = 1
    rw [betaIdx_zero, koPerm_zero]
  map_mul' v w := by
    show koPerm (betaIdx (Multiplicative.toAdd v + Multiplicative.toAdd w)) =
      koPerm (betaIdx (Multiplicative.toAdd v)) * koPerm (betaIdx (Multiplicative.toAdd w))
    rw [betaIdx_add, koPerm_mul]

@[expose] def beta6 : ↥(G6.coreMod 6) →* P24 := beta6Full.comp (G6.coreMod 6).subtype


@[expose] def xf6 (s : Fin 16) : Fin 16 :=
  ⟨([0, 10, 7, 13, 14, 4, 9, 3, 5, 15, 2, 8, 11, 1, 12, 6].getD (s : ℕ) 0) % 16,
    Nat.mod_lt _ (by norm_num)⟩


end CFSG.Quasithin.RonanH143
