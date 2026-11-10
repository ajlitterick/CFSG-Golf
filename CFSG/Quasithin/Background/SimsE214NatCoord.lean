module

public import CFSG.Quasithin.Background.SimsE2Defs
public import CFSG.Quasithin.Background.G2SL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs

public section

open scoped commutatorElement MatrixGroups

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank SL2Model

namespace E214N

variable {Γ : Type} [Group Γ]

section Coord

variable {P : Subgroup Γ} {F : Type} [Field F] {s : ℕ}
  (φ : ↥P →* Multiplicative (Fin s → Fin 2 → F))


end Coord

theorem statedSL_exists_mulVec_eq {F : Type} [Field F] {u w : Fin 2 → F} (hu : u ≠ 0)
    (hw : w ≠ 0) :
    ∃ x ∈ StatedSL 2 F, ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec u = w := by
  obtain ⟨A, hA⟩ := exists_smul_eq u w hu hw
  exact ⟨(specialLinearGroupEquivStatedSL 2 F A : GL (Fin 2) F),
    (specialLinearGroupEquivStatedSL 2 F A).2, hA⟩


end E214N

end CFSG.Quasithin.SimsE2
