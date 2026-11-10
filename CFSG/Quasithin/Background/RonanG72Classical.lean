module

public import CFSG.Quasithin.Background.RonanG72Basic
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.CoverOdd
public import CFSG.Quasithin.Background.Harris.G2.U33Module

public section

namespace CFSG.Quasithin.RonanG72

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11
  CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]


theorem statedClassicalModel_of_mulEquiv {X Y : Type} [Group X] [Group Y] (f : X ≃* Y)
    {t : StatedLieTag} {n p e : ℕ} (h : StatedClassicalModel Y t n p e) :
    StatedClassicalModel X t n p e := by
  obtain ⟨hadm, hm⟩ := h
  refine ⟨hadm, ?_⟩
  cases t with
  | PSL =>
    obtain ⟨K, i1, i2, hK, ⟨g⟩⟩ := hm
    exact ⟨K, i1, i2, hK, ⟨f.trans g⟩⟩
  | PSU =>
    obtain ⟨K, i1, i2, hK, ⟨g⟩⟩ := hm
    exact ⟨K, i1, i2, hK, ⟨f.trans g⟩⟩
  | PSp =>
    obtain ⟨K, i1, i2, hK, ⟨g⟩⟩ := hm
    exact ⟨K, i1, i2, hK, ⟨f.trans g⟩⟩
  | POmegaOdd =>
    obtain ⟨K, i1, i2, hK, ⟨g⟩⟩ := hm
    exact ⟨K, i1, i2, hK, ⟨f.trans g⟩⟩
  | POmegaPlus =>
    obtain ⟨K, i1, i2, hK, ⟨g⟩⟩ := hm
    exact ⟨K, i1, i2, hK, ⟨f.trans g⟩⟩
  | POmegaMinus =>
    obtain ⟨K, i1, i2, hK, b, c, hbc, ⟨g⟩⟩ := hm
    exact ⟨K, i1, i2, hK, b, c, hbc, ⟨f.trans g⟩⟩
  | _ => exact hm


end CFSG.Quasithin.RonanG72
