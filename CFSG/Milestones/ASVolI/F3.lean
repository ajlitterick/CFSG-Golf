module

public import CFSG.Quasithin.Background.F3Compare
public import CFSG.Quasithin.Background.F3Geometry

public section

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.CosetGeom CFSG.Quasithin.RankTwoAmalgam
open CFSG.Quasithin.RankTwoAmalgam.Completion


noncomputable abbrev incl {G : Type} [Group G] (G₁ G₂ : Subgroup G) :
    (RankTwoAmalgam.ofSubgroups G₁ G₂).Completion ↥(G₁ ⊔ G₂) :=
  RankTwoAmalgam.inclusionCompletion G₁ G₂ (G₁ ⊔ G₂) rfl


end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.CosetGeom CFSG.Quasithin.RankTwoAmalgam
open CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF


end CFSG.ASVolI
