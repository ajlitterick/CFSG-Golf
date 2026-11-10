module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.AutZCartan.LineTorus
import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.Module
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.AutZC

open CFSG.Open Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {K : Type} [Field K]

theorem lineTorus_statedSp (m : ℕ) [NeZero m] :
    LineTorus (StatedSp m K) (Pi.single (Sum.inl 0) 1) := by
  intro c
  let t : Fin m → Kˣ := Pi.mulSingle 0 c
  refine ⟨torusHom t, (torusHom t).2, ?_⟩
  rw [coe_torusHom]
  funext x
  rw [Matrix.mulVec_diagonal]
  by_cases hx : x = Sum.inl 0
  · subst hx
    simp [t, Pi.mulSingle]
  · simp [Pi.single_eq_of_ne hx]

end CFSG.LocalAnalysis.UniquenessCase.UC22.AutZC
