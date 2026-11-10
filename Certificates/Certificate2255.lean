
module

public import Certificates.Certificate2255Base

public meta import CFSG.Sporadic.Schreier.RuOrbLDefs
import Certificates.Kernel.SporSch.Ru.LB2255P
import Certificates.Kernel.SporSch.Ru.LB2255Neg
import CFSG.Assembly.QuasithinDefs
import CFSG.Foundations
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.B2Thompson
import CFSG.Quasithin.Vol2.KGFactC31RuRefKBase
import CFSG.Sporadic.HeldB.Common
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M24
import CFSG.Sporadic.Schreier.RuLGroup
import CFSG.Sporadic.Schreier.RuPair
import CFSG.Sporadic.Schreier.RuSylow
import Certificates.Certificate43
import Certificates.Kernel.SporSch.J4S.NoCP

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate2255 : (List.range 19).map ruCentCount = ruCentCounts ∧
    (List.range 19).map (fun k => ruOrd14 (compA 4060 ruA0A (ruRepZA k))) =
      [false, false, false, true, false, false, true, false, false, false, false, true, false,
        false, false, false, false, false, false] ∧
    count3 4060 ruLevC ruSqZA = 816 ∧
    [ruFibCount 3, ruFibCount 6, ruFibCount 11] = [0, 0, 4] := KernelSporSch.RuLB.facts

end Certificates
