module

public import Certificates.Kernel.Sporadic.McLHyp.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore in
open CFSG.EvenSporadicStandard.HypOne in
theorem certificate24430 : FourClassesLarge ↥(centralizerIn mclP (CFSG.Sporadic.SmallOddCore.tp 275 McL.t0)) ∧
    FourClassesLarge ↥(centralizerIn mclR (CFSG.Sporadic.SmallOddCore.tp 275 McL.t0)) ∧
    FourClassesLarge ↥(centralizerIn mclR (CFSG.Sporadic.SmallOddCore.tp 275 McL.t1)) ∧ HasElemAbelianEight ↥mclP ∧
    ∃ l ∈ mclP, orderOf (l * CFSG.Sporadic.SmallOddCore.tp 275 McL.t1 * l⁻¹ * (CFSG.Sporadic.SmallOddCore.tp 275 McL.t1)⁻¹) = 2 :=
  ⟨KernelSpor.McLHG.fourClassesLarge_P0, KernelSpor.McLHG.fourClassesLarge_R0,
    KernelSpor.McLHG.fourClassesLarge_R1, KernelSpor.McLHG.hasElemAbelianEight_mclP,
    KernelSpor.McLHG.fours_wit⟩

end Certificates
