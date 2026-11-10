module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.Sporadic.Schreier.LyCheckSep
import Certificates.Kernel.SporSch.Ly.SepGlue
public import Certificates.Certificate14970
import Certificates.Kernel.LyFivePc.Facts

public section

namespace Certificates

theorem certificate1023018 :     CFSG.StandardType.SporadicShape.SporKRestCover 5 CFSG.Blueprint.NativeSporadic.Ly :=
  CertificateChecks.KernelLyFivePc.cover_native

end Certificates
