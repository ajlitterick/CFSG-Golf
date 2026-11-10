module

public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C00
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C01
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C02
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C03
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C04
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C05
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C06
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C07
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C08
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C09
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C10
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C11
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C12
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C13
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C14
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C15
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C16
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C17
public import CFSG.Certificates.Kernel.BSeed.Chunks.M2C18
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.KC.BSeed

open CFSG.KD.BSeed CFSG.Blueprint in
theorem bseed2_lit : NativeSporadic.BSeed2 = String.ofList (charsOfS
    (M2C00.CH ++ M2C01.CH ++ M2C02.CH ++ M2C03.CH ++ M2C04.CH ++ M2C05.CH ++ M2C06.CH ++
      M2C07.CH ++ M2C08.CH ++ M2C09.CH ++ M2C10.CH ++ M2C11.CH ++ M2C12.CH ++ M2C13.CH ++
      M2C14.CH ++ M2C15.CH ++ M2C16.CH ++ M2C17.CH ++ M2C18.CH)) := by
  simp only [NativeSporadic.BSeed2, charsOfS_eq, bytesOfS_append, List.map_append,
    String.ofList_append, M2C00.lit, M2C01.lit, M2C02.lit, M2C03.lit, M2C04.lit,
    M2C05.lit, M2C06.lit, M2C07.lit, M2C08.lit, M2C09.lit, M2C10.lit, M2C11.lit,
    M2C12.lit, M2C13.lit, M2C14.lit, M2C15.lit, M2C16.lit, M2C17.lit, M2C18.lit]

end CFSG.KC.BSeed

end
