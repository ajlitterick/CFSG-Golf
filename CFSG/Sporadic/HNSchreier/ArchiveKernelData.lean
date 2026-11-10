module
public import CFSG.Sporadic.HNSchreier.IncludeKernelBytes
public meta import CFSG.Sporadic.HNSchreier.IncludeKernelBytes

public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace CFSG.Sporadic.HNSchreier.Native


@[expose] def archiveKernelBytes (_ : Unit := ()) : KernelBytes :=
  include_hex_bytes% "Data/arrays.txt"

end CFSG.Sporadic.HNSchreier.Native
