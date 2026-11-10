module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheck

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

section DecodeR

variable (tk : Array ℕ) (regs : Array (Array ℕ))

@[expose] def rdReg (p : ℕ) : Array ℕ × ℕ := (regs[tk[p]!]!, p + 1)


end DecodeR


end CFSG.ComponentClassification.RankTwoSporadic.Cert
