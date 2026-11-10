module

public import Certificates.Kernel.G23F48.Chains
public import Certificates.Kernel.G23F48.A22Data
public import Certificates.Data.Kernel.G23F48.ConjOrb
public meta import CFSG.Milestones.ASVolI.F48.Rest.G23Inputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option compiler.extract_closed false

namespace CFSG.KC.G23F48

open CFSG.ASVolI CFSG.ONSchreier.Native

meta def gInvM : Array (Array Nat) := (burnsideF48t_g23Gens ()).map (pinvCand 728)

meta def tauM : Array (Array Nat) := #[burnsideF48t_g23Tau, pinvCand 728 burnsideF48t_g23Tau]

meta def orbM (gs : List (Array Nat)) (roots : List Nat) : Array Nat := Id.run do
  let mut seen : Array Bool := Array.replicate 728 false
  for r in roots do
    seen := seen.set! r true
  for _ in [0:728] do
    for x in [0:728] do
      if seen[x]! then
        for g in gs do
          seen := seen.set! g[x]! true
  let mut out : Array Nat := #[]
  for x in [0:728] do
    if seen[x]! then
      out := out.push x
  return out

meta def restrM (om : Array Nat) (g : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for x in om do
    out := out.push (om.idxOf g[x]!)
  return out

meta def om1M : Array Nat :=
  let L := burnsideF48t_g23LArr
  orbM [L[0]!, L[1]!, L[2]!] [0, 1, 7]

meta def om2M : Array Nat :=
  let L := burnsideF48t_g23LArr
  orbM [L[0]!, L[1]!, L[3]!] [364, 365, 372]

meta def omM : Array (Array Nat) := #[om1M, om2M]

meta def r1M : Array (Array Nat) :=
  let L := burnsideF48t_g23LArr
  let K := burnsideF48t_g23KArr ()
  #[restrM om1M L[0]!, restrM om1M L[1]!, restrM om1M L[2]!, restrM om1M K[0]!,
    restrM om1M K[1]!]

meta def r2M : Array (Array Nat) :=
  let L := burnsideF48t_g23LArr
  let K := burnsideF48t_g23KArr ()
  #[restrM om2M L[0]!, restrM om2M L[1]!, restrM om2M L[3]!, restrM om2M K[0]!,
    restrM om2M K[1]!]

meta def r1IM : Array (Array Nat) :=
  #[pinvCand 121 r1M[0]!, pinvCand 121 r1M[1]!, pinvCand 121 r1M[2]!, pinvCand 121 r1M[3]!,
    pinvCand 121 r1M[4]!]

meta def r2IM : Array (Array Nat) :=
  #[pinvCand 121 r2M[0]!, pinvCand 121 r2M[1]!, pinvCand 121 r2M[2]!, pinvCand 121 r2M[3]!,
    pinvCand 121 r2M[4]!]

end CFSG.KC.G23F48

end

#kmisc_packarrs CFSG.KC.G23F48.GP CFSG.ASVolI.burnsideF48t_g23GensArr 10
#kmisc_packarrs CFSG.KC.G23F48.GPI CFSG.KC.G23F48.gInvM 10
#kmisc_packarrs CFSG.KC.G23F48.TP CFSG.KC.G23F48.tauM 10
#kmisc_packarrs CFSG.KC.G23F48.OM CFSG.KC.G23F48.omM 10
#kmisc_packarrs CFSG.KC.G23F48.R1 CFSG.KC.G23F48.r1M 7
#kmisc_packarrs CFSG.KC.G23F48.R1I CFSG.KC.G23F48.r1IM 7
#kmisc_packarrs CFSG.KC.G23F48.R2 CFSG.KC.G23F48.r2M 7
#kmisc_packarrs CFSG.KC.G23F48.R2I CFSG.KC.G23F48.r2IM 7

public section

set_option maxRecDepth 400000

namespace CFSG.KC.G23F48

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KD.G23A22


end CFSG.KC.G23F48

end
