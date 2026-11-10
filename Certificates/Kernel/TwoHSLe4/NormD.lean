module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Norm
meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Norm
public import Certificates.Kernel.TwoHSLe4.S9Defs
public import Certificates.Kernel.Misc.Perm.HexCmd
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

public section

namespace CertificateChecks.KernelTwoHSLe4.Norm

open CFSG.EvenSporadicStandard.TwoHS CFSG.KC.Enum


end CertificateChecks.KernelTwoHSLe4.Norm

#kc_items CertificateChecks.KernelTwoHSLe4.Norm.NV include_bytes "data/NormD.NV.items" 723 8868844025410228637
#kc_items CertificateChecks.KernelTwoHSLe4.Norm.SV include_bytes "data/NormD.SV.items" 256 14084992341678260601

namespace CertificateChecks.KernelTwoHSLe4.Norm

open CFSG.EvenSporadicStandard.TwoHS CFSG.KC.Enum

@[expose] noncomputable def rowR (P : ℕ) : R4 := R4.ofList ((List.range 16).map (pg 2 3 P))

@[expose] noncomputable def nvL : List R4 := (List.range 96).map fun i => rowR (NV i)

@[expose] noncomputable def svR (i : ℕ) : R4 := rowR (SV i)

@[expose] noncomputable def svL : List R4 := (List.range 32).map svR

@[expose] def SL : List R4 := shatData.map S9.rl

@[expose] def compatS (b : R4) : List (R4 × List R4) :=
  SL.map fun s => (s, SL.filter fun s' => decide ((rmul b s.mod2).mod2 = (rmul s'.mod2 b).mod2))

@[expose] def normB2S (b : R4) : Bool :=
  (SL.map R4.mod2).all (fun s => (SL.map R4.mod2).any fun s' => (rmul b s).mod2 == (rmul s' b).mod2) &&
  (SL.map R4.mod2).all (fun s' => (SL.map R4.mod2).any fun s => (rmul b s).mod2 == (rmul s' b).mod2)

@[expose] def nCaseS (T : List (R4 × List R4)) (a : R4) : Bool :=
  rmv a tRV == tRV || !(norm1B T a && SL.all (fun s' => SL.any fun s => rmul a s == rmul s' a)) ||
    (rmv a tRV == zpRV && decide (a ∈ candR))


@[expose] def bitsOf (n : ℕ) : R4 :=
  ⟨n % 2, n / 2 % 2, n / 4 % 2, n / 8 % 2, n / 16 % 2, n / 32 % 2, n / 64 % 2, n / 128 % 2,
   n / 256 % 2, n / 512 % 2, n / 1024 % 2, n / 2048 % 2, n / 4096 % 2, n / 8192 % 2,
   n / 16384 % 2, n / 32768 % 2⟩

@[expose] def bitsN : List R4 := (List.range 65536).map bitsOf

theorem mem_bitsN {b : R4} (hb : b.wf2) : b ∈ bitsN := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hb
  refine List.mem_map.2 ⟨b.a00 + 2 * b.a01 + 4 * b.a02 + 8 * b.a03 + 16 * b.a10 + 32 * b.a11 +
    64 * b.a12 + 128 * b.a13 + 256 * b.a20 + 512 * b.a21 + 1024 * b.a22 + 2048 * b.a23 +
    4096 * b.a30 + 8192 * b.a31 + 16384 * b.a32 + 32768 * b.a33,
    List.mem_range.2 (by omega), ?_⟩
  unfold bitsOf
  congr 1 <;> omega

@[expose] def liftsOK (b : R4) : Bool :=
  bitsN.all fun x => nCaseS (compatS b) (lift2 b x)


end CertificateChecks.KernelTwoHSLe4.Norm

end
