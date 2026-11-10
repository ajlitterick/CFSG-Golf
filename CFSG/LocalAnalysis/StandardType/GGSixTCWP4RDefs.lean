module

public import Certificates.Data.TcRes
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel)


@[expose] def tcChiQ (τ : Tag) (p : ℕ) (Q : Set (Fin τ.rank → ZMod p)) :
    Multiplicative (Fin τ.rank → ℤ) →* Multiplicative (Q → ZMod p) where
  toFun γ := Multiplicative.ofAdd fun v =>
    ∑ k, ((Multiplicative.toAdd γ k : ℤ) : ZMod p) * (v : Fin τ.rank → ZMod p) k
  map_one' := by
    ext v
    simp
  map_mul' γ δ := by
    ext v
    simp [add_mul, Finset.sum_add_distrib]

abbrev tcChiPl (τ : Tag) (p : ℕ) (P : Submodule (ZMod p) (Fin τ.rank → ZMod p)) :=
  tcChiQ τ p (P : Set (Fin τ.rank → ZMod p))

abbrev tcChiLn (τ : Tag) (p : ℕ) (x : Fin τ.rank → ZMod p) :=
  tcChiQ τ p ({x} : Set (Fin τ.rank → ZMod p))

@[expose] def tcrKindOfK : TwistKind → TcrKind
  | .inner => .inner | .suN => .suN | .twoD => .twoD | .exc => .exc

@[expose] def TcDataOK {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (Ψ : Set (Fin τ.rank → ℤ))
    (d : TcrCData) : Prop :=
  d.e = componentOrbitLength ρ Ψ ∧ d.r = compRank Ψ ∧ d.N = Ψ.ncard ∧
    tcrKindOfK (twistKindOf ρ Ψ) ∈ d.ks

@[expose] noncomputable def LabAt {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (F : ℕ)
    (Ψ : Set (Fin τ.rank → ℤ)) : LargeEvenLabel :=
  componentLabel (compRank Ψ) Ψ.ncard (twistKindOf ρ Ψ) (componentOrbitLength ρ Ψ * F)

@[expose] def FlagTransfer (p F f' : ℕ) : Prop :=
  ∀ d : TcrCData,
    ((tcrLabsOf d F).any (tcrSplitT p) = true → (tcrLabsOf d f').any (tcrSplitT p) = true) ∧
    ((tcrLabsOf d F).any (tcrHalfSplitT p) = true →
      (tcrLabsOf d f').any (tcrHalfSplitT p) = true) ∧
    ∀ d2 : TcrCData, (tcrLabsOf d2 F).any (fun l => (tcrLabsOf d F).contains l) = true →
      (tcrLabsOf d2 f').any (fun l => (tcrLabsOf d f').contains l) = true

end CFSG.StandardType.TableCRes

end
