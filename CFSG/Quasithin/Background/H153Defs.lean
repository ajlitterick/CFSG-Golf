module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.AppendixH.H14.Vocab
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open scoped Pointwise

namespace CFSG.Quasithin.H153

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Open


@[expose] def IsO23' (G N : Subgroup S24) : Prop :=
  N ≤ G ∧ (∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N) ∧ pCoreOf 2 G ≤ N ∧
    (∀ n ∈ N, ∃ k : ℕ, n ^ (3 ^ k) ∈ pCoreOf 2 G) ∧
    ∀ N' : Subgroup S24, N' ≤ G → (∀ g ∈ G, ∀ n ∈ N', g * n * g⁻¹ ∈ N') → pCoreOf 2 G ≤ N' →
      (∀ n ∈ N', ∃ k : ℕ, n ^ (3 ^ k) ∈ pCoreOf 2 G) → N' ≤ N


end CFSG.Quasithin.H153
