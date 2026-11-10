module

public import CFSG.Sporadic.SmallOddCore.LocalSpec


public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

structure ExactEnum (n : ℕ) (H : Subgroup (Perm (Fin n))) (E : Array Table) : Prop where
  rep : ∀ k < E.size, Rep n E[k]! (tablePerm n E[k]!)
  mem : ∀ k < E.size, tablePerm n E[k]! ∈ H
  cover : ∀ x ∈ H, ∃ k < E.size, Rep n E[k]! x
  nodup : (E.toList.map (tablePerm n)).Nodup

namespace ExactEnum

variable {n : ℕ} {H : Subgroup (Perm (Fin n))} {E : Array Table}


theorem of_enumOK (hn : n < 2 ^ 32) {cap m : ℕ} {gs : List Table}
    (hg : ∀ g ∈ gs, permOK n g = true) (h : enumOK n cap m gs = true) :
    Nat.card (genOf n gs) = m ∧
      ExactEnum n (genOf n gs) (mulClosureH n gs.toArray cap).1 := by
  obtain ⟨hcard, hrep, hcov, hdist⟩ := enumOK_spec hn hg h
  refine ⟨hcard, ⟨fun k hk => (hrep k hk).1, fun k hk => (hrep k hk).2, hcov, ?_⟩⟩
  exact nodup_of_hkeysDistinct (forall₂_tablePerm fun k hk => (hrep k hk).1) hdist


end ExactEnum

end CFSG.Sporadic.Recognition.LyonsSims
