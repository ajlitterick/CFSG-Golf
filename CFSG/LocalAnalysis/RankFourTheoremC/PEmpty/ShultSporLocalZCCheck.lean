module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZCDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

class ZCKey (A : Type) where
  key : A → ℕ

instance (priority := low) zcKeyDefault (A : Type) : ZCKey A := ⟨fun _ => 0⟩

@[expose] def zcPermKey {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  ((List.ofFn (fun i => σ i)).take 6).foldl (fun h i => h * n + i.val) 0

instance zcKeyPerm (n : ℕ) : ZCKey (Equiv.Perm (Fin n)) := ⟨zcPermKey⟩

section Bfs


end Bfs

section Words


end Words

section Check


end Check

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
