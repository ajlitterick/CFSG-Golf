module

public import CFSG.Quasithin.AppendixH.H14.H142Bfs

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Monster.Code
open scoped Pointwise

@[expose] def stdB : Finset (Fin 24) := {8, 11, 14, 20}

@[expose] def stdB' : Finset (Fin 24) := {13, 17, 18, 23}

@[expose] def stdO : Finset (Fin 24) := stdB ∪ stdB'


@[expose] def stdH : Finset (Fin 24) := stdO.erase 8


theorem stdO_eq : stdO = maskSetOf 9857280 := by
  decide


theorem smul_stdH_of_arr {g : S24} {a : Array ℕ} (hg : HasArr g a) (h8 : a[8]! = 8)
    (ho : permM a 9857280 = 9857280) : g • stdH = stdH := by
  have hg8 : g 8 = 8 := by
    apply Fin.ext
    exact (hg 8).trans h8
  have hstdO : g • stdO = stdO := by
    rw [stdO_eq, smul_maskSetOf hg, ho]
  have herase : g • (stdO.erase 8) = (g • stdO).erase (g 8) := by
    ext y
    simp only [Finset.mem_smul_finset, Finset.mem_erase]
    constructor
    · rintro ⟨x, ⟨hx8, hxO⟩, rfl⟩
      exact ⟨fun h => hx8 (g.injective (by simpa [Equiv.Perm.smul_def] using h)),
        ⟨x, hxO, rfl⟩⟩
    · rintro ⟨hne, ⟨x, hxO, rfl⟩⟩
      exact ⟨x, ⟨fun hx8 => hne (by rw [hx8, Equiv.Perm.smul_def]), hxO⟩, rfl⟩
  simp only [stdH]
  rw [herase, hstdO, hg8]


end CFSG.Quasithin.AppendixH.H14
