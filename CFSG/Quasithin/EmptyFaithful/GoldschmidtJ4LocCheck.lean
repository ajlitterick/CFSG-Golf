module

public import Certificates.Certificate4174

public section

namespace CFSG.Quasithin.J4Loc

open CFSG.Sporadic.J4.QT

theorem mem_srt {x : Nat} {l : List Nat} : x ∈ srt l ↔ x ∈ l := List.mem_mergeSort


theorem subs_prop {B : List Nat} (hB : B ∈ subs) :
    (∀ c ∈ B, c < 2048) ∧ B.Pairwise (· < ·) ∧ 0 ∈ B ∧ (∀ x ∈ B, ∀ y ∈ B, x ^^^ y ∈ B) ∧
    (∀ i < 4, ∀ c ∈ B, actT (kTab i) c ∈ B ∧ actT (kInvTab i) c ∈ B) :=
  Certificates.certificate4174.1 B hB

theorem subs_zero_mem : [0] ∈ subs :=
  Certificates.certificate4174.2.1

theorem subs_chain {B : List Nat} (hB : B ∈ subs) {v : Nat}
    (hv : v < 2048) (hvB : v ∉ B) (hfix : ∀ i < 4, (actT (kTab i) v ^^^ v) ∈ B) :
    ∃ B' ∈ subs, (∀ x ∈ B, x ∈ B') ∧ v ∈ B' ∧ ∀ y ∈ B', y ∈ B ∨ ∃ x ∈ B, y = x ^^^ v :=
  Certificates.certificate4174.2.2.1 B hB v hv hvB hfix


theorem rank_ge {t : List Nat} (ht : t ∈ tabL) (hne : t ≠ idT) :
    16 ≤ ((Finset.range 2048).image (fun c => actT t c ^^^ c)).card :=
  Certificates.certificate4174.2.2.2.1 t ht hne

end CFSG.Quasithin.J4Loc
