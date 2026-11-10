
module

public import CFSG.Sporadic.SuzRecog.SuzL34Cert.ChecksBase
public import CFSG.Monster.B.Co2.IsInvA
public import CFSG.Sporadic.SuzRecog.C1ModelT0
public import CFSG.Sporadic.SuzRecog.ModelGroupsKit

public section

namespace CFSG.Sporadic.SuzRecog.SuzL34Cert
open CFSG.PSL3Four.Native CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0
  CFSG.ComponentClassification.PSL3Four CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native


theorem fixedCard_eq_filter (p : Equiv.Perm (Fin 1782)) :
    fixedCard p = (Finset.univ.filter fun x : Fin 1782 => p x = x).card := by
  rw [fixedCard, Nat.card_eq_fintype_card]
  exact Fintype.card_subtype _


theorem mem_set_normalizer_of_finite {G : Type*} [Group G] {S : Set G} {g : G}
    (hfin : S.Finite) (h : ∀ x ∈ S, g * x * g⁻¹ ∈ S) :
    g ∈ Subgroup.normalizer S := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · exact h x
  · intro hx
    let f : G ↪ G :=
      ⟨fun y => g * y * g⁻¹, fun a b hab => by
        have := congrArg (fun z => g⁻¹ * z * g) hab
        simpa [mul_assoc] using this⟩
    have hsub : (f '' S) ⊆ S := by
      rintro _ ⟨y, hy, rfl⟩
      exact h y hy
    have heq : f '' S = S := Set.map_eq_of_subset hsub hfin
    have hx' : f x ∈ f '' S := by rw [heq]; exact hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have : y = x := f.injective hyx
    rwa [this] at hy

private def tbarInvs : Array Tab :=
  #[#[0, 1, 5, 4, 3, 2, 6, 7, 9, 8, 12, 13, 10, 11, 15, 14],
    #[0, 1, 4, 5, 2, 3, 6, 7, 15, 14, 11, 10, 13, 12, 9, 8]]

private theorem tbarIsInvA (k : ℕ) (hk : k < 2) :
    isInvA 16 (tbarTabs[k]!) (tbarInvs[k]!) = true := by
  interval_cases k <;>
    (apply isInvA_iff.2; intro j hj; interval_cases j <;> decide)

private theorem tbSize (k : ℕ) (hk : k < 2) : (tbarTabs[k]!).size = 16 := by
  interval_cases k <;> rfl

theorem f9_tabRep_tbar (k : ℕ) (hk : k < 2) :
    TabRep (tbarTabs[k]!) (tabPerm16 (tbarTabs[k]!)) :=
  ⟨tbSize k hk, (rep_permC (tbarIsInvA k hk)).1⟩


class L1TabsClosure : Prop where
  two_pow : allBelow 4
    (fun k => (l1Tabs ())[2 ^ k]! == (decs l1Decs)[k]!) = true
  permOK : allBelow (l1Tabs ()).size
    (fun k => permOK 1782 (l1Tabs ())[k]!) = true
  has_id : anyBelow (l1Tabs ()).size
    (fun k => (l1Tabs ())[k]! == idTab 1782) = true
  mul : allBelow (l1Tabs ()).size fun i =>
    allBelow (l1Tabs ()).size fun j =>
      anyBelow (l1Tabs ()).size fun k =>
        (l1Tabs ())[k]! == comp 1782 (l1Tabs ())[i]! (l1Tabs ())[j]!
  inv : allBelow (l1Tabs ()).size fun i =>
    anyBelow (l1Tabs ()).size fun k =>
      comp 1782 (l1Tabs ())[i]! (l1Tabs ())[k]! == idTab 1782
  nodup : (l1Tabs ()).toList.Nodup
  found : allBelow (l1Tabs ()).size
    (fun k => found (indexOf (l1Tabs ())) (l1Tabs ()) (l1Tabs ())[k]!) = true

private theorem l1TabsClosure_parts :
    (allBelow 4 (fun k => (l1Tabs ())[2 ^ k]! == (decs l1Decs)[k]!) = true) ∧
      (allBelow (l1Tabs ()).size (fun k => permOK 1782 (l1Tabs ())[k]!) = true) ∧
      (anyBelow (l1Tabs ()).size (fun k => (l1Tabs ())[k]! == idTab 1782) = true) ∧
      (allBelow (l1Tabs ()).size fun i =>
        allBelow (l1Tabs ()).size fun j =>
          anyBelow (l1Tabs ()).size fun k =>
            (l1Tabs ())[k]! == comp 1782 (l1Tabs ())[i]! (l1Tabs ())[j]!) ∧
      (allBelow (l1Tabs ()).size fun i =>
        anyBelow (l1Tabs ()).size fun k =>
          comp 1782 (l1Tabs ())[i]! (l1Tabs ())[k]! == idTab 1782) ∧
      (l1Tabs ()).toList.Nodup ∧
      (allBelow (l1Tabs ()).size
        (fun k => found (indexOf (l1Tabs ())) (l1Tabs ()) (l1Tabs ())[k]!) = true) := by
  have h := l1TabsClosureCheck_holds
  simpa only [l1TabsClosureCheck, Bool.and_eq_true, and_assoc, decide_eq_true_eq] using h

instance : L1TabsClosure where
  two_pow := l1TabsClosure_parts.1
  permOK := l1TabsClosure_parts.2.1
  has_id := l1TabsClosure_parts.2.2.1
  mul := l1TabsClosure_parts.2.2.2.1
  inv := l1TabsClosure_parts.2.2.2.2.1
  nodup := l1TabsClosure_parts.2.2.2.2.2.1
  found := l1TabsClosure_parts.2.2.2.2.2.2


end CFSG.Sporadic.SuzRecog.SuzL34Cert
