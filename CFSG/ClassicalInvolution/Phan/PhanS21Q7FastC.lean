module

public import CFSG.ClassicalInvolution.Phan.PhanS21Q7FastA
public import CFSG.ClassicalInvolution.Phan.PhanS21Q7FastB
public import CFSG.ClassicalInvolution.Phan.PhanS21Q7Sound

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

open CFSG.ClassicalInvolution.PhanB3.S.Std


theorem nodup_flatMap_of_key {α : Type} {l : List Nat} {f : Nat → List α} {key : α → Nat}
    (hl : l.Nodup) (hf : ∀ x ∈ l, (f x).Nodup) (hk : ∀ x ∈ l, ∀ y ∈ f x, key y = x) :
    (l.flatMap f).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨hf, List.Pairwise.imp_of_mem ?_ hl⟩
  intro a b ha hb hab y h1 h2
  exact hab ((hk a ha y h1).symm.trans (hk b hb y h2))

theorem candsA_nodup (c : N7) : (candsA c).Nodup := by
  unfold candsA
  refine nodup_flatMap_of_key (key := N7.x2) List.nodup_range (fun x2 _ => ?_) ?_
  · refine nodup_flatMap_of_key (key := N7.x5) List.nodup_range (fun x5 _ => ?_) ?_
    · exact List.Nodup.map (fun a b h => congrArg N7.x6 h) List.nodup_range
    · intro x5 _ y hy
      obtain ⟨x6, _, rfl⟩ := List.mem_map.1 hy
      rfl
  · intro x2 _ y hy
    obtain ⟨x5, _, hy⟩ := List.mem_flatMap.1 hy
    obtain ⟨x6, _, rfl⟩ := List.mem_map.1 hy
    rfl

theorem candsB_nodup (c : N7) : (candsB c).Nodup := by
  unfold candsB
  refine nodup_flatMap_of_key (key := N7.x4) List.nodup_range (fun x4 _ => ?_) ?_
  · exact List.Nodup.map (fun a b h => congrArg N7.x6 h) List.nodup_range
  · intro x4 _ y hy
    obtain ⟨x6, _, rfl⟩ := List.mem_map.1 hy
    rfl

theorem candsC_nodup (c : N7) : (candsC c).Nodup := by
  unfold candsC
  exact List.Nodup.map (fun a b h => congrArg N7.x5 h) List.nodup_range

theorem mem_candsA_x1 {c y : N7} (h : y ∈ candsA c) : y.x1 = 1 := by
  simp only [candsA, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨x2, _, x5, _, x6, _, rfl⟩ := h
  rfl

theorem mem_candsB_x {c y : N7} (h : y ∈ candsB c) : y.x1 = 0 ∧ y.x2 = 1 := by
  simp only [candsB, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨x4, _, x6, _, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem mem_candsC_x {c y : N7} (h : y ∈ candsC c) : y.x1 = 0 ∧ y.x2 = 0 ∧ y.x4 = 1 := by
  simp only [candsC, List.mem_map, List.mem_range] at h
  obtain ⟨x5, _, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

theorem mem_candsD_x {c y : N7} (h : y ∈ candsD c) : y.x1 = 0 ∧ y.x2 = 0 ∧ y.x4 = 0 := by
  simp only [candsD, List.mem_singleton] at h
  subst h
  exact ⟨rfl, rfl, rfl⟩

theorem q7Cands_nodup (c : N7) : (q7Cands c).Nodup := by
  unfold q7Cands
  refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨List.nodup_append.2 ⟨candsA_nodup c,
    candsB_nodup c, ?_⟩, candsC_nodup c, ?_⟩, ?_, ?_⟩
  · intro a ha b hb hab
    have h1 := mem_candsA_x1 ha
    have h2 := (mem_candsB_x hb).1
    rw [hab] at h1
    omega
  · intro a ha b hb hab
    rcases List.mem_append.1 ha with ha | ha
    · have h1 := mem_candsA_x1 ha
      have h2 := (mem_candsC_x hb).1
      rw [hab] at h1
      omega
    · have h1 := (mem_candsB_x ha).2
      have h2 := (mem_candsC_x hb).2.1
      rw [hab] at h1
      omega
  · simp [candsD]
  · intro a ha b hb hab
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_append.1 ha with ha | ha
      · have h1 := mem_candsA_x1 ha
        have h2 := (mem_candsD_x hb).1
        rw [hab] at h1
        omega
      · have h1 := (mem_candsB_x ha).2
        have h2 := (mem_candsD_x hb).2.1
        rw [hab] at h1
        omega
    · have h1 := (mem_candsC_x ha).2.2
      have h2 := (mem_candsD_x hb).2.2
      rw [hab] at h1
      omega

theorem q7Pts_nodup (c : N7) : (q7Pts c).Nodup := (q7Cands_nodup c).filter _


end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
