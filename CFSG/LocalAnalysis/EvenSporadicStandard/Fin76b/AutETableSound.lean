module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutECore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutETableDefs

public section

namespace CFSG.EvenSporadicStandard.Fin76b.AutETable

theorem tab_getD {n k : ℕ} (f : ℕ → ℕ) (hk : k < n) : (tab n f).getD k 0 = f k := by
  simp [tab, hk]

theorem mt_tab2 {n a b : ℕ} (mul : ℕ → ℕ → ℕ) (ha : a < n) (hb : b < n) :
    mt (tab2 n mul) a b = mul a b := by
  have : (tab2 n mul).getD a #[] = tab n (mul a) := by simp [tab2, ha]
  rw [mt, this, tab_getD _ hb]

theorem ix_tab {n k : ℕ} (f : ℕ → ℕ) (hk : k < n) : ix (tab n f) k = f k := tab_getD f hk

section ev

variable {M : Array (Array ℕ)} {n : ℕ}

theorem ev_congr {g g' : ℕ → ℕ} {w : List ℕ} (h : ∀ i ∈ w, g i = g' i) :
    ev M g w = ev M g' w := by
  unfold ev
  suffices H : ∀ acc, w.foldl (fun acc i => mt M acc (g i)) acc =
      w.foldl (fun acc i => mt M acc (g' i)) acc from H 0
  induction w with
  | nil => intro acc; rfl
  | cons i w ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [h i (List.mem_cons_self ..)]
    exact ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) _


end ev

structure Realizes (H : Type*) [Group H] (n : ℕ) (M : Array (Array ℕ)) (elt : ℕ → H) : Prop where
  pos : 0 < n
  lt : ∀ a b, a < n → b < n → mt M a b < n
  mul : ∀ a b, a < n → b < n → elt (mt M a b) = elt a * elt b
  inj : ∀ a b, a < n → b < n → elt a = elt b → a = b
  surj : ∀ h : H, ∃ a, a < n ∧ elt a = h
  one : elt 0 = 1

section sigma

variable {H : Type*} [Group H] {n : ℕ} {M : Array (Array ℕ)} {elt : ℕ → H}

open Classical in
noncomputable def sg (_R : Realizes H n M elt) (a : MulAut H) (k : ℕ) : ℕ :=
  if h : ∃ m, m < n ∧ elt m = a (elt k) then Classical.choose h else 0

theorem sg_spec (R : Realizes H n M elt) (a : MulAut H) (k : ℕ) :
    sg R a k < n ∧ elt (sg R a k) = a (elt k) := by
  have h : ∃ m, m < n ∧ elt m = a (elt k) := R.surj (a (elt k))
  have := Classical.choose_spec h
  simpa only [sg, h, ↓reduceDIte] using this

theorem sg_lt (R : Realizes H n M elt) (a : MulAut H) (k : ℕ) : sg R a k < n :=
  (sg_spec R a k).1

theorem sg_elt (R : Realizes H n M elt) (a : MulAut H) (k : ℕ) :
    elt (sg R a k) = a (elt k) :=
  (sg_spec R a k).2

theorem sg_mt (R : Realizes H n M elt) (a : MulAut H) {k l : ℕ} (hk : k < n) (hl : l < n) :
    sg R a (mt M k l) = mt M (sg R a k) (sg R a l) := by
  apply R.inj _ _ (sg_lt R a _) (R.lt _ _ (sg_lt R a _) (sg_lt R a _))
  rw [sg_elt R a, R.mul _ _ hk hl, map_mul, R.mul _ _ (sg_lt R a _) (sg_lt R a _),
    sg_elt R a, sg_elt R a]

theorem sg_zero (R : Realizes H n M elt) (a : MulAut H) : sg R a 0 = 0 := by
  apply R.inj _ _ (sg_lt R a _) R.pos
  rw [sg_elt R a, R.one, map_one]


theorem sg_mul (R : Realizes H n M elt) (a b : MulAut H) (k : ℕ) :
    sg R (a * b) k = sg R a (sg R b k) := by
  apply R.inj _ _ (sg_lt R _ _) (sg_lt R _ _)
  rw [sg_elt R _ _, sg_elt R _ _, sg_elt R _ _]
  rfl

theorem sg_one (R : Realizes H n M elt) {k : ℕ} (hk : k < n) : sg R (1 : MulAut H) k = k := by
  apply R.inj _ _ (sg_lt R _ _) hk
  rw [sg_elt R _ _]
  rfl

end sigma

section complete


end complete
end CFSG.EvenSporadicStandard.Fin76b.AutETable
