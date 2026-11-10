module

public import Certificates.Data.CFSGNative.MonsterB.Primes
public import CFSG.Monster.B.Pinned.Primes.Extraspecial
public import CFSG.Monster.B.Pinned.Primes.Data
public import CFSG.Monster.B.Intertwiner.ArithSpec
public import CFSG.Monster.B.Max2.Prog
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Monster.B.Pinned

open Bin Primes.Native

section Programs

variable {G : Type*} [Group G]

@[expose] def insStepG (r : ℕ → G) : Ins → ℕ → G
  | .mu i j k => Function.update r k (r i * r j)
  | .iv i k => Function.update r k (r i)⁻¹
  | .pwr e i k => Function.update r k (r i ^ e)

@[expose] def runG (prog : List Ins) (a b : G) : ℕ → G := prog.foldl insStepG (progInit a b)

theorem map_insStepG {H : Type*} [Group H] (f : G →* H) (r : ℕ → G) (ins : Ins) :
    (fun i => f (insStepG r ins i)) = insStepG (fun i => f (r i)) ins := by
  funext i
  cases ins with
  | mu a b k =>
    simp only [insStepG]
    by_cases h : i = k
    · subst h; simp
    · simp [Function.update_of_ne h]
  | iv a k =>
    simp only [insStepG]
    by_cases h : i = k
    · subst h; simp
    · simp [Function.update_of_ne h]
  | pwr e a k =>
    simp only [insStepG]
    by_cases h : i = k
    · subst h; simp
    · simp [Function.update_of_ne h]

theorem map_foldl_insStepG {H : Type*} [Group H] (f : G →* H) :
    ∀ (l : List Ins) (r : ℕ → G) (k : ℕ),
      f (l.foldl insStepG r k) = l.foldl insStepG (fun i => f (r i)) k
  | [], r, k => rfl
  | ins :: l, r, k => by
    rw [List.foldl_cons, List.foldl_cons, map_foldl_insStepG f l, map_insStepG]

theorem map_runG {H : Type*} [Group H] (f : G →* H) (prog : List Ins) (a b : G) (k : ℕ) :
    f (runG prog a b k) = runG prog (f a) (f b) k := by
  unfold runG
  rw [map_foldl_insStepG]
  have e : (fun i => f (progInit a b i)) = progInit (f a) (f b) := by
    funext i
    unfold progInit
    split_ifs <;> simp
  rw [e]

@[expose] def insReads : Ins → List ℕ
  | .mu i j _ => [i, j]
  | .iv i _ => [i]
  | .pwr _ i _ => [i]

@[expose] def insOut : Ins → ℕ
  | .mu _ _ k => k
  | .iv _ k => k
  | .pwr _ _ k => k

@[expose] def initOK : List Ins → List ℕ → Bool
  | [], _ => true
  | ins :: l, S => (insReads ins).all (S.contains ·) && initOK l (insOut ins :: S)

theorem insStepG_congr {r r' : ℕ → G} {S : List ℕ} {ins : Ins}
    (hread : (insReads ins).all (S.contains ·) = true) (h : ∀ i ∈ S, r i = r' i) :
    ∀ i ∈ insOut ins :: S, insStepG r ins i = insStepG r' ins i := by
  have hr : ∀ i ∈ insReads ins, r i = r' i := fun i hi =>
    h i (by simpa using List.all_eq_true.1 hread i hi)
  intro i hi
  cases ins with
  | mu a b k =>
    simp only [insStepG]
    by_cases e : i = k
    · subst e
      rw [Function.update_self, Function.update_self, hr a (by simp [insReads]),
        hr b (by simp [insReads])]
    · rw [Function.update_of_ne e, Function.update_of_ne e]
      exact h i (by simpa [insOut, e] using hi)
  | iv a k =>
    simp only [insStepG]
    by_cases e : i = k
    · subst e
      rw [Function.update_self, Function.update_self, hr a (by simp [insReads])]
    · rw [Function.update_of_ne e, Function.update_of_ne e]
      exact h i (by simpa [insOut, e] using hi)
  | pwr d a k =>
    simp only [insStepG]
    by_cases e : i = k
    · subst e
      rw [Function.update_self, Function.update_self, hr a (by simp [insReads])]
    · rw [Function.update_of_ne e, Function.update_of_ne e]
      exact h i (by simpa [insOut, e] using hi)

theorem foldl_insStepG_congr :
    ∀ (l : List Ins) (S : List ℕ) (r r' : ℕ → G), initOK l S = true → (∀ i ∈ S, r i = r' i) →
      ∀ k ∈ S, l.foldl insStepG r k = l.foldl insStepG r' k
  | [], _, _, _, _, h => h
  | ins :: l, S, r, r', hok, h => by
    simp only [initOK, Bool.and_eq_true] at hok
    intro k hk
    rw [List.foldl_cons, List.foldl_cons]
    exact foldl_insStepG_congr l (insOut ins :: S) _ _ hok.2 (insStepG_congr hok.1 h) k
      (List.mem_cons_of_mem _ hk)

theorem runG_of_initOK {prog : List Ins} (hok : initOK prog [1, 2] = true) {a b : G}
    (r : ℕ → G) (h1 : r 1 = a) (h2 : r 2 = b) :
    prog.foldl insStepG r 1 = runG prog a b 1 ∧ prog.foldl insStepG r 2 = runG prog a b 2 := by
  have h : ∀ i ∈ [1, 2], r i = progInit a b i := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · rw [h1]; rfl
    · rw [h2]; rfl
  exact ⟨foldl_insStepG_congr prog [1, 2] r _ hok h 1 (by simp),
    foldl_insStepG_congr prog [1, 2] r _ hok h 2 (by simp)⟩

end Programs

@[expose] def wordG {M : Type*} [Monoid M] (a b : M) (w : List Char) : M :=
  (w.map fun c => if c = 'a' then a else if c = 'b' then b else 1).prod

theorem wordG_append {M : Type*} [Monoid M] (a b : M) (v w : List Char) :
    wordG a b (v ++ w) = wordG a b v * wordG a b w := by
  simp [wordG, List.prod_append]


section RepMonoid

variable {M : Type*} [Monoid M] {n : ℕ} (f : M →* Matrix (Fin n) (Fin n) (ZMod 2))

@[expose] def Rep (X : Mat) (g : M) : Prop := X.size ≤ n ∧ cmat n X = f g

variable {f}

theorem Rep.of_eq {X : Mat} {g g' : M} (h : Rep f X g) (e : g = g') : Rep f X g' := e ▸ h

theorem rep_mul {X Y : Mat} {g h : M} (hX : Rep f X g) (hY : Rep f Y h) :
    Rep f (mulP n X Y) (g * h) :=
  ⟨by rw [mulP_size]; exact hX.1, by rw [cmat_mulP _ _ _ hY.1, hX.2, hY.2, map_mul]⟩

theorem rep_pow {X : Mat} {g : M} (hX : Rep f X g) (e : ℕ) : Rep f (powM n X e) (g ^ e) :=
  ⟨powM_size hX.1 e, by rw [cmat_powM hX.1, hX.2, map_pow]⟩

theorem rep_one : Rep f (idMat n) (1 : M) := ⟨(idMat_size n).le, by rw [cmat_idMat, map_one]⟩

theorem eq_of_rep (hf : Function.Injective f) {X Y : Mat} {g h : M} (hX : Rep f X g)
    (hY : Rep f Y h) (he : (X == Y) = true) : g = h :=
  hf (hX.2.symm.trans ((cmat_eq_of_beq he).trans hY.2))

theorem ne_one_of_rep {X : Mat} {g : M} (hX : Rep f X g) (h : neM n X (idMat n) = true) :
    g ≠ 1 := by
  intro hg
  apply cmat_ne_of_neM h
  rw [hX.2, hg, map_one, cmat_idMat]


theorem ordOK_spec (hf : Function.Injective f) {p : ℕ} {X : Mat} {g : M} (hX : Rep f X g)
    (h : ordOK n p X = true) : g ^ p = 1 ∧ g ≠ 1 := by
  simp only [ordOK, Bool.and_eq_true] at h
  exact ⟨eq_of_rep hf (rep_pow hX p) rep_one h.1, ne_one_of_rep hX h.2⟩


theorem orderOf_eq_of_exact {g : M} {e : ℕ} {rs : List ℕ} (he : 0 < e) (h1 : g ^ e = 1)
    (h2 : ∀ r ∈ rs, g ^ (e / r) ≠ 1) (hcov : ∀ r ≤ e, r.Prime → r ∣ e → r ∈ rs) :
    orderOf g = e :=
  orderOf_eq_of_pow_and_pow_div_prime he h1 fun r hr hre =>
    h2 r (hcov r (Nat.le_of_dvd he hre) hr hre)


end RepMonoid

section RepGroup

variable {G : Type*} [Group G] {n : ℕ} {f : G →* Matrix (Fin n) (Fin n) (ZMod 2)}


end RepGroup

theorem rowsMat_val {p k : ℕ} [NeZero p] {Mr : List (List ℕ)} {i j : Fin k}
    (h : (Mr.getD i []).getD j 0 < p) : (rowsMat p k Mr i j).val = (Mr.getD i []).getD j 0 := by
  rw [rowsMat, Matrix.of_apply, ZMod.val_natCast, Nat.mod_eq_of_lt h]

theorem bcomm_all {G : Type*} [Group G] {p k : ℕ} [NeZero p] {q : Fin k → G} {z : G}
    (hz : z ^ p = 1)
    {Mr : List (List ℕ)} (hlt : ∀ i j : Fin k, (Mr.getD i []).getD j 0 < p)
    (hdiag : ∀ i : Fin k, (Mr.getD i []).getD i 0 = 0)
    (hanti : ∀ i j : Fin k, ((Mr.getD i []).getD j 0 + (Mr.getD j []).getD i 0) % p = 0)
    (h : ∀ i j : Fin k, i < j → bcomm (q i) (q j) = z ^ ((Mr.getD i []).getD j 0)) :
    ∀ i j, bcomm (q i) (q j) = z ^ (rowsMat p k Mr i j).val := by
  intro i j
  rw [rowsMat_val (hlt i j)]
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact h i j hij
  · rw [hdiag, pow_zero, bcomm_eq_one_iff]
  · rw [bcomm_swap (q j) (q i), h j i hij, eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_add]
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero (hanti i j)
    rw [ht, pow_mul, hz, one_pow]

end CFSG.Monster.B.Pinned
