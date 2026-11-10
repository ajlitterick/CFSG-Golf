module

public import CFSG.YGroups.DCE.B433Rules
public import CFSG.YGroups.DCE.OmegaBigSpec
public import Certificates.Data.CFSGNative.YGroups.DCE.B433Data
public meta import Certificates.Data.CFSGNative.YGroups.DCE.B433Data
public import Certificates.Certificate10093
public import Certificates.Certificate10095
public import Certificates.Certificate10098
public import Certificates.Certificate10100
public import Certificates.Certificate10101
public import Certificates.Certificate10102
public import Certificates.Certificate10103
public import CFSG.YGroups.Model233F

public section

namespace CFSG.YGroups.DCE.B433

open CFSG.YGroups.DCE.B433Native Pointwise
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

theorem lettersB_eq : lettersB () = y432FArrays.map (bofArr 31671) := rfl

theorem lettersB_size : (lettersB ()).size = 10 := by
  rw [lettersB_eq, Array.size_map]
  exact y432F_check.1

theorem lettersB_rep {l : ℕ} (hl : l < 10) :
    RepB 31671 (lettersB ())[l]! (rho432F (yGen 4 3 2 l)) := by
  have hl' : l < y432FArrays.size := by rw [y432F_check.1]; exact hl
  rw [lettersB_eq, BigOmega.getElem!_map_lt hl']
  exact repB_bofArr (by norm_num) (rho432F_rep hl)

theorem wordB_rep {L : Array ByteArray}
    (hL : ∀ l < 10, RepB 31671 L[l]! (rho432F (yGen 4 3 2 l))) (w : Array ℕ)
    (hw : ∀ l ∈ w, l < 10) :
    RepB 31671 (wordB L w) (rho432F (evalWord (yGen 4 3 2) w.toList)) := by
  have hw' : ∀ l ∈ w.toList, l < 10 := fun l hl => hw l (Array.mem_toList_iff.1 hl)
  unfold wordB
  rw [← Array.foldr_toList]
  generalize w.toList = ws at hw' ⊢
  induction ws with
  | nil =>
    simp only [List.foldr_nil, evalWord_nil, map_one]
    exact repB_bid (by norm_num)
  | cons a ws ih =>
    simp only [List.foldr_cons, evalWord_cons, map_mul]
    exact repB_bcomp (by norm_num) (hL a (hw' a List.mem_cons_self))
      (ih fun l hl => hw' l (List.mem_cons_of_mem _ hl))

private theorem foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) (init : β) (h0 : P init)
    (hf : ∀ b a, P b → P (f b a)) : ∀ l : List α, P (l.foldl f init) := by
  intro l
  induction l generalizing init with
  | nil => exact h0
  | cons a l ih => exact ih (f init a) (hf init a h0)

private theorem inner_lt (sm : UInt64 → UInt64 × UInt64) (s : UInt64) (k : ℕ) :
    ∀ l ∈ (List.foldl (fun b _ => ((sm b.1).1, #[((sm b.1).2 % 10).toNat] ++ b.2))
      (s, (#[] : Array ℕ)) (List.range' 0 k)).2, l < 10 := by
  refine foldl_inv (fun st : UInt64 × Array ℕ => ∀ l ∈ st.2, l < 10) _ _
    (by intro l hl; simp at hl) (fun b _ hb => ?_) _
  intro l hl
  simp only [Array.mem_append, Array.mem_singleton] at hl
  rcases hl with rfl | hl
  · rw [UInt64.toNat_mod]
    exact Nat.mod_lt _ (by decide)
  · exact hb l hl

theorem treeWords_lt : ∀ w ∈ treeWords, ∀ l ∈ w, l < 10 := by
  unfold treeWords
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure]
  generalize splitmix = sm
  generalize (987654321 : UInt64) = s0
  refine foldl_inv (fun st : UInt64 × Array (Array ℕ) => ∀ w ∈ st.2, ∀ l ∈ w, l < 10) _ _
    (by intro w hw; simp at hw) (fun b _ hb => ?_) _
  intro w hw
  simp only [Array.mem_push] at hw
  rcases hw with hw | hw
  · exact hb w hw
  · rw [hw]
    exact inner_lt sm b.1 _

theorem treeGens_rep
    {L : Array ByteArray}
    (hL : ∀ l < 10, RepB 31671 L[l]! (rho432F (yGen 4 3 2 l))) (hsz : L.size = 10) :
    ∀ l < (treeGens L).size, ∃ e : YGroup 4 3 2, RepB 31671 (treeGens L)[l]! (rho432F e) := by
  intro l hl
  unfold treeGens at hl ⊢
  rw [Array.size_append, Array.size_map] at hl
  by_cases hlL : l < L.size
  · refine ⟨yGen 4 3 2 l, ?_⟩
    have e : (L ++ Array.map (wordB L) treeWords)[l]! = L[l]! := by
      rw [getElem!_pos (L ++ Array.map (wordB L) treeWords) l (by simpa using hl),
        Array.getElem_append_left hlL, getElem!_pos L l hlL]
    rw [e]
    exact hL l (by omega)
  · have hk : l - L.size < treeWords.size := by omega
    have e : (L ++ Array.map (wordB L) treeWords)[l]! = wordB L treeWords[l - L.size]! := by
      rw [getElem!_pos (L ++ Array.map (wordB L) treeWords) l (by simpa using hl),
        Array.getElem_append_right (by omega), Array.getElem_map, getElem!_pos treeWords _ hk]
    rw [e]
    exact ⟨_, wordB_rep hL _ (treeWords_lt _ (by
      rw [getElem!_pos treeWords _ hk]
      exact Array.getElem_mem hk))⟩


structure Checked (L : Array ByteArray) (O : BigOmega) (cert : B.Cert) : Prop where
  hL : L = lettersB ()
  hO : O = omegaB433 L
  big : bigOK O L fixB = true
  small : smallOK O L cert = true

namespace Checked

variable {L : Array ByteArray} {O : BigOmega} {cert : B.Cert} (S : Checked L O cert)

include S

theorem letters_rep
    {l : ℕ} (hl : l < 10) : RepB 31671 L[l]! (rho432F (yGen 4 3 2 l)) := by
  rw [S.hL]
  exact lettersB_rep hl

theorem letters_size : L.size = 10 := by
  rw [S.hL]
  exact lettersB_size

theorem n_eq : O.n = 31671 := by
  rw [S.hO]
  rfl

theorem X0_eq : O.X0 = x0B := by
  rw [S.hO]
  rfl

theorem tg_eq : O.tg = treeGens L := by
  rw [S.hO]
  rfl

theorem small_spec : L.size = 10 ∧ O.N = 86316516 ∧
    bisInv deg (gB L) (binvCand deg (gB L)) = true ∧
    ∀ j < cert.words.size, j = 0 ∨ cert.words[j]!.1 < j := by
  have h := S.small
  unfold smallOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun j hj => ?_⟩
  have := CFSG.Monster.B.Co2.allLt_iff.1 h4 j hj
  simpa using this

theorem N_eq : O.N = 86316516 := S.small_spec.2.1

theorem exists_g :
    ∃ g : ℕ → Equiv.Perm (Fin 31671),
    ∀ l < O.tg.size, g l ∈ rho432F.range ∧ RepB 31671 O.tg[l]! (g l) := by
  have H : ∀ l < O.tg.size, ∃ γ ∈ rho432F.range, RepB 31671 O.tg[l]! γ := by
    intro l hl
    rw [S.tg_eq] at hl ⊢
    obtain ⟨e, he⟩ := treeGens_rep (fun l hl => S.letters_rep hl) S.letters_size l hl
    exact ⟨rho432F e, ⟨e, rfl⟩, he⟩
  choose! g hg using H
  exact ⟨g, fun l hl => ⟨(hg l hl).1, (hg l hl).2⟩⟩

theorem rowMem
    {p : ℕ} (hp : p < O.N) :
    BigOmega.rowFinset 31671 O p ∈ MulAction.orbit (YGroup 4 3 2) (listFinset 31671 x0B) := by
  obtain ⟨g, hg⟩ := S.exists_g
  have h1 := BigOmega.rowFinset_mem_orbit rho432F.range g hg S.big S.n_eq p hp
  rw [S.X0_eq] at h1
  rwa [orbit_eq]

theorem good :
    Good x0B := by
  obtain ⟨g, hg⟩ := S.exists_g
  refine ⟨fun l hl => ?_, ?_⟩
  · have hu : ∀ l < L.size, rho432F (yGen 4 3 2 l) ∈ rho432F.range ∧
        RepB 31671 L[l]! (rho432F (yGen 4 3 2 l)) :=
      fun l hl' => ⟨⟨_, rfl⟩, S.letters_rep (by rwa [S.letters_size] at hl')⟩
    have h := BigOmega.fix_smul_listFinset (O := O) rho432F.range
      (fun l => rho432F (yGen 4 3 2 l)) hu S.big l (by simp only [fixB, List.mem_cons]; omega)
    rw [S.X0_eq] at h
    exact h
  · have h := BigOmega.card_orbit_ge rho432F.range g hg S.big S.n_eq
    rw [S.X0_eq, ← orbit_eq, S.N_eq] at h
    exact h

theorem hcard :
    (MulAction.orbit rho432F.range (listFinset 31671 O.X0)).ncard ≤ O.N := by
  rw [S.X0_eq, ← orbit_eq, S.N_eq]
  exact ncard_orbit_le S.good

@[expose] def pt :
    ℕ → Pts x0B := fun p =>
  if hp : p < O.N then ⟨BigOmega.rowFinset 31671 O p, S.rowMem hp⟩ else basePt x0B

theorem pt_zero :
    S.pt 0 = basePt x0B := by
  have h0 : 0 < O.N := by rw [S.N_eq]; norm_num
  unfold pt
  rw [dite_eq_left h0]
  apply Subtype.ext
  show BigOmega.rowFinset 31671 O 0 = listFinset 31671 x0B
  rw [BigOmega.rowFinset_zero S.big, S.X0_eq]


end Checked


end CFSG.YGroups.DCE.B433
