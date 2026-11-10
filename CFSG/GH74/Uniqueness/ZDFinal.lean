module

public import CFSG.GH74.Uniqueness.Section17Lemma311
public import CFSG.GH74.Uniqueness.Section122
public import CFSG.GH74.Uniqueness.Section127
public import CFSG.GH74.Uniqueness.Section128
public import CFSG.GH74.Uniqueness.Section129
public import CFSG.GH74.Uniqueness.Section1210
public import CFSG.GH74.Uniqueness.Section1213
public import CFSG.GH74.Uniqueness.Section131
public import CFSG.GH74.Uniqueness.Section14Facts
public import CFSG.GH74.Uniqueness.Section14Final
public import CFSG.GH74.Uniqueness.Section14Lem47
public import CFSG.GH74.Uniqueness.Section14Lem48
public import CFSG.GH74.Uniqueness.Section14Weak149
public import CFSG.GH74.Uniqueness.Section14FrobRank
public import CFSG.GH74.Uniqueness.Section14Frob149
public import CFSG.GH74.Uniqueness.Section14ZStar
public import CFSG.GH74.Uniqueness.Section14Lem46c
public import CFSG.GH74.Uniqueness.Section15
public import CFSG.GH74.Uniqueness.Section15Hering
public import CFSG.GH74.Uniqueness.Section162
public import CFSG.GH74.Uniqueness.Section164
public import CFSG.GH74.Uniqueness.Section165
public import CFSG.GH74.Uniqueness.Section166
public import CFSG.GH74.Uniqueness.Section167
public import CFSG.GH74.Uniqueness.Section171
public import CFSG.GH74.Uniqueness.Section172
public import CFSG.GH74.Uniqueness.Section173
public import CFSG.GH74.Uniqueness.Section174
public import CFSG.GH74.Uniqueness.Section175
public import CFSG.GH74.Uniqueness.Section176
public import CFSG.GH74.Uniqueness.Section126Count

public section

namespace CFSG.GH74.Uniqueness

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.prop141
    (S : ZDSetup X Z M) (h12 : Sec12Results Z M) (h131 : Prop131Stmt Z M) :
    Prop141Stmt Z M := by
  intro c n h
  obtain ⟨r, Q, U, S2, F⟩ := Sec14.exists_facts14 S h12 h131 c h
  have h146 := lemma146 F
  have h147 := lemma147 F h146
  have h148 := lemma148 F h146 h147
  exact Sec14F.false_of_lemmas F h146
    (lemma149 F h146 h147 h148 (weak149 (frob149 frobRank))) zstar14


end CFSG.GH74.Uniqueness
