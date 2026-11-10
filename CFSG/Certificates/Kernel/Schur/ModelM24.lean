module

public import CFSG.Certificates.Kernel.McL.Model
public import CFSG.Certificates.Kernel.McL.RangeX
public import CFSG.Certificates.Kernel.Schur.Pack
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KC.Schur.M24

@[expose] def M0 : Nat := nat_lit 6736755261288091546128960264285268478067075
@[expose] def M1 : Nat := nat_lit 6736755261288091546128960264285268478067075
@[expose] def M2 : Nat := nat_lit 7765686648183738834401240450036853835597059
@[expose] def M3 : Nat := nat_lit 6399096711543196369546030405101881909109573
#kc_select CFSG.KC.Schur.M24 MG M 4
@[expose] def R0 : Nat := nat_lit 8
@[expose] def R1 : Nat := nat_lit 538976268
@[expose] def R2 : Nat := nat_lit 19239554410385646369007847458680028103495104244371622695877704874278829582481280835664248419261727328996903878840
@[expose] def R3 : Nat := nat_lit 1260893095046136334935276973050772614330815558475180333808555427999657440158504333716903634594949724779217578886172864
@[expose] def R4 : Nat := nat_lit 68352628135791968671869327766455099795025176394078555879763106250048646768019109126946991887093920
@[expose] def R5 : Nat := nat_lit 23871879601792482813206463530518016013799245762050755265074927120534062361147440459939984
@[expose] def R6 : Nat := nat_lit 34888613676033116589051557917617139885789525442668103056043064937140637936145471548441166418043253782599708151083957106741049346876244192
#kc_select CFSG.KC.Schur.M24 REL R 7
@[expose] def ED4 : Nat := nat_lit 49
#kc_select CFSG.KC.Schur.M24 EP EP 163
#kc_select CFSG.KC.Schur.M24 ED ED 163
@[expose] def BP : Nat := nat_lit 417753473088
@[expose] def OJ0 : Nat := nat_lit 3389215278611547699133847600801352312075978813457478336922086186721001619150175331461120356422550638991305284741528289280
@[expose] def OJ1 : Nat := nat_lit 1074940077419248885425802400291786702569909750010735349893903290488319493703810418766485549622906583949596335777253056
@[expose] def OJ2 : Nat := nat_lit 8302131984756535411737474914349688749935271004215392785521761806588242145146663393935007395184614935466277342656
@[expose] def OJ3 : Nat := nat_lit 47160262554655946373624778721673752232686271934228750668477163442918623334890365467627200704440965116466304
@[expose] def OJ4 : Nat := nat_lit 243230110222592198202037837479042713286817422125705225676495562080790287456375692344930383288451734464
@[expose] def OJ5 : Nat := nat_lit 65364890733909125863166731141594288172509508135300285547520224197358263770030784
@[expose] def OJ6 : Nat := nat_lit 2701404224

theorem gens : McL.Sub.gensOK MG (nat_lit 24) (nat_lit 2) = true := by quickRfl
theorem rels : McL.Sub.relsHold MG REL (nat_lit 24) (nat_lit 7) = true := by quickRfl
theorem rels_letters : McL.RangeX.entsBelow REL (nat_lit 7) (nat_lit 4) = true := by quickRfl
theorem ents : McL.Model.elemsOK MG EP ED (nat_lit 24) (nat_lit 2) BP (nat_lit 163) = true := by quickRfl
theorem ep_wrap : McL.RangeX.epWrap EP ED (nat_lit 163) (nat_lit 256) = true := by quickRfl
theorem orb0 : Nat.beq (McL.Model.orbCount (McL.Model.orbitRun EP ED BP (nat_lit 0) (nat_lit 23) OJ0)) (nat_lit 24) = true := by quickRfl
theorem bp0 : Nat.blt (McL.Model.bpt BP (nat_lit 0)) (nat_lit 24) = true := by quickRfl
theorem orb1 : Nat.beq (McL.Model.orbCount (McL.Model.orbitRun EP ED BP (nat_lit 1) (nat_lit 22) OJ1)) (nat_lit 23) = true := by quickRfl
theorem bp1 : Nat.blt (McL.Model.bpt BP (nat_lit 1)) (nat_lit 24) = true := by quickRfl
theorem orb2 : Nat.beq (McL.Model.orbCount (McL.Model.orbitRun EP ED BP (nat_lit 2) (nat_lit 21) OJ2)) (nat_lit 22) = true := by quickRfl
theorem bp2 : Nat.blt (McL.Model.bpt BP (nat_lit 2)) (nat_lit 24) = true := by quickRfl
theorem orb3 : Nat.beq (McL.Model.orbCount (McL.Model.orbitRun EP ED BP (nat_lit 3) (nat_lit 20) OJ3)) (nat_lit 21) = true := by quickRfl
theorem bp3 : Nat.blt (McL.Model.bpt BP (nat_lit 3)) (nat_lit 24) = true := by quickRfl
theorem orb4 : Nat.beq (McL.Model.orbCount (McL.Model.orbitRun EP ED BP (nat_lit 4) (nat_lit 19) OJ4)) (nat_lit 20) = true := by quickRfl
theorem bp4 : Nat.blt (McL.Model.bpt BP (nat_lit 4)) (nat_lit 24) = true := by quickRfl
theorem orb5 : Nat.beq (McL.Model.orbCount (McL.Model.orbitRun EP ED BP (nat_lit 5) (nat_lit 15) OJ5)) (nat_lit 16) = true := by quickRfl
theorem bp5 : Nat.blt (McL.Model.bpt BP (nat_lit 5)) (nat_lit 24) = true := by quickRfl
theorem orb6 : Nat.beq (McL.Model.orbCount (McL.Model.orbitRun EP ED BP (nat_lit 6) (nat_lit 2) OJ6)) (nat_lit 3) = true := by quickRfl
theorem bp6 : Nat.blt (McL.Model.bpt BP (nat_lit 6)) (nat_lit 24) = true := by quickRfl

end CFSG.KC.Schur.M24

end
