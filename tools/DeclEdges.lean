/-
Dump the constant reference graph of the modules built so far.

    lake env lean --run tools/DeclEdges.lean <buildLibDir> <out.tsv>

Output:
    C <tab> <key> <tab> <module> <tab> <constant name>     every constant of a scanned module
    E <tab> <key> <tab> <key of a constant it mentions>     (type and value / proof)
Keys are 62-bit name hashes.  Used by tools/check_dead_against_oleans.py to test the
source-level dead-code list against what compiled terms really reference.
-/
import Lean
open Lean
/-- 62-bit key of a name (unboxed `Nat`), from the 64-bit name hash. -/
@[inline] def key (n : Name) : Nat := (hash n).toNat % (2 ^ 62)

structure St where
  deps   : Std.HashMap Nat (Array Nat) := {}
  modOf  : Std.HashMap Nat Nat := {}
  mods   : Array String := #[]
  names  : Array (Array (Nat × String)) := #[]   -- per module: (key, name)
  noValue : Nat := 0   -- theorems whose proof is literally `sorryAx` (sanity check)

def usedIn (ci : ConstantInfo) : Array Name :=
  let a := ci.type.getUsedConstants
  match ci with
  | .thmInfo v   => a ++ v.value.getUsedConstants
  | .defnInfo v  => a ++ v.value.getUsedConstants
  | .opaqueInfo v => a ++ v.value.getUsedConstants
  | .recInfo v   => v.rules.foldl (fun acc r => acc ++ r.rhs.getUsedConstants) a
  | .inductInfo v => a ++ (v.ctors.toArray)
  | .ctorInfo v  => a.push v.induct
  | _ => a

unsafe def freeRegionUnsafe (r : CompactedRegion) : IO Unit := r.free
@[implemented_by freeRegionUnsafe] def freeRegion (_ : CompactedRegion) : IO Unit := pure ()

def scanData (st : St) (modIdx : Nat) (md : ModuleData) : St := Id.run do
  let mut st := st
  let mut arr := st.names[modIdx]!
  for ci in md.constants do
    let n := ci.name
    let k := key n
    if st.modOf.contains k then continue
    let ds := usedIn ci
    -- copy out of the compacted region: keys are scalars, names become fresh strings
    let mut dk : Array Nat := Array.mkEmpty ds.size
    for d in ds do
      let kd := key d
      if kd != k then dk := dk.push kd
    if let .thmInfo v := ci then
      if v.value.isConstOf ``sorryAx then st := { st with noValue := st.noValue + 1 }
    st := { st with deps := st.deps.insert k dk, modOf := st.modOf.insert k modIdx }
    -- `toString` of a one-component name can return the string stored in the compacted
    -- region; `push` forces a fresh copy that survives freeing the region (the trailing
    -- space is stripped by the readers)
    arr := arr.push (k, (toString n).push ' ')
  return { st with names := st.names.set! modIdx arr }

/-- Load the parts, scan them, and return only scalar data (the regions) so that every
reference into the compacted regions is dropped before the caller frees them. -/
def loadAndScan (st : St) (modIdx : Nat) (parts : Array System.FilePath) :
    IO (St × Array CompactedRegion) := do
  let loaded ← readModuleDataParts parts
  let mut st := st
  -- private part first: it carries proofs; the exported copy of a constant is then skipped
  for part in loaded.reverse do
    st := scanData st modIdx part.1
  return (st, loaded.map (·.2))

/-- Load `.olean`, `.olean.server`, `.olean.private` (whichever exist, in that order: later
parts share objects with earlier ones), scan all constants, then free the regions. -/
def scanModule (st : St) (modIdx : Nat) (olean : System.FilePath) : IO St := do
  let mut parts : Array System.FilePath := #[olean]
  for ext in ["server", "private"] do
    let f := olean.addExtension ext
    if ← f.pathExists then parts := parts.push f
  let (st, regions) ← loadAndScan st modIdx parts
  for r in regions.reverse do
    freeRegion r
  return st

partial def walkDir (dir : System.FilePath) (acc : Array System.FilePath) : IO (Array System.FilePath) := do
  let mut acc := acc
  for e in ← dir.readDir do
    if (← e.path.isDir) then
      acc ← walkDir e.path acc
    else if e.path.extension == some "olean" then
      acc := acc.push e.path
  return acc

def main (args : List String) : IO UInt32 := do
  let [libDir, out] := args
    | IO.eprintln "usage: DeclEdges <buildLibDir> <out.tsv>"; return 2
  let lib : System.FilePath := libDir
  let files ← walkDir lib #[]
  let files := files.qsort (fun a b => a.toString < b.toString)
  IO.println s!"modules: {files.size}"
  let h ← IO.FS.Handle.mk out .write
  let mut total := 0
  let mut i := 0
  for f in files do
    let rel := (f.toString.drop (libDir.length + 1)).dropEnd 6
    let modName := rel.replace "/" "."
    -- a fresh state per module keeps memory flat; duplicates across parts are skipped inside
    let mut st : St := { mods := #[modName], names := #[#[]] }
    try
      st ← scanModule st 0 f
    catch e =>
      IO.eprintln s!"skipping {modName}: {e}"
    for (k, n) in st.names[0]! do
      h.putStrLn s!"C\t{k}\t{modName}\t{n}"
      if let some ds := st.deps[k]? then
        for d in ds do
          h.putStrLn s!"E\t{k}\t{d}"
    total := total + st.names[0]!.size
    i := i + 1
    if i % 2000 == 0 then IO.println s!"  scanned {i}/{files.size} ({total} constants)"
  h.flush
  IO.println s!"constants: {total}; wrote {out}"
  return 0
