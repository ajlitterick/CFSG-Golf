/-
Declaration-level reachability from the final theorem.

Reads every `.olean` and `.olean.private` under a build directory one at a time (no
global `importModules`, so memory stays bounded), records for each constant the set
of constants its type and value mention, then walks from a root constant.

    lake env lean --run tools/DeclReach.lean <buildLibDir> <rootConst> <out.tsv>
    e.g. lake env lean --run tools/DeclReach.lean .lake/build/lib/lean \
           CFSGComparator.classification reach.tsv

Output `out.tsv`:
    M <tab> <module> <tab> <used> <tab> <total>          one line per module
    D <tab> <module> <tab> U|N <tab> <constant name>      one line per constant
Constants outside the scanned build directory (Mathlib, TauCeti, core) are treated
as leaves.  Elaboration-only dependencies (instances found by type-class search in a
tactic, simp lemmas, `decide` instances) do not appear in proof terms, so an unused
constant is a *candidate* for deletion, to be confirmed by rebuilding.
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
    arr := arr.push (k, toString n)
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
  let [libDir, rootName, out] := args
    | IO.eprintln "usage: DeclReach <buildLibDir> <rootConst> <out.tsv>"; return 2
  let lib : System.FilePath := libDir
  let files ← walkDir lib #[]
  let files := files.qsort (fun a b => a.toString < b.toString)
  IO.println s!"modules: {files.size}"
  let mut st : St := {}
  let mut i := 0
  for f in files do
    let rel := (f.toString.drop (libDir.length + 1)).dropEnd 6   -- strip ".olean"
    let modName := rel.replace "/" "."
    let idx := st.mods.size
    st := { st with mods := st.mods.push modName, names := st.names.push #[] }
    try
      st ← scanModule st idx f
    catch e =>
      IO.eprintln s!"skipping {modName}: {e}"
    i := i + 1
    if i % 5000 == 0 then IO.println s!"  scanned {i}/{files.size} ({st.modOf.size} constants)"
  IO.println s!"constants: {st.modOf.size}   theorems proved by sorryAx: {st.noValue}"
  -- BFS
  let root := key rootName.toName
  let rootFound := st.modOf.contains root
  unless rootFound do
    IO.eprintln s!"root constant {rootName} not found in scanned modules (writing all-N output)"
  let mut seen : Std.HashSet Nat := {}
  let mut stack : Array Nat := if rootFound then #[root] else #[]
  while h : stack.size > 0 do
    let k := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains k then continue
    seen := seen.insert k
    if let some ds := st.deps[k]? then
      for d in ds do
        if !seen.contains d then stack := stack.push d
  IO.println s!"reachable constants: {seen.size}"
  -- output
  let h ← IO.FS.Handle.mk out .write
  let mut usedMods := 0
  for idx in [0:st.mods.size] do
    let m := st.mods[idx]!
    let arr := st.names[idx]!
    let used : Nat := arr.foldl (fun (c : Nat) (p : Nat × String) => if seen.contains p.1 then c + 1 else c) 0
    if used > 0 then usedMods := usedMods + 1
    h.putStrLn s!"M\t{m}\t{used}\t{arr.size}"
    for (k, n) in arr do
      h.putStrLn s!"D\t{m}\t{if seen.contains k then "U" else "N"}\t{n}"
  h.flush
  IO.println s!"modules with a used constant: {usedMods}/{st.mods.size}; wrote {out}"
  return (if rootFound then 0 else 1)
