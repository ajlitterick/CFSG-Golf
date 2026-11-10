module

public meta import Lean

/-! `#text_range0 name "file" lo hi hash`: define `name : String` as the bytes `lo..hi` of a
file, after checking their hash.  Imports only `Lean`, so that modules outside the certificate
layer can use it without bringing certificate namespaces into scope. -/

open Lean Elab Command

syntax (name := textRange0) "#text_range0 " ident str num num num : command

elab_rules : command
  | `(command| #text_range0 $sId:ident $path:str $lo:num $hi:num $hash:num) => do
  let path := path.getString
  let (lo, hi) := (lo.getNat, hi.getNat)
  let b ← IO.FS.readBinFile path
  unless lo ≤ hi ∧ hi ≤ b.size do throwError "{path}: range {lo} {hi} outside its {b.size} bytes"
  let r := b.extract lo hi
  unless r.hash.toNat == hash.getNat do
    throwError "{path}: range {lo} {hi} has hash {r.hash.toNat}, pinned {hash.getNat}"
  let some txt := String.fromUTF8? r | throwError "{path}: the range is not UTF-8"
  let sN := (← getCurrNamespace) ++ sId.getId
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDecl (forceExpose := true) <| .defnDecl
      { name := sN, levelParams := [], type := mkConst ``String, value := mkStrLit txt,
        hints := .regular 0, safety := .safe }
    compileDecls #[sN]
