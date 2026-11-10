// Declaration graph analysis on the data written by `text_reach.py --save DIR`:
// visibility-filtered reachability and dominator tree.
//
//   rustc --edition 2021 -O -o domtree tools/domtree/domtree.rs
//   ./domtree DIR OUTPREFIX [MIN_BYTES]
//
// Graph.  One node per chunk (top-level command) plus a virtual root.  A chunk c in file F that
// mentions the name x gets an edge to every declaration d named x that c could actually refer
// to: d is in a file transitively imported by F, or d is earlier in F itself.  (text_reach.py
// alone links every declaration with that name anywhere, which lets local hypothesis names
// collide with unrelated theorems.)
//
// Roots: every chunk of the root files (Comparator/Solution.lean), instances and
// attribute-tagged declarations, and commands that can act at a distance (attribute, notation,
// macro, #-commands, ...).  `variable`/`include`/`omit`/`open … in`/`universe`/`set_option`
// commands are context: not roots, but every later chunk of the same file depends on them.
//
// Outputs:
//   OUTPREFIX.dead.tsv   unreached declarations: path, first line, last line, bytes, kw, name
//   OUTPREFIX.dom.tsv    declarations dominating >= MIN_BYTES:
//       dominated_bytes own_bytes dominated_decls depth name path:line parent_name parent_loc
//   summary on stderr.
//
// "Dominated bytes" of a declaration D is the source that is reachable from the roots only
// through D: what a different proof of D (not using its present dependencies) would free.

use std::collections::HashMap;
use std::env;
use std::fs;
use std::io::{BufWriter, Write};

fn read_i64(p: &str) -> Vec<i64> {
    let b = fs::read(p).expect(p);
    b.chunks_exact(8).map(|c| i64::from_le_bytes(c.try_into().unwrap())).collect()
}
fn read_u32(p: &str) -> Vec<u32> {
    let b = fs::read(p).expect(p);
    b.chunks_exact(4).map(|c| u32::from_le_bytes(c.try_into().unwrap())).collect()
}
fn read_lines(p: &str) -> Vec<String> {
    fs::read_to_string(p).expect(p).split('\n').map(|s| s.to_string()).collect()
}

const CONTEXT: &[&str] = &["variable", "include", "omit", "open", "universe", "set_option",
    "section", "namespace", "end", "import", "public", "module", "meta", "noncomputable",
    "private", "prelude", "mutual", "suppress_compilation", "unseal", "seal"];

fn main() {
    let args: Vec<String> = env::args().collect();
    let dir = &args[1];
    let outp = &args[2];
    let min_bytes: i64 = if args.len() > 3 { args[3].parse().unwrap() } else { 50_000 };
    let f = |n: &str| format!("{}/{}", dir, n);
    let indptr = read_i64(&f("indptr.i64"));
    let toks = read_u32(&f("toks.u32"));
    let kind = fs::read(f("kind.i8")).unwrap();
    let name = read_i64(&f("name.i64"));
    let bytes = read_i64(&f("bytes.i64"));
    let file = read_i64(&f("file.i64"));
    let sline = read_i64(&f("sline.i64"));
    let eline = read_i64(&f("eline.i64"));
    let rootf = fs::read(f("root.u8")).unwrap();
    let paths = read_lines(&f("paths.txt"));
    let names = read_lines(&f("names.txt"));
    let kw = read_lines(&f("kw.txt"));
    let first = read_lines(&f("first.txt"));
    let fptr = read_i64(&f("fimp_ptr.i64"));
    let fimp = read_u32(&f("fimp.u32"));
    let nc = kind.len();
    let nn = names.len();
    let nf = paths.len();
    eprintln!("chunks {} names {} files {} mention edges {}", nc, nn, nf, toks.len());

    // ---- import closure bitsets (file x file), DP in DFS postorder ----
    let w = (nf + 63) / 64;
    let mut clo = vec![0u64; nf * w];
    {
        let mut state = vec![0u8; nf];
        let mut stack: Vec<(u32, u32)> = Vec::new();
        for s in 0..nf {
            if state[s] != 0 {
                continue;
            }
            state[s] = 1;
            stack.push((s as u32, 0));
            while let Some(top) = stack.last().cloned() {
                let (v, k) = (top.0 as usize, top.1 as usize);
                let deg = (fptr[v + 1] - fptr[v]) as usize;
                if k < deg {
                    stack.last_mut().unwrap().1 += 1;
                    let x = fimp[fptr[v] as usize + k] as usize;
                    if state[x] == 0 {
                        state[x] = 1;
                        stack.push((x as u32, 0));
                    }
                } else {
                    // all imports done: closure(v) = union over imports x of ({x} ∪ closure(x))
                    for k in 0..deg {
                        let x = fimp[fptr[v] as usize + k] as usize;
                        if x == v {
                            continue;
                        }
                        let (a, b) = if x < v {
                            let (l, r) = clo.split_at_mut(v * w);
                            (&l[x * w..x * w + w], &mut r[..w])
                        } else {
                            let (l, r) = clo.split_at_mut(x * w);
                            (&r[..w], &mut l[v * w..v * w + w])
                        };
                        for i in 0..w {
                            b[i] |= a[i];
                        }
                        b[x / 64] |= 1u64 << (x % 64);
                    }
                    state[v] = 2;
                    stack.pop();
                }
            }
        }
    }
    eprintln!("import closures done");
    let visible = |from: usize, to: usize| -> bool { clo[from * w + to / 64] >> (to % 64) & 1 == 1 };

    // ---- name -> declaration chunks ----
    let mut cnt = vec![0u32; nn + 1];
    for i in 0..nc {
        if kind[i] == 0 && name[i] >= 0 {
            cnt[name[i] as usize + 1] += 1;
        }
    }
    for i in 0..nn {
        cnt[i + 1] += cnt[i];
    }
    let nptr = cnt.clone();
    let mut fill = cnt.clone();
    let mut ndecl = vec![0u32; nptr[nn] as usize];
    for i in 0..nc {
        if kind[i] == 0 && name[i] >= 0 {
            let x = name[i] as usize;
            ndecl[fill[x] as usize] = i as u32;
            fill[x] += 1;
        }
    }

    // ---- classify chunks: root / context ----
    let ctx: HashMap<&str, ()> = CONTEXT.iter().map(|s| (*s, ())).collect();
    let mut is_root = vec![false; nc];
    let mut is_ctx = vec![false; nc];
    let mut root_files = vec![false; nf];
    // root files are those where a declaration chunk carries the root flag
    for i in 0..nc {
        if rootf[i] != 0 && kind[i] == 0 {
            root_files[file[i] as usize] = true;
        }
    }
    for i in 0..nc {
        if root_files[file[i] as usize] {
            is_root[i] = true;
        } else if kind[i] == 1 {
            if !kw[i].is_empty() {
                is_root[i] = true; // instance / attribute-tagged declaration
            } else {
                let fw = first[i].as_str();
                let fw = fw.trim_start_matches("@[").trim();
                if ctx.contains_key(fw) {
                    is_ctx[i] = indptr[i + 1] > indptr[i];
                } else {
                    is_root[i] = true;
                }
            }
        }
    }

    // ---- chunk -> chunk edges (CSR) ----
    // chunks of one file are contiguous and ordered by line
    let mut eptr = vec![0u64; nc + 1];
    let mut edges: Vec<u32> = Vec::new();
    let mut ctx_in_file: Vec<u32> = Vec::new();
    let mut cur_file = usize::MAX;
    let mut dropped: u64 = 0;
    for c in 0..nc {
        let fc = file[c] as usize;
        if fc != cur_file {
            cur_file = fc;
            ctx_in_file.clear();
        }
        for &t in &toks[indptr[c] as usize..indptr[c + 1] as usize] {
            let x = t as usize;
            for &d in &ndecl[nptr[x] as usize..nptr[x + 1] as usize] {
                let d = d as usize;
                let fd = file[d] as usize;
                let ok = if fd == fc { d < c } else { visible(fc, fd) };
                if ok {
                    edges.push(d as u32);
                } else {
                    dropped += 1;
                }
            }
        }
        for &x in &ctx_in_file {
            edges.push(x);
        }
        if is_ctx[c] {
            ctx_in_file.push(c as u32);
        }
        eptr[c + 1] = edges.len() as u64;
    }
    drop(clo);
    eprintln!("chunk edges {} (dropped as invisible {})", edges.len(), dropped);
    let roots: Vec<u32> = (0..nc).filter(|&i| is_root[i]).map(|i| i as u32).collect();
    eprintln!("roots {}", roots.len());

    // node ids: 0 root, 1..=nc chunks
    let n = nc + 1;
    let succ_len = |v: usize| -> usize {
        if v == 0 { roots.len() } else { (eptr[v] - eptr[v - 1]) as usize }
    };
    let succ_at = |v: usize, k: usize| -> usize {
        if v == 0 { roots[k] as usize + 1 } else { edges[eptr[v - 1] as usize + k] as usize + 1 }
    };
    let mut post: Vec<u32> = Vec::with_capacity(n);
    let mut state = vec![0u8; n];
    let mut stack: Vec<(u32, u32)> = vec![(0, 0)];
    state[0] = 1;
    loop {
        let top = match stack.last() {
            Some(t) => *t,
            None => break,
        };
        let (v, k) = (top.0 as usize, top.1 as usize);
        if k < succ_len(v) {
            stack.last_mut().unwrap().1 += 1;
            let x = succ_at(v, k);
            if state[x] == 0 {
                state[x] = 1;
                stack.push((x as u32, 0));
            }
        } else {
            post.push(v as u32);
            stack.pop();
        }
    }
    let m = post.len();
    // ---- dead declarations ----
    {
        let mut wd = BufWriter::new(fs::File::create(format!("{}.dead.tsv", outp)).unwrap());
        let (mut nd, mut bd, mut ndecl_total) = (0u64, 0i64, 0u64);
        let mut by_dir: HashMap<String, i64> = HashMap::new();
        for c in 0..nc {
            if kind[c] == 1 {
                // unreached context commands that mention names must go with the dead
                // declarations they would otherwise refer to
                if is_ctx[c] && state[c + 1] == 0 {
                    let p = &paths[file[c] as usize];
                    writeln!(wd, "{}\t{}\t{}\t{}\tctx\t{}", p, sline[c] + 1, eline[c], bytes[c], first[c]).unwrap();
                }
                continue;
            }
            ndecl_total += 1;
            if state[c + 1] == 0 {
                nd += 1;
                bd += bytes[c];
                let p = &paths[file[c] as usize];
                let parts: Vec<&str> = p.split('/').collect();
                let key = if parts.len() > 2 { format!("{}/{}", parts[0], parts[1]) } else { parts[0].to_string() };
                *by_dir.entry(key).or_insert(0) += bytes[c];
                let nm = if name[c] >= 0 { names[name[c] as usize].as_str() } else { "" };
                writeln!(wd, "{}\t{}\t{}\t{}\t{}\t{}", p, sline[c] + 1, eline[c], bytes[c], kw[c], nm).unwrap();
            }
        }
        let total: i64 = bytes.iter().sum();
        eprintln!("unreached declarations: {} of {}  ({:.1} MB of {:.1} MB, {:.2}%)",
            nd, ndecl_total, bd as f64 / 1e6, total as f64 / 1e6, 100.0 * bd as f64 / total as f64);
        let mut v: Vec<(String, i64)> = by_dir.into_iter().collect();
        v.sort_by(|a, b| b.1.cmp(&a.1));
        for (d, b) in v.iter().take(30) {
            eprintln!("  {:8.2} MB  {}", *b as f64 / 1e6, d);
        }
    }

    // ---- dominators (Cooper-Harvey-Kennedy) ----
    let mut rpo = vec![u32::MAX; n];
    for (i, &v) in post.iter().enumerate() {
        rpo[v as usize] = (m - 1 - i) as u32;
    }
    let order: Vec<u32> = post.iter().rev().cloned().collect();
    let mut pcnt = vec![0u64; m + 1];
    for r in 0..m {
        let v = order[r] as usize;
        for k in 0..succ_len(v) {
            pcnt[rpo[succ_at(v, k)] as usize + 1] += 1;
        }
    }
    for i in 0..m {
        pcnt[i + 1] += pcnt[i];
    }
    let mut pfill = pcnt.clone();
    let mut preds = vec![0u32; pcnt[m] as usize];
    for r in 0..m {
        let v = order[r] as usize;
        for k in 0..succ_len(v) {
            let x = rpo[succ_at(v, k)] as usize;
            preds[pfill[x] as usize] = r as u32;
            pfill[x] += 1;
        }
    }
    let undef = u32::MAX;
    let mut idom = vec![undef; m];
    idom[0] = 0;
    let mut changed = true;
    let mut iters = 0;
    while changed {
        changed = false;
        iters += 1;
        for b in 1..m {
            let mut new = undef;
            for &p in &preds[pcnt[b] as usize..pcnt[b + 1] as usize] {
                if idom[p as usize] == undef {
                    continue;
                }
                if new == undef {
                    new = p;
                } else {
                    let (mut x, mut y) = (p, new);
                    while x != y {
                        while x > y {
                            x = idom[x as usize];
                        }
                        while y > x {
                            y = idom[y as usize];
                        }
                    }
                    new = x;
                }
            }
            if idom[b] != new {
                idom[b] = new;
                changed = true;
            }
        }
        eprintln!("dominator pass {}", iters);
    }
    let mut sub = vec![0i64; m];
    let mut subn = vec![0u32; m];
    for r in 1..m {
        let c = order[r] as usize - 1;
        sub[r] = bytes[c];
        if kind[c] == 0 {
            subn[r] = 1;
        }
    }
    for r in (1..m).rev() {
        let d = idom[r] as usize;
        sub[d] += sub[r];
        subn[d] += subn[r];
    }
    eprintln!("reachable chunks {}, bytes under root {}", m - 1, sub[0]);
    let mut par = vec![undef; m];
    let mut depth = vec![0u32; m];
    for r in 1..m {
        let mut d = idom[r] as usize;
        while d != 0 && kind[order[d] as usize - 1] != 0 {
            d = idom[d] as usize;
        }
        if d != 0 {
            par[r] = d as u32;
            depth[r] = depth[d] + 1;
        }
    }
    let mut rows: Vec<usize> = (1..m)
        .filter(|&r| kind[order[r] as usize - 1] == 0 && sub[r] >= min_bytes)
        .collect();
    rows.sort_by(|&a, &b| sub[b].cmp(&sub[a]));
    let mut wo = BufWriter::new(fs::File::create(format!("{}.dom.tsv", outp)).unwrap());
    let label = |r: usize| -> (String, String) {
        let c = order[r] as usize - 1;
        let nm = if name[c] >= 0 { names[name[c] as usize].clone() } else { "?".to_string() };
        (nm, format!("{}:{}", paths[file[c] as usize], sline[c] + 1))
    };
    for &r in &rows {
        let c = order[r] as usize - 1;
        let (nm, loc) = label(r);
        let (pn, pl) = if par[r] != undef { label(par[r] as usize) } else { ("-".into(), "-".into()) };
        writeln!(wo, "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}", sub[r], bytes[c], subn[r], depth[r], nm, loc, pn, pl).unwrap();
    }
    eprintln!("wrote {} dominator rows", rows.len());
}
