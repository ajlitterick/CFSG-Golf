// Redundant imports: an import of F is redundant when the module is already made visible by
// another import of F through a chain of `public import`s.
//
//   rustc --edition 2021 -O -o impreduce tools/impreduce/impreduce.rs
//   ./impreduce DIR OUT.tsv HASHES.tsv
//
// DIR is written by dump_imports.py.  For every repository module F:
//   V_any(F) = modules reachable from an `import`/`public import` of F by >= 1 public edges
//   V_pub(F) = the same, starting only from the `public import`s of F
// A plain `import A` is redundant if A is in V_any(F); a `public import A` is redundant if A
// is in V_pub(F) (so that what F re-exports is unchanged).  `meta` and `import all` lines are
// never touched and never used as a starting point.  A repeated identical line is redundant.
//
// OUT.tsv:     module <tab> kind(0 private / 1 public) <tab> redundant import
// HASHES.tsv:  module <tab> hash of (direct ∪ V_any) <tab> hash of (public direct ∪ V_pub)
// The hashes are what F can see and what F re-exports; they must be identical before and
// after the redundant lines are removed (run the tool on both trees and diff HASHES).

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
fn mix(x: u64) -> u64 {
    let mut z = x.wrapping_add(0x9E3779B97F4A7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
    z ^ (z >> 31)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let dir = &args[1];
    let f = |n: &str| format!("{}/{}", dir, n);
    let ptr = read_i64(&f("ptr.i64"));
    let tgt = read_u32(&f("tgt.u32"));
    let kind = fs::read(f("kind.u8")).unwrap();
    let names: Vec<String> = fs::read_to_string(f("names.txt")).unwrap().split('\n').map(|s| s.to_string()).collect();
    let meta = fs::read_to_string(f("meta.txt")).unwrap();
    let nrepo: usize = meta.split_whitespace().nth(1).unwrap().parse().unwrap();
    let n = names.len();
    // name hashes (stable across trees: by module name, not index)
    let nh: Vec<u64> = names.iter().map(|s| {
        let mut h: u64 = 1469598103934665603;
        for b in s.bytes() { h = (h ^ b as u64).wrapping_mul(1099511628211); }
        mix(h)
    }).collect();
    let mut stamp_any = vec![0u32; n];
    let mut stamp_pub = vec![0u32; n];
    let mut queue: Vec<u32> = Vec::new();
    let mut out = BufWriter::new(fs::File::create(&args[2]).unwrap());
    let mut hout = BufWriter::new(fs::File::create(&args[3]).unwrap());
    let (mut removed, mut total) = (0u64, 0u64);
    for fidx in 0..nrepo {
        let ep = (fidx + 1) as u32;
        let (lo, hi) = (ptr[fidx] as usize, ptr[fidx + 1] as usize);
        let mut hash_pub: u64 = 0;
        let mut hash_any: u64 = 0;
        // pass 1: from public imports
        queue.clear();
        for e in lo..hi {
            if kind[e] == 1 {
                let b = tgt[e] as usize;
                for e2 in ptr[b] as usize..ptr[b + 1] as usize {
                    if kind[e2] == 1 {
                        let x = tgt[e2] as usize;
                        if stamp_pub[x] != ep { stamp_pub[x] = ep; stamp_any[x] = ep; queue.push(x as u32); }
                    }
                }
            }
        }
        let mut qi = 0;
        while qi < queue.len() {
            let v = queue[qi] as usize; qi += 1;
            hash_pub = hash_pub.wrapping_add(nh[v]);
            for e2 in ptr[v] as usize..ptr[v + 1] as usize {
                if kind[e2] == 1 {
                    let x = tgt[e2] as usize;
                    if stamp_pub[x] != ep { stamp_pub[x] = ep; stamp_any[x] = ep; queue.push(x as u32); }
                }
            }
        }
        hash_any = hash_any.wrapping_add(hash_pub);
        // pass 2: additionally from private imports
        queue.clear();
        for e in lo..hi {
            if kind[e] == 0 {
                let b = tgt[e] as usize;
                for e2 in ptr[b] as usize..ptr[b + 1] as usize {
                    if kind[e2] == 1 {
                        let x = tgt[e2] as usize;
                        if stamp_any[x] != ep { stamp_any[x] = ep; queue.push(x as u32); }
                    }
                }
            }
        }
        let mut qi = 0;
        while qi < queue.len() {
            let v = queue[qi] as usize; qi += 1;
            hash_any = hash_any.wrapping_add(nh[v]);
            for e2 in ptr[v] as usize..ptr[v + 1] as usize {
                if kind[e2] == 1 {
                    let x = tgt[e2] as usize;
                    if stamp_any[x] != ep { stamp_any[x] = ep; queue.push(x as u32); }
                }
            }
        }
        // direct imports: redundancy and hashes (count each direct module once)
        let mut seen_dir: Vec<(u8, u32)> = Vec::with_capacity(hi - lo);
        for e in lo..hi {
            let k = kind[e];
            if k > 1 { continue; }
            total += 1;
            let a = tgt[e] as usize;
            let dup = seen_dir.iter().any(|&(k2, a2)| a2 == a as u32 && k2 == k);
            let red = if k == 0 { stamp_any[a] == ep } else { stamp_pub[a] == ep };
            if dup || red {
                removed += 1;
                writeln!(out, "{}\t{}\t{}", names[fidx], k, names[a]).unwrap();
            }
            if !dup {
                seen_dir.push((k, a as u32));
            }
        }
        // visible sets = direct ∪ reach (hash each module once)
        let mut added: Vec<u32> = Vec::new();
        for &(k, a) in &seen_dir {
            let a = a as usize;
            if stamp_any[a] != ep && !added.contains(&(a as u32)) {
                hash_any = hash_any.wrapping_add(nh[a]);
                added.push(a as u32);
            }
            if k == 1 && stamp_pub[a] != ep {
                // public direct import not otherwise re-exported
                hash_pub = hash_pub.wrapping_add(nh[a].rotate_left(1));
            }
        }
        // a public direct import that is also in V_pub must hash the same before/after removal:
        // it contributes through V_pub only (above), so nothing more to add.
        writeln!(hout, "{}\t{:016x}\t{:016x}", names[fidx], hash_any, hash_pub).unwrap();
    }
    eprintln!("plain/public import lines: {}; redundant: {}", total, removed);
}
