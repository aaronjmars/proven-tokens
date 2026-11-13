#!/usr/bin/env python3
"""Write a Lean file that dumps the statement of every theorem of the axioms test of a project,
and of every definition of the project or of the kit that these statements use (transitively,
through the types and the bodies of definitions; proofs are not followed).

For each constant the dump has: its name with the root namespace (`<Root>Verify.` or `TokenKit.`)
removed, its kind, a hash of its type and of its body computed after the same removal in every
name inside, and the printed type. Two dumps of the same project, one in the old layout (generic
files in `<Root>/Evm`) and one in the kit layout, are equal exactly when nothing changed but the
namespace of the generic files.

Usage: dump_statements.py <project> <out.txt>   writes <project>/KitDump.lean; then, on the
box, in <project>: `lake env lean KitDump.lean` writes <out.txt>. Compare two dumps with
`dump_statements.py --diff <a.txt> <b.txt>`."""
import os
import re
import sys

LEAN = r'''import @ROOT@.Test.Axioms
import Lean

open Lean Elab Command Meta

namespace KitDump

def roots : List Name := [`@ROOT@, `TokenKit]

def userName (n : Name) : Name := privateToUserName n

def ours (n : Name) : Bool := roots.contains (userName n).getRoot

def normName (n : Name) : Name :=
  let u := userName n
  let u := roots.foldl (fun (a : Name) r => if a.getRoot == r then a.replacePrefix r .anonymous else a) u
  `K ++ u

partial def normExpr (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => some (.const (normName n) ls)
    | .proj s i b => some (.proj (normName s) i (normExpr b))
    | _ => none

abbrev M := StateT (NameSet × Array (String × String)) MetaM

partial def visit (tops : NameSet) (n : Name) : M Unit := do
  if (← get).1.contains n then return
  modify fun (s, a) => (s.insert n, a)
  let some ci := (← getEnv).find? n | return
  let ty := ci.type
  let th := (normExpr ty).hash
  let tyS := toString (← ppExpr ty)
  let tyC := ty.getUsedConstants
  let (kind, vh, deps) : String × UInt64 × Array Name := match ci with
    | .thmInfo _ => ("theorem", 0, tyC)
    | .defnInfo v => ("def", (normExpr v.value).hash, tyC ++ v.value.getUsedConstants)
    | .opaqueInfo v => ("opaque", (normExpr v.value).hash, tyC ++ v.value.getUsedConstants)
    | .inductInfo v => ("inductive", 0, tyC ++ v.ctors.toArray)
    | .ctorInfo _ => ("constructor", 0, tyC)
    | .recInfo _ => ("recursor", 0, #[])
    | .axiomInfo _ => ("axiom", 0, tyC)
    | .quotInfo _ => ("quot", 0, #[])
  let tag := if tops.contains n then "TOP" else "DEP"
  let deps := deps.filter ours
  let uses := " ".intercalate ((deps.map fun d => toString (normName d)).qsort (· < ·)).toList.eraseDups
  modify fun (s, a) =>
    (s, a.push (toString (normName n), s!"{tag} {kind} typehash={th} bodyhash={vh}\n  uses: {uses}\n  {tyS}"))
  for d in deps do
    visit tops d

elab "kit_dump " out:str ids:ident* : command => do
  let names ← ids.mapM fun i => liftCoreM <| realizeGlobalConstNoOverload i
  let (_, (_, rows)) ← liftTermElabM <|
    (do for n in names do visit (names.foldl (fun s n => s.insert n) {}) n : M Unit).run ({}, #[])
  let rows := rows.qsort fun a b => a.1 < b.1
  let text := rows.foldl (fun acc r => acc ++ s!"## {r.1} {r.2}\n") ""
  IO.FS.writeFile out.getString text
  logInfo m!"kit_dump: {names.size} theorems of the axioms test, {rows.size} constants written"

end KitDump

@OPENS@

set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 100000
set_option maxRecDepth 100000

kit_dump "@OUT@"
@NAMES@
'''


def diff(a, b):
    strip = lambda t: re.sub(r'\b(\w+Verify|TokenKit)\.', '', t)

    def load(p):
        raw, key = {}, None
        for line in open(p).read().split('\n'):
            if line.startswith('## '):
                key = line.split(' ')[1]
                raw[key] = [line]
            elif key:
                raw[key].append(line)
        # the printer breaks lines by width, and the width of a name changes with its namespace,
        # so the texts are compared with every run of blanks made one blank
        rows = {k: re.sub(r'\s+', ' ', strip('\n'.join(v))) for k, v in raw.items()}
        uses = {k: set(strip(v[1]).split()[1:]) for k, v in raw.items()}
        return rows, uses
    (ra, _), (rb, uses) = load(a), load(b)
    top = lambda r: sum(1 for v in r.values() if v.split(' ')[2] == 'TOP')
    print('constants: %d in %s (%d of the axioms test), %d in %s (%d of the axioms test)' % (
        len(ra), a, top(ra), len(rb), b, top(rb)))
    changed = set()
    for k in sorted(set(ra) | set(rb)):
        if ra.get(k) != rb.get(k):
            changed.add(k)
            print('CHANGED' if k in ra and k in rb else ('ONLY IN ' + (a if k in ra else b)), k)
            for r in (ra, rb):
                if k in r:
                    print('   ', r[k][:1500])
    print('different or missing: %d' % len(changed))
    # the theorems of the axioms test whose statement uses a changed constant, directly or not
    hit, grew = set(changed), True
    while grew:
        grew = False
        for k, u in uses.items():
            if k not in hit and u & hit:
                hit.add(k)
                grew = True
    tops = sorted(k for k in hit if k in rb and rb[k].split(' ')[2] == 'TOP')
    print('theorems of the axioms test that use a changed constant: %d' % len(tops))
    for k in tops:
        print('   ', k)
    return len(changed)


def main():
    if sys.argv[1] == '--diff':
        sys.exit(1 if diff(sys.argv[2], sys.argv[3]) else 0)
    proj, out = sys.argv[1], sys.argv[2]
    root = [d for d in sorted(os.listdir(proj))
            if d.endswith('Verify') and os.path.isdir(os.path.join(proj, d))][0]
    text = open(os.path.join(proj, root, 'Test', 'Axioms.lean')).read()
    opens = '\n'.join(l for l in text.split('\n') if l.startswith('open '))
    names = re.findall(r'^#print axioms (\S+)', text, flags=re.M)
    lean = (LEAN.replace('@ROOT@', root).replace('@OPENS@', opens).replace('@OUT@', out)
            .replace('@NAMES@', '\n'.join('  ' + n for n in names)))
    open(os.path.join(proj, 'KitDump.lean'), 'w').write(lean)
    print(proj, ':', len(names), 'theorems, KitDump.lean written')


main()
