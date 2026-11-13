#!/usr/bin/env python3
"""Write <Root>/Test/Axioms.lean. It has two parts.

1. One `#print axioms` per main theorem. The list is: the hand-written theorems named in the
   configuration (`axioms.names`), every path theorem, every completeness theorem (`ok_<fn>`),
   every readable corollary (`<fn>_readable`), every witness of a success path (`<fn>_runs`),
   the read-only theorems of the loops (`ro_<fn>`), every invariant theorem and whatever else
   the configuration lists under `axioms.after` (theorems of files that import the generated
   ones).
2. A scan of EVERY constant (theorem, definition, instance) of every module of the project and
   of the shared library TokenKit that the root file of the project imports. The build fails
   when one of them uses an axiom other than the three standard ones, or when a module declares
   an axiom. So no theorem can be hidden from the test by leaving its name out of part 1.

Switches of the configuration, and what each one does to part 1 (none of them touches part 2):

- `axioms.skip` is GONE (fix round of the QNT, BNB and WETH audit): the generator stops when it finds the key. It
  was a list of names to drop from part 1, with no check.
- a function with `"frame": true` (its path stops at a CALL, see gen_paths.py) has no generated
  `ok_<fn>` and no generated invariant theorem. Its entry in the configuration must then name
  the hand-written theorems that take their place (`frame_theorems`); they are added to part 1.
  The generator stops when the list is missing or empty.
- `axioms.declared_only` (WETH): a generated name that no Lean file of the project or of the
  library declares is left out of part 1 (a function that stops at an opcode outside the
  simulated set has no generated theorem of some kinds). Each name left out is printed and is
  written in the head of Test/Axioms.lean. It cannot hide a theorem: a name is left out only
  when no theorem of that name exists, and part 2 scans every constant.

Usage: gen_axioms.py <config/token.json>"""
import re
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tokenlib  # noqa: E402


def main():
    tok = tokenlib.load()
    R = tok.root
    ax = tok.cfg.get('axioms', {})
    d = json.load(open(tok.paths_json))
    have = lambda *p: os.path.exists(os.path.join(tok.lean_dir, *p))
    names = list(ax.get('names', []))
    SANITY_NAMES = os.path.join(tok.root_dir, 'work', 'sanity_names.json')
    # the invariant theorems: mode `delta` of gen_supply.py names them delta_<fn> and
    # supply_step; gen_solvent.py (backing = ether) names them solvent_<fn>
    delta = tok.cfg.get('supply', {}).get('mode') == 'delta'
    if tok.cfg.get('backing') == 'ether':
        sup, sup_all = 'solvent_', 'solvent_preserved'
    elif delta:
        sup, sup_all = 'delta_', 'supply_step'
    else:
        sup, sup_all = 'supply_', 'supply_preserved'
    if 'skip' in ax:
        raise SystemExit('axioms.skip is not supported any more: a function with "frame": true '
                         'names its hand-written theorems under "frame_theorems"; every other '
                         'generated name must exist')
    for f in tok.funcs + tok.cfg.get('fallbacks', []) + tok.cfg.get('segments', []):
        fn = f['name']
        names += [p['name'] for p in d[fn]['paths']]
        if f.get('frame'):
            # no generated `ok_<fn>` and no generated invariant theorem (gen_paths.py stops the
            # path at the CALL): the hand-written theorems that take their place are checked
            if not f.get('frame_theorems'):
                raise SystemExit(f'{fn}: "frame": true needs "frame_theorems", the hand-written '
                                 'theorems that stand for ok_%s and %s%s' % (fn, sup, fn))
            names += f['frame_theorems']
        else:
            names.append(f'ok_{fn}')
        if have('Readable.lean') and fn in tok.cfg.get('readable', {}):
            names.append(f'Readable.{fn}_readable')
        if not f.get('frame'):
            names.append(f'{sup}{fn}')
        sanity = tok.cfg.get('sanity', {})
        # local (WBTC): when gen_sanity.py wrote work/sanity_names.json (entries with several
        # witnesses per function and revert witnesses), the names come from that file below
        if os.path.exists(SANITY_NAMES):
            continue
        if have('Sanity', sanity.get('file', 'Zero') + '.lean') and fn in sanity:
            san = sanity[fn]
            # a list or a dict with `args`: one witness `<fn>_runs`; a dict of path names (a
            # function with several success paths): one witness per path
            one = isinstance(san, list) or 'args' in san
            names += [f'Sanity.{t}_runs' for t in ([fn] if one else san)]
    if os.path.exists(SANITY_NAMES):
        names += json.load(open(SANITY_NAMES))
    if have('Gen', 'Loops.lean'):
        for f in tok.loops:
            names += [f'Loops.ro_{f["name"]}', f'{sup}{f["name"]}']
    names.append(sup_all)
    names += ax.get('after', [])
    left_out = []
    if ax.get('declared_only'):
        # keep the names that a Lean file of the project or of the kit library declares (a function that stops at an
        # opcode outside the simulated set has no generated theorem of some kinds)
        src = ''
        for top in (os.path.join(tok.root_dir, R), tok.kit_lib):
            for base, _, files in os.walk(top):
                for fl in files:
                    if fl.endswith('.lean') and fl != 'Axioms.lean':
                        src += open(os.path.join(base, fl)).read()
        decl = set(src.replace('\n', ' ').split('theorem ')[i].split(' ')[0]
                   for i in range(1, src.count('theorem ') + 1))
        if ax.get('dotted_decl'):
            # `axioms.dotted_decl = true` (USDE, ENA): a dotted declaration
            # (`theorem Supply.inv_congr`) is declared under its last part too
            decl |= {x.split('.')[-1] for x in decl}
        kept = [n for n in names if n.split('.')[-1] in decl]
        left_out = [n for n in names if n not in kept]
        print('Axioms.lean: not declared, left out:', ', '.join(left_out))
        names = kept
    imports = list(ax.get('imports', [f'{tok.mod}.Invariant']))
    # part 2 scans what this file imports: every module that the root file of the project
    # imports (but this file itself)
    root_file = os.path.join(tok.root_dir, R + '.lean')
    if os.path.exists(root_file):
        for m in re.findall(r'^import (\S+)', open(root_file).read(), re.M):
            if m.startswith(R + '.') and m != f'{R}.Test.Axioms' and m not in imports:
                imports.append(m)
    wrap = lambda words, width=96: [ln for ln in __import__('textwrap').wrap(words, width)]
    o = ['import Lean', '\n'.join(f'import {m}' for m in imports), '', '/-!',
         '# Test: the axioms of the main theorems', '',
         'The build prints, for each main theorem, the axioms its proof uses. The expected ones are the',
         'three standard axioms of Lean (`propext`, `Classical.choice`, `Quot.sound`) or a subset; a',
         '`sorryAx` or any other name would show an unproved step. `scripts/check_axioms.sh` reads the',
         'build log and fails on any other name.', '',
         'The last command scans every constant of every module of the project and of TokenKit that',
         'this file imports (all the modules that the root file imports). It stops the build when one',
         'of them uses another axiom or when a module declares an axiom, and prints `AXIOM SCAN OK`',
         'with the counts when none does. So a theorem whose name is not in the list below is still',
         'checked.', '',
         'Generated by `scripts/gen_axioms.py` from the configuration of the token and paths.json; do',
         f'not edit. {len(names)} theorems.']
    if left_out:
        o += [''] + wrap('Generated names that no Lean file declares, left out of the list '
                         '(`axioms.declared_only`): ' + ', '.join(left_out) + '.')
    o += ['-/', '', 'open TokenKit', f'open {R} {R}.Paths {R}.Complete', '']
    o += [f'#print axioms {n}' for n in names]
    o += ['', '-- Every constant of the modules of the project and of TokenKit that this file imports.',
          'open Lean Elab Command in',
          '#eval show CommandElabM Unit from do',
          '  let env ← getEnv',
          '  let mut n : Nat := 0',
          '  let mut nthm : Nat := 0',
          '  let mut used : NameSet := {}',
          '  let mut declared : Array Name := #[]',
          '  let mut bad : Array Name := #[]',
          '  for (c, ci) in env.constants.toList do',
          '    let some mi := env.getModuleIdxFor? c | continue',
          '    let mod := env.header.moduleNames[mi.toNat]!',
          f'    if (`{R}).isPrefixOf mod || (`TokenKit).isPrefixOf mod then',
          '      n := n + 1',
          '      match ci with',
          '      | .axiomInfo _ => declared := declared.push c',
          '      | .thmInfo _ => nthm := nthm + 1',
          '      | _ => pure ()',
          '      let axs ← Lean.collectAxioms c',
          '      for x in axs do',
          '        used := used.insert x',
          '        if x != ``propext && x != ``Classical.choice && x != ``Quot.sound then',
          '          bad := bad.push c',
          '  if !declared.isEmpty || !bad.isEmpty then',
          '    throwError "AXIOM SCAN FAILED: axioms declared: {declared}; constants that use another axiom: {bad}"',
          f'  logInfo m!"AXIOM SCAN OK: {{n}} constants ({{nthm}} theorems) of {R} and TokenKit, axioms used: {{used.toList}}"']
    os.makedirs(os.path.join(tok.root_dir, R, 'Test'), exist_ok=True)
    open(os.path.join(tok.root_dir, R, 'Test', 'Axioms.lean'), 'w').write('\n'.join(o) + '\n')
    print('Axioms.lean:', len(names), 'theorems')


main()
