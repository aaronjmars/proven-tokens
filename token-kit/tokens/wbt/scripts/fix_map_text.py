#!/usr/bin/env python3
# SUPERSEDED, DO NOT RUN (the ten-token audit, finding WBT-4): this local copy is merged into the kit
# (token-kit/scripts, see kit-status.json wbt_merge) and differs from it. The files of WBT are
# regenerated with the kit: bash token-kit/scripts/regen.sh tokens/wbt/config/wbt.json
"""Correct one sentence of the head of Map.lean that the kit's gen_dispatch.py (mode `walk`)
writes: it says the code was compiled with the optimizer. WBT was compiled with the optimizer
off; solc still splits the selector table by GT comparisons. Only a comment changes.

Usage: fix_map_text.py <project folder>"""
import glob
import os
import sys

OLD = ('The code was compiled with the optimizer, so the table\n'
       'is split by GT comparisons and is not walked entry by entry.')
NEW = ('The table is split by GT comparisons (solc does so\n'
       'with the optimizer off too) and is not walked entry by entry.')
for p in glob.glob(os.path.join(sys.argv[1], '*', '*', 'Map.lean')):
    s = open(p).read()
    if OLD in s:
        open(p, 'w').write(s.replace(OLD, NEW))
        print('Map.lean: sentence on the optimizer corrected')
    elif NEW not in s:
        raise SystemExit('fix_map_text: the sentence was not found in ' + p)
