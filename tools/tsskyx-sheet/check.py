# -*- coding: utf-8 -*-
"""Cross-check Tsskyx's BMS Analysis workbook against this project.

Three things are checked, all of them on the "Bashicu Hydra" band, which is
the plain BM4 matrix that the trio project models:

  A  reading of a column       every column of every matrix, against the
                               label Tsskyx drew for it.  ebp2bms/algorithm/2
                               claims row y names the Omega subscript, with
                               (x,y,0) = Omega_y and (x,y,1) = Omega_w; the
                               drawing says the same thing independently.
  B  order and normal form     the matrices must increase strictly down a
                               sheet (the ordinals do) and be in normal form
                               (tools/trio_term.py).
  C  psi_0(Omega_alpha) rows   where the Buchholz hydra is the root plus one
                               leaf alpha, the ordinal is psi_0(Omega_alpha)
                               and the matrix must be what
                               tools/build_omega_alpha.py builds.
  D  the same rows as drawings so that the blocks the sheet draws without
                               typing a matrix are covered as well.
  E  ebp2bms/sheet/{1,2}       the tables in the READMEs against the builder
                               that generated them.

One typed matrix still contradicts its own drawing and one block carries the
wrong Buchholz label; ERRATA and LABEL_ERRATA below record them, and the checks
then pass everywhere.  Pass --raw to check the sheet as typed.

usage: python3 check.py [--raw] [xlsx]
       default: ../papers/tsskyx-bms-analysis.xlsx
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'tools'))

from bms2bmshydra import Unsupported, labels_of                       # noqa: E402
from extract import (bands, forest, parse_band, read_rows, render,      # noqa: E402
                     split_blocks)
from trio_term import cnf, olt, translate                               # noqa: E402
import openpyxl                                                         # noqa: E402


def blocks_of(ws):
    """[(block number, first row, {band key: (nodes, matrix)})]"""
    out = []
    bd = bands(ws)
    root = dict((k, c0) for k, _, c0, _ in bd)['S']
    for n, block in enumerate(split_blocks(read_rows(ws), root), 1):
        got = {}
        for key, _, c0, c1 in bd:
            nodes, mat = parse_band(block, c0, c1)
            if nodes or mat:
                got[key] = (nodes, mat)
        out.append((n, block[0][0], got))
    return out


# ---- what the sheet still gets wrong ----
#
# A block draws its matrix twice: once as a hydra, once as a row of column
# strings.  The 2026-08-23 revision of the workbook fixed eight of the nine
# disagreements found in the previous one; this is what is left.  Keyed by
# (sheet, block number) -> corrected matrix.
ERRATA = {
    ('Up to 0w^2', 47): '000 111 210 111 110 211 320 211',   # S226 310 -> 320
}

# Not a matrix but a label: block [50] of 'Up to 0w^w' draws
# M(w^2+w) ++ the '+1' anchor, which by every other block of that shape
# (0w^2[35] [76] [94], 0w^w[31]) is psi_0(psi_alpha(Omega_beta)) with beta the
# first y-1 add units of alpha plus 1 -- here 0(w^2+w(w^2+1)), not 0(w^2+w+1).
# So it is not a psi_0(Omega_alpha) row at all and checks C and D skip it.
LABEL_ERRATA = {
    ('Up to 0w^w', 50): '0(w^2+w(w^2+1))',
}


def apply_errata(sheets):
    """Replace the typed matrices that contradict their own drawing."""
    n = 0
    for title, blocks in sheets:
        for bn, row, bd in blocks:
            fix = ERRATA.get((title, bn))
            if fix and 'S' in bd:
                nodes, _ = bd['S']
                bd['S'] = (nodes, [tuple(int(ch) for ch in c) for c in fix.split()])
                n += 1
    return n


# ---- A: what a column says ----
# labels_of is tools/bms2bmshydra.py's reading of a column, the one
# ebp2bms/algorithm/2 states; this is where it gets checked against the sheet.


def check_reading(sheets):
    bad = miss = ok = 0
    for title, blocks in sheets:
        for n, row, bd in blocks:
            nodes, mat = bd.get('S', (None, None))
            if not mat or not nodes:
                continue
            if len(nodes) != len(mat):
                print('  %s [%d] row %d: %d drawn nodes vs %d columns'
                      % (title, n, row, len(nodes), len(mat)))
                bad += 1
                continue
            try:
                want = labels_of(mat)
            except Unsupported:
                miss += 1                       # outside the z<2 fragment
                continue
            got = [lab for _, _, lab in nodes]
            hs = [h for _, h, _ in nodes]
            xs = [c[0] for c in mat]
            if got == want and hs == xs:
                ok += 1
            else:
                bad += 1
                print('  %s [%d] row %d' % (title, n, row))
                print('     matrix %s' % ''.join('(%d,%d,%d)' % c for c in mat))
                if hs != xs:
                    print('     height %s vs x %s' % (hs, xs))
                if got != want:
                    print('     drawn  %s' % ','.join(got))
                    print('     read   %s' % ','.join(want))
    print('A reading of a column: %d blocks agree, %d disagree, %d z>=2 skipped'
          % (ok, bad, miss))
    return bad


# ---- B: order and normal form ----

def check_order(sheets):
    bad = 0
    for title, blocks in sheets:
        prev = prevn = None
        for n, row, bd in blocks:
            mat = bd.get('S', (None, None))[1]
            if not mat:
                continue
            t = translate(mat)
            if not cnf(t):
                print('  %s [%d] row %d: not in normal form: %s'
                      % (title, n, row, ''.join('(%d,%d,%d)' % c for c in mat)))
                bad += 1
            if prev is not None and not olt(prev, t):
                print('  %s [%d] row %d: does not exceed [%d]' % (title, n, row, prevn))
                print('     [%d] %s' % (prevn, ''.join('(%d,%d,%d)' % c for c in prevmat)))
                print('     [%d] %s' % (n, ''.join('(%d,%d,%d)' % c for c in mat)))
                bad += 1
            prev, prevn, prevmat = t, n, mat
    print('B order and normal form: %d violations' % bad)
    return bad


# ---- C: the psi_0(Omega_alpha) rows ----

def leaf_alpha(nodes):
    """alpha when the Buchholz hydra is the root plus one leaf, else None."""
    roots, kids = forest(nodes)
    if len(roots) != 1 or nodes[roots[0]][2] != '0':
        return None
    ch = kids[roots[0]]
    if len(ch) != 1 or kids[ch[0]]:
        return None
    return nodes[ch[0]][2]


def check_builder(sheets):
    from probe_eps_range import Many, Unsupported
    bad = ok = skip = 0
    for title, blocks in sheets:
        for n, row, bd in blocks:
            if 'B' not in bd:
                continue
            mat = bd.get('S', (None, None))[1]
            alpha = leaf_alpha(bd['B'][0])
            if alpha is None or not mat or (title, n) in LABEL_ERRATA:
                continue
            expr = alpha.replace('·', '*')
            try:
                got = Many(expr)
            except Unsupported as e:
                print('  %s [%d] psi_0(W_%s): not built yet (%s)' % (title, n, alpha, e))
                skip += 1
                continue
            got = [tuple(c) for c in got] if got else None
            if got == mat:
                ok += 1
                print('  %s [%d] psi_0(W_%s) = %s  ok'
                      % (title, n, alpha, ''.join('(%d,%d,%d)' % c for c in mat)))
            else:
                bad += 1
                print('  %s [%d] psi_0(W_%s)' % (title, n, alpha))
                print('     sheet %s' % ''.join('(%d,%d,%d)' % c for c in mat))
                print('     built %s' % (''.join('(%d,%d,%d)' % c for c in got)
                                         if got else 'parse error'))
    print('C psi_0(Omega_alpha) rows: %d match, %d differ, %d unsupported'
          % (ok, bad, skip))
    return bad


def hydra_of(mat):
    """The matrix drawn the way the sheet draws it: depth x, label the subscript."""
    return render([(i, c[0], lab) for i, (c, lab) in enumerate(zip(mat, labels_of(mat)))])


def check_builder_hydra(sheets):
    """Same rows as check C, but compared as drawings -- this reaches the blocks
    that the sheet draws without typing a matrix underneath."""
    from probe_eps_range import Many, Unsupported
    bad = ok = skip = 0
    for title, blocks in sheets:
        for n, row, bd in blocks:
            if 'B' not in bd or 'S' not in bd or not bd['S'][0]:
                continue
            alpha = leaf_alpha(bd['B'][0])
            if alpha is None or (title, n) in LABEL_ERRATA:
                continue
            try:
                mat = Many(alpha.replace('\u00b7', '*'))
            except Unsupported as e:
                print('  %s [%d] psi_0(W_%s): not built yet (%s)' % (title, n, alpha, e))
                skip += 1
                continue
            got = hydra_of([tuple(c) for c in mat]) if mat else 'parse error'
            want = render(bd['S'][0])
            if got == want:
                ok += 1
                print('  %s [%d] psi_0(W_%s) = %s  ok' % (title, n, alpha, want))
            else:
                bad += 1
                print('  %s [%d] psi_0(W_%s)' % (title, n, alpha))
                print('     sheet %s' % want)
                print('     built %s' % got)
    print('D psi_0(Omega_alpha) drawings: %d match, %d differ, %d unsupported'
          % (ok, bad, skip))
    return bad


# ---- E: the ebp2bms tables against the builder ----

def md_alpha(cell):
    a = cell.strip().strip('$` ')
    for tex, plain in (('\\omega', 'w'), ('\\cdot', '*'), ('\\varepsilon_0', 'psi_0(W)'),
                       ('\\Omega', 'W'), ('\\psi', 'psi'), ('\\Lambda', 'L')):
        a = a.replace(tex, plain)
    a = re.sub(r'\\[a-zA-Z]+', '', a)
    return a.replace('{', '(').replace('}', ')').replace(' ', '')


def md_matrix(cell):
    """The pmatrix runs of one table cell; a run may hold several columns."""
    out = []
    for body in re.findall(r'\\begin\{pmatrix\}(.*?)\\end\{pmatrix\}', cell):
        rows = [[int(v) for v in re.findall(r'-?\d+', r)] for r in body.split('\\cr')]
        out += [tuple(col) for col in zip(*rows)]
    return out


def check_tables():
    from probe_eps_range import Many
    bad = 0
    for name in ('sheet/1/README.md', 'sheet/2/README.md',
                 'sheet/1/README-en.md', 'sheet/2/README-en.md'):
        path = os.path.join(ROOT, 'ebp2bms', name)
        ok = n = 0
        for line in open(path):
            if not line.startswith('| $'):
                continue
            cells = line.strip().strip('|').split('|')
            if len(cells) != 2:
                continue
            mat = md_matrix(cells[1])
            if not mat:
                continue
            n += 1
            got = [tuple(c) for c in (Many(md_alpha(cells[0])) or [])]
            if got == mat:
                ok += 1
            else:
                bad += 1
                print('  %s alpha=%s' % (name, md_alpha(cells[0])))
                print('     table %s' % ''.join('(%d,%d,%d)' % c for c in mat))
                print('     built %s' % ''.join('(%d,%d,%d)' % c for c in got))
        print('  ebp2bms/%-22s %d/%d rows agree with the builder' % (name, ok, n))
    print('E ebp2bms tables: %d rows differ' % bad)
    return bad


def main(path, errata):
    wb = openpyxl.load_workbook(path, data_only=False)
    sheets = [(ws.title, blocks_of(ws)) for ws in wb.worksheets]
    print('%d sheets, %d blocks, %d with a matrix'
          % (len(sheets), sum(len(b) for _, b in sheets),
             sum(1 for _, bs in sheets for _, _, b in bs
                 if b.get('S', (None, None))[1])))
    if errata:
        print('%d typed matrices replaced by the errata table' % apply_errata(sheets))
    print()
    check_reading(sheets)
    print()
    check_order(sheets)
    print()
    check_builder(sheets)
    print()
    check_builder_hydra(sheets)
    print()
    check_tables()


if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if a != '--raw']
    main(args[0] if args else os.path.join(ROOT, '..', 'papers',
                                           'tsskyx-bms-analysis.xlsx'),
         '--raw' not in sys.argv)
