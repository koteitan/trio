# -*- coding: utf-8 -*-
"""Draw a Bashicu matrix as the hydra it stands for.

This is the "Bashicu Hydra" of Tsskyx's BMS Analysis: one node per column,
hung on the row-0 forest, each node labelled by the Omega subscript that its
upper rows name.  ebp2bms/algorithm/2 reads those rows as

    (x, y, 0) = Omega_y        (x, y, 1) = Omega_w

so a column's label is y when it has no z, and w when it does.  Both readings
are checked against the whole of Tsskyx's sheet by
tools/tsskyx-sheet/check.py.

The picture puts a node at character column i (its position in the matrix) and
at height x_i (its depth in the row-0 forest), which is how the sheet draws it:

    $ python3 tools/bms2bmshydra.py '(0,0,0)(1,1,1)(2,1,0)(3,2,1)'
       w
      1
     w
    0

The one-line form writes the same tree with ^ for a child and + between
siblings, bracketing a node's children when there is more than one.
"""
import re
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from trio import parent


class Unsupported(Exception):
    """A column whose upper rows name a subscript this reading does not do."""


def parse(text):
    """'(0,0,0)(1,1,1)' -> [(0,0,0), (1,1,1)].

    A group without commas is read one digit per row, the way the sheet types
    its matrices, so '(000)(111)' means the same thing.  Stray commas and
    spaces are ignored.
    """
    groups = re.findall(r'\(([^)]*)\)', text)
    if not groups or re.sub(r'\([^)]*\)', '', text).strip():
        return None
    mat = []
    for g in groups:
        parts = [p.strip() for p in g.split(',')] if ',' in g else list(g.strip())
        parts = [p for p in parts if p]
        if not parts or not all(p.isdigit() for p in parts):
            return None
        mat.append(tuple(int(p) for p in parts))
    if len(set(len(c) for c in mat)) != 1:
        return None
    return mat


def label(col):
    """The Omega subscript the column's upper rows name."""
    top = max((y for y in range(1, len(col)) if col[y] > 0), default=0)
    if top == 0:
        return '0'
    if top == 1:
        return str(col[1])
    if top == 2 and col[2] == 1:
        return 'w'
    raise Unsupported('(%s): only the z<2 fragment is read'
                      % ','.join(str(v) for v in col))


def labels_of(mat):
    return [label(c) for c in mat]


def forest(mat):
    """(roots, children) of the row-0 forest."""
    kids = dict((i, []) for i in range(len(mat)))
    roots = []
    for i in range(len(mat)):
        p = parent(mat, 0, i)
        if p is None:
            roots.append(i)
        else:
            kids[p].append(i)
    return roots, kids


def picture(mat):
    """The hydra drawn with column i at character column i and height x_i."""
    labs = labels_of(mat)
    w = max(len(s) for s in labs)
    lines = []
    for x in range(max(c[0] for c in mat), -1, -1):
        row = [' '] * (len(mat) * w)
        for i, c in enumerate(mat):
            if c[0] == x:
                row[i * w:i * w + len(labs[i])] = labs[i]
        lines.append(''.join(row).rstrip())
    return '\n'.join(lines)


def oneline(mat):
    """The same tree as label^child, siblings joined by + inside brackets."""
    labs = labels_of(mat)
    roots, kids = forest(mat)

    def go(i):
        ch = kids[i]
        if not ch:
            return labs[i]
        if len(ch) == 1:
            return '%s^%s' % (labs[i], go(ch[0]))
        return '%s^(%s)' % (labs[i], '+'.join(go(j) for j in ch))
    return '+'.join(go(i) for i in roots)


USAGE = '''\
usage: python3 bms2bmshydra.py <matrix> [--oneline]

  matrix     a Bashicu matrix, as parenthesised columns: '(0,0,0)(1,1,1)'.
             A group without commas is one digit per row, so '(000)(111)'
             is the same matrix. Any number of rows is accepted, but the
             labelling only reads the z<2 fragment of the trio system.
  --oneline  print the tree on one line (^ = child, + = sibling) instead of
             drawing it.

The picture puts one node per column: character column i is the column's
position in the matrix, the height is its x, and the character is the Omega
subscript the upper rows name (y, or w when z = 1).

examples:
  python3 bms2bmshydra.py '(0,0,0)(1,1,1)(2,1,0)(3,2,1)'
  python3 bms2bmshydra.py '(0,0,0)(1,1,1)(1,0,0)(2,1,1)' --oneline
'''


def main(argv):
    args = [a for a in argv if not a.startswith('-')]
    flags = [a for a in argv if a.startswith('-')]
    if not args or set(flags) - {'--oneline'}:
        print(USAGE)
        return 0 if flags and set(flags) <= {'-h', '--help'} else 1
    mat = parse(args[0])
    if mat is None:
        print('cannot read that as a matrix; run --help for the accepted form.')
        return 1
    try:
        print(oneline(mat) if '--oneline' in flags else picture(mat))
    except Unsupported as e:
        print('not read yet: %s' % e)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
