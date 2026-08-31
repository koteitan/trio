#!/usr/bin/env python3
"""Lean の `Conv3.b2d3`（`lean/Dbms3.lean`）と Python の `rows3.b2d3`（v14 h1）の
突き合わせ。課題 G4 の `bms2dbms/tools/lean_v13_check.py` と同じやり方。

`Dbms3.olean` はビルドされていないので import できない。そこで **`Dbms3.lean` の
本文をそのまま貼った**使い捨ての Lean file を作り、末尾で `#eval` に全入力の像を
書き出させる。それを Python の像と行ごとに diff する（Lean の定義を Python で
再実装するのではなく、**Lean に計算させた結果**を比べる）。

    python3 l1_check.py gen <in.txt> <outdir>
    leanman check -C /home/koteitan/proofs/dbms/lean <outdir>/l1check.lean
    python3 l1_check.py diff <outdir>

`in.txt` は `l1_sets.py` が作る「1 行 1 行列」の file。
"""
import os
import sys

TOOLS = '/home/koteitan/proofs/dbms/bms2dbms/tools'
sys.path.insert(0, TOOLS)
import rows3                                                   # noqa: E402

LEAN = '/home/koteitan/proofs/dbms/lean/Dbms3.lean'
CHUNK = 200


def read_mats(path):
    out = []
    for line in open(path):
        line = line.strip()
        if not line:
            continue
        out.append(tuple(tuple(int(x) for x in c.split(','))
                         for c in line.split()))
    return out


def enc(M):
    return ' '.join('%d,%d,%d' % tuple(c) for c in M)


def lean_mat(M):
    return '[' + ', '.join('(%d,%d,%d)' % tuple(c) for c in M) + ']'


def gen(inp, out):
    G = read_mats(inp)
    with open(os.path.join(out, 'py.txt'), 'w') as f:
        for M in G:
            f.write(enc(rows3.b2d3(M)) + '\n')
    body = open(LEAN, encoding='utf-8').read()
    # 使い捨ての copy では `#guard` は要らない（時間の無駄）
    body = '\n'.join(l for l in body.split('\n') if not l.startswith('#guard'))
    parts, names = [], []
    for i in range(0, len(G), CHUNK):
        nm = 'inp%d' % (i // CHUNK)
        names.append(nm)
        parts.append('def %s : List (List (ℕ × ℕ × ℕ)) :=\n  [%s]\n'
                     % (nm, ',\n   '.join(lean_mat(M) for M in G[i:i + CHUNK])))
    tail = '''

/-! Python (`bms2dbms/tools/rows3.py` の `b2d3`, v14 h1) との突き合わせ用の使い捨て file。 -/
open TRIO

%s
def inpAll : List (List (ℕ × ℕ × ℕ)) := %s

def encCol (c : ℕ × ℕ × ℕ) : String := s!"{c.1},{c.2.1},{c.2.2}"

def encMat (M : List (ℕ × ℕ × ℕ)) : String :=
  String.intercalate " " (M.map encCol)

#eval show IO Unit from
  IO.FS.writeFile "%s"
    (String.intercalate "\\n" (inpAll.map (fun M => encMat (Conv3.b2d3 M))) ++ "\\n")
''' % ('\n'.join(parts), ' ++ '.join(names), os.path.join(out, 'lean.txt'))
    with open(os.path.join(out, 'l1check.lean'), 'w', encoding='utf-8') as f:
        f.write(body + tail)
    print('inputs', len(G))


def diff(out):
    py = open(os.path.join(out, 'py.txt')).read().rstrip('\n').split('\n')
    ln = open(os.path.join(out, 'lean.txt')).read().rstrip('\n').split('\n')
    if len(py) != len(ln):
        print('LENGTH MISMATCH', len(py), len(ln))
        return
    bad = [i for i, (a, b) in enumerate(zip(py, ln)) if a != b]
    print('compared', len(py), 'mismatches', len(bad))
    for i in bad[:10]:
        print(' line', i, 'py:', py[i], 'lean:', ln[i])


if __name__ == '__main__':
    if sys.argv[1] == 'gen':
        gen(sys.argv[2], sys.argv[3])
    else:
        diff(sys.argv[2])
