#!/usr/bin/env python3
"""Lean の `Conv3.b2d3`（Dbms3.lean）と Python の `rows3.b2d3`（v13）の突き合わせ。

Lean 側は `Dbms3.olean` が無いので import できない。そこで **Dbms3.lean の本文を
そのまま貼った** 使い捨ての Lean file を作り、末尾で `#eval` に全入力の像を
書き出させる。それを Python の像と行ごとに diff する（Lean の定義を Python で
再実装するのではなく、Lean に計算させた結果を比べる）。

    python3 lean_v13_check.py gen 6 <outdir>      # Lean file と Python の像
    leanman check -C <lean> <outdir>/v13check.lean
    python3 lean_v13_check.py diff <outdir>       # 件数と不一致数

`gen` は `<outdir>/v13check.lean` / `py.txt` を作り、Lean は `<outdir>/lean.txt`
に書き出す。
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rows3                                                  # noqa: E402

LEAN = '/home/koteitan/proofs/dbms/lean/Dbms3.lean'
CHUNK = 200


def enc(M):
    return ' '.join('%d,%d,%d' % tuple(c) for c in M)


def lean_col(c):
    return '(%d,%d,%d)' % tuple(c)


def lean_mat(M):
    return '[' + ', '.join(lean_col(c) for c in M) + ']'


def pick7(seed=12345):
    """7 列の三つ組: v12 と像が違う 290 個 ＋ 縮約が発火する 294 個 ＋ 無作為 5000。

    v13 の 2 条項がいちばん効くところ（v12 との差）と、いちばん壊れやすいところ
    （縮約）を全部入れる。`gen3` は 7 列で 68895 個あるので全数は載せない。
    """
    import random
    G7 = [M for M in rows3.gen3('BMS', 7, zcap=1) if len(M) == 7]
    i13 = [rows3.b2d3n(M) for M in G7]
    rows3.V13['wchain'] = False
    rows3.V13['sibL'] = False
    i12 = [rows3.b2d3(M) for M in G7]
    rows3.V13['wchain'] = True
    rows3.V13['sibL'] = True
    sel = {M for M, a, b in zip(G7, i13, i12) if a[0] != b}
    sel |= {M for M, a in zip(G7, i13) if a[1] > 0}
    rnd = random.Random(seed)
    sel |= set(rnd.sample(G7, 5000))
    return sorted(sel)


def gen(lim, out):
    G = pick7() if lim == 7 else rows3.gen3('BMS', lim, zcap=1)
    with open(os.path.join(out, 'py.txt'), 'w') as f:
        for M in G:
            f.write(enc(rows3.b2d3(M)) + '\n')
    body = open(LEAN, encoding='utf-8').read()
    # 使い捨ての copy では `#guard` は要らない（時間の無駄）
    body = '\n'.join(l for l in body.split('\n') if not l.startswith('#guard'))
    parts = []
    names = []
    for i in range(0, len(G), CHUNK):
        nm = 'inp%d' % (i // CHUNK)
        names.append(nm)
        parts.append('def %s : List (List (ℕ × ℕ × ℕ)) :=\n  [%s]\n'
                     % (nm, ',\n   '.join(lean_mat(M) for M in G[i:i + CHUNK])))
    tail = '''

/-! Python (`tools/dbms/rows3.py` の `b2d3`, v13) との突き合わせ用の使い捨て file。 -/
open TRIO

%s
def inpAll : List (List (ℕ × ℕ × ℕ)) := %s

def encCol (c : ℕ × ℕ × ℕ) : String := s!"{c.1},{c.2.1},{c.2.2}"

def encMat (M : List (ℕ × ℕ × ℕ)) : String :=
  String.intercalate " " (M.map encCol)

#eval show IO Unit from
  IO.FS.writeFile "%s"
    (String.intercalate "\\n" (inpAll.map (fun M => encMat (Conv3.b2d3 M))) ++ "\\n")
''' % ('\n'.join(parts), ' ++ '.join(names),
       os.path.join(out, 'lean.txt'))
    with open(os.path.join(out, 'v13check.lean'), 'w', encoding='utf-8') as f:
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
        gen(int(sys.argv[2]), sys.argv[3])
    else:
        diff(sys.argv[2])
