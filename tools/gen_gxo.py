"""行を「語 + 吊るし」に分解し、GxN の SCF の規則で証明項を作る。
中身は森: 錐のタイ (·,v+1,0)（子の森を持つ）と、段 v 以下の根の部分木（荷）。"""
import re, sys

def load_rows(path):
    rows = {}
    for line in open(path):
        f = line.rstrip('\n').split('\t')
        if len(f) < 2 or not f[0].isdigit():
            continue
        m = [tuple(map(int, t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)', f[1])]
        if m:
            rows[int(f[0])] = m
    return rows

class Fail(Exception):
    pass

def subtree_end(M, i):
    a = M[i][0]
    j = i + 1
    while j < len(M) and M[j][0] > a:
        j += 1
    return j

def children(M, i, end):
    a = M[i][0]
    out = []
    j = i + 1
    while j < end:
        if M[j][0] != a + 1:
            raise Fail('gap')
        e = subtree_end(M, j)
        out.append((j, e))
        j = e
    return out

def forest(M, kids, d, v):
    t = f'(SCF_nil {d} {v})'
    for (s, e) in reversed(kids):
        c = M[s]
        if c[1] == v + 1 and c[2] == 0:
            sub = forest(M, children(M, s, e), d + 1, v)
            item = f'(SCF_child (d := {d}) (u := {v}) {sub})'
        elif c[2] == 0 and c[1] <= v:
            item = f'(SCF_load (u := {v}) {d} (Wg_up {tree(M, s)} (by omega)) rfl)'
        else:
            raise Fail('item %s' % (c,))
        t = f'(SCF_seq {item} {t})'
    return t

def tree(M, i):
    a, v, z = M[i]
    if z != 0:
        raise Fail('root z')
    end = subtree_end(M, i)
    ch = children(M, i, end)
    k = 0
    words = []
    while k < len(ch) and M[ch[k][0]] == (a + 1, v + 1, 1):
        s, e = ch[k]
        words.append(forest(M, children(M, s, e), 0, v))
        k += 1
    w = f'(WordsG_nil {v})'
    for f in reversed(words):
        w = f'(WordsG_cons (v := {v}) {f} {w})'
    s = f'(starOK_wordsG (v := {v}) {w})'
    for (s2, e2) in ch[k:]:
        c = M[s2]
        if c[2] != 0:
            raise Fail('hang z %s' % (c,))
        s = f'(starOK_hang {s} {tree(M, s2)} rfl)'
    return f'(Wg_of_starOK {s})'

def lit(M):
    return '[' + ', '.join('(%d, %d, %d)' % c for c in M) + ']'

if __name__ == '__main__':
    rows = load_rows('/home/koteitan/proofs/trio/tmp/fixed-sheet/to-psi-I.tsv')
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    out = sys.argv[3] if len(sys.argv) > 3 else None
    ok, bad, body = [], [], []
    for r in range(lo, hi + 1):
        if r not in rows:
            continue
        M = rows[r]
        try:
            p = 'GxB.Wg0_sub_W0 ' + tree(M, 0)
        except Fail as ex:
            bad.append((r, str(ex)))
            continue
        ok.append(r)
        body.append(f'/-- ★ シート行 {r}。 -/\ntheorem R{r}_mem : ({lit(M)} : TrioSeq) ∈ W 0 := by\n'
                    f'  have h := {p}\n  simpa [shiftr01, rword, rcol] using h\n')
    print('ok', len(ok), 'bad', len(bad))
    runs = []
    for r in ok:
        if runs and r == runs[-1][1] + 1:
            runs[-1][1] = r
        else:
            runs.append([r, r])
    print('ok runs (first 20)', runs[:20])
    print('bad first', bad[:10])
    if out:
        name = out.split('/')[-1].replace('.lean', '')
        hdr = (f'/-\n{name}.lean: tools/gen_gxo.py が生成。錐のタイの森と荷の中身を持つシート行。\n-/\n'
               f'import GxN\n\nnamespace TRIO\nnamespace {name}\n\n'
               'open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN\n\n')
        open(out, 'w').write(hdr + '\n'.join(body) + f'\nend {name}\nend TRIO\n')
