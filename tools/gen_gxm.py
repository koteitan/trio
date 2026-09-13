"""行を「語 + 吊るし」に分解し、GxL の補題で証明項を作る。
中身は頭の直上の単位（錐のタイ (1,v+1,0) か、段 v 以下の荷）だけを扱う。"""
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

def tree(M, i):
    """M[i] = (a, v, 0) を根とする部分木の Wg (2v) の証明項。"""
    a, v, z = M[i]
    if z != 0:
        raise Fail('root z')
    end = subtree_end(M, i)
    ch = children(M, i, end)
    k = 0
    words = []
    while k < len(ch) and M[ch[k][0]] == (a + 1, v + 1, 1):
        s, e = ch[k]
        units = []
        for (s2, e2) in children(M, s, e):
            c = M[s2]
            if c == (a + 2, v + 1, 0) and e2 == s2 + 1:
                units.append(None)
            elif c[2] == 0 and c[1] <= v:
                units.append((tree(M, s2), c[1]))
            else:
                raise Fail('unit %s' % (c,))
        words.append(units)
        k += 1
    raw = f'(RawU_nil {v})'
    wterm = f'(WordsOK_nil {v})'
    for units in reversed(words):
        r = f'(RawU_nil {v})'
        for u in reversed(units):
            if u is None:
                r = f'(RawU_cons_none (v := {v}) {r})'
            else:
                t, j = u
                r = f'(RawU_cons_some (v := {v}) (Wg_up {t} (by omega)) rfl {r})'
        wterm = f'(WordsOK_cons (v := {v}) {r} {wterm})'
    s = f'(starOK_words (v := {v}) {wterm})'
    for (s2, e2) in ch[k:]:
        c = M[s2]
        if c[2] != 0:
            raise Fail('hang z %s' % (c,))
        s = f'(starOK_hang {s} {tree(M, s2)} rfl)'
    return f'(Wg_of_starOK {s})'

def row_proof(M):
    t = tree(M, 0)
    assert t.startswith('(Wg_of_starOK ')
    return 'GxB.Wg0_sub_W0 ' + t

def lit(M):
    return '[' + ', '.join('(%d, %d, %d)' % c for c in M) + ']'

if __name__ == '__main__':
    rows = load_rows('/home/koteitan/proofs/trio/tmp/fixed-sheet/to-psi-I.tsv')
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    out = sys.argv[3] if len(sys.argv) > 3 else None
    ok, bad = [], []
    body = []
    for r in range(lo, hi + 1):
        if r not in rows:
            continue
        M = rows[r]
        try:
            p = row_proof(M)
        except Fail as ex:
            bad.append((r, str(ex)))
            continue
        ok.append(r)
        body.append(f'/-- ★ シート行 {r}。 -/\ntheorem R{r}_mem : ({lit(M)} : TrioSeq) ∈ W 0 := by\n'
                    f'  have h := {p}\n  simpa [unitsC, unitC, rword, rcol, shiftr01] using h\n')
    print('ok', len(ok), 'bad', len(bad))
    print('bad first', bad[:15])
    if out:
        hdr = ('/-\nGxM.lean: tools/gen_gxm.py が生成。頭の直上の単位だけの中身を持つシート行。\n-/\n'
               'import GxL\n\nnamespace TRIO\nnamespace GxM\n\nopen Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL\n\n')
        open(out, 'w').write(hdr + '\n'.join(body) + '\nend GxM\nend TRIO\n')
        print('rows', ok[0] if ok else None, '..', ok[-1] if ok else None)
