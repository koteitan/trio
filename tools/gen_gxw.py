"""gen_gxu に、タイの下の語（字の中身は荷とタイ）を足した生成器。GxW の BWF / GNF を使う。"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
from gen_gxo import load_rows, subtree_end, children, Fail, lit

def load_item(M, s, v):
    c = M[s]
    if c[2] == 0 and c[1] <= v:
        return f'(Wg_up {tree(M, s)} (by omega)) rfl'
    raise Fail('item %s' % (c,))

def gf_nil(sig, v):
    return f'(GF_nil1 {v})' if sig == 1 else f'(GF_nil (σ := {sig}) (by omega) {v})'

def letter_content(M, kids, v):
    t = f'(GNF_nil {v})'
    for (s, e) in kids:
        c = M[s]
        if c[2] == 0 and c[1] <= v:
            t = f'(GNF_load (u := {v}) {t} {load_item(M, s, v)})'
        elif c[2] == 0 and c[1] == v + 1:
            t = f'(GNF_tie (u := {v}) {t} {node_children(M, children(M, s, e), v, 1)})'
        else:
            raise Fail('content %s' % (c,))
    return t

def node_children(M, kids, v, sig):
    k = 0
    if sig == 1:
        b = f'(BWF_nil {v})'
        nl = 0
        while k < len(kids) and M[kids[k][0]][2] == 1 and M[kids[k][0]][1] == v + 2:
            s, e = kids[k]
            b = f'(BWF_snoc (u := {v}) {b} {letter_content(M, children(M, s, e), v)})'
            k += 1
            nl += 1
        t = f'(GF_of_BWF {b})' if nl > 0 else gf_nil(sig, v)
    else:
        t = gf_nil(sig, v)
    for (s, e) in kids[k:]:
        c = M[s]
        if c[2] == 0 and c[1] > v:
            s2 = c[1] - v
            t = (f'(GF_node (ρ := {sig}) (σ := {s2}) (u := {v}) (by omega) (by omega) {t} '
                 f'{node_children(M, children(M, s, e), v, s2)})')
        elif c[2] == 0:
            t = f'(GF_load (σ := {sig}) (u := {v}) (by omega) {t} {load_item(M, s, v)})'
        else:
            raise Fail('child z %s' % (c,))
    return t

def top_forest(M, kids, v):
    t = f'(TF_nil {v})'
    for (s, e) in kids:
        c = M[s]
        if c[1] == v + 1 and c[2] == 0:
            t = f'(TF_tieG (u := {v}) {t} {node_children(M, children(M, s, e), v, 1)})'
        elif c[2] == 0 and c[1] <= v:
            t = f'(TF_load (u := {v}) {t} {load_item(M, s, v)})'
        else:
            raise Fail('top %s' % (c,))
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
        words.append(top_forest(M, children(M, s, e), v))
        k += 1
    w = f'(WordsG_nil {v})'
    for f in reversed(words):
        w = f'(WordsG_consT (v := {v}) {f} {w})'
    st = f'(starOK_wordsG (v := {v}) {w})'
    for (s2, e2) in ch[k:]:
        c = M[s2]
        if c[2] != 0:
            raise Fail('hang z %s' % (c,))
        st = f'(starOK_hang {st} {tree(M, s2)} rfl)'
    return f'(Wg_of_starOK {st})'

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
    print('ok runs (first 30)', runs[:30])
    print('bad first', bad[:12])
    if out:
        name = out.split('/')[-1].replace('.lean', '')
        hdr = (f'/-\n{name}.lean: tools/gen_gxw.py が生成。タイの下の語を持つシート行。\n-/\n'
               f'import GxW\n\nnamespace TRIO\nnamespace {name}\n\n'
               'open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW\n\n')
        open(out, 'w').write(hdr + '\n'.join(body) + f'\nend {name}\nend TRIO\n')
