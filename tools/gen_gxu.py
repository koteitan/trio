"""行を「語 + 吊るし」に分解し、GxT の差し込み口 Gof（行 1 の差 σ で添字づけ）で証明項を作る。
中身: 最上段はタイ (·,v+1,0) と荷。タイより下の節は行 1 の差 σ = 行1 − v ≥ 1 を持つ任意の節と荷。"""
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

def node_children(M, kids, v, sig):
    t = gf_nil(sig, v)
    for (s, e) in kids:
        c = M[s]
        if c[2] == 0 and c[1] > v:
            s2 = c[1] - v
            t = (f'(GF_node (ρ := {sig}) (σ := {s2}) (u := {v}) (by omega) (by omega) {t} '
                 f'{node_children(M, children(M, s, e), v, s2)})')
        else:
            t = f'(GF_load (σ := {sig}) (u := {v}) (by omega) {t} {load_item(M, s, v)})'
    return t

def top_forest(M, kids, v):
    t = f'(TF_nil {v})'
    for (s, e) in kids:
        c = M[s]
        if c[1] == v + 1 and c[2] == 0:
            t = f'(TF_tieG (u := {v}) {t} {node_children(M, children(M, s, e), v, 1)})'
        else:
            t = f'(TF_load (u := {v}) {t} {load_item(M, s, v)})'
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
        hdr = (f'/-\n{name}.lean: tools/gen_gxu.py が生成。行 1 の差 σ の節と荷の中身を持つシート行。\n-/\n'
               f'import GxT\n\nnamespace TRIO\nnamespace {name}\n\n'
               'open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT\n\n')
        open(out, 'w').write(hdr + '\n'.join(body) + f'\nend {name}\nend TRIO\n')
