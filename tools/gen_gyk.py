"""錨の列つきの子の述語（GyK の GPF / PVF / RLF）で証明項を作る生成器。

節点の子の並び gp(A, o): 先頭の字（行 1 が v+o+1 の z=1）は語、以降は節点と荷。
字の中身 rl(A, o): 荷と、行 1 の差 τ ≤ o+1 の節点（τ = o+1 が F）。字の中身の中の字は未対応。
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
from gen_gxo import load_rows, subtree_end, children, Fail, lit


def lean_list(A):
    return '[' + ', '.join(str(a) for a in A) + ']'


def side(A, o):
    L = lean_list(A)
    return f'(A := {L}) (o := {o}) (by decide) (by decide) (by decide)'


def load_item(M, s, v):
    c = M[s]
    if c[2] == 0 and c[1] <= v:
        return f'(Wg_up {tree(M, s)} (by omega)) rfl'
    raise Fail('item %s' % (c,))


def is_far(M, s, e, r):
    """遠い語: 行 1 が r の字で、中身が同じ行 1 の中身のない字 1 個だけ。"""
    return e - s == 2 and M[s][1] == r and M[s][2] == 1 and M[s + 1] == (M[s][0] + 1, r, 1)


def gp(M, kids, v, A, o):
    k = 0
    nl = 0
    if A == [] and o == 1:
        w = f'(PVF_nil1 {v})'
    else:
        w = f'(PVF_nil (A := {lean_list(A)}) (o := {o}) (by decide) (by decide) {v})'
    nf = 0
    while nf < len(kids) and is_far(M, kids[nf][0], kids[nf][1], v + o + 1):
        nf += 1
    if nf > 0:
        # 先頭に続く遠い語（GzF.PVF_farR）
        w = f'(PVF_farR {side(A, o)} {v} {nf})'
        k = nf
        nl = nf
    while k < len(kids) and M[kids[k][0]][2] == 1 and M[kids[k][0]][1] == v + o + 1:
        s, e = kids[k]
        w = (f'(PVF_snoc (A := {lean_list(A)}) (o := {o}) (by decide) {w} '
             f'{rl(M, children(M, s, e), v, A, o)})')
        k += 1
        nl += 1
    if nl > 0:
        t = f'(GPF_of_PVF {w})'
    elif A == [] and o == 1:
        t = f'(GPF_nil1 {v})'
    else:
        t = f'(GPF_nil (A := {lean_list(A)}) (o := {o}) (by decide) (by decide) {v})'
    for (s, e) in kids[k:]:
        c = M[s]
        if c[2] == 0 and c[1] > v:
            tau = c[1] - v
            A2 = [a for a in A if a < tau]
            t = (f'(GPF_node {side(A, o)} (b := {v}) (τ := {tau}) {lean_list(A2)} (by decide) {t} '
                 f'{gp(M, children(M, s, e), v, A2, tau)})')
        elif c[2] == 0:
            t = f'(GPF_load {side(A, o)} (b := {v}) {t} {load_item(M, s, v)})'
        else:
            raise Fail('child z %s' % (c,))
    return t


def rl(M, kids, v, A, o):
    t = f'(RLF_nil {side(A, o)} {v})'
    for (s, e) in kids:
        c = M[s]
        if c[2] == 0 and c[1] <= v:
            t = f'(RLF_load {side(A, o)} (b := {v}) {t} {load_item(M, s, v)})'
        elif c[2] == 0 and c[1] - v <= o + 1:
            tau = c[1] - v
            A2 = [a for a in [o] + A if a < tau]
            t = (f'(RLF_child {side(A, o)} (b := {v}) (τ := {tau}) {lean_list(A2)} (by decide) '
                 f'(by decide) {t} {gp(M, children(M, s, e), v, A2, tau)})')
        else:
            raise Fail('content %s' % (c,))
    return t


def top_forest(M, kids, v):
    t = f'(TF_nil {v})'
    for (s, e) in kids:
        c = M[s]
        if c[1] == v + 1 and c[2] == 0:
            t = f'(TF_tieG (u := {v}) {t} (GF_of_GPF {gp(M, children(M, s, e), v, [], 1)}))'
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
    nf = 0
    while k < len(ch) and M[ch[k][0]] == (a + 1, v + 1, 1):
        s, e = ch[k]
        if nf == k and is_far(M, s, e, v + 1):
            nf += 1  # 先頭に続く遠い語（GzF.starOK_farN）
        else:
            words.append(top_forest(M, children(M, s, e), v))
        k += 1
    w = f'(WordsG_nil {v})'
    for f in reversed(words):
        w = f'(WordsG_consT (v := {v}) {f} {w})'
    if nf > 0:
        st = f'(starOK_farN (v := {v}) {nf} {w})'
    else:
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
    only = set(int(x) for x in sys.argv[4].split(',')) if len(sys.argv) > 4 else None
    ok, bad, body = [], [], []
    for r in range(lo, hi + 1):
        if r not in rows or (only is not None and r not in only):
            continue
        M = rows[r]
        try:
            roots = [i for i in range(len(M)) if M[i][0] == 0]
            p = tree(M, roots[0])
            for r0 in roots[1:]:
                p = f'(Wg_app {p} {tree(M, r0)} (by omega) (by intro p _; simp [entry]))'
            p = 'GxB.Wg0_sub_W0 ' + p
        except Fail as ex:
            bad.append((r, str(ex)))
            continue
        ok.append(r)
        body.append(f'/-- ★ シート行 {r}。 -/\ntheorem R{r}_mem : ({lit(M)} : TrioSeq) ∈ W 0 := by\n'
                    f'  have h := {p}\n  simpa [shiftr01, rword, rcol, farR] using h\n')
    print('ok', len(ok), 'bad', len(bad))
    runs = []
    for r in ok:
        if runs and r == runs[-1][1] + 1:
            runs[-1][1] = r
        else:
            runs.append([r, r])
    print('ok runs (first 40)', runs[:40])
    from collections import Counter
    print('bad reasons', Counter(b[1] for b in bad).most_common(8))
    if out:
        name = out.split('/')[-1].replace('.lean', '')
        hdr = (f'/-\n{name}.lean: tools/gen_gyk.py が生成。錨の列つきの子の述語で証明するシート行。\n-/\n'
               f'import GzF\n\nnamespace TRIO\nnamespace {name}\n\n'
               'open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY\n'
               'open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF\n\n')
        open(out, 'w').write(hdr + '\n'.join(body) + f'\nend {name}\nend TRIO\n')
