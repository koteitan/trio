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


SIMP = 'shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate'


def far_units(M, s, e, r, v, top):
    """遠い字の語: 字 (a,r,1)、中身の最初が中身のない遠い字 (a+1,r,1)、残りは単位。
    単位 = 荷（行 1 ≤ v の z=0 の木）か、行 1 が v+1 の子のないタイ（節点の下だけ）。
    最上段では最後の子のないタイを 1 個だけ許す（返り値の 2 つ目）。"""
    if M[s][1] != r or M[s][2] != 1:
        return None
    ch = children(M, s, e)
    if not ch or M[ch[0][0]] != (M[s][0] + 1, r, 1) or ch[0][1] - ch[0][0] != 1:
        return None
    rest = ch[1:]
    tie_last = False
    if top and rest and M[rest[-1][0]] == (M[s][0] + 1, v + 1, 0) and rest[-1][1] - rest[-1][0] == 1:
        tie_last = True
        rest = rest[:-1]
    us = []
    for (a, b) in rest:
        c = M[a]
        if c[2] == 0 and c[1] <= v:
            us.append(('some', a, b))
        elif (not top) and c == (M[s][0] + 1, v + 1, 0) and b - a == 1:
            us.append(('none',))
        else:
            return None
    return (us, tie_last)


def far_contents(M, s, e, r, v):
    """遠い字のあとの低い列（荷と、行 1 が v+1 の子つきのタイ）。GzN の okWF の規則で作る。"""
    if M[s][1] != r or M[s][2] != 1:
        return None
    ch = children(M, s, e)
    if not ch or M[ch[0][0]] != (M[s][0] + 1, r, 1) or ch[0][1] - ch[0][0] != 1:
        return None
    items = []
    for (a, b) in ch[1:]:
        c = M[a]
        if c[2] == 0 and c[1] <= v:
            items.append(('load', a, b))
        elif c == (M[s][0] + 1, v + 1, 0):
            items.append(('tie', a, b))
        else:
            return None
    return items


def far_contents_k(M, s, e, r, v, kk):
    """遠い字のあとの低い列（荷と、行 1 が v+τ（1 ≤ τ ≤ kk）の子つきの節点）。GzV / GzW の okWkF の規則で作る。"""
    if M[s][1] != r or M[s][2] != 1:
        return None
    ch = children(M, s, e)
    if not ch or M[ch[0][0]] != (M[s][0] + 1, r, 1) or ch[0][1] - ch[0][0] != 1:
        return None
    items = []
    for (a, b) in ch[1:]:
        c = M[a]
        if c[2] == 0 and c[1] <= v:
            items.append(('load', a, b))
        elif c[2] == 0 and 1 <= c[1] - v <= kk:
            items.append(('node', a, b, c[1] - v))
        else:
            return None
    return items


def okwfk_lean(M, items, v, kk, tac='decide'):
    proof = f'(okWkF_nil {kk} {v})'
    for it in items:
        if it[0] == 'load':
            _, a, b = it
            proof = f'(okWkF_load (k := {kk}) (by {tac}) {proof} {load_mem(M, a, b, v)} rfl)'
        else:
            _, a, b, tau = it
            proof = (f'(okWkF_node (k := {kk}) (τ := {tau}) (by {tac}) (by {tac}) {proof} '
                     f'{gp(M, children(M, a, b), v, [], tau)})')
    return proof


def far_contents_Fr(M, s, e, r, v, kk):
    """遠い字のあとが低い列（荷と段 v+τ（τ ≤ kk）の節点）で、最後が行 1 が字と同じ r の子のない節点（F）の語。GzY.PVF_farW_Fr。"""
    if M[s][1] != r or M[s][2] != 1:
        return None
    ch = children(M, s, e)
    if len(ch) < 2 or M[ch[0][0]] != (M[s][0] + 1, r, 1) or ch[0][1] - ch[0][0] != 1:
        return None
    last = ch[-1]
    if M[last[0]] != (M[s][0] + 1, r, 0) or last[1] - last[0] != 1:
        return None
    items = []
    for (a, b) in ch[1:-1]:
        c = M[a]
        if c[2] == 0 and c[1] <= v:
            items.append(('load', a, b))
        elif c[2] == 0 and 1 <= c[1] - v <= kk:
            items.append(('node', a, b, c[1] - v))
        else:
            return None
    return items


def far_contents_bot(M, s, e, r, v, kk, A, o):
    """遠い字のあとが低い列で、最後が行 1 が v+σ（2 ≤ σ ≤ o、全ての錨 a で σ ≤ a+1）の子のない節点の語。HaA.PVF_farW_bot。"""
    if M[s][1] != r or M[s][2] != 1:
        return None
    ch = children(M, s, e)
    if len(ch) < 2 or M[ch[0][0]] != (M[s][0] + 1, r, 1) or ch[0][1] - ch[0][0] != 1:
        return None
    last = ch[-1]
    c = M[last[0]]
    sig = c[1] - v
    if c[2] != 0 or last[1] - last[0] != 1:
        return None
    if not (2 <= sig <= o and all(sig <= a + 1 for a in A)):
        return None
    items = []
    for (a, b) in ch[1:-1]:
        c = M[a]
        if c[2] == 0 and c[1] <= v:
            items.append(('load', a, b))
        elif c[2] == 0 and 1 <= c[1] - v <= kk:
            items.append(('node', a, b, c[1] - v))
        else:
            return None
    return (items, sig)


def far_contents_F(M, s, e, r, v):
    """遠い字のあとが低い列で、最後が行 1 が v+2 の子のない節点の語（o = 1 なら F）。GzP.GPF_farW_bot2。"""
    if M[s][1] != r or M[s][2] != 1:
        return None
    ch = children(M, s, e)
    if len(ch) < 2 or M[ch[0][0]] != (M[s][0] + 1, r, 1) or ch[0][1] - ch[0][0] != 1:
        return None
    last = ch[-1]
    if M[last[0]] != (M[s][0] + 1, v + 2, 0) or last[1] - last[0] != 1:
        return None
    items = []
    for (a, b) in ch[1:-1]:
        c = M[a]
        if c[2] == 0 and c[1] <= v:
            items.append(('load', a, b))
        elif c == (M[s][0] + 1, v + 1, 0):
            items.append(('tie', a, b))
        else:
            return None
    return items


def okwf_lean(M, items, v):
    proof = f'(okWF_nil {v})'
    for it in items:
        kind, a, b = it[0], it[1], it[2]
        if kind == 'load':
            proof = f'(okWF_load {proof} {load_mem(M, a, b, v)} rfl)'
        elif kind == 'tie' or (kind == 'node' and it[3] == 1):
            proof = f'(okWF_tie {proof} (GF_of_GPF {gp(M, children(M, a, b), v, [], 1)}))'
        else:
            raise Fail('k-node before F word')
    return proof


def load_lit(M, a, b):
    base = M[a][0]
    return lit([(x - base, y, z) for (x, y, z) in M[a:b]])


def load_mem(M, a, b, v):
    return (f'(show ({load_lit(M, a, b)} : TrioSeq) ∈ Wg (2 * {v}) by '
            f'have h := Wg_up (w := 2 * {v}) {tree(M, a)} (by omega); simpa [{SIMP}] using h)')


def units_lean(M, us, v):
    items = []
    proof = f'(RawU_nil {v})'
    for u in reversed(us):
        if u[0] == 'some':
            _, a, b = u
            items.insert(0, f'some ({load_lit(M, a, b)} : TrioSeq)')
            proof = f'(RawU_cons_some {load_mem(M, a, b, v)} rfl {proof})'
        else:
            items.insert(0, 'none')
            proof = f'(RawU_cons_none {proof})'
    return '([' + ', '.join(items) + '] : List (Option TrioSeq))', proof


def uss_lean(M, uss, v):
    lits = []
    proof = f'(RawUs_nil {v})'
    for us in reversed(uss):
        l, p = units_lean(M, us, v)
        lits.insert(0, l)
        proof = f'(RawUs_cons {p} {proof})'
    return '([' + ', '.join(lits) + '] : List (List (Option TrioSeq)))', proof


def side0(A, o):
    return f'(A0 := {lean_list(A)}) (o := {o}) (by decide) (by decide) (by decide)'


def far_items_A(M, s, e, r, v, A, o, allow_F=False):
    """級 (A, o) の遠い語の中身（HaG の okRA）: 荷と段 v+τ（1 ≤ τ ≤ o）の節点。
    allow_F なら最後に行 1 が字と同じ r の子のない節点（F）を許す（返り値の 2 つ目）。"""
    if M[s][1] != r or M[s][2] != 1:
        return None
    ch = children(M, s, e)
    if not ch or M[ch[0][0]] != (M[s][0] + 1, r, 1) or ch[0][1] - ch[0][0] != 1:
        return None
    rest = ch[1:]
    hasF = False
    if allow_F and rest and M[rest[-1][0]] == (M[s][0] + 1, r, 0) and rest[-1][1] - rest[-1][0] == 1:
        hasF = True
        rest = rest[:-1]
    items = []
    for (a, b) in rest:
        c = M[a]
        if c[2] == 0 and c[1] <= v:
            items.append(('load', a, b))
        elif c[2] == 0 and 1 <= c[1] - v <= o:
            items.append(('node', a, b, c[1] - v))
        else:
            return None
    return (items, hasF)


def okra_lean(M, items, v, A, o, ks=None):
    """中身の okRA の証明。ks=None なら上限は o、ks='k' なら fun k hk の中（側条件は omega）。"""
    kk = o if ks is None else ks
    Al = lean_list(A)
    proof = f'(okRA_nil {Al} {kk} {v})'
    for it in items:
        if it[0] == 'load':
            _, a, b = it
            ho = '(by decide)' if ks is None else '(by omega)'
            proof = f'(okRA_load (A0 := {Al}) (o := {kk}) (by decide) {ho} {proof} {load_mem(M, a, b, v)} rfl)'
        else:
            _, a, b, tau = it
            A2 = [x for x in A if x < tau]
            if ks is None:
                sd = '(by decide) (by decide) (by decide) (by decide)'
            else:
                sd = '(by decide) (by omega) (fun a ha => by simp at ha <;> omega) (by omega)'
            proof = (f'(okRA_node (A0 := {Al}) (o := {kk}) (τ := {tau}) {sd} {lean_list(A2)} (by decide) '
                     f'{proof} {gp(M, children(M, a, b), v, A2, tau)})')
    return proof


def okwff_lean(M, items, v):
    proof = f'(okWFkF_nil 1 {v})'
    for it in items:
        kind, a, b = it[0], it[1], it[2]
        if kind == 'load':
            proof = f'(okWFkF_load le_rfl {proof} {load_mem(M, a, b, v)} rfl)'
        else:
            proof = f'(okWFkF_tie {proof} (GF_of_GPF {gp(M, children(M, a, b), v, [], 1)}))'
    return proof


def gp_ra(M, kids, v, A, o):
    """錨つきの中身の一様な経路（HaG）。gp_old が失敗したときに使う。"""
    k = 0
    nl = 0
    if A == [] and o == 1:
        w = f'(PVF_nil1 {v})'
    else:
        w = f'(PVF_nil (A := {lean_list(A)}) (o := {o}) (by decide) (by decide) {v})'
    nf = 0
    fcs = []
    r0 = v + o + 1

    def is_word(i, want_F):
        s0, e0 = kids[i]
        if M[s0][1] != r0 or M[s0][2] != 1:
            return False
        cc = children(M, s0, e0)
        exp = [(M[s0][0] + 1, r0, 1)] + ([(M[s0][0] + 1, r0, 0)] if want_F else [])
        return len(cc) == len(exp) and all(M[a0] == x and b0 - a0 == 1 for (a0, b0), x in zip(cc, exp))
    fcsF = []
    jF = 1
    if len(kids) >= 2 and is_word(0, True):
        while jF < len(kids):
            fcF = far_contents(M, kids[jF][0], kids[jF][1], r0, v)
            if fcF is None:
                break
            fcsF.append(fcF)
            jF += 1
    if fcsF and any(fcsF):
        # F の語（中身なし）のあとに、中身が荷と子つきのタイの遠い語（HaV.PVF_farWF）
        P = f'(OkWsFk_nil {v})'
        for fc in reversed(fcsF):
            P = f'(OkWsFk_cons le_rfl {okwff_lean(M, fc, v)} {P})'
        w = f'(PVF_farWF (A := {lean_list(A)}) (o := {o}) (by decide) (by decide) (by decide) {v} _ {P})'
        k = jF
        nl = jF
        nf = len(kids)
    elif len(kids) >= 2 and is_word(0, True) and is_word(1, False):
        # F の語（中身なし）のあとに n 個の中身なしの遠い語（HaN.PVF_QFn）
        nq = 1
        while nq + 1 < len(kids) and is_word(nq + 1, False):
            nq += 1
        w = f'(PVF_QFn {nq} (A := {lean_list(A)}) (o := {o}) (by decide) (by decide) (by decide) {v})'
        k = nq + 1
        nl = nq + 1
        nf = len(kids)
    while nf < len(kids):
        fi = far_items_A(M, kids[nf][0], kids[nf][1], v + o + 1, v, A, o)
        if fi is None:
            break
        fcs.append(fi[0])
        nf += 1
    if 0 < nf and fcs:
        P = f'(OkWsA_nil {lean_list(A)} {o} {v})'
        for fc in reversed(fcs):
            P = f'(OkWsA_cons le_rfl {okra_lean(M, fc, v, A, o)} {P})'
        w = f'(PVF_farWA {side0(A, o)} {v} _ {P})'
        k = nf
        nl = nf
    if nf < len(kids) and k == 0:
        fF = far_items_A(M, kids[nf][0], kids[nf][1], v + o + 1, v, A, o, allow_F=True)
        if fF is not None and fF[1]:
            Pp = f'(OkWsA_nil {lean_list(A)} k {v})'
            for fc in reversed(fcs):
                Pp = f'(OkWsA_cons le_rfl {okra_lean(M, fc, v, A, o, "k")} {Pp})'
            w = (f'(PVF_farWA_F {side0(A, o)} le_rfl (fun k hk => {Pp}) '
                 f'(fun k hk => {okra_lean(M, fF[0], v, A, o, "k")}))')
            k = nf + 1
            nl = nf + 1
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


def gp(M, kids, v, A, o):
    try:
        return gp_old(M, kids, v, A, o)
    except Fail:
        return gp_ra(M, kids, v, A, o)


def gp_old(M, kids, v, A, o):
    k = 0
    nl = 0
    if A == [] and o == 1:
        w = f'(PVF_nil1 {v})'
    else:
        w = f'(PVF_nil (A := {lean_list(A)}) (o := {o}) (by decide) (by decide) {v})'
    nf = 0
    uss = []
    fcs = []
    use_w = False
    kk = min(A + [o])
    while nf < len(kids):
        fc = far_contents_k(M, kids[nf][0], kids[nf][1], v + o + 1, v, kk)
        if fc is None:
            break
        fu = far_units(M, kids[nf][0], kids[nf][1], v + o + 1, v, False)
        if fu is None:
            use_w = True
        else:
            uss.append(fu[0])
        fcs.append(fc)
        nf += 1
    if nf > 0:
        if use_w:
            # 先頭に続く遠い字と低い列（荷・段 v+τ（τ ≤ k）の子つきの節点）の語（GzV.PVF_farWsk）
            P = f'(OkWsk_nil {kk} {v})'
            for fc in reversed(fcs):
                P = f'(OkWsk_cons le_rfl {okwfk_lean(M, fc, v, kk)} {P})'
            w = f'(PVF_farWsk {side(A, o)} (by decide) (by decide) {v} _ {P})'
        else:
            # 先頭に続く遠い字と単位の語（GzI.PVF_farU）
            L, P = uss_lean(M, uss, v)
            w = f'(PVF_farU {side(A, o)} {v} {L} {P})'
        k = nf
        nl = nf
    tF = None
    fr = None
    if A == [] and nf < len(kids):
        fr = far_contents_Fr(M, kids[nf][0], kids[nf][1], v + o + 1, v, o)
    fb = None
    if fr is None and nf < len(kids):
        fb = far_contents_bot(M, kids[nf][0], kids[nf][1], v + o + 1, v, kk, A, o)
    if fr is None and fb is not None:
        # 遠い字と低い列のあとの段 v+σ（σ ≤ 錨+1）の子のない節点（HaA.PVF_farW_bot）。中身は全ての k ≥ kk で okWk k
        items_b, sig = fb
        Pp = f'(OkWsk_nil k {v})'
        for fc in reversed(fcs):
            Pp = f'(OkWsk_cons le_rfl {okwfk_lean(M, fc, v, "k", "omega")} {Pp})'
        w = (f'(PVF_farW_bot (A := {lean_list(A)}) (o := {o}) (s := {sig}) (k0 := {kk}) '
             + '(by decide) ' * 9 + f'le_rfl (fun k hk => {Pp}) '
             + f'(fun k hk => {okwfk_lean(M, items_b, v, "k", "omega")}))')
        k = nf + 1
        nl = nf + 1
    elif fr is not None:
        # 遠い字と低い列のあとの、行 1 が字と同じ F（GzY.PVF_farW_Fr）。中身は全ての k ≥ o で okWk k
        Pp = f'(OkWsk_nil k {v})'
        for fc in reversed(fcs):
            Pp = f'(OkWsk_cons le_rfl {okwfk_lean(M, fc, v, "k", "omega")} {Pp})'
        w = (f'(PVF_farW_Fr (o := {o}) (by decide) le_rfl (fun k hk => {Pp}) '
             f'(fun k hk => {okwfk_lean(M, fr, v, "k", "omega")}))')
        k = nf + 1
        nl = nf + 1
    elif all(a >= 2 for a in A) and nf < len(kids):
        fF = far_contents_F(M, kids[nf][0], kids[nf][1], v + o + 1, v)
        if fF is not None:
            # 遠い字と低い列のあとの空の F（GzP.GPF_farW_F）。あとに字が続くと PVF が要るので不可
            P = f'(OkWs_nil {v})'
            for fc in reversed(fcs):
                P = f'(OkWs_cons le_rfl {okwf_lean(M, fc, v)} {P})'
            k = nf + 1
            if k < len(kids) and M[kids[k][0]][2] == 1 and M[kids[k][0]][1] == v + o + 1:
                if o >= 2:
                    # 節点の段以下の空の節点は t の持ち上げで動かないので語の述語（GzP.PVF_farW_bot2）
                    w = f'(PVF_farW_bot2A (A := {lean_list(A)}) (o := {o}) (by decide) (by decide) (by decide) le_rfl {P} {okwf_lean(M, fF, v)})'
                    nl = nf + 1
                else:
                    raise Fail('letter after F word')
            else:
                tF = f'(GPF_farW_bot2A (A := {lean_list(A)}) (o := {o}) (by decide) (by decide) (by decide) le_rfl {P} {okwf_lean(M, fF, v)})'
    while tF is None and k < len(kids) and M[kids[k][0]][2] == 1 and M[kids[k][0]][1] == v + o + 1:
        s, e = kids[k]
        w = (f'(PVF_snoc (A := {lean_list(A)}) (o := {o}) (by decide) {w} '
             f'{rl(M, children(M, s, e), v, A, o)})')
        k += 1
        nl += 1
    if tF is not None:
        t = tF
    elif nl > 0:
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
    uss = []
    tie_us = None
    while k < len(ch) and M[ch[k][0]] == (a + 1, v + 1, 1):
        s, e = ch[k]
        fu = far_units(M, s, e, v + 1, v, True)
        if fu is None:
            break
        k += 1
        if fu[1]:
            tie_us = fu[0]
            break
        uss.append(fu[0])
    tie_n = 0
    if tie_us == [] and uss == []:
        # 子のないタイで終わる遠い語のあとに n 個の中身なしの遠い語（HaN.starOK_tieFarN）
        while k < len(ch) and M[ch[k][0]] == (a + 1, v + 1, 1):
            s, e = ch[k]
            cc = children(M, s, e)
            if len(cc) == 1 and M[cc[0][0]] == (a + 2, v + 1, 1) and cc[0][1] - cc[0][0] == 1:
                tie_n += 1
                k += 1
            else:
                break
    tie_tie = False
    if tie_us == [] and uss == [] and tie_n == 0 and k < len(ch) and M[ch[k][0]] == (a + 1, v + 1, 1):
        s, e = ch[k]
        cc = children(M, s, e)
        if (len(cc) == 2 and M[cc[0][0]] == (a + 2, v + 1, 1) and cc[0][1] - cc[0][0] == 1
                and M[cc[1][0]] == (a + 2, v + 1, 0) and cc[1][1] - cc[1][0] == 1):
            # [W_tie, W_tie]（HaT.starOK_tieTie）
            tie_tie = True
            k += 1
    tie_flat = False
    if tie_us == [] and uss == [] and not tie_tie and k < len(ch) and M[ch[k][0]] == (a + 1, v + 1, 1):
        s, e = ch[k]
        cc = children(M, s, e)
        if (len(cc) == 2 and M[cc[0][0]] == (a + 2, v + 1, 1) and cc[0][1] - cc[0][0] == 1
                and M[cc[1][0]] == (a + 2, 0, 0) and cc[1][1] - cc[1][0] == 1):
            # [W_tie] ++ (W_far)^n のあとに遠い字と零列の語（HaP.starOK_tieFarFlat）
            tie_flat = True
            k += 1
    while k < len(ch) and M[ch[k][0]] == (a + 1, v + 1, 1):
        s, e = ch[k]
        words.append(top_forest(M, children(M, s, e), v))
        k += 1
    w = f'(WordsG_nil {v})'
    for f in reversed(words):
        w = f'(WordsG_consT (v := {v}) {f} {w})'
    if tie_tie:
        st = f'(starOK_tieTie (v := {v}) {w})'
    elif tie_flat:
        st = f'(starOK_tieFarFlat {tie_n} (v := {v}) {w})'
    elif tie_n > 0:
        st = f'(starOK_tieFarN {tie_n} (v := {v}) {w})'
    elif tie_us is not None:
        # 先頭に続く遠い字と荷の語、最後の語は最後に子のないタイ（GzJ.starOK_topFarTie）
        L, P = uss_lean(M, uss, v)
        U, PU = units_lean(M, tie_us, v)
        st = (f'(starOK_topFarTie (v := {v}) {L} {P} (by simp [NoTie]) {U} {PU} '
              f'(by simp [NoTie]) {w})')
    elif uss:
        # 先頭に続く遠い字と荷の語（GzJ.starOK_topFar）
        L, P = uss_lean(M, uss, v)
        st = f'(starOK_topFar (v := {v}) {L} {P} (by simp [NoTie]) {w})'
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
                    f'  have h := {p}\n  simpa [{SIMP}] using h\n')
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
               f'import GzJ\nimport GzS\nimport HaJ\nimport HaL\nimport HaP\nimport HaT\nimport HaV\n\nnamespace TRIO\nnamespace {name}\n\n'
               'open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY\n'
               'open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzJ GzM GzN GzP GzS GzU GzV GzW GzY HaA HaC HaD HaE HaF HaG HaJ HaL HaN HaP HaR HaS HaT HaV\n\n')
        open(out, 'w').write(hdr + '\n'.join(body) + f'\nend {name}\nend TRIO\n')
