import sys
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()

src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
assert "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')" in src

# ---- experimental flags -------------------------------------------------
src = src.replace("V12 = {", """TRACE = [False]
TLOG = []
VX = {
    'residprev': False,   # 縮約の残余の先頭で st['prev'] を None に戻す
    'anchbr': False,      # アンカー (1,1,0) も分岐列として深い／浅いを選ぶ
    'anchbr_sib': False,  # 同上、ただし sibL が深い側を渡したときだけ
    'sibbody': False,     # 行 1 の影を立てた柱の兄弟を本体の横 dd に付ける
    'sibbody_v0': False,  # 同上、兄弟の先頭が行 1 = 0 のときだけ
    'wch_first': False,   # wchain は「鎖の中で最初の分岐列」のときだけ
    'wch_anyprev': False, # wchain の prev==1 の条件を外す
    'wch_repeat': False,  # wchain は逐語コピーの中では発火しない
    'residprev_w': False, # 残余の頭が「x w」の柱のときだけ prev を戻す
    'sibbody_noA': False, # sibbody_v0 ＋「子を持たない柱に限る」
    'wch_free': False,    # wchain の prev==1 も closes_unit も要らない
    'newterm_w': False,   # 「x w」の柱 (k,0,0) k>=1 でも段の状態をリセット
    'closes_w': False,    # 次が自分以下の深さの「x w」の柱ならユニットを閉じる
}


V12 = {""", 1)

# ---- rename local `src` to avoid clashing with the module-level name ----
src = src.replace("    src = None\n", "    src_ = None\n", 1)
src = src.replace("        src = e[5] if len(e) > 5 else None",
                  "        src_ = e[5] if len(e) > 5 else None", 1)
src = src.replace("sib_ok(off, src, st)", "sib_ok(off, src_, st)")

# ---- anchbr: let ANCHOR enter the branch state machine -----------------
old = """    if is_branch(p):
        nxt = M[1] if len(M) > 1 else nx"""
new = """    _isbr = is_branch(p)
    if not _isbr and tuple(p) == ANCHOR and v >= 1:
        if VX['anchbr']:
            _isbr = True
        elif VX['anchbr_sib'] and base_sd != base_d:
            _isbr = True
    if _isbr:
        st['_pv0'] = st['prev']
        nxt = M[1] if len(M) > 1 else nx"""
assert old in src
src = src.replace(old, new, 1)

# ---- trace on the branch decision --------------------------------------
old = """            base = base_s if shallow else deep
            # P1 `wide0_noprev`: 位置から読んで深くしたときは、深さは像に出るが
            # 1 ビットの状態は 0 のまま置く（`prev == 1` は「ユニットがまだ
            # 閉じていないので深く綴った」の意味で、`after_w` / `wchain` は
            # それを見て発火する）。
            if not (V15['wide0_noprev'] and not shallow
                    and st['prev'] == 0 and _w0):
                st['prev'] = 0 if shallow else 1
        else:
            st['rec'][off] = 'tie'      # 浅い／深いの選択肢が無い
            base = deep"""
new = """            base = base_s if shallow else deep
            if TRACE[0]:
                _w = None
                if st.get('_pv0') == 1 and is_w_col(pv) and closes_unit(onx):
                    _w = 'after_w'
                elif V13['wchain'] and st.get('_pv0') == 1 and closes_unit(onx) \\
                        and wchain_head(Mo, off) is not None:
                    _w = 'wchain j=%d' % wchain_head(Mo, off)
                if closes_hi_unit(p, onx, pv, pv2, hi, is_repeat(Mo, off)):
                    _w = (_w or '') + '+closes_hi'
                TLOG.append(dict(off=off, col=tuple(p), kind='branch',
                                 prev0=st.get('_pv0'), shallow=shallow,
                                 base_s=base_s, base_d=base_d, base_sd=base_sd,
                                 deep=deep, base=base, rule=_w, hi=hi,
                                 closes=closes_unit(nxt), onx=onx, pv=pv))
            if not (V15['wide0_noprev'] and not shallow
                    and st['prev'] == 0 and _w0):
                st['prev'] = 0 if shallow else 1
        else:
            st['rec'][off] = 'tie'      # 浅い／深いの選択肢が無い
            base = deep
            if TRACE[0]:
                TLOG.append(dict(off=off, col=tuple(p), kind='tie',
                                 prev0=st.get('_pv0'), base_s=base_s,
                                 base_d=base_d, base_sd=base_sd, deep=deep,
                                 base=base))"""
assert old in src
src = src.replace(old, new, 1)

# `else: base = base_d` guard must follow the new `_isbr`
src = src.replace("""            base = deep
            if TRACE[0]:
                TLOG.append(dict(off=off, col=tuple(p), kind='tie',
                                 prev0=st.get('_pv0'), base_s=base_s,
                                 base_d=base_d, base_sd=base_sd, deep=deep,
                                 base=base))
    else:
        base = base_d""",
                  """            base = deep
            if TRACE[0]:
                TLOG.append(dict(off=off, col=tuple(p), kind='tie',
                                 prev0=st.get('_pv0'), base_s=base_s,
                                 base_d=base_d, base_sd=base_sd, deep=deep,
                                 base=base))
    else:
        base = base_d""", 1)

# ---- trace emitted columns ---------------------------------------------
old2 = """    cols.append((dd, e1, e2))
    ST = ST[:dd] + ((e1, e2),)"""
new2 = """    cols.append((dd, e1, e2))
    if TRACE[0]:
        TLOG.append(dict(off=off, col=tuple(p), kind='emit', cols=list(cols),
                         base=base, e1=e1, e2=e2, dd=dd, lad0=lad0, lad1=lad1))
    ST = ST[:dd] + ((e1, e2),)"""
assert old2 in src
src = src.replace(old2, new2, 1)

# ---- sibbody: attach the sibling block beside the body, not the shadow --
old3 = """    cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0, st,
               B[0] if B else nx, oA)
    cB = conv3(B, d, LS, FA, (v, s2), (e1, e2), False, False, st, nx, oB)
    return cols + cA + cB"""
new3 = """    cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0, st,
               B[0] if B else nx, oA)
    dB = d
    if lad1 and B and (VX['sibbody'] or
                       (VX['sibbody_v0'] and B[0][1] == 0) or
                       (VX['sibbody_noA'] and B[0][1] == 0 and not A)):
        dB = dd
    cB = conv3(B, dB, LS, FA, (v, s2), (e1, e2), False, False, st, nx, oB)
    return cols + cA + cB"""
assert old3 in src
src = src.replace(old3, new3, 1)

# ---- wchain guards ------------------------------------------------------
old5 = """            elif V13['wchain'] and st['prev'] == 1 and closes_unit(onx):
                j = wchain_head(Mo, off)
                if j is not None:
                    shallow = not (hi and not (_p0(Mo, j) == 0))"""
new5 = """            elif (V13['wchain'] and (VX['wch_free'] or (closes_unit(onx)
                    and (st['prev'] == 1 or VX['wch_anyprev'])))):
                j = wchain_head(Mo, off)
                if j is not None and VX['wch_first'] and any(
                        is_branch(Mo[t]) for t in range(j + 1, off)):
                    j = None
                if j is not None and VX['wch_repeat'] and is_repeat(Mo, off):
                    j = None
                if j is not None:
                    shallow = not (hi and not (_p0(Mo, j) == 0))"""
assert old5 in src
src = src.replace(old5, new5, 1)

# ---- residprev ----------------------------------------------------------
old4 = """    out = []
    while rest:
        m0 = rest[0][0]"""
new4 = """    out = []
    if VX['residprev'] or (VX['residprev_w'] and rest and rest[0][1] == 0):
        st['prev'] = None
    while rest:
        m0 = rest[0][0]"""
assert old4 in src
src = src.replace(old4, new4, 1)


# ---- newterm_w / closes_w ----------------------------------------------
src = src.replace("""def is_branch(c):""", """def closes_w_ok(Mo, off, p):
    \"\"\"次の柱が「自分より浅い x w 柱で、その親も x w 柱」ならユニットを閉じる。
    W_(w^2) 系（hi_block）の中でだけ。\"\"\"
    if not VX['closes_w']:
        return False
    j = off + 1
    if j >= len(Mo):
        return False
    c = Mo[j]
    if not (c[1] == 0 and c[2] == 0 and c[0] >= 1 and c[0] < p[0]):
        return False
    q = par0(Mo, j)
    if q < 0 or not is_w_col(Mo[q]):
        return False
    return hi_block(Mo, off)


def opens_sub(Mo, off):
    \"\"\"この「x w」柱が部分木を開くか（次の柱が自分より深いか）。\"\"\"
    return off + 1 < len(Mo) and Mo[off + 1][0] > Mo[off][0]


def closes2(p, nxt, hi=False):
    return closes_unit(nxt)


def is_branch(c):""", 1)
assert 'def closes2(' in src

o = """    if V12['newterm'] and p[0] == 0:
        st['prev'] = None"""
n = """    if V12['newterm'] and p[0] == 0:
        st['prev'] = None
    if VX['newterm_w'] and is_w_col(p) and opens_sub(st['Mo'], off):
        st['prev'] = None"""
assert o in src
src = src.replace(o, n, 1)

o = "            shallow = (st['prev'] == 0) or closes_unit(nxt)"
assert o in src
src = src.replace(o, """            _cw = closes_w_ok(st['Mo'], off, p)
            shallow = (st['prev'] == 0) or closes_unit(nxt) or _cw""", 1)

o = "            if st['prev'] == 1 and is_w_col(pv) and closes_unit(onx):"
assert o in src
src = src.replace(o, "            if st['prev'] == 1 and is_w_col(pv) and (closes_unit(onx) or _cw):", 1)

o = """            elif (V13['wchain'] and (VX['wch_free'] or (closes_unit(onx)
                    and (st['prev'] == 1 or VX['wch_anyprev'])))):"""
assert o in src
src = src.replace(o, """            elif (V13['wchain'] and (VX['wch_free'] or ((closes_unit(onx) or _cw)
                    and (st['prev'] == 1 or VX['wch_anyprev'])))):""", 1)


open('/tmp/claude-1000/-home-koteitan-proofs-dbms/ebd5ffaf-97c2-45bc-92a0-5391fe3b1a6d/scratchpad/rows3t.py', 'w').write(src)
print('ok')
