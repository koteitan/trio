"""`mkt.py` が作る旗つき写し `rows3t.py` に、さらに追記 4 の条項を足して
`rows3u.py` を作る。旗ぜんぶ off で `rows3.b2d3` と像が一致することを確かめること:

    python3 exp/mkt.py && python3 exp/mku.py
    python3 -c "
    import sys; sys.path.insert(0,'<scratch>'); sys.path.insert(0,'<tools/dbms>')
    import rows3, rows3u
    A=sorted(rows3.gen3('BMS',7,zcap=1))
    print(sum(1 for M in A if rows3.b2d3(list(M))!=rows3u.b2d3(list(M))))"
"""
import sys, os
SC = os.environ.get('SCRATCH') or sys.argv[1] if len(sys.argv) > 1 else None
if not SC:
    raise SystemExit('使い方: SCRATCH=<rows3t.py のあるディレクトリ> python3 mku.py')
src = open(os.path.join(SC, 'rows3t.py')).read()

src = src.replace("    'closes_w': False,", """    'closes_w': False,
    'sibbody_nolad0': False,  # 行 1 の影だけを立てた柱の兄弟を本体の横に
    'sibbody_d2': False,      # 同上、ただし兄弟の行 0 が 2 以上のときだけ
    'closes_w2': False,       # 写しの頭 (k,0,0) k<p0 を上位のアンカーと同じに扱う
    'nxtge': False,           # prev==0 の枝だけ「次が自分以上の柱か」で決め直す
    'nxtge_last': False,      # nxtge を after_w / wchain より後に当てる
    'nxtge_shal': False,      # 「次が自分より浅いなら浅い」を最後に上書き
    'nxtge_pure': False,      # 状態を使わず「次が自分以上の深さ」だけ（最後に）
    'nxtge_purebr': False,    # 同上、ただし次が分岐列のときだけ
    'brnext': False,          # 状態を捨て「次が自分以上の分岐列なら深い」（最初に）
    'brnext_only': False,     # 同上、さらに after_w / wchain / closes_hi も止める
""", 1)

old = """    if lad1 and B and (VX['sibbody'] or
                       (VX['sibbody_v0'] and B[0][1] == 0) or
                       (VX['sibbody_noA'] and B[0][1] == 0 and not A)):"""
new = """    if lad1 and B and (VX['sibbody'] or
                       (VX['sibbody_v0'] and B[0][1] == 0) or
                       (VX['sibbody_noA'] and B[0][1] == 0 and not A) or
                       (VX['sibbody_nolad0'] and B[0][1] == 0 and not lad0) or
                       (VX['sibbody_d2'] and B[0][1] == 0 and B[0][0] >= 2)):"""
assert old in src
src = src.replace(old, new, 1)

old = """            _cw = closes_w_ok(st['Mo'], off, p)
            shallow = (st['prev'] == 0) or closes_unit(nxt) or _cw"""
new = """            _cw = closes_w_ok(st['Mo'], off, p)
            if VX['closes_w2'] and nxt is not None and nxt[1] == 0 \\
                    and nxt[2] == 0 and nxt[0] < p[0]:
                # 写しの中では、上位のアンカー (1,1,0) が (k,0,0) に化ける。
                # 行 1 のユニットを閉じる働きは同じなので、同じに扱う。
                _cw = True
            if VX['brnext'] or VX['brnext_only']:
                shallow = not (nxt is not None and is_branch(nxt)
                               and nxt[0] >= p[0])
            elif VX['nxtge']:
                if closes_unit(nxt) or _cw:
                    shallow = True
                elif st['prev'] != 0:
                    shallow = False
                else:
                    shallow = not (nxt is not None and nxt[0] >= p[0])
            else:
                shallow = (st['prev'] == 0) or closes_unit(nxt) or _cw"""
assert old in src
src = src.replace(old, new, 1)

old = """            if st['prev'] == 1 and is_w_col(pv) and (closes_unit(onx) or _cw):"""
new = """            if VX['brnext_only']:
                pass
            elif st['prev'] == 1 and is_w_col(pv) and (closes_unit(onx) or _cw):"""
assert old in src
src = src.replace(old, new, 1)

old = """            if closes_hi_unit(p, onx, pv, pv2, hi, is_repeat(Mo, off)):
                shallow = True"""
new = """            if (not VX['brnext_only']) and closes_hi_unit(
                    p, onx, pv, pv2, hi, is_repeat(Mo, off)):
                shallow = True"""
assert old in src
src = src.replace(old, new, 1)

old = """            base = base_s if shallow else deep
            if TRACE[0]:"""
new = """            if VX['nxtge_shal'] and nxt is not None and nxt[0] < p[0]:
                shallow = True
            if VX['nxtge_last']:
                if closes_unit(nxt) or _cw:
                    shallow = True
                elif st['prev'] != 0:
                    shallow = False
                else:
                    shallow = not (nxt is not None and nxt[0] >= p[0])
            elif VX['nxtge_pure']:
                shallow = (closes_unit(nxt) or _cw
                           or not (nxt is not None and nxt[0] >= p[0]))
            elif VX['nxtge_purebr']:
                shallow = (closes_unit(nxt) or _cw
                           or not (nxt is not None and is_branch(nxt)
                                   and nxt[0] >= p[0]))
            base = base_s if shallow else deep
            if TRACE[0]:"""
assert old in src
src = src.replace(old, new, 1)

open(os.path.join(SC, 'rows3u.py'), 'w').write(src)
print('ok')
