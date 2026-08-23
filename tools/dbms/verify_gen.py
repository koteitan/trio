"""シート外の行列で変換規則を検証する。

種（対角行列）から展開を繰り返して BMS 標準形を集め、変換器について
  (a) 出力が DBMS 標準形か
  (b) 単射か
  (c) 順序を保つか（BMS の順序と DBMS の順序が一致）
  (d) 極限行列 M について convert(M[n]) < convert(M[n+1]) < convert(M) か
を確かめる。(d) はシートを一切使わない必要条件。
"""
import sys, os, itertools, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import parse, show, expand, isstd, cmpmat, diag
import rule as R

Y = 3


def gen(seeds, rounds=5, ns=(0, 1, 2, 3, 4, 5), cap=60000, maxcols=40):
    seen = set()
    frontier = list(seeds)
    for m in frontier:
        seen.add(m)
    for _ in range(rounds):
        nxt = []
        for m in frontier:
            if not m or all(v == 0 for v in m[-1]):
                continue
            for n in ns:
                try:
                    e = expand(m, n)
                except Exception:
                    continue
                if len(e) > maxcols or e in seen:
                    continue
                seen.add(e); nxt.append(e)
                if len(seen) >= cap:
                    return sorted(seen, key=len)
        frontier = nxt
        if not frontier:
            break
    return sorted(seen, key=len)


def seeds():
    seeds = [diag('BMS', k, Y) for k in range(1, 10)]
    seeds += [parse(s, Y) for s in (
        '(0,0,0)(1,1,1)(2,2,1)(3,2,0)(4,3,1)',
        '(0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)(5,1,0)(6,2,1)',
        '(0,0,0)(1,1,1)(2,1,1)(2,1,0)(2,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(4,2,0)(4,1,0)',
        '(0,0,0)(1,1,1)(2,1,0)(3,2,0)(4,2,0)(4,1,0)(5,2,0)(6,2,0)',
        '(0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)(5,1,0)(6,2,1)(7,2,0)',
        '(0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,0,0)(2,1,0)',
        '(0,0,0)(1,1,1)(2,1,0)(3,2,0)(4,2,0)(3,2,0)(4,1,0)(5,2,0)',
        '(0,0,0)(1,1,1)(1,1,0)(2,2,1)(3,2,0)(4,3,1)(5,3,0)',
        '(0,0,0)(1,1,1)(2,2,1)(3,3,1)(4,3,0)(5,4,1)',
        '(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(2,0,0)',
        '(0,0,0)(1,1,1)(2,1,1)(2,1,0)(2,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(4,2,0)(4,1,0)(4,1,0)',
        '(0,0,0)(1,1,1)(2,1,0)(3,2,0)(4,2,0)(4,1,0)(5,2,0)(6,1,0)(7,1,0)',
        '(0,0,0)(1,1,1)(2,1,0)(3,2,0)(4,3,0)(5,3,0)(3,2,0)',
        '(0,0,0)(1,1,1)(2,1,0)(3,2,1)(1,1,0)(2,2,1)(3,2,0)(4,3,1)',
        '(0,0,0)(1,1,1)(2,2,1)(3,2,0)(4,3,1)(5,3,0)(6,4,1)',
        '(0,0,0)(1,1,1)(2,1,1)(3,2,2)(4,2,1)(5,3,2)',
        '(0,0,0)(1,1,1)(2,1,0)(3,1,0)(2,1,0)(3,1,0)(1,1,0)(2,2,1)(3,2,0)(4,2,0)(3,2,0)(4,1,0)(3,1,0)',
        '(0,0,0)(1,1,1)(2,1,0)(3,2,0)(4,2,0)(3,1,0)(4,2,0)(5,2,0)(4,1,0)',
    )]
    return [m for m in seeds if isstd(m, 'BMS')]


def main():
    ms = gen(seeds())
    print('生成した BMS 標準形 %d 個（最大 %d 列）' % (ms, max(len(m) for m in ms))
          if False else '生成した BMS 標準形 %d 個（最大 %d 列）'
          % (len(ms), max(len(m) for m in ms)))
    conv = {}
    bad = []
    for m in ms:
        try:
            g = R.convert(m, Y)
        except Exception as e:
            bad.append(('例外', m, repr(e))); continue
        if not isstd(g, 'DBMS'):
            bad.append(('非標準形', m, show(g, 1)))
        conv[m] = g
    print('(a) 非標準形/例外: %d 件' % len(bad))
    for t, m, g in bad[:3]:
        print('    %s %s -> %s' % (t, show(m, 1), g))

    inv = {}
    dup = 0
    for m, g in conv.items():
        if g in inv:
            dup += 1
            if dup <= 3:
                print('    衝突 %s と %s -> %s' % (show(inv[g], 1), show(m, 1), show(g, 1)))
        inv[g] = m
    print('(b) 単射でない対: %d 件' % dup)

    keys = list(conv)
    random.seed(1)
    pairs = [(a, b) for a, b in itertools.combinations(random.sample(keys, min(500, len(keys))), 2)]
    viol = 0
    for a, b in pairs:
        s1 = cmpmat(a, b); s2 = cmpmat(conv[a], conv[b])
        if (s1 > 0) != (s2 > 0) or (s1 == 0) != (s2 == 0):
            viol += 1
            if viol <= 2:
                print('    順序違反 %s vs %s' % (show(a, 1), show(b, 1)))
    print('(c) 順序違反: %d / %d 対' % (viol, len(pairs)))

    lim = mono = 0
    for m in keys:
        if not m or all(v == 0 for v in m[-1]):
            continue
        lim += 1
        prev = None; okm = True
        for n in range(1, 5):
            try:
                e = R.convert(expand(m, n), Y)
            except Exception:
                okm = False; break
            if cmpmat(e, conv[m]) >= 0:
                okm = False; break
            if prev is not None and cmpmat(prev, e) >= 0:
                okm = False; break
            prev = e
        if okm:
            mono += 1
        elif lim - mono <= 2:
            print('    展開が単調でない %s' % show(m, 1))
    print('(d) 極限 %d 個中、展開が単調増加かつ上限未満: %d 個' % (lim, mono))


if __name__ == '__main__':
    main()
