"""G2 段 3: probe6.pkl（段 2 の逆算）を族にまとめて表にする。

族の指紋（5 つ）
  1. `tail2`  破れた A の末尾 2 柱の型（br 分岐列 / anch アンカー / w x w の柱 /
              diag 対角列 / lo0 lo1 その他）
  2. `ms`     破れる m の集合
  3. `head`   conv3 A の**悪い部分の頭** N[r] を出した conv3 の分岐（sh0/sh1/body）
  4. `slot`   T の中で最初に像で有り得なくなる柱が、写しの何番目・写しの中の
              何本目か（`cp`, `src-r`）
  5. `prov`   その柱を出した conv3 の分岐
"""
import sys, collections, pickle
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/g2')
import rows3, provc
from core import show, parse, pim
from rows3 import key
from g2a import ctype, tail2

SC = '/home/koteitan/proofs/dbms/tools/dbms/g2/'
R = pickle.load(open(SC + 'probe6.pkl', 'rb'))
byA = collections.defaultdict(list)
for d in R:
    byA[d['A']].append(d)
for v in byA.values():
    v.sort(key=lambda d: d['m'])

FIVE = [tuple(parse(s, 3)) for s in
        ["(0,0,0)(1,1,1)(2,0,0)(3,1,1)(1,1,1)",
         "(0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,1,0)",
         "(0,0,0)(1,1,1)(2,1,0)(2,1,0)(1,1,0)",
         "(0,0,0)(1,1,1)(2,1,0)(3,1,0)(1,1,0)"]]


def blk(S):
    X = len(S); x = X - 1; Y = len(S[0])
    t = max(y for y in range(Y) if S[x][y] > 0)
    return t, pim(S)[x][t], x - pim(S)[x][t]


def pstr(p):
    return (p[0] + ('' if p[2] is None else ':' + p[2])
            + ('' if not p[3] else '@' + '/'.join(p[3])))


INFO = {}
for A in byA:
    N, PR = provc.b2d3p(list(A))
    t, r, bp = blk(N)
    INFO[A] = (N, PR, t, r, bp, pstr(PR[r]))


def fam(A):
    d0 = byA[A][0]
    N, PR, t, r, bp, head = INFO[A]
    if 'col' not in d0:
        sl, pv = 'なし', '-'
    else:
        sl, pv = d0['src'] - d0['r'], pstr(d0['prov'])
    return (tail2(A), head, pv, sl, tuple(sorted(x['m'] for x in byA[A])))


C = collections.Counter(fam(A) for A in byA)
mem = collections.defaultdict(list)
for A in byA:
    mem[fam(A)].append(A)
for v in mem.values():
    v.sort(key=key)

print('=== 族の表（件数の降順）%d 族 / A %d 個 / 対 %d ==='
      % (len(C), len(byA), len(R)))
print('%3s %-12s %-7s %-18s %-4s %-9s %s'
      % ('件', '末尾2柱', '悪頭', '詰まる柱の出どころ', '写内', 'm', '代表の A'))
for f, n in C.most_common():
    A = mem[f][0]
    d0 = byA[A][0]
    print('%3d %-12s %-7s %-18s %-4s %-9s %s   [k=%d/%d, 写し %s 本目]'
          % (n, f[0], f[1], f[2], str(f[3]), str(f[4]), show(A),
             d0['k'], d0['LT'], str(d0.get('cp'))))

print('\n=== <=5 列の 4 個（G1）がどの族か ===')
fs5 = set()
for A in FIVE:
    f = fam(A)
    fs5.add(f)
    print('  %-34s 族の件数 %d  %s' % (show(A), C[f], str(f)))
print('  -> 4 個と同じ族に入る A: %d 個 / %d' % (sum(C[f] for f in fs5), len(byA)))

print('\n=== まとめ ===')
print('  詰まる柱の写しの中の位置:',
      sorted(collections.Counter(fam(A)[3] for A in byA).items(), key=str))
print('  何番目の写しで詰まるか   :',
      sorted(collections.Counter(byA[A][0].get('cp') for A in byA).items(),
             key=str))
print('  k == r + cp*bp（写しの頭）:',
      sum(1 for A in byA
          if byA[A][0].get('cp') is not None
          and byA[A][0]['k'] == byA[A][0]['r']
          + byA[A][0]['cp'] * byA[A][0]['bp']), '/', len(byA))
print('  悪い部分の頭 N[r] の出どころ:',
      collections.Counter(INFO[A][5] for A in byA).most_common())
print('  詰まる柱の出どころ          :',
      collections.Counter(fam(A)[2] for A in byA).most_common())
print('  詰まる柱の型                :',
      collections.Counter(ctype(byA[A][0].get('col')) for A in byA).most_common())
print('  打ち切り                    :', sum(1 for d in R if d['capped']),
      '/', len(R))
print('  T 全部が像として通る対      :', sum(1 for d in R if 'col' not in d))
