"""G2 段 3: probe6.pkl を族にまとめて表にする。"""
import sys, collections, pickle
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/g2')
from core import show
from rows3 import key
from g2a import ctype, tail2

SC = '/home/koteitan/proofs/dbms/tools/dbms/g2/'
R = pickle.load(open(SC + 'probe6.pkl', 'rb'))
byA = collections.defaultdict(list)
for d in R:
    byA[d['A']].append(d)
for v in byA.values():
    v.sort(key=lambda d: d['m'])

FIVE = set()
for s in ["(0,0,0)(1,1,1)(2,0,0)(3,1,1)(1,1,1)",
          "(0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,1,0)",
          "(0,0,0)(1,1,1)(2,1,0)(2,1,0)(1,1,0)",
          "(0,0,0)(1,1,1)(2,1,0)(3,1,0)(1,1,0)"]:
    from core import parse
    FIVE.add(tuple(parse(s, 3)))


def slot(d):
    """詰まる柱が写しの何番目・写しの中の何本目か。"""
    if 'col' not in d:
        return ('全部いける', None)
    return (d['cp'], d['src'] - d['r'])


def prov(d):
    if 'prov' not in d:
        return '-'
    k, off, why, ctx = d['prov']
    s = k + ('' if why is None else ':' + why)
    if ctx:
        s += '@' + '/'.join(ctx)
    return s


def fam(A):
    ds = byA[A]
    d0 = ds[0]                      # いちばん小さい m の破れ
    return (tail2(A), prov(d0), slot(d0)[1],
            tuple(sorted(x['m'] for x in ds)))


C = collections.Counter(fam(A) for A in byA)
print('=== 族の表（件数の降順） ===')
print('%-4s %-14s %-18s %-5s %-10s %s' %
      ('件', '末尾2柱', '詰まる柱の出どころ', '写内', '破れる m', '代表の A'))
reps = {}
for f, n in C.most_common():
    As = sorted([A for A in byA if fam(A) == f], key=key)
    reps[f] = As
    d0 = byA[As[0]][0]
    print('%-4d %-14s %-18s %-5s %-10s %s   [T の %d/%d 柱まで像]'
          % (n, f[0], f[1], str(f[2]), str(f[3]), show(As[0]),
             d0['k'], d0['LT']))
print()
print('=== <=5 列の 4 個がどの族か ===')
for A in sorted(FIVE, key=key):
    f = fam(A)
    print('  %-34s -> 族 %s  (件数 %d)' % (show(A), str(f), C[f]))
print()
n5 = sum(C[fam(A)] for A in set(fam(A) for A in FIVE) and
         {f: 1 for f in set(fam(A) for A in FIVE)})
fs5 = set(fam(A) for A in FIVE)
print('  4 個と同じ族に入る A: %d 個 / 88' % sum(C[f] for f in fs5))
print()
print('=== 詰まる柱の位置のまとめ ===')
print('  写しの中の何本目か:',
      sorted(collections.Counter(slot(byA[A][0])[1] for A in byA).items(),
             key=lambda t: (t[0] is None, t[0])))
print('  何番目の写しか  :',
      sorted(collections.Counter(slot(byA[A][0])[0] for A in byA).items(),
             key=lambda t: str(t[0])))
print('  出どころ        :',
      collections.Counter(prov(byA[A][0]) for A in byA).most_common())
print('  詰まる柱の型    :',
      collections.Counter(ctype(byA[A][0].get('col')) for A in byA).most_common())
print('  もとの柱 A[off] :',
      collections.Counter(ctype(byA[A][0].get('ocol')) for A in byA).most_common())
print('  打ち切り        :', sum(1 for d in R if d['capped']), '/', len(R))
