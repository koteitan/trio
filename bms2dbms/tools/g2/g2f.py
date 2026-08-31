"""G2 段 6: 段 2（maxpre）と段 5（d2b3 候補との食い違い）を突き合わせて族の表を出す。"""
import sys, collections, pickle
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/g2')
import rows3, provc
from core import show, parse, pim
from rows3 import key
from g2a import ctype, tail2
from g2e import pstr

SC = '/home/koteitan/proofs/dbms/bms2dbms/tools/g2/'
R = pickle.load(open(SC + 'probe6.pkl', 'rb'))
DG = pickle.load(open(SC + 'diag6.pkl', 'rb'))
KS = pickle.load(open(SC + 'kstar6.pkl', 'rb'))
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


def mech(A):
    """締め直した k*（g2g）から見た仕掛け。"""
    d = KS[A]
    if 'col' not in d:
        return 'III 末尾切れ'      # T 全体が像の接頭辞だが、ちょうど止まる像が無い
    if d['src'] == d['r']:
        return 'I 写し頭 ' + d['prov'][0]   # 写しの先頭の柱（影の上昇コピー）
    return 'II 写し途中 %d' % (d['src'] - d['r'])


def fam(A):
    """族の鍵は**直す側から見た**指紋: 食い違いの型 x それを出した分岐 x ずれ。
    仕掛け（写しの頭 / 途中 / 末尾切れ）は説明の欄に回す（写しの中の番号は
    ブロックの長さで動くので鍵に入れない）。"""
    o = DG[A]
    return (o['cls'], pstr(o['prov']) if 'prov' in o else '-',
            str(o.get('delta', '-')))


C = collections.Counter(fam(A) for A in byA)
mem = collections.defaultdict(list)
for A in byA:
    mem[fam(A)].append(A)
for v in mem.values():
    v.sort(key=key)

NAME = {}
for i, (f, n) in enumerate(C.most_common(), 1):
    NAME[f] = 'F%d' % i

print('=== 族の表（件数の降順, %d 族 / A %d 個 / 対 %d） ===' %
      (len(C), len(byA), len(R)))
print('%-4s %-4s %-16s %-22s %-11s %-10s %s'
      % ('族', '件', '食い違い', 'ずれた柱を出した分岐', 'ずれ',
         'm', '代表の A'))
for f, n in C.most_common():
    A = mem[f][0]
    ms = tuple(sorted(x['m'] for x in byA[A]))
    print('%-4s %-4d %-16s %-22s %-11s %-10s %s'
          % (NAME[f], n, f[0], f[1], f[2], str(ms), show(A)))
    t2 = collections.Counter(tail2(x) for x in mem[f])
    msc = collections.Counter(tuple(sorted(y['m'] for y in byA[x]))
                              for x in mem[f])
    mc = collections.Counter(mech(x) for x in mem[f])
    print('      仕掛け %s   末尾2柱 %s   m %s'
          % (dict(mc.most_common(3)), dict(t2.most_common(4)),
             dict(msc.most_common(3))))

print('\n=== <=5 列の 4 個（G1）がどの族か ===')
fs5 = set()
for A in FIVE:
    f = fam(A)
    fs5.add(f)
    print('  %-34s %s  件数 %d' % (show(A), NAME[f], C[f]))
print('  -> 同じ族の A: %d 個 / %d' % (sum(C[f] for f in fs5), len(byA)))
cls5 = set(f[0:2] for f in fs5)
print('  -> 同じ「食い違いの型 x 分岐」の A: %d 個'
      % sum(n for f, n in C.items() if f[0:2] in cls5))
cl5 = set(f[0] for f in fs5)
print('  -> 同じ「食い違いの型」の A: %d 個'
      % sum(n for f, n in C.items() if f[0] in cl5))
