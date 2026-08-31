# (L-ROT): T = A ++ Q^n ++ Q[0..j] で、的 t=|A|+n|Q|+j の親 c から
#          窓 V = T[c+1 .. t-1] が「Q の巡回窓」かを実測する。
import sys, itertools
sys.path.insert(0, 'tools')
from trio import parent

def srow(S, j):
    c = S[j]
    return 2 if c[2] > 0 else (1 if c[1] > 0 else 0)

def cyc(Q, y, L):           # Q を y だけ回した先頭 L 個
    m = len(Q)
    return [Q[(y + k) % m] for k in range(L)]

def gen_Q(maxlen, maxv):
    for L in range(1, maxlen + 1):
        for cols in itertools.product(
                [(a, b, c) for a in range(maxv + 1) for b in range(a + 1)
                           for c in range(min(b, 1) + 1)], repeat=L):
            Q = list(cols)
            r0 = Q[0][0]
            if any(q[0] < r0 for q in Q):   # hr0 Q（根が最浅）
                continue
            yield Q

AS = [[], [(0,0,0)], [(0,0,0),(1,1,0)], [(0,0,0),(1,1,1)],
      [(2,0,0)], [(0,0,0),(2,2,1)], [(1,1,0),(0,0,0)], [(3,3,1),(1,0,0)]]

cnt = dict(tot=0, rotY=0, rotN=0, inA=0, orph=0, subw=0, skipQ=0)
bad = []
srowtab = {}
for Q in gen_Q(3, 3):
    m = len(Q)
    for A in AS:
        for n in range(1, 4):
            for j in range(m):
                T = A + Q * n + Q[:j+1]
                t = len(T) - 1
                s = srow(T, t)
                c = parent(T, s, t)
                cnt['tot'] += 1
                srowtab[s] = srowtab.get(s, 0) + 1
                if c is None:
                    cnt['orph'] += 1;  continue          # 孤児＝無料
                if c < len(A):
                    cnt['inA'] += 1;   continue          # 残差（親が A）
                V = T[c+1:t]
                off = (c - len(A)) % m                   # 親の Q 内オフセット
                y = (off + 1) % m
                if V == cyc(Q, y, len(V)):
                    cnt['rotY'] += 1
                    if len(V) < m and c - len(A) >= n*m: cnt['subw'] += 1
                else:
                    cnt['rotN'] += 1
                    if len(bad) < 4: bad.append((Q, A, n, j, s, c, V))
print("分母", cnt['tot'], " srow別", srowtab)
print("  孤児(無料)      ", cnt['orph'])
print("  親が A（残差）  ", cnt['inA'])
print("  ✅ V は Q の巡回窓", cnt['rotY'], f"({100*cnt['rotY']/max(1,cnt['rotY']+cnt['rotN']):.4f}% of 非残差)")
print("  ⛔ 巡回窓でない  ", cnt['rotN'])
for b in bad: print("   ex", b)
