# -*- coding: utf-8 -*-
"""課題 R39: **`rsum` の破れは `B` を切れば回避できるか。**

§R38 で `WCat` の届かない 36% のうち **76% は `rsum` が `B` 内部で破れている**
（B の根が B 自身の最浅ですらない）と分かった。

`rsum A B : ∀ p ∈ A ++ B, B[0].1 <= p.1`

そこで **B を「最浅の列」で切って `W_add` を繰り返す**:

    B = B1 ++ B2   （B2 は B の最浅の列から始まる）
    A ++ B = (A ++ B1) ++ B2
    `rsum (A ++ B1) B2` は B2 の根が最浅なので**成り立ちやすい**

これが効けば、要るのは新しい補題ではなく **`W_add` の使い方**だけになる。
効かなければ、`rsum` を本当に緩める補題が要る。

⚠ 退化検査: 「切って届いた」が、切らずに届く事例と同じでないこと。
"""
import sys, random
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
from r60 import why2, lev0, wadd_ok
from r49 import has_parent


def cat_direct(A, B):
    """切らずに届くか（(C10)(C11) ＋ 7 本の証明書）。"""
    if A == B:
        return 'C10'
    if lev0(B) <= lev0(A) and wadd_ok(A, B):
        return 'C11'
    return why2(A + B)


def cat_split(A, B, d=3):
    """**B を最浅の列で切って `W_add` を繰り返す**（深さ d まで）。"""
    r = cat_direct(A, B)
    if r:
        return r
    if d <= 0 or len(B) < 2:
        return None
    mn = min(p[0] for p in B)
    s = next(j for j, p in enumerate(B) if p[0] == mn)     # 最浅の列の位置
    if s == 0:
        return None                        # 既に根が最浅。切っても同じ
    B1, B2 = B[:s], B[s:]
    if why2(B1) is None or why2(B2) is None:
        return None
    if lev0(B1) > lev0(A):
        return None
    left = cat_split(A, B1, d - 1)
    if left is None:
        return None
    T1 = A + B1
    if lev0(B2) <= lev0(T1) and wadd_ok(T1, B2):
        return '**切って W_add（%d 段）**' % (4 - d)
    return cat_split(T1, B2, d - 1)


if __name__ == '__main__':
    CAP = int(sys.argv[1]); PAIRS = int(sys.argv[2])
    rng = random.Random(20260829)
    COLS = [(a, b, c) for a in range(6) for b in range(6) for c in range(2)]
    P = set()
    while len(P) < CAP:
        P.add(tuple(rng.choice(COLS) for _ in range(rng.randint(1, 5))))
    OK = [M for M in P if why2(M) is not None]
    print('証明書つき %d / %d' % (len(OK), len(P)), flush=True)
    c = Counter(); ex = []; n = 0
    while n < PAIRS:
        A = rng.choice(OK); B = rng.choice(OK)
        if A == B or lev0(B) > lev0(A):
            continue
        n += 1
        if cat_direct(A, B):
            c['切らずに届く'] += 1
            continue
        r = cat_split(A, B)
        if r:
            c['**切ったら届いた**'] += 1
            if len(ex) < 4:
                ex.append((A, B, r))
        else:
            c['切っても届かない'] += 1
            # 原因
            mn = min(p[0] for p in B)
            s = next(j for j, p in enumerate(B) if p[0] == mn)
            if s == 0:
                c['  B の根は既に B 内で最浅（A との関係が原因）'] += 1
            else:
                B1, B2 = B[:s], B[s:]
                if why2(B1) is None:
                    c['  **切った左 B1 に証明書が無い**'] += 1
                elif why2(B2) is None:
                    c['  **切った右 B2 に証明書が無い**'] += 1
                else:
                    c['  両片に証明書はあるが `rsum` がまだ破れる'] += 1
    print('== `rsum` の破れを「B を切る」で回避できるか（A != B、母数 %d 組）' % PAIRS)
    for k in sorted(c, key=str):
        print('   %-46s %d' % (k, c[k]))
    for A, B, r in ex:
        print('   切って届いた例 A=%s B=%s  [%s]'
              % (''.join(map(str, A)), ''.join(map(str, B)), r))
