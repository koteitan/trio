"""DBMS の「読み」translateD の候補を、264 件の正解に当てて探す。

trio-agent の指摘:
  * translateD は「引数と後続に割る 2 分岐の構造再帰」でなければならない。
    そうでないと Seqlex.lean の olt_iff_seqlex の証明が移植できない。
  * translateD が決まれば f は Lean に書く必要すらない
    （f := translateD (f M) = translate M をみたす唯一の DBMS 標準形）。

正解データ: ~/proofs/trio/tmp/dbms2row_targets.json（264 件、A/E/target）
"""
import sys, os, json, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

DATA = os.path.expanduser('~/proofs/trio/tmp/dbms2row_targets.json')


def tr(cols):
    """BMS の読み（Term.lean:131 と同じ）。"""
    if not cols:
        return ('Z',)
    p, rest = cols[0], cols[1:]
    i = 0
    while i < len(rest) and p[0] < rest[i][0]:
        i += 1
    return ('P', p[1], tr(rest[:i]), tr(rest[i:]))


def show(t):
    if t[0] == 'Z':
        return 'Z'
    return 'P%d(%s,%s)' % (t[1], show(t[2]), show(t[3]))


def mk(sub, split):
    """2 分岐の構造再帰。`sub(p, rest)` が添字、`split(p, rest)` が引数の長さ。"""
    def go(cols):
        if not cols:
            return ('Z',)
        p, rest = cols[0], cols[1:]
        i = split(p, rest)
        return ('P', sub(p, rest), go(rest[:i]), go(rest[i:]))
    return go


def split_row0(p, rest):
    i = 0
    while i < len(rest) and p[0] < rest[i][0]:
        i += 1
    return i


def split_row0_ge(p, rest):
    i = 0
    while i < len(rest) and p[0] <= rest[i][0]:
        i += 1
    return i


def split_row1(p, rest):
    i = 0
    while i < len(rest) and p[1] < rest[i][1]:
        i += 1
    return i


def runlen(p, rest):
    """`p` から始まる階段の連の長さ（`(+1,+1)` で続く限り）。"""
    k = 0
    cur = p
    while k < len(rest) and rest[k][0] == cur[0] + 1 and rest[k][1] == cur[1] + 1:
        cur = rest[k]; k += 1
    return k, cur


def mk_run_first(argsplit, run_on_succ=False):
    """連を取るのは「親の最初の子」のときだけ。

    引数（子）に降りるときは first=True、後続（兄弟）に進むときは first=False。
    行列全体の先頭も first=True とする。
    """
    def go(cols, first):
        if not cols:
            return ('Z',)
        p, rest = cols[0], cols[1:]
        if first or run_on_succ:
            k, top = runlen(p, rest)
        else:
            k, top = 0, p
        tail = rest[k:]
        i = argsplit(top, tail)
        return ('P', top[1], go(tail[:i], True), go(tail[i:], False))
    return lambda cols: go(cols, True)


def mk_chain4(argsplit, dual=True):
    """連の各段に、後続を**深さで振り分ける**版。

    連 c_0..c_k は段 c_1.1 … c_k.1 のノードの入れ子になる。
    連のあとに続く列は、その行 0（深さ）に対応する段のノードの後続になる。
    連より浅い列は、連全体の後続。
    """
    def go(cols, first, plev):
        if not cols:
            return ('Z',)
        p, rest0 = cols[0], cols[1:]
        if first and p[1] == plev:
            k, top = runlen(p, rest0)
        else:
            k, top = 0, p
        run = [p] + rest0[:k]
        tail = rest0[k:]
        i = argsplit(top, tail)
        arg = go(tail[:i], True, top[1])
        rest = tail[i:]

        # 二役（梯子 + 本体）の判定
        j = 0
        while j < len(rest) and rest[j][0] == top[0] and rest[j][1] == top[1]:
            j += 1
        r2 = rest[j:]
        # 二役が起きるのは連の長さが 1 のとき（影の子が 1 段だけ上がる形）だけ
        if k == 1 and dual and r2 and r2[0][0] == top[0] and r2[0][1] < top[1]:
            m = 0
            while m < len(r2) and r2[m][0] >= top[0]:
                m += 1
            inner = go([top] + tail[:i] + rest[:j] + r2[:m], True, p[1])
            succ = ('P', p[1], inner, go(r2[m:], False, plev))
            for _ in range(j):
                succ = ('P', top[1], ('Z',), succ)
            node = ('P', top[1], arg, succ)
            for t in range(k - 1, 0, -1):
                node = ('P', run[t][1], node, ('Z',))
            return node

        # 深さごとに後続を切り分ける
        if k == 0:
            return ('P', top[1], arg, go(rest, False, plev))
        # 深さごとに後続を切り分ける。最後に余った浅い列は一番内側の兄弟鎖に繋ぐ
        succs = []
        for t in range(k, 0, -1):
            n = 0
            while n < len(rest) and rest[n][0] >= run[t][0]:
                n += 1
            succs.append(rest[:n])
            rest = rest[n:]
        node = ('P', top[1], arg, go(succs[0] + rest, False, top[1]))
        for idx, t in enumerate(range(k - 1, 0, -1)):
            node = ('P', run[t][1], node, go(succs[idx + 1], False, run[t][1]))
        return node
    return lambda cols: go(cols, True, 0)


def mk_chain3(argsplit, dual=True):
    """`mk_chain2` の 2 点直し。

    * 連の鎖の**後続は一番外のノードに付く**（内側の段に付けてはいけない）。
    * 二役の判定は「引数を取り切ったあと」に、同じ深さで段が下がる列が来るかで見る
      （引数が空とは限らない）。
    """
    def go(cols, first, plev):
        if not cols:
            return ('Z',)
        p, rest = cols[0], cols[1:]
        if first and p[1] == plev:
            k, top = runlen(p, rest)
        else:
            k, top = 0, p
        tail = rest[k:]
        i = argsplit(top, tail)
        arg = go(tail[:i], True, top[1])
        after = tail[i:]
        # 同じ深さ・同じ段の兄弟は飛ばしてから、段が下がるかを見る
        j = 0
        while j < len(after) and after[j][0] == top[0] and after[j][1] == top[1]:
            j += 1
        rest2 = after[j:]
        if (k >= 1 and dual and rest2
                and rest2[0][0] == top[0] and rest2[0][1] < top[1]):
            m = 0
            while m < len(rest2) and rest2[m][0] >= top[0]:
                m += 1
            inner = go([top] + tail[:i] + after[:j] + rest2[:m], True, p[1])
            succ = ('P', p[1], inner, go(rest2[m:], False, plev))
            for _ in range(j):
                succ = ('P', top[1], ('Z',), succ)
        else:
            succ = go(after, False, plev)
        node = ('P', top[1], arg, ('Z',))
        for t in range(k - 1, 0, -1):
            node = ('P', rest[t - 1][1], node, ('Z',))
        # 後続は一番外に付ける
        return (node[0], node[1], node[2], succ)
    return lambda cols: go(cols, True, 0)


def mk_chain2(argsplit, dual=True):
    """連の底が「影」か「本物の列」かを、**親の段と同じか**で見分ける版。

    影は親と同じ段に置く足場なので `p.行1 = 親の行1`。
    親より段が下がっていれば、それは新しい加算項の頭であって影ではない。
    """
    def go(cols, first, plev):
        if not cols:
            return ('Z',)
        p, rest = cols[0], cols[1:]
        if first and p[1] == plev:
            k, top = runlen(p, rest)
        else:
            k, top = 0, p
        tail = rest[k:]
        i = argsplit(top, tail)
        if k >= 1 and dual and i == 0:
            j = 0
            while j < len(tail) and tail[j][0] == top[0] and tail[j][1] == top[1]:
                j += 1
            after = tail[j:]
            if after and after[0][0] == top[0] and after[0][1] < top[1]:
                m = 0
                while m < len(after) and after[m][0] >= top[0]:
                    m += 1
                inner = go([top] + tail[:j] + after[:m], True, p[1])
                node = ('P', p[1], inner, go(after[m:], False, plev))
                for _ in range(j + 1):
                    node = ('P', top[1], ('Z',), node)
                return node
        node = ('P', top[1], go(tail[:i], True, top[1]), go(tail[i:], False, plev))
        for t in range(k - 1, 0, -1):
            node = ('P', rest[t - 1][1], node, ('Z',))
        return node
    return lambda cols: go(cols, True, 0)


def mk_chain(argsplit, dual=True):
    """連は 1 ノードではなく**添字の鎖**として読む。

    連 c_0..c_k（`(+1,+1)` で続く）は、添字 c_1.1, c_2.1, …, c_k.1 のノードを
    引数側に入れ子にした鎖になる。DBMS の対角 (1,0)(2,1)(3,2) が
    `P1(P2(Z,Z),Z)` と読まれるのはこれ。

    さらに、連の兄弟が尽きたあと同じ深さで段が下がる列が来るときは、
    連が「梯子 + 本体」の二役を果たしている（縮約の逆）ので開き直す。
    """
    def go(cols, first):
        if not cols:
            return ('Z',)
        p, rest = cols[0], cols[1:]
        if first:
            k, top = runlen(p, rest)
        else:
            k, top = 0, p
        tail = rest[k:]
        i = argsplit(top, tail)
        if k >= 1 and dual and i == 0:
            j = 0
            while j < len(tail) and tail[j][0] == top[0] and tail[j][1] == top[1]:
                j += 1
            after = tail[j:]
            if after and after[0][0] == top[0] and after[0][1] < top[1]:
                m = 0
                while m < len(after) and after[m][0] >= top[0]:
                    m += 1
                inner = go([top] + tail[:j] + after[:m], True)
                node = ('P', p[1], inner, go(after[m:], False))
                for _ in range(j + 1):
                    node = ('P', top[1], ('Z',), node)
                return node
        node = ('P', top[1], go(tail[:i], True), go(tail[i:], False))
        # 連の途中の段を、引数側に入れ子で積む
        for t in range(k - 1, 0, -1):
            node = ('P', rest[t - 1][1], node, ('Z',))
        return node
    return lambda cols: go(cols, True)


def mk_run_dual2(argsplit):
    """連が「梯子 + 本体」の二役を果たす場合を、兄弟の連なりごと開く版。

    E の `(1,0)(2,1)(2,1)` は BMS の `(1,1)(1,1)`（梯子としての役）と
    `(1,0)(2,1)(2,1)`（本体としての役）の両方を兼ねている（縮約で 1 本に潰れている）。
    そこで
      * まず同じ段の兄弟ぶんだけ `P 頂上の行1` を後続でつなぐ
      * 最後に影の段のノード `P 影の行1` を置き、その引数で頂上から読み直す
    段が下がる列が続くときだけこの形にする。
    """
    def go(cols, first):
        if not cols:
            return ('Z',)
        p, rest = cols[0], cols[1:]
        if first:
            k, top = runlen(p, rest)
        else:
            k, top = 0, p
        tail = rest[k:]
        i = argsplit(top, tail)
        arg = go(tail[:i], True)
        if k >= 1 and i == 0:
            # 同じ深さ・同じ段の兄弟
            j = 0
            while j < len(tail) and tail[j][0] == top[0] and tail[j][1] == top[1]:
                j += 1
            after = tail[j:]
            if after and after[0][0] == top[0] and after[0][1] < top[1]:
                # 影の段に属するのは、深さが頂上以上で続くところまで
                m = 0
                while m < len(after) and after[m][0] >= top[0]:
                    m += 1
                inner = go([top] + tail[:j] + after[:m], True)
                node = ('P', p[1], inner, go(after[m:], False))
                for _ in range(j + 1):
                    node = ('P', top[1], ('Z',), node)
                return node
        return ('P', top[1], arg, go(tail[i:], False))
    return lambda cols: go(cols, True)


def mk_run_dual(argsplit):
    """連が「影 + 本体」の二役を果たす場合を扱う版。

    連 c_0..c_k のあとに、連の頂上と**同じ深さ**の列が続くとき、
    その連は BMS 側では「影の列」と「本体の列」の 2 本ぶんの役をしている
    （縮約で 1 本に潰れている）。そこで
        P c_k.1 (引数) ( P c_0.1 (頂上から読み直したもの) Z )
    と 2 段に開く。
    """
    def go(cols, first):
        if not cols:
            return ('Z',)
        p, rest = cols[0], cols[1:]
        if first:
            k, top = runlen(p, rest)
        else:
            k, top = 0, p
        tail = rest[k:]
        i = argsplit(top, tail)
        arg = go(tail[:i], True)
        if (k >= 1 and i == 0 and tail and tail[0][0] == top[0]
                and tail[0][1] < top[1]):
            # 影の段に属するのは、頂上と同じ深さ以上で続くところまで
            j = 0
            while j < len(tail) and tail[j][0] >= top[0]:
                j += 1
            inner = go([top] + tail[:j], True)
            return ('P', top[1], arg, ('P', p[1], inner, go(tail[j:], False)))
        return ('P', top[1], arg, go(tail[i:], False))
    return lambda cols: go(cols, True)


def mk_run(argsplit):
    """階段の連を 1 ノードとして読む。添字は連の先頭ではなく**末尾**の行 1。"""
    def go(cols):
        if not cols:
            return ('Z',)
        p, rest = cols[0], cols[1:]
        k, top = runlen(p, rest)
        tail = rest[k:]
        i = argsplit(top, tail)
        return ('P', top[1], go(tail[:i]), go(tail[i:]))
    return go


CANDS = {
    'BMS と同じ（対照）': (lambda p, r: p[1], split_row0),
    '添字 = 行1+1': (lambda p, r: p[1] + 1, split_row0),
    '添字 = 行0-行1': (lambda p, r: p[0] - p[1], split_row0),
    '添字 = 行1、割りは行0 >=': (lambda p, r: p[1], split_row0_ge),
    '添字 = 行1、割りは行1': (lambda p, r: p[1], split_row1),
    '添字 = 行1+1、割りは行0 >=': (lambda p, r: p[1] + 1, split_row0_ge),
    '連を 1 ノード（割りは行0 >）': (None, None),
    '連を 1 ノード（割りは行0 >=）': (None, None),
    '連は最初の子のときだけ': (None, None),
    '連が二役の場合を開く': (None, None),
    '二役を兄弟ごと開く': (None, None),
    '連は添字の鎖': (None, None),
    '連は添字の鎖（二役なし）': (None, None),
    '底が影かを親の段で判定': (None, None),
    '後続は鎖の外・二役は引数の後ろで判定': (None, None),
    '後続を深さで振り分ける': (None, None),
}


def main():
    d = json.load(open(DATA))
    print('正解 %d 件' % len(d))
    for name, (sub, split) in CANDS.items():
        if name == '連を 1 ノード（割りは行0 >）':
            f = mk_run(split_row0)
        elif name == '連を 1 ノード（割りは行0 >=）':
            f = mk_run(split_row0_ge)
        elif name == '連は最初の子のときだけ':
            f = mk_run_first(split_row0)
        elif name == '連が二役の場合を開く':
            f = mk_run_dual(split_row0)
        elif name == '二役を兄弟ごと開く':
            f = mk_run_dual2(split_row0)
        elif name == '連は添字の鎖':
            f = mk_chain(split_row0, dual=True)
        elif name == '連は添字の鎖（二役なし）':
            f = mk_chain(split_row0, dual=False)
        elif name == '底が影かを親の段で判定':
            f = mk_chain2(split_row0, dual=True)
        elif name == '後続は鎖の外・二役は引数の後ろで判定':
            f = mk_chain3(split_row0, dual=True)
        elif name == '後続を深さで振り分ける':
            f = mk_chain4(split_row0, dual=True)
        else:
            f = mk(sub, split)
        ok = 0
        bad = None
        for x in d:
            E = [tuple(c) for c in x['E']]
            got = show(f(E))
            if got == x['target']:
                ok += 1
            elif bad is None:
                bad = (x['E'], x['target'], got)
        print('%-26s %3d/%d' % (name, ok, len(d)))
        if bad and ok < len(d):
            print('     E %s' % bad[0])
            print('     正 %s' % bad[1])
            print('     得 %s' % bad[2])


if __name__ == '__main__':
    main()
