"""「ここまでは正しい」と宣言した表を持ち、その上に構成器で積み上げる。

再帰版の構成器は基本列を根まで展開するので、手間が急増加関数になり使えない。
かわりに **正しいと認めた範囲を表に持つ**。

    f(M) を求める
      M が表にある            -> 表から返す（宣言した範囲。再帰しない）
      無い                    -> 構成器で 1 段だけ計算する
                                 そこで要る f(M[n]) は M[n] < M なので、
                                 順序数の小さい順に進めていれば必ず表にある

表の種はシートの 1621 行（真値）。将来ここを「Lean で証明できた範囲」に
差し替えれば、証明済みの土台の上に構成が乗る形になる。
"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import expand, isstd, cmpmat, show, parse
import rule as R
import sup_build as SB

CACHE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'verified.json')


class Table:
    """正しいと認めた f の表。"""

    def __init__(self, seed_sheet=True):
        self.t = {}
        self.src = {}
        if seed_sheet:
            from check_sheet import load
            for r, mb, md, Y in load():
                if mb:
                    self.t[mb] = md
                    self.src[mb] = 'シート %s' % r['row']

    def __len__(self):
        return len(self.t)

    def below(self, M, Y=3):
        """宣言した範囲での f。表にあれば表、無ければ規則版。**再帰しない**。

        再帰すると基本列を根まで展開することになり、手間が急増加関数になる。
        「ここまでは正しい」と決めた表を土台にするのがこの設計の要点。
        """
        v = self.t.get(M)
        return v if v is not None else R.convert(M, Y)

    def get(self, M, Y=3, build=True):
        """M の像。表になければ構成器で 1 段だけ作って表に足す。"""
        if M in self.t:
            return self.t[M]
        if not M:
            return ()
        if SB.is_succ(M):
            v = self.below(M[:-1], Y) + (tuple([0] * Y),)
            self.t[M] = v; self.src[M] = '後続'
            return v
        if not build:
            return None
        # 基本列の像は「自分より小さい順序数」。表 or 規則版で埋める（再帰なし）
        conv = lambda z: self.below(z, Y)
        v = SB.build(M, Y, conv=conv)
        if v is None:
            v = R.convert(M, Y)
            self.src[M] = '構成できず→規則版'
        else:
            self.src[M] = '構成'
        self.t[M] = v
        return v

    def save(self, path=CACHE):
        json.dump({'t': [[[list(c) for c in k], [list(c) for c in v]]
                         for k, v in self.t.items()]}, open(path, 'w'))

    def load(self, path=CACHE):
        if not os.path.exists(path):
            return 0
        d = json.load(open(path))
        n = 0
        for k, v in d['t']:
            key = tuple(tuple(c) for c in k)
            if key not in self.t:
                self.t[key] = tuple(tuple(c) for c in v)
                self.src[key] = '保存済み'
                n += 1
        return n


def sweep(n=None, Y=3, verbose=True):
    """シートを順序数の小さい順に舐め、構成器の答えと規則版・真値を比べる。"""
    from check_sheet import load
    import collections
    d = [x for x in load() if x[3] == Y]
    if n:
        d = d[:n]
    T = Table(seed_sheet=False)          # 種を入れずに、下から積み上げる
    c = collections.Counter()
    bad = []
    import time
    for i, (r, mb, md, _) in enumerate(d):
        t0 = time.time()
        v = T.get(mb, Y)
        T.t[mb] = md                     # 済んだ行は真値で上書き（土台を正しく保つ）
        T.src[mb] = 'シート %s' % r['row']
        rule = R.convert(mb, Y)
        k = ('構成=真値' if v == md else '構成≠真値')
        c[k] += 1
        c['規則=真値' if rule == md else '規則≠真値'] += 1
        if v != md and len(bad) < 8:
            bad.append((r['row'], show(mb, 1), show(md, 1), show(v, 1)))
        if verbose:
            print('  [%4d/%d] row %-5s %2d 列 %.2f 秒 %s'
                  % (i + 1, len(d), r['row'], len(mb), time.time() - t0,
                     '構成=真値' if v == md else '構成≠真値'), flush=True)
    print('結果: %s' % dict(c))
    for rw, a, t, g in bad:
        print('  row %-5s %s' % (rw, a))
        print('     真値 %s' % t); print('     構成 %s' % g)
    return T


if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    sweep(n)
