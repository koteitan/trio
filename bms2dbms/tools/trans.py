"""シートから「1 列足したとき像がどう変わるか」を抽出する。

f が左→右のトランスデューサに近いなら、f(M'++c) は f(M') の
末尾を少し直して何列か足したものになるはず。その形を分類する。
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import show, flat
from check_sheet import load


def table(Y):
    d = [x for x in load() if x[3] == Y]
    return {mb: md for r, mb, md, _ in d}


def transitions(tab):
    out = []
    for M, N in tab.items():
        if len(M) < 1:
            continue
        P = M[:-1]
        if P not in tab:
            continue
        out.append((P, tab[P], M[-1], N))
    return out


def classify(P, FP, c, FM):
    """f(P)=FP, f(P++c)=FM の関係を分類。"""
    if FM[:len(FP)] == FP:
        return 'ext', len(FM) - len(FP), FM[len(FP):]
    k = len(FP) - 1
    if k >= 0 and FM[:k] == FP[:k] and len(FM) > k:
        return 'lift', len(FM) - k, FM[k:]
    # 共通接頭辞の長さ
    n = 0
    while n < len(FP) and n < len(FM) and FP[n] == FM[n]:
        n += 1
    return 'other', n - len(FP), FM[n:]


if __name__ == '__main__':
    Y = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    tab = table(Y)
    tr = transitions(tab)
    from collections import Counter
    kinds = Counter()
    for P, FP, c, FM in tr:
        k = classify(P, FP, c, FM)[0]
        kinds[k] += 1
    print('Y=%d  matrices=%d  transitions=%d  %s' % (Y, len(tab), len(tr), dict(kinds)))
