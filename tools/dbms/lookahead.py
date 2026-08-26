"""「有限の窓（先読み）で決まるか」をシートで測る。

f が窓 L のトランスデューサで書けるなら、a[:k+L] が e[k] を一意に決めるはず。
添字を素朴に揃えた代理指標なので「窓 L の変換器が実在する」証明ではないが、
「原理的に規則で書けない」の反証にはなる。

  python3 tools/dbms/lookahead.py [rows]
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collections import defaultdict
from check_sheet import load


def main():
    Y = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    d = [x for x in load() if x[3] == Y]
    print('Y=%d  rows=%d' % (Y, len(d)))
    for L in range(0, 8):
        m, cnt = defaultdict(set), defaultdict(int)
        for r, mb, md, _ in d:
            for k in range(len(md)):
                key = (k, mb[:k + L])
                m[key].add(md[k]); cnt[key] += 1
        amb = sum(cnt[k] for k in m if len(m[k]) > 1)
        print('  先読み %d 列: キー %5d, 曖昧 %4d' % (L, len(m), amb))
        if amb == 0:
            break


if __name__ == '__main__':
    main()
