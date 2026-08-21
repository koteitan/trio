"""psi_0(Omega_alpha) の一般項の観測。

BM4-Analysis の「To psi(I)」シートから純粋な psi(W_alpha) 行（和・積・冪で
汚れていない Omega_alpha 崩壊）を全部抜き、次を計測する:

1. 展開閉包: M が pure で分岐 T2/T0（alpha 極限）なら M[n] も pure。
   分岐 T1（alpha 後続 = (d-2) 塔）なら M[n] は pure 族を出る
   （psi(W_w^...) の冪塔に潜る）— dom 対応表の予言。
2. pure 表を tools/omega_alpha_rows.tsv に保存（一般項の文法学習の材料）。
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(__file__))
from trio import expand
from probe_dom import classify

XLSX = os.path.expanduser('~/proofs/papers/BM4-Analysis-2021.4.27.xlsx')

def pure_sub(label):
    """psi(W_alpha) 単独形なら alpha 文字列を返す。それ以外は None。"""
    if not (isinstance(label, str) and label.startswith('psi(W') and label.endswith(')')):
        return None
    body = label[4:-1]
    if body == 'W':
        return '1'
    if not body.startswith('W_'):
        # psi(W2) 等は W_ 無し = Omega*2 系なので除外。W のみ上で処理済。
        return None
    sub = body[2:]
    depth = 0
    for ch in sub:
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth = max(0, depth - 1)
        elif ch in '+*^' and depth == 0:
            return None
    return sub

def mat(s):
    cols = [tuple(int(v) for v in c.split(',')) for c in re.findall(r'\(([^)]*)\)', s)]
    return [c + (0,) * (3 - len(c)) for c in cols]

def main():
    import openpyxl
    wb = openpyxl.load_workbook(XLSX, read_only=True)
    ws = wb['To psi(I)']
    rows = [(i + 1, r[0], r[1]) for i, r in enumerate(ws.iter_rows(values_only=True))
            if r and isinstance(r[0], str) and r[0].startswith('(')
            and isinstance(r[1], str)]
    label = {m: lab for _, m, lab in rows}
    pure = [(n, m, lab, pure_sub(lab)) for n, m, lab in rows if pure_sub(lab)]
    print('To psi(I): %d 行, pure psi(W_alpha): %d 行' % (len(rows), len(pure)))

    with open(os.path.join(os.path.dirname(__file__), 'omega_alpha_rows.tsv'), 'w') as f:
        f.write('row\talpha\tbranch\tmatrix\n')
        for n, m, lab, a in pure:
            b = classify(mat(m))[0]
            f.write('%d\t%s\t%s\t%s\n' % (n, a, b, m))

    from collections import Counter
    stat = Counter()
    bad = []
    for n, m, lab, a in pure:
        M = mat(m)
        b = classify(M)[0]
        for k in (2, 3):
            E = expand(M, k)
            key = ''.join('(%d,%d,%d)' % c for c in E)
            lab2 = label.get(key)
            kind = ('absent' if lab2 is None
                    else 'pure' if pure_sub(lab2) else 'impure')
            stat[(b, kind)] += 1
            # dom 対応表の予言との突合
            if b in ('T2', 'T0') and kind == 'impure':
                bad.append((n, a, b, k, lab2))
            if b == 'T1' and kind == 'pure':
                bad.append((n, a, b, k, lab2))
    print('\n分岐 x 展開先 (n=2,3 の延べ):')
    for key in sorted(stat):
        print('  %-4s -> %-7s %5d' % (key[0], key[1], stat[key]))
    print('\n予言違反 (T2/T0->impure, T1->pure): %d 件' % len(bad))
    for v in bad[:10]:
        print('   ', v)
    branches = Counter(classify(mat(m))[0] for _, m, _, _ in pure)
    print('\npure 行の分岐分布:', dict(branches))
    print('\nall done')

if __name__ == '__main__':
    main()
