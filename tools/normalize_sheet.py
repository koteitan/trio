# -*- coding: utf-8 -*-
"""BM4-Analysis「To psi(I)」シートのラベルを機械可読な形式に正規化する。

**形式だけを直す**。順序数の値・行列は一切変更しない。

正規化の 3 規則:
  1. 別名併記  'A = B = C' を分割し、`psi(W...)` 形の最初の別名を正規形とする
     （無ければ最初の別名）。
  2. 括弧不整合  各別名について、不足する ')' を末尾に足す／末尾の余分な ')' を落とす。
  3. 先頭タイポ  'si(' で始まるラベルを 'psi(' に直す。

出力:
  tmp/fixed-sheet/to-psi-I.tsv   （バージョン管理外）
    row / matrix / label_orig / label_norm / fix   （fix は適用した規則のカンマ区切り）
  tools/omega_alpha_rows.tsv     （バージョン管理下。probe/ビルダーの入力）
    正規化ラベルから純粋な psi_0(Omega_alpha) 行だけを抜いたもの
"""
import openpyxl, os, re, sys

XLSX = os.path.expanduser('~/proofs/papers/BM4-Analysis-2021.4.27.xlsx')
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, '..', 'tmp', 'fixed-sheet', 'to-psi-I.tsv')
ROWS = os.path.join(HERE, 'omega_alpha_rows.tsv')

def depth(s):
    d = 0
    for c in s:
        d += (c == '(') - (c == ')')
    return d

def balance(s):
    """括弧を合わせる。不足は末尾に足し、余りは末尾から落とす。"""
    d = depth(s)
    if d > 0:
        return s + ')' * d, 'paren+%d' % d
    if d < 0:
        t = s
        while depth(t) < 0 and t.endswith(')'):
            t = t[:-1]
        return t, 'paren%d' % d
    return s, None

def normalize(label):
    fixes = []
    s = label.strip()
    if s.startswith('si('):                      # 規則 3
        s = 'p' + s
        fixes.append('typo')
    parts = [p.strip() for p in s.split(' = ')]
    if len(parts) > 1:
        fixes.append('alias%d' % len(parts))
    fixed = []
    for p in parts:
        q, f = balance(p)
        if f: fixes.append(f)
        fixed.append(q)
    canon = next((p for p in fixed if p.startswith('psi(W')), fixed[0])
    return canon, fixes

def main():
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    wb = openpyxl.load_workbook(XLSX, read_only=True)
    ws = wb['To psi(I)']
    n = nfix = 0
    with open(OUT, 'w', encoding='utf-8') as f:
        f.write('row\tmatrix\tlabel_orig\tlabel_norm\tfix\n')
        for i, r in enumerate(ws.iter_rows(values_only=True)):
            row = i + 1
            mat, lab = (r[0], r[1]) if r else (None, None)
            if not isinstance(lab, str) or not lab.strip():
                continue
            n += 1
            canon, fixes = normalize(lab)
            if fixes: nfix += 1
            f.write('%d\t%s\t%s\t%s\t%s\n'
                    % (row, mat if isinstance(mat, str) else '',
                       lab.strip(), canon, ','.join(fixes)))
    print('ラベル付き行 %d / 形式修正あり %d -> %s' % (n, nfix, os.path.normpath(OUT)))
    write_rows()

def write_rows():
    """正規化ラベルから純粋な psi_0(Omega_alpha) 行を抜いて tools/ に置く。"""
    sys.path.insert(0, HERE)
    from probe_omega_alpha import pure_sub
    from probe_dom import classify
    def cols(s):
        cs = [tuple(int(v) for v in x.split(',')) for x in re.findall(r'\((\d+(?:,\d+)*)\)', s)]
        return [c + (0,) * (3 - len(c)) for c in cs]
    out = ['row\talpha\tbranch\tmatrix']
    for L in open(OUT, encoding='utf-8'):
        p = L.rstrip('\n').split('\t')
        if p[0] == 'row': continue
        a = pure_sub(p[3])
        if not a or not p[1].startswith('('): continue
        try: b = classify(cols(p[1]))[0]
        except Exception: b = '?'
        out.append('%s\t%s\t%s\t%s' % (p[0], a, b, p[1]))
    open(ROWS, 'w', encoding='utf-8').write('\n'.join(out) + '\n')
    print('純粋な psi_0(Omega_alpha) 行 %d -> %s' % (len(out) - 1, os.path.normpath(ROWS)))

if __name__ == '__main__':
    main()
