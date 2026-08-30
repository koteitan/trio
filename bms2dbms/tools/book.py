# -*- coding: utf-8 -*-
"""BM4-Analysis ブック**全 7 シート**から 3 行 z<2 の行列を、シート順・行番号順に取り出す。

`psiI.json` は sheet2「To psi(I)」1 枚だけ。ブックには 7 枚あり、天井は `psi(K*w)`。
"""
import sys, os, re, zipfile
import xml.etree.ElementTree as ET
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
from core import parse, rows, isstd

XLSX = '/home/koteitan/proofs/papers/BM4-Analysis-2021.4.27.xlsx'
NS = '{http://schemas.openxmlformats.org/spreadsheetml/2006/main}'
SHEETS = [(2, 'To psi(I)'), (3, 'To psi(W(2,0))'), (4, 'To psi(W_(M+1))'),
          (5, 'To psi(N)'), (6, 'To psi(K)'), (7, 'To psi(e(K+1))')]


def _shared(z):
    out = []
    r = ET.fromstring(z.read('xl/sharedStrings.xml'))
    for si in r.findall(NS + 'si'):
        out.append(''.join(t.text or '' for t in si.iter(NS + 't')))
    return out


def cells(z, n, ss):
    """(行番号, {列名: 値}) を行番号順に。"""
    r = ET.fromstring(z.read('xl/worksheets/sheet%d.xml' % n))
    for row in r.iter(NS + 'row'):
        d = {}
        for c in row.findall(NS + 'c'):
            ref = c.get('r') or ''
            col = re.match(r'([A-Z]+)', ref)
            if not col:
                continue
            v = c.find(NS + 'v')
            if v is None or v.text is None:
                continue
            d[col.group(1)] = (ss[int(v.text)] if c.get('t') == 's'
                               else v.text)
        if d:
            yield int(row.get('r')), d


def load_book(zcap=1):
    """(シート番号, シート名, 行番号, 行列, ラベル) を**シート順・行番号順**に。"""
    z = zipfile.ZipFile(XLSX)
    ss = _shared(z)
    out = []
    for n, nm in SHEETS:
        for rn, d in cells(z, n, ss):
            a = (d.get('A') or '').strip()
            if not a or not a.startswith('('):
                continue
            try:
                b = parse(a)
                if rows(b) != 3:
                    continue
                b = tuple(tuple(c) for c in parse(a, 3))
            except Exception:
                continue
            if any(c[2] > zcap for c in b):
                continue
            lab = (d.get('B') or d.get('D') or d.get('C') or '').strip()
            out.append((n, nm, rn, b, lab))
    return out


if __name__ == '__main__':
    from collections import Counter
    T = load_book()
    c = Counter((n, nm) for n, nm, _, _, _ in T)
    print('ブック全 7 シートの **3 行 z<2** 行列（シート順・行番号順）')
    for (n, nm), k in sorted(c.items()):
        print('   sheet%d %-20s %5d 行' % (n, nm, k))
    print('   ---------------------------- 合計 **%d 行**' % len(T))
    print('   列数 %d .. %d' % (min(len(b) for _, _, _, b, _ in T),
                                max(len(b) for _, _, _, b, _ in T)))
    print('   先頭', [(n, r, ''.join(map(str, b)), l) for n, _, r, b, l in T[:2]])
    print('   末尾', [(n, r, ''.join(map(str, b)), l) for n, _, r, b, l in T[-2:]])
