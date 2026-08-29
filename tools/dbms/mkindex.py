#!/usr/bin/env python3
"""lean/*.lean から theorem/def/lemma の完全な型と docstring を 1 行ずつ抜き出して
lean/LEMMA-INDEX.tsv を作る。書く前に grep するための索引。

列: file:line <TAB> kind name <TAB> 型 <TAB> docstring（1 行に畳んだもの）

docstring を入れる理由（2026-09-01）: L3 と team-lead が 5 回の「使い所を数える」のうち
2 回、決め手が docstring にあった（`nextR_src_ge` / `oper_snoc_flat_root` /
`W_flatMap_copies`）。型だけでは「なぜその形か」が読めない。
"""
import re, glob, os

os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'lean'))
out = []
for f in sorted(x for x in glob.glob('*.lean') if not x.startswith('.')):
    lines = open(f, encoding='utf-8').read().split('\n')
    for i, l in enumerate(lines):
        m = re.match(r'^(theorem|def|lemma|abbrev)\s+([A-Za-z_][A-Za-z0-9_\'!?]*)', l)
        if not m:
            continue
        # 型: 宣言行から ':=' か 'by' まで（最大 6 行）
        sig, j = [l], i + 1
        while j < len(lines) and j < i + 6 and ':=' not in sig[-1] \
                and not sig[-1].rstrip().endswith('by'):
            sig.append(lines[j]); j += 1
        typ = re.sub(r'\s+', ' ', ' '.join(x.strip() for x in sig)).split(':=')[0].strip()
        # docstring: 直前の /-- ... -/ を遡って拾う（最大 40 行）
        doc = ''
        k = i - 1
        while k >= 0 and lines[k].strip() == '':
            k -= 1
        if k >= 0 and lines[k].rstrip().endswith('-/'):
            end = k
            while k >= 0 and not lines[k].lstrip().startswith('/--'):
                if end - k > 40:
                    k = -1
                    break
                k -= 1
            if k >= 0:
                body = ' '.join(lines[k:end + 1])
                doc = re.sub(r'\s+', ' ', body.replace('/--', '').replace('-/', '')).strip()
        out.append(f"{f}:{i+1}\t{m.group(1)} {m.group(2)}\t{typ[:300]}\t{doc[:400]}")

open('LEMMA-INDEX.tsv', 'w', encoding='utf-8').write('\n'.join(out) + '\n')
print(f"{len(out)} entries")
