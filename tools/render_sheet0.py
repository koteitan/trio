# -*- coding: utf-8 -*-
"""Generate ebp2bms/sheet/0/README{,-en}.md: the ordinals up to psi_0(Omega_omega).

Everything below psi_0(Omega_omega) is written with row 2 identically 0, so this range is
exactly the pair-sequence (2-row) part of BM4. The matrices are taken verbatim from the
"To psi(I)" sheet of BM4-Analysis and padded to three rows.
"""
import openpyxl, os, re

XLSX = os.path.expanduser('~/proofs/papers/BM4-Analysis-2021.4.27.xlsx')

# (sheet row, ordinal, note-ja, note-en); row 0 = the empty matrix
ROWS = [
  (  2, r'0',                                   '空行列', 'the empty matrix'),
  (  3, r'1 = \psi_0(0)',                       '', ''),
  (  4, r'2',                                   '', ''),
  (  8, r'\omega = \psi_0(1)',                  '', ''),
  (  9, r'\omega+1',                            '', ''),
  ( 12, r'\omega\cdot 2',                       '', ''),
  ( 15, r'\omega^2 = \psi_0(2)',                '', ''),
  ( 19, r'\omega^3',                            '', ''),
  ( 20, r'\omega^\omega = \psi_0(\omega)',      '1 行行列（原始数列）の限界',
                                                'the limit of 1-row matrices (primitive sequences)'),
  ( 25, r'\omega^{\omega+1}',                   '', ''),
  ( 29, r'\omega^{\omega^\omega}',              '', ''),
  ( 31, r'\varepsilon_0 = \psi_0(\Omega)',      'PA の証明論的順序数。行 1 が初めて立つ',
                                                'the proof-theoretic ordinal of PA; the first matrix that uses row 1'),
  ( 35, r'\varepsilon_0\cdot 2',                '', ''),
  ( 43, r'\varepsilon_0^2 = \psi_0(\Omega+\varepsilon_0)', '', ''),
  ( 53, r'\varepsilon_0^{\varepsilon_0}',       '', ''),
  ( 60, r'\varepsilon_1 = \psi_0(\Omega\cdot 2)', '', ''),
  ( 69, r'\varepsilon_\omega = \psi_0(\Omega\cdot\omega)', '', ''),
  ( 81, r'\varepsilon_{\varepsilon_0} = \psi_0(\Omega\cdot\varepsilon_0)', '', ''),
  ( 91, r'\zeta_0 = \psi_0(\Omega^2)',          '', ''),
  (108, r'\zeta_1 = \psi_0(\Omega^2\cdot 2)',   '', ''),
  (122, r'\varphi(3,0) = \psi_0(\Omega^3)',     '', ''),
  (132, r'\varphi(\omega,0) = \psi_0(\Omega^\omega)', '', ''),
  (143, r'\varphi(\varepsilon_0,0) = \psi_0(\Omega^{\varepsilon_0})', '', ''),
  (146, r'\Gamma_0 = \psi_0(\Omega^\Omega)',    'フェファーマン・シュッテ順序数（ATR₀）',
                                                'the Feferman-Schutte ordinal (ATR_0)'),
  (152, r'\Gamma_1 = \psi_0(\Omega^\Omega\cdot 2)', '', ''),
  (155, r'\varphi(1,1,0) = \psi_0(\Omega^{\Omega+1})', '', ''),
  (158, r'\varphi(2,0,0) = \psi_0(\Omega^{\Omega\cdot 2})', '', ''),
  (160, r'\varphi(1,0,0,0) = \psi_0(\Omega^{\Omega^2})', 'アッカーマン順序数',
                                                'the Ackermann ordinal'),
  (162, r'\psi_0(\Omega^{\Omega^\omega})',      '小ヴェブレン順序数 (SVO)', 'the small Veblen ordinal (SVO)'),
  (169, r'\psi_0(\Omega^{\Omega^\Omega})',      '大ヴェブレン順序数 (LVO)', 'the large Veblen ordinal (LVO)'),
  (180, r'\psi_0(\Omega_2)',                    'バッハマン・ハワード順序数（ID₁ / KP）',
                                                'the Bachmann-Howard ordinal (ID_1 / KP)'),
  (241, r'\psi_0(\Omega_3)',                    '', ''),
  (267, r'\psi_0(\Omega_\omega)',               '**2 行の限界**（ペア数列の限界）。行 2 が初めて立つ',
                                                '**the limit of two rows** (of pair sequences); the first matrix that uses row 2'),
]

def load():
    ws = openpyxl.load_workbook(XLSX, read_only=True)['To psi(I)']
    return list(ws.iter_rows(min_row=1, max_row=300, max_col=2, values_only=True))

def mat(s):
    s = str(s).strip()
    if s.lower().startswith('empty'): return []
    cols = [tuple(int(v) for v in c.split(',')) for c in re.findall(r'\(([^)]*)\)', s)]
    return [c + (0,) * (3 - len(c)) for c in cols]

def pmat(cols):
    if not cols: return r'\varepsilon'
    return (r'\begin{pmatrix}'
            + r'\cr '.join(' & '.join(str(c[i]) for c in cols) for i in range(3))
            + r'\end{pmatrix}')

NAV = ('[← 戻る](../../../README.md) | [Japanese](README.md) | [English](README-en.md) | '
       '[M <= ψ0(Ω_ω)](README.md) | [ψ0(Ω_ω) <= M < ψ0(Ω_ε₀)](../1/README.md) | '
       '[ψ0(Ω_ε₀) ≤ M <= ψ0(Ω_Λ)](../2/README.md)')
NAV_EN = ('[← Back](../../../README.md) | [Japanese](README.md) | [English](README-en.md) | '
          '[M <= ψ0(Ω_ω)](README-en.md) | [ψ0(Ω_ω) <= M < ψ0(Ω_ε₀)](../1/README-en.md) | '
          '[ψ0(Ω_ε₀) ≤ M <= ψ0(Ω_Λ)](../2/README-en.md)')

HEAD_JA = """# 拡張ブーフホルツ psi ↔ トリオ数列 対応表: M ≤ ψ₀(Ω_ω)

%s

トリオ数列（3 行バシク行列, BM4）が表す順序数のうち、$`\\psi_0(\\Omega_\\omega)`$ 以下の部分。
この範囲は**行 2 が恒等的に 0**、つまり 2 行バシク行列（ペア数列）そのものである。
$`\\psi_0(\\Omega_\\omega)`$ がペア数列の限界で、そこで初めて行 2 が立つ。

行列は BM4-Analysis シート「To psi(I)」の 2〜267 行から採り、3 行に 0 で埋めたもの。
生成: `tools/render_sheet0.py`。

ペア数列の停止性は姉妹プロジェクト
[lean-yapss](https://github.com/koteitan/yet-another-pss-proof) で形式化済みなので、
**この表の範囲は証明が終わっている**。トリオの仕事は
[ここから上](../1/README.md)である。

| 順序数 | 注 | トリオ数列 |
|---|---|---|
""" % NAV

HEAD_EN = """# Extended Buchholz psi <-> trio sequence: M <= psi_0(Omega_omega)

%s

The part of the trio sequence (3-row Bashicu matrix, BM4) at or below
$`\\psi_0(\\Omega_\\omega)`$. Throughout this range **row 2 is identically 0**, so it is
exactly the 2-row Bashicu matrix (pair sequence). $`\\psi_0(\\Omega_\\omega)`$ is the limit of
the pair sequences, and it is the first matrix to use row 2.

The matrices are taken verbatim from rows 2-267 of the "To psi(I)" sheet of BM4-Analysis
and padded to three rows. Generated by `tools/render_sheet0.py`.

Termination for pair sequences is already formalised in the sibling project
[lean-yapss](https://github.com/koteitan/yet-another-pss-proof), so **this whole range is
already proved**. Trio's work starts [above it](../1/README-en.md).

| ordinal | note | trio sequence |
|---|---|---|
""" % NAV_EN

def main():
    sheet = load()
    ja = [HEAD_JA]; en = [HEAD_EN]
    for r, ordinal, nja, nen in ROWS:
        cols = mat(sheet[r - 1][0])
        cell = '$`%s`$' % pmat(cols)
        ja.append('| $`%s`$ | %s | %s |\n' % (ordinal, nja, cell))
        en.append('| $`%s`$ | %s | %s |\n' % (ordinal, nen, cell))
    base = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'ebp2bms', 'sheet', '0')
    os.makedirs(base, exist_ok=True)
    open(os.path.join(base, 'README.md'), 'w').write(''.join(ja))
    open(os.path.join(base, 'README-en.md'), 'w').write(''.join(en))
    print('wrote %d rows' % len(ROWS))

if __name__ == '__main__':
    main()
