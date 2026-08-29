# 拡張ブーフホルツ psi ↔ トリオ数列 対応表: M ≤ ψ₀(Ω_ω)

[← 戻る](../../../README.md) | [Japanese](README.md) | [English](README-en.md) | [M <= ψ0(Ω_ω)](README.md) | [ψ0(Ω_ω) <= M < ψ0(Ω_ε₀)](../1/README.md) | [ψ0(Ω_ε₀) ≤ M <= ψ0(Ω_Λ)](../2/README.md)

トリオ数列（3 行バシク行列, BM4）が表す順序数のうち、$`\psi_0(\Omega_\omega)`$ 以下の部分。
この範囲は**行 2 が恒等的に 0**、つまり 2 行バシク行列（ペア数列）そのものである。
$`\psi_0(\Omega_\omega)`$ がペア数列の限界で、そこで初めて行 2 が立つ。

行列は BM4-Analysis シート「To psi(I)」の 2〜267 行から採り、3 行に 0 で埋めたもの。
生成: `tools/render_sheet0.py`。

ペア数列の停止性は姉妹プロジェクト
[lean-yapss](https://github.com/koteitan/yet-another-pss-proof) で形式化済みなので、
**この表の範囲は証明が終わっている**。トリオの仕事は
[ここから上](../1/README.md)である。

| 順序数 | 注 | トリオ数列 |
|---|---|---|
| $`0`$ | 空行列 | $`\varepsilon`$ |
| $`1 = \psi_0(0)`$ |  | $`\begin{pmatrix}0\cr 0\cr 0\end{pmatrix}`$ |
| $`2`$ |  | $`\begin{pmatrix}0 & 0\cr 0 & 0\cr 0 & 0\end{pmatrix}`$ |
| $`\omega = \psi_0(1)`$ |  | $`\begin{pmatrix}0 & 1\cr 0 & 0\cr 0 & 0\end{pmatrix}`$ |
| $`\omega+1`$ |  | $`\begin{pmatrix}0 & 1 & 0\cr 0 & 0 & 0\cr 0 & 0 & 0\end{pmatrix}`$ |
| $`\omega\cdot 2`$ |  | $`\begin{pmatrix}0 & 1 & 0 & 1\cr 0 & 0 & 0 & 0\cr 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\omega^2 = \psi_0(2)`$ |  | $`\begin{pmatrix}0 & 1 & 1\cr 0 & 0 & 0\cr 0 & 0 & 0\end{pmatrix}`$ |
| $`\omega^3`$ |  | $`\begin{pmatrix}0 & 1 & 1 & 1\cr 0 & 0 & 0 & 0\cr 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\omega^\omega = \psi_0(\omega)`$ | 1 行行列（原始数列）の限界 | $`\begin{pmatrix}0 & 1 & 2\cr 0 & 0 & 0\cr 0 & 0 & 0\end{pmatrix}`$ |
| $`\omega^{\omega+1}`$ |  | $`\begin{pmatrix}0 & 1 & 2 & 1\cr 0 & 0 & 0 & 0\cr 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\omega^{\omega^\omega}`$ |  | $`\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 0 & 0 & 0\cr 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_0 = \psi_0(\Omega)`$ | PA の証明論的順序数。行 1 が初めて立つ | $`\begin{pmatrix}0 & 1\cr 0 & 1\cr 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_0\cdot 2`$ |  | $`\begin{pmatrix}0 & 1 & 0 & 1\cr 0 & 1 & 0 & 1\cr 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_0^2 = \psi_0(\Omega+\varepsilon_0)`$ |  | $`\begin{pmatrix}0 & 1 & 1 & 2\cr 0 & 1 & 0 & 1\cr 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_0^{\varepsilon_0}`$ |  | $`\begin{pmatrix}0 & 1 & 1 & 2 & 2 & 3\cr 0 & 1 & 0 & 1 & 0 & 1\cr 0 & 0 & 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_1 = \psi_0(\Omega\cdot 2)`$ |  | $`\begin{pmatrix}0 & 1 & 1\cr 0 & 1 & 1\cr 0 & 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_\omega = \psi_0(\Omega\cdot\omega)`$ |  | $`\begin{pmatrix}0 & 1 & 2\cr 0 & 1 & 0\cr 0 & 0 & 0\end{pmatrix}`$ |
| $`\varepsilon_{\varepsilon_0} = \psi_0(\Omega\cdot\varepsilon_0)`$ |  | $`\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 0 & 1\cr 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\zeta_0 = \psi_0(\Omega^2)`$ |  | $`\begin{pmatrix}0 & 1 & 2\cr 0 & 1 & 1\cr 0 & 0 & 0\end{pmatrix}`$ |
| $`\zeta_1 = \psi_0(\Omega^2\cdot 2)`$ |  | $`\begin{pmatrix}0 & 1 & 2 & 1 & 2\cr 0 & 1 & 1 & 1 & 1\cr 0 & 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\varphi(3,0) = \psi_0(\Omega^3)`$ |  | $`\begin{pmatrix}0 & 1 & 2 & 2\cr 0 & 1 & 1 & 1\cr 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\varphi(\omega,0) = \psi_0(\Omega^\omega)`$ |  | $`\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 0\cr 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\varphi(\varepsilon_0,0) = \psi_0(\Omega^{\varepsilon_0})`$ |  | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4\cr 0 & 1 & 1 & 0 & 1\cr 0 & 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\Gamma_0 = \psi_0(\Omega^\Omega)`$ | フェファーマン・シュッテ順序数（ATR₀） | $`\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 1 & 1\cr 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\Gamma_1 = \psi_0(\Omega^\Omega\cdot 2)`$ |  | $`\begin{pmatrix}0 & 1 & 2 & 3 & 1 & 2 & 3\cr 0 & 1 & 1 & 1 & 1 & 1 & 1\cr 0 & 0 & 0 & 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\varphi(1,1,0) = \psi_0(\Omega^{\Omega+1})`$ |  | $`\begin{pmatrix}0 & 1 & 2 & 3 & 2\cr 0 & 1 & 1 & 1 & 1\cr 0 & 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\varphi(2,0,0) = \psi_0(\Omega^{\Omega\cdot 2})`$ |  | $`\begin{pmatrix}0 & 1 & 2 & 3 & 2 & 3\cr 0 & 1 & 1 & 1 & 1 & 1\cr 0 & 0 & 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\varphi(1,0,0,0) = \psi_0(\Omega^{\Omega^2})`$ | アッカーマン順序数 | $`\begin{pmatrix}0 & 1 & 2 & 3 & 3\cr 0 & 1 & 1 & 1 & 1\cr 0 & 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\psi_0(\Omega^{\Omega^\omega})`$ | 小ヴェブレン順序数 (SVO) | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4\cr 0 & 1 & 1 & 1 & 0\cr 0 & 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\psi_0(\Omega^{\Omega^\Omega})`$ | 大ヴェブレン順序数 (LVO) | $`\begin{pmatrix}0 & 1 & 2 & 3 & 4\cr 0 & 1 & 1 & 1 & 1\cr 0 & 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\psi_0(\Omega_2)`$ | バッハマン・ハワード順序数（ID₁ / KP） | $`\begin{pmatrix}0 & 1 & 2\cr 0 & 1 & 2\cr 0 & 0 & 0\end{pmatrix}`$ |
| $`\psi_0(\Omega_3)`$ |  | $`\begin{pmatrix}0 & 1 & 2 & 3\cr 0 & 1 & 2 & 3\cr 0 & 0 & 0 & 0\end{pmatrix}`$ |
| $`\psi_0(\Omega_\omega)`$ | **2 行の限界**（ペア数列の限界）。行 2 が初めて立つ | $`\begin{pmatrix}0 & 1\cr 0 & 1\cr 0 & 1\end{pmatrix}`$ |
