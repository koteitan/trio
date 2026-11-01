# 悪い吸収の上げの形と、エンジンの広げ方（2026-11-01、trio-claude）

## 測定（tmp/claude/abs_slack.py、結果 abs_slack_20261101.json）
吸収 AbsAt が破れた 226 枠（t0 2、t2 224）で、Lhd z でない変化の列:
- BadAbsShape の 220 枠: 列 i だけ（v・o とも Lhd_{v(m)}、m = P1 i）。
- 残り 6 枠（41・42・43 列、graftD など）: 列 i と c = i − 1 だけ。どちらも Lhd_{v(m)}。
6 枠の形: P0 i = P1 i = m、i は m に数えられない（CL M m = [32]）、upg M c = some i、v(c) = v(i)、
CL c = CL i = []、P0 c = p ≠ m、P1 c = m、CL M p = CL N p = [c]、v(p) 不変、o(p) は Lhd z。
回収: Lhd_{v(p)} は 6 枠中 4 枠で偽。代わりに ∀ u, ∀ g ∈ comps u v(m), g < σ.o c が 6 枠すべてで真。

## Lean
- V3AbsUpgLemma（84ce3c7d）: lhd_psi_disG（Lhd V b0 b と ∀ u ≤ v, comps u V ≤ b0 から ψ_v(b0) ◁ ψ_v(b)）、
  o_frame_lhdVG。
- 次（codex に C2 として依頼）: WfT2X1U.bad_frameG（許容 V が添字でない bad_frame）、
  deps_lhd_otXU（hBdS を hBdUp: 上げの閉包、hBdF: 枠の形 に替える。vupg が悪い列を読む枝と、
  最後の数える子が許容 v(P1 c) ≠ v(p) の枝を足す）。
- その後: WfT2X2/X3/R4 を通して T2BelowAtV3 の入力を AbsWNx の広い形（BadAbsShape ∨ 上げの形）に替える。
- t = 0: T0AbsW（AbsWN）を AbsWNx 版に替え、t0_dep_otS の結論を PX 形にする（B0 で鎖を列挙中）。
