/-
Small.lean: 小さい行列を 1 個ずつ `W` に入れる。

残核 `Subst1gReviveSelf` は一般の閉包だが、**個別の行列**なら既存の緑の補題だけで
落ちることがある。最初の 1 個:

    (0,0,0)(1,1,1)(1,0,0) ∈ W 0        (= psi_0(Omega_omega + 1) の標準形)

末尾列 `(1,0,0)` は行 1 も行 2 も 0 なので `srow = 0`、したがって増分は
`d0 = d1 = 0`。しかも親が根なので `M.take 0 = []`。展開は `(0,0,0)(1,1,1)` を
**そのまま** n 個並べるだけになり、`W_flatMap_copies` がそのまま閉じる。
一般形は `L53.mem_W_of_flat_root`（`srow = 0` かつ `parent = 0`）で、この文書は
その最初の具体例である。

⚠ 同じ手は残り 8 個には効かない。`srow > 0` だとコピーが `shTower` になり
（`ShiftTowerClosed`）、`parent ≥ 1` だと `take` が空でなくなって `rsum` が要る
（＝残核）。表:

| 3 列目    | srow | parent |                      |
|-----------|------|--------|----------------------|
| `(1,0,0)` | 0    | 0      | ← ここだけ落ちる     |
| `(1,1,0)` | 1    | 0      | shTower              |
| `(1,1,1)` | 2    | 0      | shTower              |
| `(2,0,0)` | 0    | 1      | rsum（残核）         |
| `(2,1,0)` | 1    | 0      | shTower              |
| `(2,1,1)` | 2    | 0      | shTower              |
| `(2,2,0)` | 1    | 1      | 両方                 |
| `(2,2,1)` | 2    | 0      | shTower              |

**緑の補題だけで届く範囲**（`tools/probe_green.py` で閉包を取った実測）。
`zeroRow2_mem_Wself` / `snoc_zeroRow2` / `two_col_mem_W` / `snoc_orphan_W` /
`mem_W_of_flat_root` / `prefixCopies_of_rsum` / `W_add` の 7 本を、短い行列から
順に当てられるだけ当てる:

    z<2 標準形（<=5 列・値<=3）903 個のうち 257 個
      1 列   1/1      2 列   4/4      3 列  12/19
      4 列  48/120    5 列 192/759

**届かない最小のものは、ちょうど上の表の 7 個**（`(2,2,2)` は z=2 で断片の外）。
7 個それぞれについて `⟦n⟧` を n<=6 まで閉包に当てても、`(1,0,0)` 以外は
`⟦2⟧` で既に届かない。壁の位置は実測でここに確定している。
-/
import L53Subst

namespace TRIO
namespace Small

open Wset

/-- 2 列の塊 `(0,0,0)(1,1,1)`。 -/
def Q : TrioSeq := [(0, 0, 0), (1, 1, 1)]

/-- 目標の 3 列 `(0,0,0)(1,1,1)(1,0,0)`。 -/
def M : TrioSeq := [(0, 0, 0), (1, 1, 1), (1, 0, 0)]

theorem Q_mem : Q ∈ W 0 := two_col_mem_W (by omega) (by omega) (1, 1, 1)

theorem Q_root : ∀ p ∈ Q, entry Q 0 0 ≤ p.1 := by
  intro p _; simp [Q, entry]

theorem M_len : M.length = 3 := by simp [M]

theorem M_srow : srow M 2 = 0 := by simp [srow, M, entry]

theorem M_hasParent : hasParent M 0 2 := by
  rw [hasParent_zero_iff (by rw [M_len]; omega)]
  exact ⟨0, by omega, by simp [M, entry]⟩

/-- 親は根。行 1 の列 `(1,1,1)` は深さ 1 なので候補から外れる。 -/
theorem M_parent : parent M 0 2 = 0 := by
  have h := parent_nextR M_hasParent
  rw [nextR, if_pos rfl] at h
  obtain ⟨-, -, hlt, hval, -⟩ := h
  have h1 : entry M 0 2 = 1 := by simp [M, entry]
  have hcase : parent M 0 2 = 0 ∨ parent M 0 2 = 1 := by omega
  rcases hcase with h | h
  · exact h
  · rw [h, h1] at hval; simp [M, entry] at hval

/-- 展開はどの `n` でも `Q` をそのまま `n` 個並べたもの。 -/
theorem oper_M (n : ℕ) : M⟦n⟧ = (List.range n).flatMap fun _ => Q := by
  have h2 : M.length - 1 = 2 := by rw [M_len]
  simp only [oper, h2, M_srow, M_parent]
  rw [if_neg (by omega), if_neg (by simp [M, entry]),
    if_neg (by rw [h2, M_srow]; exact not_not_intro M_hasParent)]
  simp [M, entry, Q, List.range']

/-- **`(0,0,0)(1,1,1)(1,0,0) ∈ W 0`** — 残核を使わずに落ちる最初の 3 列。
一般形 `L53.mem_W_of_flat_root` の具体例として書いてある。 -/
theorem M_mem : M ∈ W 0 := by
  refine L53.mem_W_of_flat_root (Q := Q) (j1 := 2) (by rw [M_len]) (by omega)
    (by simp [M, entry]) M_srow M_hasParent M_parent ?_ Q_mem Q_root
  simp [M, entry, Q, List.range']

/-- 同じことを段のない形で: `M ∈ Wself`（根のレベルが 0 なので `W 0` と同値）。 -/
theorem M_mem_Wself : M ∈ Wself := ((mem_Wself_iff 0 M).mp M_mem).1

#print axioms M_mem
#print axioms M_mem_Wself

end Small
end TRIO
