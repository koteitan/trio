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
`mem_W_of_flat_root` / `prefixCopies_of_rsum` / `W_add` / `mem_of_oper_mem` の
8 本を、短い行列から順に当てられるだけ当てる（不動点まで反復）:

    z<2 標準形（<=5 列・値<=3）903 個のうち 261 個
      1 列   1/1      2 列   4/4      3 列  12/19
      4 列  49/120    5 列 195/759

`(0,0,0)(1,1,1)(1,0,0)` の上に**行 0 だけの列**を足す限りは伸びる:

    X := (0,0,0)(1,1,1)(1,0,0)
      X(0,0,0)  srow=0  snoc_orphan_W
      X(1,0,0)  srow=0  mem_W_of_flat_root
      X(2,0,0)  srow=0  mem_of_oper_mem（各段は flat_root、n の帰納法が要る）
      X(2,1,0)  srow=1  届かない
      X(2,1,1)  srow=2  届かない

**末尾列の `srow` が 0 でなくなった瞬間に落ちる。** ただしこれはこの梯子の上での
話で、全体では `srow = 0` でも到達は 40%（行 2 に 1 がある行列に絞ると 8%）。

**届かない最小のものは、ちょうど上の表の 7 個**（`(2,2,2)` は z=2 で断片の外）。
7 個それぞれについて `⟦n⟧` を n<=6 まで閉包に当てても、`(1,0,0)` 以外は
`⟦2⟧` で既に届かない。壁の位置は実測でここに確定している。
-/
import L53Subst
import H12Export

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

/-! ## 梯子の次の段

`X ++ (1,0,0)^m`（`X = (0,0,0)(1,1,1)`）は、末尾の `(1,0,0)` の親が必ず根なので
`mem_W_of_flat_root` が毎回当たる。`m` の帰納法で全部 `W 0` に入り、その上で
`X(1,0,0)(2,0,0)⟦n⟧ = X ++ (1,0,0)^n` だから規則 A で `X(1,0,0)(2,0,0)` も入る。 -/

/-- `X ++ (1,0,0)^m`。 -/
def Mm (m : ℕ) : TrioSeq := [(0, 0, 0), (1, 1, 1)] ++ List.replicate m (1, 0, 0)

theorem Mm_len (m : ℕ) : (Mm m).length = m + 2 := by simp [Mm]

theorem Mm_zero : Mm 0 = Q := by simp [Mm, Q]

theorem Mm_succ (m : ℕ) : Mm (m + 1) = Mm m ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
  simp [Mm, List.replicate_succ']

theorem Mm_dropLast (m : ℕ) : (Mm (m + 1)).dropLast = Mm m := by
  rw [Mm_succ]; simp

theorem Mm_entry0 (m : ℕ) : entry (Mm m) 0 0 = 0 := by simp [Mm, entry]

theorem Mm_entry_pos {m j : ℕ} (hj : 1 ≤ j) (hlt : j < m + 2) :
    entry (Mm m) 0 j = 1 := by
  have : (Mm m).getD j (0, 0, 0) = ((1, 1, 1) : ℕ × ℕ × ℕ) ∨
      (Mm m).getD j (0, 0, 0) = ((1, 0, 0) : ℕ × ℕ × ℕ) := by
    rcases Nat.lt_or_ge j 2 with h | h
    · left
      have : j = 1 := by omega
      subst this; simp [Mm]
    · right
      have hj2 : j - 2 < m := by omega
      simp only [Mm, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by simp; omega)]
      simp [hj2]
  rcases this with h | h <;> simp only [entry, h] <;> rfl

/-- 3 行を並べたものは、その列そのもの。 -/
theorem triple_entry (M : TrioSeq) {j : ℕ} (hj : j < M.length) :
    ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ) = M[j] := by
  simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

/-- `mem_W_of_flat_root` が要求するブロックの形は、ただの `take`。 -/
theorem map_range'_entry {M : TrioSeq} {k : ℕ} (hk : k ≤ M.length) :
    (List.range' 0 k).map
        (fun j => ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ))
      = M.take k := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    have hik : i < k := by simpa using h1
    simp only [List.getElem_map, List.getElem_range', List.getElem_take, Nat.zero_add, Nat.one_mul]
    exact triple_entry M (lt_of_lt_of_le hik hk)

theorem Mm_last (m : ℕ) : (Mm (m + 1))[m + 2]? = some ((1, 0, 0) : ℕ × ℕ × ℕ) := by
  simp [Mm]

theorem Mm_entry_last (m : ℕ) :
    entry (Mm (m + 1)) 0 (m + 2) = 1 ∧ entry (Mm (m + 1)) 1 (m + 2) = 0 ∧
      entry (Mm (m + 1)) 2 (m + 2) = 0 := by
  have h : (Mm (m + 1)).getD (m + 2) (0, 0, 0) = ((1, 0, 0) : ℕ × ℕ × ℕ) := by
    rw [List.getD_eq_getElem?_getD, Mm_last]; rfl
  refine ⟨?_, ?_, ?_⟩ <;> simp only [entry, h] <;> rfl

theorem Mm_srow (m : ℕ) : srow (Mm (m + 1)) (m + 2) = 0 := by
  obtain ⟨-, h1, h2⟩ := Mm_entry_last m
  simp [srow, h1, h2]

theorem Mm_hasParent (m : ℕ) : hasParent (Mm (m + 1)) 0 (m + 2) := by
  rw [hasParent_zero_iff (by rw [Mm_len]; omega)]
  exact ⟨0, by omega, by rw [Mm_entry0, (Mm_entry_last m).1]; omega⟩

theorem Mm_parent (m : ℕ) : parent (Mm (m + 1)) 0 (m + 2) = 0 := by
  have h := parent_nextR (Mm_hasParent m)
  rw [nextR, if_pos rfl] at h
  obtain ⟨-, -, hlt, hval, -⟩ := h
  by_contra hne
  have h1 : 1 ≤ parent (Mm (m + 1)) 0 (m + 2) := by omega
  rw [Mm_entry_pos h1 (by omega), (Mm_entry_last m).1] at hval
  omega

/-- **`X ++ (1,0,0)^m ∈ W 0`**（`m` の帰納法、各段が `mem_W_of_flat_root`）。 -/
theorem Mm_mem : ∀ m, Mm m ∈ W 0
  | 0 => by rw [Mm_zero]; exact Q_mem
  | (m + 1) => by
      obtain ⟨he0, -, -⟩ := Mm_entry_last m
      refine L53.mem_W_of_flat_root (Q := Mm m) (j1 := m + 2)
        (by rw [Mm_len]; omega) (by omega) (by rw [he0]; simp)
        (Mm_srow m) (Mm_hasParent m) (Mm_parent m) ?_ (Mm_mem m) ?_
      · rw [Nat.sub_zero, map_range'_entry (by rw [Mm_len]; omega),
          ← Mm_dropLast m, List.dropLast_eq_take, Mm_len]
        congr 1
      · intro p _; rw [Mm_entry0]; exact Nat.zero_le _

/-! ## 梯子の 2 段目: `X(1,0,0)(2,0,0)`

展開はどの `n` でも `Mm n`。したがって規則 A（`mem_of_oper_mem`）で閉じる。 -/

/-- `X ++ (1,0,0)(2,0,0)` = ψ(Ω_ω)·ω^ω の標準形。 -/
def M2 : TrioSeq := [(0, 0, 0), (1, 1, 1), (1, 0, 0), (2, 0, 0)]

theorem M2_len : M2.length = 4 := by simp [M2]

theorem M2_srow : srow M2 3 = 0 := by simp [srow, M2, entry]

theorem M2_hasParent : hasParent M2 0 3 := by
  rw [hasParent_zero_iff (by rw [M2_len]; omega)]
  exact ⟨2, by omega, by simp [M2, entry]⟩

/-- 親は 2 番目の列 `(1,0,0)`。手前の 2 列は最小性で外れる。 -/
theorem M2_parent : parent M2 0 3 = 2 := by
  have h := parent_nextR M2_hasParent
  rw [nextR, if_pos rfl] at h
  obtain ⟨-, -, hlt, -, hmin⟩ := h
  have hcase : parent M2 0 3 = 0 ∨ parent M2 0 3 = 1 ∨ parent M2 0 3 = 2 := by omega
  rcases hcase with h | h | h
  · exact absurd (hmin 1 ⟨by omega, by omega⟩) (by simp [M2, entry])
  · exact absurd (hmin 2 ⟨by omega, by omega⟩) (by simp [M2, entry])
  · exact h

theorem flatMap_singleton_range (a : ℕ × ℕ × ℕ) (n : ℕ) :
    (List.range n).flatMap (fun _ => [a]) = List.replicate n a := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.flatMap_append, ih]; simp [List.replicate_succ']

theorem oper_M2 (n : ℕ) : M2⟦n⟧ = Mm n := by
  have h3 : M2.length - 1 = 3 := by rw [M2_len]
  simp only [oper, h3, M2_srow, M2_parent]
  rw [if_neg (by omega), if_neg (by simp [M2, entry]),
    if_neg (by rw [h3, M2_srow]; exact not_not_intro M2_hasParent)]
  simp [Mm, M2, entry, flatMap_singleton_range]

/-- **`X(1,0,0)(2,0,0) ∈ W 0`** — 梯子の 2 段目。 -/
theorem M2_mem : M2 ∈ W 0 :=
  mem_of_oper_mem (fun n _ => (oper_M2 n) ▸ Mm_mem n)

/-! ## 一般化した 1 段: 根の直下に `(1,0,0)` を継ぐ

`Mm` の各段でやったことは、行列に固有ではない。**根が `(0,0,0)` で、他の列が全部
深さ 1 以上**なら、末尾に `(1,0,0)` を継いでよい（親が必ず根なので
`mem_W_of_flat_root`）。これで梯子の (1,0,0) 方向は何段でも伸びる。 -/

/-- **根の直下に `(1,0,0)` を継ぐのは無料**（`P` の根が深さ 0、他が深さ 1 以上のとき）。 -/
theorem snoc_one {P : TrioSeq} (hP : P ∈ W 0) (hne : P ≠ [])
    (h0 : entry P 0 0 = 0)
    (hdeep : ∀ j, 1 ≤ j → j < P.length → 1 ≤ entry P 0 j) :
    P ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  set M : TrioSeq := P ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] with hM
  have hplen : 0 < P.length := List.length_pos_iff.mpr hne
  have hlen : M.length = P.length + 1 := by rw [hM]; simp
  have hlast : entry M 0 P.length = 1 ∧ entry M 1 P.length = 0 ∧
      entry M 2 P.length = 0 := by
    have h : M.getD P.length (0, 0, 0) = ((1, 0, 0) : ℕ × ℕ × ℕ) := by
      rw [hM, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp
    refine ⟨?_, ?_, ?_⟩ <;> simp only [entry, h] <;> rfl
  have hpre : ∀ j, j < P.length → entry M 0 j = entry P 0 j := by
    intro j hj
    simp [hM, entry, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  have hsr : srow M P.length = 0 := by
    obtain ⟨-, h1, h2⟩ := hlast; simp [srow, h1, h2]
  have hpar : hasParent M 0 P.length := by
    rw [hasParent_zero_iff (by omega)]
    exact ⟨0, hplen, by rw [hpre 0 hplen, h0, hlast.1]; omega⟩
  have hj0 : parent M 0 P.length = 0 := by
    have h := parent_nextR hpar
    rw [nextR, if_pos rfl] at h
    obtain ⟨-, -, hlt, hval, -⟩ := h
    by_contra hne0
    have h1 : 1 ≤ parent M 0 P.length := by omega
    rw [hpre _ (by omega), hlast.1] at hval
    have := hdeep (parent M 0 P.length) h1 (by omega)
    omega
  refine L53.mem_W_of_flat_root (Q := P) (j1 := P.length)
    (by rw [hlen]; omega) (by omega) (by rw [hlast.1]; simp) hsr hpar hj0 ?_ hP ?_
  · rw [Nat.sub_zero, map_range'_entry (by rw [hlen]; omega), hM, List.take_left]
  · intro p _; rw [h0]; exact Nat.zero_le _

/-! ## 継ぎ足しの不変量

`snoc_one` の仮定「根が深さ 0・他は深さ 1 以上」は継ぎ足しで保たれる。名前を付けて
おくと、梯子を何段でも回せる。 -/

/-- 根が深さ 0 で、他の列は深さ 1 以上。 -/
def Deep (P : TrioSeq) : Prop :=
  entry P 0 0 = 0 ∧ ∀ j, 1 ≤ j → j < P.length → 1 ≤ entry P 0 j

theorem entry_append_lt {P : TrioSeq} {c : ℕ × ℕ × ℕ} {i j : ℕ} (hj : j < P.length) :
    entry (P ++ [c]) i j = entry P i j := by
  simp [entry, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem entry_append_last {P : TrioSeq} {c : ℕ × ℕ × ℕ} :
    entry (P ++ [c]) 0 P.length = c.1 ∧ entry (P ++ [c]) 1 P.length = c.2.1 ∧
      entry (P ++ [c]) 2 P.length = c.2.2 := by
  have h : (P ++ [c]).getD P.length (0, 0, 0) = c := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp
  refine ⟨?_, ?_, ?_⟩ <;> simp [entry, h]

theorem Deep_snoc {P : TrioSeq} {c : ℕ × ℕ × ℕ} (hP : Deep P) (hne : P ≠ [])
    (hc : 1 ≤ c.1) : Deep (P ++ [c]) := by
  have hplen : 0 < P.length := List.length_pos_iff.mpr hne
  refine ⟨by rw [entry_append_lt hplen]; exact hP.1, ?_⟩
  intro j h1 h2
  simp only [List.length_append, List.length_cons, List.length_nil] at h2
  rcases Nat.lt_or_ge j P.length with h | h
  · rw [entry_append_lt h]; exact hP.2 j h1 h
  · have : j = P.length := by omega
    subst this; rw [entry_append_last.1]; exact hc

theorem Deep_replicate {P : TrioSeq} (hne : P ≠ []) (hd : Deep P) :
    ∀ m, Deep (P ++ List.replicate m ((1, 0, 0) : ℕ × ℕ × ℕ))
  | 0 => by simpa using hd
  | (m + 1) => by
      have ih := Deep_replicate hne hd m
      have hne' : P ++ List.replicate m ((1, 0, 0) : ℕ × ℕ × ℕ) ≠ [] := by
        simp [List.append_eq_nil_iff, hne]
      have h := Deep_snoc (c := ((1, 0, 0) : ℕ × ℕ × ℕ)) ih hne' (le_refl 1)
      rwa [List.append_assoc, ← List.replicate_succ'] at h

/-- **`(1,0,0)` は何段でも継げる。** -/
theorem snoc_one_iter {P : TrioSeq} (hP : P ∈ W 0) (hne : P ≠ []) (hd : Deep P) :
    ∀ m, P ++ List.replicate m ((1, 0, 0) : ℕ × ℕ × ℕ) ∈ W 0
  | 0 => by simpa using hP
  | (m + 1) => by
      have ih := snoc_one_iter hP hne hd m
      have hne' : P ++ List.replicate m ((1, 0, 0) : ℕ × ℕ × ℕ) ≠ [] := by
        simp [List.append_eq_nil_iff, hne]
      have hd' := Deep_replicate hne hd m
      have h := snoc_one ih hne' hd'.1 hd'.2
      rwa [List.append_assoc, ← List.replicate_succ'] at h

/-! ## `(1,0,0)(2,0,0)` を継ぐ

`P ++ [(1,0,0),(2,0,0)]` の展開はどの `m` でも `P ++ (1,0,0)^m`。したがって
`snoc_one_iter` と規則 A で閉じる。`Deep` は保たれるので、この組は**何段でも**継げる。 -/

theorem entry_app2_lt {P : TrioSeq} {a b : ℕ × ℕ × ℕ} {i j : ℕ} (hj : j < P.length) :
    entry (P ++ [a, b]) i j = entry P i j := by
  simp [entry, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem getD_app2_a {P : TrioSeq} {a b : ℕ × ℕ × ℕ} :
    (P ++ [a, b]).getD P.length (0, 0, 0) = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]; simp

theorem getD_app2_b {P : TrioSeq} {a b : ℕ × ℕ × ℕ} :
    (P ++ [a, b]).getD (P.length + 1) (0, 0, 0) = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]; simp

/-- **`(1,0,0)(2,0,0)` を継ぐのも無料。** -/
theorem snoc_two {P : TrioSeq} (hP : P ∈ W 0) (hne : P ≠ []) (hd : Deep P) :
    P ++ [((1, 0, 0) : ℕ × ℕ × ℕ), (2, 0, 0)] ∈ W 0 := by
  set M : TrioSeq := P ++ [((1, 0, 0) : ℕ × ℕ × ℕ), (2, 0, 0)] with hM
  have hplen : 0 < P.length := List.length_pos_iff.mpr hne
  have hlen : M.length - 1 = P.length + 1 := by rw [hM]; simp
  have hb : entry M 0 (P.length + 1) = 2 ∧ entry M 1 (P.length + 1) = 0 ∧
      entry M 2 (P.length + 1) = 0 := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [entry, hM, getD_app2_b]
  have ha : entry M 0 P.length = 1 := by simp [entry, hM, getD_app2_a]
  have hsr : srow M (P.length + 1) = 0 := by simp [srow, hb.2.1, hb.2.2]
  have hpar : hasParent M 0 (P.length + 1) := by
    rw [hasParent_zero_iff (by rw [hM]; simp)]
    exact ⟨P.length, by omega, by rw [ha, hb.1]; omega⟩
  have hj0 : parent M 0 (P.length + 1) = P.length := by
    have h := parent_nextR hpar
    rw [nextR, if_pos rfl] at h
    obtain ⟨-, -, hlt, -, hmin⟩ := h
    by_contra hne0
    have hlt' : parent M 0 (P.length + 1) < P.length := by omega
    have := hmin P.length ⟨hlt', by omega⟩
    rw [ha, hb.1] at this
    omega
  refine mem_of_oper_mem (fun m _ => ?_)
  have hop : M⟦m⟧ = P ++ List.replicate m ((1, 0, 0) : ℕ × ℕ × ℕ) := by
    simp only [oper, hlen, hsr, hj0]
    rw [if_neg (by omega), if_neg (by rw [hb.1]; simp),
      if_neg (by rw [hlen, hsr]; exact not_not_intro hpar)]
    have htk : M.take P.length = P := by rw [hM, List.take_left]
    have hcol : ((entry M 0 P.length, entry M 1 P.length, entry M 2 P.length) : ℕ × ℕ × ℕ)
        = (1, 0, 0) := by simp [entry, hM, getD_app2_a]
    rw [htk]
    congr 1
    simp only [show P.length + 1 - P.length = 1 from by omega,
      show (List.range' P.length 1) = [P.length] from rfl,
      List.map_cons, List.map_nil, lt_self_iff_false, if_false, Nat.not_lt_zero,
      Nat.mul_zero, ite_self, Nat.add_zero, hcol]
    exact flatMap_singleton_range _ m
  rw [hop]
  exact snoc_one_iter hP hne hd m

theorem Deep_snoc_two {P : TrioSeq} (hne : P ≠ []) (hd : Deep P) :
    Deep (P ++ [((1, 0, 0) : ℕ × ℕ × ℕ), (2, 0, 0)]) := by
  have h1 := Deep_snoc (c := ((1, 0, 0) : ℕ × ℕ × ℕ)) hd hne (le_refl 1)
  have h2 := Deep_snoc (c := ((2, 0, 0) : ℕ × ℕ × ℕ)) h1
    (by simp [List.append_eq_nil_iff, hne]) (by omega)
  rwa [List.append_assoc] at h2

/-! ## 梯子: `X ++ [(1,0,0)(2,0,0)]^n`

`snoc_two` と `Deep_snoc_two` を交互に回すだけで、この族は**全ての `n`** で `W 0`。
これは以前の計測で「緑の補題では届かない」と出ていた 3 つの行列のうちの 1 族である
（届かなかったのは判定器の打ち切りのせいで、数学的な壁ではなかった）。 -/

/-- `X ++ [(1,0,0)(2,0,0)]^n`。 -/
def Rep : ℕ → TrioSeq
  | 0 => Q
  | (n + 1) => Rep n ++ [((1, 0, 0) : ℕ × ℕ × ℕ), (2, 0, 0)]

theorem Q_deep : Deep Q := by
  refine ⟨by simp [Q, entry], ?_⟩
  intro j h1 h2
  simp only [Q, List.length_cons, List.length_nil] at h2
  have : j = 1 := by omega
  subst this; simp [Q, entry]

theorem Rep_ne : ∀ n, Rep n ≠ []
  | 0 => by simp [Rep, Q]
  | (n + 1) => by simp [Rep]

theorem Rep_deep : ∀ n, Deep (Rep n)
  | 0 => Q_deep
  | (n + 1) => Deep_snoc_two (Rep_ne n) (Rep_deep n)

/-- **`X ++ [(1,0,0)(2,0,0)]^n ∈ W 0`（全ての `n`）。** -/
theorem Rep_mem : ∀ n, Rep n ∈ W 0
  | 0 => Q_mem
  | (n + 1) => snoc_two (Rep_mem n) (Rep_ne n) (Rep_deep n)

/-- ついでに、その上に `(1,0,0)` を何段でも足せる。 -/
theorem Rep_one_mem (n m : ℕ) :
    Rep n ++ List.replicate m ((1, 0, 0) : ℕ × ℕ × ℕ) ∈ W 0 :=
  snoc_one_iter (Rep_mem n) (Rep_ne n) (Rep_deep n) m

/-! ## master 補題: 末尾に 1 列継ぐ

`L53.oper_flat` は `srow = 0` の末尾列について展開を閉じた形で与える。ブロックは
「`take j1` してから `drop j0`」に他ならないので、`A ++ [b]` の形に整えると
**「コピー族が済んでいれば末尾 1 列は無料」**という 1 本にまとまる。
`snoc_one` / `snoc_two` はこの系である。 -/

theorem map_range'_entry_drop {M : TrioSeq} {j0 j1 : ℕ} (h1 : j1 ≤ M.length) (h0 : j0 ≤ j1) :
    (List.range' j0 (j1 - j0)).map
        (fun j => ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ))
      = (M.take j1).drop j0 := by
  apply List.ext_getElem
  · simp; omega
  · intro i hA hB
    have hik : i < j1 - j0 := by simpa using hA
    simp only [List.getElem_map, List.getElem_range', List.getElem_drop, List.getElem_take,
      Nat.one_mul]
    exact triple_entry M (by omega)

/-- **末尾 1 列は、そのコピー族が済んでいれば無料。** -/
theorem snoc_flat {A : TrioSeq} {b : ℕ × ℕ × ℕ} {j0 : ℕ} (hne : A ≠ [])
    (hb : b.1 ≠ 0) (hb1 : b.2.1 = 0) (hb2 : b.2.2 = 0)
    (hpar : hasParent (A ++ [b]) 0 A.length)
    (hj0 : parent (A ++ [b]) 0 A.length = j0)
    (hcop : ∀ n, A.take j0 ++ (List.range n).flatMap (fun _ => A.drop j0) ∈ W 0) :
    A ++ [b] ∈ W 0 := by
  set M : TrioSeq := A ++ [b] with hM
  have hplen : 0 < A.length := List.length_pos_iff.mpr hne
  have hlen : M.length - 1 = A.length := by rw [hM]; simp
  have hlast : entry M 0 A.length = b.1 ∧ entry M 1 A.length = b.2.1 ∧
      entry M 2 A.length = b.2.2 := entry_append_last
  have hsr : srow M A.length = 0 := by
    simp [srow, hlast.2.1, hlast.2.2, hb1, hb2]
  have hj0le : j0 ≤ A.length := by
    rw [← hj0]; exact le_of_lt (nextR_index_lt (parent_nextR hpar))
  refine mem_of_oper_mem (fun n _ => ?_)
  have hop := L53.oper_flat (M := M) (j1 := A.length) (j0 := j0) hlen.symm (by omega)
    (by rw [hlast.1]; simp [hb]) hsr hpar hj0.symm n
  rw [hop, map_range'_entry_drop (by rw [hM]; simp) hj0le]
  have htk : M.take A.length = A := by rw [hM, List.take_left]
  rw [htk, show M.take j0 = A.take j0 by rw [hM, List.take_append_of_le_length hj0le]]
  exact hcop n

/-! ## 一般の継ぎ足しでの `Deep`

`Deep` が見るのは行 0 だけなので、継ぎ足す列が全部深さ 1 以上なら保たれる。 -/

theorem entry0_eq {M : TrioSeq} {j : ℕ} : entry M 0 j = (M.getD j (0, 0, 0)).1 := rfl

theorem Deep_append {P B : TrioSeq} (hd : Deep P) (hne : P ≠ [])
    (hB : ∀ c ∈ B, 1 ≤ c.1) : Deep (P ++ B) := by
  have hplen : 0 < P.length := List.length_pos_iff.mpr hne
  have hlt : ∀ j, j < P.length → entry (P ++ B) 0 j = entry P 0 j := by
    intro j hj
    simp [entry, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  refine ⟨by rw [hlt 0 hplen]; exact hd.1, ?_⟩
  intro j h1 h2
  rcases Nat.lt_or_ge j P.length with h | h
  · rw [hlt j h]; exact hd.2 j h1 h
  · have hj : j - P.length < B.length := by simp at h2; omega
    have hg : (P ++ B).getD j (0, 0, 0) = B[j - P.length] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h]
      simp [List.getElem?_eq_getElem hj]
    rw [entry0_eq, hg]
    exact hB _ (List.getElem_mem hj)

/-! ## 継ぎ足す塊 `App k = (1,0,0)(2,0,0)^k`

`P ++ App (k+1)` の末尾列 `(2,0,0)` の親は、`k` によらず必ず `(1,0,0)`（位置 `|P|`）。
間の列は全部深さ 2 なので最小性を邪魔しない。 -/

/-- `(1,0,0)(2,0,0)^k`。 -/
def App (k : ℕ) : TrioSeq := ((1, 0, 0) : ℕ × ℕ × ℕ) :: List.replicate k ((2, 0, 0) : ℕ × ℕ × ℕ)

theorem App_len (k : ℕ) : (App k).length = k + 1 := by simp [App]

theorem App_succ (k : ℕ) : App (k + 1) = App k ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] := by
  simp [App, List.replicate_succ']

theorem App_col (k : ℕ) : ∀ c ∈ App k, 1 ≤ c.1 := by
  intro c hc
  rcases List.mem_cons.mp hc with h | h
  · subst h; exact le_refl 1
  · rw [List.eq_of_mem_replicate h]; omega

theorem App_getD (k i : ℕ) (hi : i < k + 1) :
    (App k).getD i (0, 0, 0) = if i = 0 then ((1, 0, 0) : ℕ × ℕ × ℕ) else (2, 0, 0) := by
  cases i with
  | zero => simp [App]
  | succ i =>
      have : i < k := by omega
      simp [App, List.getD_eq_getElem?_getD, List.getElem?_replicate, this]

theorem entry_app_at {P : TrioSeq} {k i : ℕ} (hi : i < k + 1) :
    entry (P ++ App k) 0 (P.length + i) = if i = 0 then 1 else 2 := by
  have hg : (P ++ App k).getD (P.length + i) (0, 0, 0) = (App k).getD i (0, 0, 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      List.getD_eq_getElem?_getD]
    simp
  rw [entry0_eq, hg, App_getD k i hi]
  cases i <;> simp

theorem Reps_col (k n : ℕ) :
    ∀ c ∈ (List.range n).flatMap (fun _ => App k), 1 ≤ c.1 := by
  intro c hc
  rw [List.mem_flatMap] at hc
  obtain ⟨-, -, h⟩ := hc
  exact App_col k c h

theorem App_hasParent {P : TrioSeq} (hne : P ≠ []) (k : ℕ) :
    hasParent ((P ++ App k) ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) 0 (P ++ App k).length := by
  have hlen : (P ++ App k).length = P.length + (k + 1) := by simp [App_len]
  rw [hasParent_zero_iff (by simp)]
  refine ⟨P.length, by omega, ?_⟩
  rw [entry_append_lt (by omega), entry_append_last.1,
    show P.length = P.length + 0 from by omega, entry_app_at (by omega)]
  simp

theorem App_parent {P : TrioSeq} (hne : P ≠ []) (k : ℕ) :
    parent ((P ++ App k) ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) 0 (P ++ App k).length = P.length := by
  have hlen : (P ++ App k).length = P.length + (k + 1) := by simp [App_len]
  have hone : entry ((P ++ App k) ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) 0 P.length = 1 := by
    rw [entry_append_lt (by omega), show P.length = P.length + 0 from by omega,
      entry_app_at (by omega)]; simp
  have htwo : ∀ i, 1 ≤ i → i < k + 1 →
      entry ((P ++ App k) ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) 0 (P.length + i) = 2 := by
    intro i h1 h2
    rw [entry_append_lt (by omega), entry_app_at h2]
    simp; omega
  have h := parent_nextR (App_hasParent hne k)
  rw [nextR, if_pos rfl] at h
  set p := parent ((P ++ App k) ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) 0 (P ++ App k).length with hp
  obtain ⟨-, -, hlt, hval, hmin⟩ := h
  rw [entry_append_last.1] at hval
  by_contra hne0
  rcases Nat.lt_or_ge p P.length with h1 | h1
  · have := hmin P.length ⟨h1, by omega⟩
    rw [entry_append_last.1, hone] at this
    omega
  · have hi : p = P.length + (p - P.length) := by omega
    rw [hi, htwo (p - P.length) (by omega) (by omega)] at hval
    omega

/-- **`App k` は何段でも継げる**（`k` の帰納法、内側は `n` の帰納法）。 -/
theorem app_iter : ∀ k, ∀ {P : TrioSeq}, P ∈ W 0 → P ≠ [] → Deep P →
    ∀ n, P ++ (List.range n).flatMap (fun _ => App k) ∈ W 0 := by
  intro k
  induction k with
  | zero =>
      intro P hP hne hd n
      rw [show ((List.range n).flatMap fun _ => App 0)
          = List.replicate n ((1, 0, 0) : ℕ × ℕ × ℕ) from by
        simpa [App] using flatMap_singleton_range ((1, 0, 0) : ℕ × ℕ × ℕ) n]
      exact snoc_one_iter hP hne hd n
  | succ k ih =>
      have single : ∀ {P : TrioSeq}, P ∈ W 0 → P ≠ [] → Deep P → P ++ App (k + 1) ∈ W 0 := by
        intro P hP hne hd
        rw [App_succ, ← List.append_assoc]
        refine snoc_flat (A := P ++ App k) (b := ((2, 0, 0) : ℕ × ℕ × ℕ)) (j0 := P.length)
          (by simp [List.append_eq_nil_iff, hne]) (by omega) rfl rfl
          (App_hasParent hne k) (App_parent hne k) ?_
        intro n
        rw [List.take_left, List.drop_left]
        exact ih hP hne hd n
      intro P hP hne hd n
      induction n with
      | zero => simpa using hP
      | succ n ihn =>
          rw [show ((List.range (n + 1)).flatMap fun _ => App (k + 1))
              = ((List.range n).flatMap fun _ => App (k + 1)) ++ App (k + 1) from by
            rw [List.range_succ, List.flatMap_append]; simp]
          rw [← List.append_assoc]
          exact single ihn (by simp [List.append_eq_nil_iff, hne])
            (Deep_append hd hne (Reps_col (k + 1) n))

/-- 1 回分（`n = 1`）。 -/
theorem app_mem {P : TrioSeq} (hP : P ∈ W 0) (hne : P ≠ []) (hd : Deep P) (k : ℕ) :
    P ++ App k ∈ W 0 := by simpa using app_iter k hP hne hd 1

theorem Q_ne : Q ≠ [] := by simp [Q]

/-! ## 梯子の 3 段目: `X(1,0,0)(2,0,0)(3,0,0)`

展開は `X ++ App n`。`app_mem` が全ての `n` で与えるので規則 A で閉じる。 -/

/-- `X ++ (1,0,0)(2,0,0)(3,0,0)` = ψ(Ω_ω)·ω^ω^ω の標準形。 -/
def M3 : TrioSeq := [(0, 0, 0), (1, 1, 1), (1, 0, 0), (2, 0, 0), (3, 0, 0)]

theorem QApp1 : Q ++ App 1 = [(0, 0, 0), (1, 1, 1), (1, 0, 0), (2, 0, 0)] := by
  simp [Q, App]

theorem M3_eq : M3 = (Q ++ App 1) ++ [((3, 0, 0) : ℕ × ℕ × ℕ)] := by
  rw [QApp1]; rfl

theorem M3_hasParent : hasParent ((Q ++ App 1) ++ [((3, 0, 0) : ℕ × ℕ × ℕ)]) 0 4 := by
  rw [QApp1]
  rw [hasParent_zero_iff (by simp)]
  exact ⟨3, by omega, by simp [entry]⟩

theorem M3_parent : parent ((Q ++ App 1) ++ [((3, 0, 0) : ℕ × ℕ × ℕ)]) 0 4 = 3 := by
  have h := parent_nextR M3_hasParent
  rw [nextR, if_pos rfl] at h
  set p := parent ((Q ++ App 1) ++ [((3, 0, 0) : ℕ × ℕ × ℕ)]) 0 4 with hp
  obtain ⟨-, -, hlt, -, hmin⟩ := h
  have hcase : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega
  rcases hcase with h | h | h | h
  · exact absurd (hmin 3 ⟨by omega, by omega⟩) (by rw [QApp1]; simp [entry])
  · exact absurd (hmin 3 ⟨by omega, by omega⟩) (by rw [QApp1]; simp [entry])
  · exact absurd (hmin 3 ⟨by omega, by omega⟩) (by rw [QApp1]; simp [entry])
  · exact h

/-- **`X(1,0,0)(2,0,0)(3,0,0) ∈ W 0`** — 梯子の 3 段目。 -/
theorem M3_mem : M3 ∈ W 0 := by
  rw [M3_eq]
  refine snoc_flat (A := Q ++ App 1) (b := ((3, 0, 0) : ℕ × ℕ × ℕ)) (j0 := 3)
    (by simp [Q, App]) (by omega) rfl rfl
    (by simpa [QApp1] using M3_hasParent) (by simpa [QApp1] using M3_parent) ?_
  intro n
  rw [show (Q ++ App 1).take 3 = Q ++ App 0 from by simp [Q, App],
    show (Q ++ App 1).drop 3 = [((2, 0, 0) : ℕ × ℕ × ℕ)] from by simp [Q, App]]
  rw [show ((List.range n).flatMap fun _ => [((2, 0, 0) : ℕ × ℕ × ℕ)])
      = List.replicate n ((2, 0, 0) : ℕ × ℕ × ℕ) from flatMap_singleton_range _ n]
  rw [show Q ++ App 0 ++ List.replicate n ((2, 0, 0) : ℕ × ℕ × ℕ) = Q ++ App n from by
    simp [App, List.append_assoc]]
  exact app_mem Q_mem Q_ne Q_deep n

/-! ## 次の的: `Iterable`

`snoc_flat` は「末尾 1 列は、**その親の位置での接尾辞コピー族**が済んでいれば無料」
と言っている。だから次の性質が閉じれば、梯子は深さに関係なく全部回る。

    Iterable P := ∀ q < |P|, ∀ n, P.take q ++ (P.drop q)^n ∈ W 0

`Deep`（根が深さ 0・他は深さ 1 以上）は、これの**深さ 1 に特化した弱い版**である。
深さ 1 でだけ `Deep` で足りたのは、継ぎ足す塊の親が必ず根で、`take 0 = []` に
なってコピー族が `W_flatMap_copies` で無料になるから。深さ 2 以上では
`take q ≠ []` になり、`PrefixCopiesOpen` の開いている場合に入る。

計測（`tools/probe_iterable.py`、上界は `r49.Wup` で False が健全）:
梯子が生成する形 `X ++ (1,0,0)^a1 (2,0,0)^a2 … (d,0,0)^ad`（d ≤ 4, a ≤ 3）で
**判定 3219 件・反例 0**。 -/

/-- どの接尾辞も繰り返せる。`snoc_flat` の仮定をまとめたもの。 -/
def Iterable (P : TrioSeq) : Prop :=
  ∀ q, q < P.length → ∀ n,
    P.take q ++ (List.range n).flatMap (fun _ => P.drop q) ∈ W 0

/-! ### なぜ深さ 1 で止まるか（再帰を追った結果）

`snoc_flat` で末尾 1 列を剥がすと、親の位置 `j0` で

    P ++ Q^n  ⟶  (P ++ Q^(n-1) ++ Q[:r]) ++ (Q[r : |Q|-1])^m

となる。**深さ 1 の梯子**では `Q = App k = (1,0,0)(2,0,0)^k` で、親は必ず `Q` の
先頭の `(1,0,0)`（`r = 0`）なので

    P ++ (App k)^n  ⟶  P ++ (App (k-1))^m

と **`k` が 1 つ減る**。底の `App 0 = [(1,0,0)]` では親が根に落ちて `take 0 = []` に
なり、`W_flatMap_copies` で無料。だから `app_iter` は回る。

**深さ 2 では底が変わる**。`AppAt2 k = (2,0,0)(3,0,0)^k` の底 `[(2,0,0)]` を継ぐと、
親は根ではなく `(1,0,0)` になり

    (X ++ (1,0,0) ++ S) ++ (2,0,0)^m
      ⟶  X ++ [(1,0,0) ++ S ++ (2,0,0)^(m-1)]^i

で、ブロックが **`S` を巻き込んで伸びる**。`S` は再帰のたびに育つので、
ブロックの長さでも深さでも整礎な測度が取れない。

⟹ **深さ 1 が特別だったのは「親が根に落ちて `take` が空になる」からで、
深さ 2 以上ではそこが閉じない。** 止まる理由は順序数の減少しかなく、それは `W`
そのもの。つまりここが `PrefixCopiesOpen` が開いている理由の、梯子から見た姿である。

計測（両側とも健全、`tools/probe_pcdeep.py`）:

    P in W 0, Deep P, Q の根が深さ 1, Q の全列が深さ 1 以上  ==>  P ++ Q^n in W 0
    判定 12870 件 / 反例 0

`Mm` / `Rep` / `app_iter` は全部この特殊ケースで、梯子の 4 段目以降は
一般形を要求する。 -/

/-! ## bump: 接頭辞を不問にする

`B` の末尾列が `B` の中に親を持つなら、`A ++ bump B` のバッドルートも `bump B` の
中で止まるので、**`A` が何であってもよい**（`bump B` = 行 0 に一律 +1）。

`Column.oper_append_right` はこれを `entry T 0 0 = 0` で実現しているが、`bump B` の
根は深さ 1 なので使えない。`Wset.nextR_src_ge`（アンカー仮定なしで「接頭辞は親を
供給できない」）から作った版なら通る。 -/

/-- **`oper_append_right` のアンカー不要版**。 -/
theorem oper_append_right_of (A T : TrioSeq) (n : ℕ) (hT : 2 ≤ T.length)
    (hp : hasParent T (srow T (T.length - 1)) (T.length - 1)) :
    oper (A ++ T) n = A ++ oper T n := by
  have hlenAT : (A ++ T).length - 1 = A.length + (T.length - 1) := by
    rw [List.length_append]; omega
  unfold oper
  set j1 := T.length - 1 with hj1
  rw [hlenAT, if_neg (by omega : ¬ (A.length + j1 = 0)), if_neg (by omega : ¬ (j1 = 0))]
  rw [entry_append_right A T 0 j1, entry_append_right A T 1 j1, entry_append_right A T 2 j1]
  have hz : ¬ (entry T 0 j1 = 0 ∧ entry T 1 j1 = 0 ∧ entry T 2 j1 = 0) := by
    rintro ⟨h0, -, -⟩
    exact no_hasParent_of_row0_zero h0 hp
  rw [if_neg hz, if_neg hz, srow_append_right A T j1]
  have hpAT : hasParent (A ++ T) (srow T j1) (A.length + j1) :=
    Wset.hasParent_append_right_of A T hp
  rw [if_neg (not_not.2 hpAT), if_neg (not_not.2 hp)]
  have hpar : parent (A ++ T) (srow T j1) (A.length + j1)
      = A.length + parent T (srow T j1) j1 := parent_append_right_of A T hp
  set j0 := parent T (srow T j1) j1 with hj0
  simp only [hpar]
  have hd0 : entry T 0 j1 - entry (A ++ T) 0 (A.length + j0)
      = entry T 0 j1 - entry T 0 j0 := by rw [entry_append_right]
  have hd1 : entry T 1 j1 - entry (A ++ T) 1 (A.length + j0)
      = entry T 1 j1 - entry T 1 j0 := by rw [entry_append_right]
  rw [hd0, hd1]
  have hrange : (A.length + j1) - (A.length + j0) = j1 - j0 := by omega
  rw [hrange, take_append_right, List.append_assoc, hpar]
  congr 1
  congr 1
  apply List.flatMap_congr
  intro k _
  exact copyblock_append A T j0 j0 (j1 - j0) k _ _

/-- `bump B` = 行 0 に一律 +1。 -/
def bump (B : TrioSeq) : TrioSeq := shiftr01 1 0 B

theorem bump_len (B : TrioSeq) : (bump B).length = B.length := by simp [bump, shiftr01]

theorem bump_nil : bump [] = [] := by simp [bump, shiftr01]

theorem bump_col {B : TrioSeq} : ∀ c ∈ bump B, 1 ≤ c.1 := by
  intro c hc
  simp only [bump, shiftr01, List.mem_map] at hc
  obtain ⟨p, -, rfl⟩ := hc
  omega

/-- **展開は bump をすり抜ける。** -/
theorem oper_bump (A B : TrioSeq) (n : ℕ) (hlen : 2 ≤ B.length)
    (hp : hasParent B (srow B (B.length - 1)) (B.length - 1)) :
    (A ++ bump B)⟦n⟧ = A ++ bump (B⟦n⟧) := by
  have h2 : 2 ≤ (bump B).length := by rw [bump_len]; exact hlen
  have hp' : hasParent (bump B) (srow (bump B) ((bump B).length - 1))
      ((bump B).length - 1) := by
    rw [bump_len, bump, srow_shiftr01, hasParent_shiftr01]; exact hp
  rw [bump, oper_append_right_of A _ n (by simpa [bump] using h2) (by simpa [bump] using hp'),
    oper_shiftr01]
  rfl

/-! ## 平坦な `B`

行 1・行 2 が恒等的に 0 の `B`（＝埋め込まれた原始数列）なら `srow = 0` なので、
末尾列が全零でない限り必ず親を持つ。これで場合分けが 2 つに閉じる。 -/

/-- 行 1・行 2 が恒等的に 0。 -/
def Flat (B : TrioSeq) : Prop := ∀ c ∈ B, c.2.1 = 0 ∧ c.2.2 = 0

theorem Flat_entry {B : TrioSeq} (h : Flat B) (j : ℕ) :
    entry B 1 j = 0 ∧ entry B 2 j = 0 := by
  rcases Nat.lt_or_ge j B.length with hj | hj
  · have hm := h _ (List.getElem_mem hj)
    have hg : B.getD j (0, 0, 0) = B[j] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    constructor <;> simp only [entry, hg] <;> simp [hm.1, hm.2]
  · constructor <;>
      simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hj]

theorem Flat_srow {B : TrioSeq} (h : Flat B) (j : ℕ) : srow B j = 0 := by
  obtain ⟨h1, h2⟩ := Flat_entry h j
  simp [srow, h1, h2]

theorem Flat_dropLast {B : TrioSeq} (h : Flat B) : Flat B.dropLast :=
  fun c hc => h c (List.dropLast_subset _ hc)

theorem Flat_pred {B : TrioSeq} (h : Flat B) : Flat (Pred B) := by
  unfold Pred
  by_cases hc : B.length ≤ 1
  · rw [if_pos hc]; exact h
  · rw [if_neg hc]; exact Flat_dropLast h

/-- **平坦なら展開も平坦。** `srow = 0` なので増分は `d0 = d1 = 0`、写しは元の列
そのものになる。 -/
theorem Flat_oper {B : TrioSeq} (h : Flat B) (n : ℕ) : Flat (B⟦n⟧) := by
  by_cases hL : B.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]; exact h
  by_cases hz : entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
      entry B 2 (B.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL hz]; exact Flat_pred h
  by_cases hp : hasParent B 0 (B.length - 1)
  · rw [L53.oper_flat (j0 := parent B 0 (B.length - 1)) rfl hL hz
      (Flat_srow h _) hp rfl n]
    intro c hc
    rcases List.mem_append.mp hc with hm | hm
    · exact h c (List.mem_of_mem_take hm)
    · rw [List.mem_flatMap] at hm
      obtain ⟨k, -, hm2⟩ := hm
      rw [List.mem_map] at hm2
      obtain ⟨j, hj, rfl⟩ := hm2
      have hjr := List.mem_range'_1.1 hj
      exact h _ (Wset.entry_pair_mem (by omega))
  · rw [oper_eq_pred_of_noParent n hL hz (by rw [Flat_srow h]; exact hp)]
    exact Flat_pred h

/-! ## 本丸: bump に沿った帰納法

`B` が平坦（行 1・行 2 が 0）で根が深さ 0 なら、`A ++ bump B` の**バッドルートは
必ず `bump B` の中で止まる**。だから展開は `A` を素通りして `A ++ bump (B⟦n⟧)` に
なり、`B` 自身の `W` 帰納法がそのまま `A ++ bump B` の帰納法になる。`A` は
`W 0` の `Deep` な行列なら何でもよい。 -/

/-- **`B ∈ W 0`（平坦・根 0）なら、どの `Deep` な `A ∈ W 0` に対しても
`A ++ bump B ∈ W 0`。** -/
theorem bump_mem :
    ∀ B ∈ W 0, Flat B → entry B 0 0 = 0 →
      ∀ A : TrioSeq, A ∈ W 0 → A ≠ [] → Deep A → A ++ bump B ∈ W 0 := by
  have key : W 0 ⊆ {B : TrioSeq | Flat B → entry B 0 0 = 0 →
      ∀ A : TrioSeq, A ∈ W 0 → A ≠ [] → Deep A → A ++ bump B ∈ W 0} := by
    refine A2' ?_
    intro B hB
    simp only [Set.mem_setOf_eq]
    intro hflat hroot A hA hAne hAd
    by_cases hshort : B.length ≤ 1
    · rcases (by omega : B.length = 0 ∨ B.length = 1) with h0 | h1
      · have hnil : B = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        simpa [bump_nil] using hA
      · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
        obtain ⟨hc1, hc2⟩ := hflat c (by simp)
        have hc0 : c.1 = 0 := hroot
        have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1 hc2)
        subst hcz
        have hb : bump [((0, 0, 0) : ℕ × ℕ × ℕ)] = [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
          simp [bump, shiftr01]
        rw [hb]
        exact snoc_one hA hAne hAd.1 hAd.2
    have hlen2 : 2 ≤ B.length := by omega
    have hBne : B ≠ [] := by
      intro hc; rw [hc] at hlen2; simp at hlen2
    rcases hB with ⟨hl, -⟩ | hnat | ⟨m, hm, -, -⟩
    · exact absurd hl hshort
    · by_cases hlast : entry B 0 (B.length - 1) = 0
      · -- 末尾列は `(0,0,0)`。展開は `dropLast`、`bump` の末尾は `(1,0,0)`。
        obtain ⟨he1, he2⟩ := Flat_entry hflat (B.length - 1)
        have hz : entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
            entry B 2 (B.length - 1) = 0 := ⟨hlast, he1, he2⟩
        have hcol : B.getD (B.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ)
            = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hlast (Prod.ext he1 he2)
        have hgl : B.getLast hBne = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
          have h1 : B.getLast hBne = B.getD (B.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
            rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show B.length - 1 < B.length by omega)]
            rfl
          rw [h1, hcol]
        have hsplit : B = B.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
          rw [← hgl]
          exact (List.dropLast_append_getLast hBne).symm
        have hop : B⟦1⟧ = B.dropLast := by
          rw [oper_eq_pred_of_zero 1 (by omega) hz]
          unfold Pred
          rw [if_neg (by omega)]
        have hdl := hnat 1 le_rfl
        rw [hop] at hdl
        simp only [Set.mem_setOf_eq] at hdl
        have hdl0 : entry B.dropLast 0 0 = 0 := by
          rw [List.dropLast_eq_take,
            Wset.entry_take (show (0 : ℕ) < B.length - 1 by omega)]
          exact hroot
        have hIH := hdl (Flat_dropLast hflat) hdl0 A hA hAne hAd
        have hDne : A ++ bump B.dropLast ≠ [] := by
          simp [List.append_eq_nil_iff, hAne]
        have hD : Deep (A ++ bump B.dropLast) :=
          Deep_append hAd hAne (fun c hc => bump_col c hc)
        have hbs : bump B = bump B.dropLast ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
          conv_lhs => rw [hsplit]
          simp [bump, shiftr01]
        rw [hbs, ← List.append_assoc]
        exact snoc_one hIH hDne hD.1 hD.2
      · -- 末尾列は非零。根が深さ 0 なので `B` の中に親がある。
        have hp0 : hasParent B 0 (B.length - 1) := by
          rw [Wset.hasParent_zero_iff (show B.length - 1 < B.length by omega)]
          exact ⟨0, by omega, by rw [hroot]; omega⟩
        have hp : hasParent B (srow B (B.length - 1)) (B.length - 1) := by
          rw [Flat_srow hflat]; exact hp0
        refine A1_intro (Or.inr (Or.inl ?_))
        intro n hn
        rw [oper_bump A B n hlen2 hp]
        exact hnat n hn (Flat_oper hflat n)
          (by rw [Wset.oper_head_eq hn]; exact hroot) A hA hAne hAd
    · exact absurd hm (Nat.not_lt_zero m)
  intro B hB
  exact key hB

/-! ## 系: 平坦な `B` は無条件で `W 0` に居る

行 2 が恒等的に 0 の行列は（2 行 BMS そのものなので）`Wtower2.zeroRow2_mem_Wself`
で `Wself` に入る。平坦なら根のレベルも 0 なので段は 0 でよい。したがって
`bump_mem` の `B ∈ W 0` は仮定ではなく**定理**になる。 -/

theorem Flat_mem_W {B : TrioSeq} (h : Flat B) : B ∈ W 0 := by
  refine (mem_Wself_iff 0 B).mpr ⟨zeroRow2_mem_Wself (fun p hp => (h p hp).2), ?_⟩
  obtain ⟨h1, h2⟩ := Flat_entry h 0
  simp [lev, h1, h2]

/-- **`A ++ bump B`（`B` は任意の平坦な行列）。** 順序数では `o(A) * o(B)`。 -/
theorem bump_flat {B : TrioSeq} (hf : Flat B) (hroot : entry B 0 0 = 0)
    {A : TrioSeq} (hA : A ∈ W 0) (hAne : A ≠ []) (hAd : Deep A) :
    A ++ bump B ∈ W 0 :=
  bump_mem B (Flat_mem_W hf) hf hroot A hA hAne hAd

/-- 継ぎ足した後も `Deep` なので、いくらでも重ねられる。 -/
theorem Deep_bump_flat {B A : TrioSeq} (hAne : A ≠ []) (hAd : Deep A) :
    Deep (A ++ bump B) :=
  Deep_append hAd hAne (fun c hc => bump_col c hc)

/-! ## 梯子 `X(1,0,0)(2,0,0)…(k,0,0)`

`Chain k = (0,0,0)(1,0,0)…(k,0,0)` は平坦で根が深さ 0。`bump` すると
`(1,0,0)(2,0,0)…(k+1,0,0)`。これで `M`・`M2`・`M3` が一斉に出る。 -/

/-- 平らな梯子 `(0,0,0)(1,0,0)…(k,0,0)`。 -/
def Chain (k : ℕ) : TrioSeq := (List.range (k + 1)).map fun i => ((i, 0, 0) : ℕ × ℕ × ℕ)

theorem Chain_flat (k : ℕ) : Flat (Chain k) := by
  intro c hc
  simp only [Chain, List.mem_map] at hc
  obtain ⟨i, -, rfl⟩ := hc
  exact ⟨rfl, rfl⟩

theorem Chain_root (k : ℕ) : entry (Chain k) 0 0 = 0 := by
  simp [Chain, entry, List.getD_eq_getElem?_getD, List.range_succ_eq_map]

theorem bump_Chain (k : ℕ) :
    bump (Chain k) = (List.range (k + 1)).map fun i => ((i + 1, 0, 0) : ℕ × ℕ × ℕ) := by
  simp [bump, shiftr01, Chain, List.map_map, Function.comp_def]

/-- **`A ++ (1,0,0)(2,0,0)…(k+1,0,0) ∈ W 0`（すべての `k`）。** -/
theorem chain_mem {A : TrioSeq} (hA : A ∈ W 0) (hAne : A ≠ []) (hAd : Deep A) (k : ℕ) :
    A ++ (List.range (k + 1)).map (fun i => ((i + 1, 0, 0) : ℕ × ℕ × ℕ)) ∈ W 0 := by
  rw [← bump_Chain]
  exact bump_flat (Chain_flat k) (Chain_root k) hA hAne hAd

/-- 梯子の 3 段目 `M3` を `bump_flat` で取り直す（`M3_mem` の別証明）。 -/
theorem M3_mem' : M3 ∈ W 0 := by
  have h := chain_mem Q_mem Q_ne Q_deep 2
  simpa [M3, Q, List.range_succ] using h

/-! ## 一般化: 行 2 ≡ 0 の `B`

`Flat`（行 1 も 0）は「行 2 ≡ 0 ＋ **深さ 0 の列は `(0,0,0)` に限る**」まで緩められ
る。同じ帰納法が回る理由は「末尾列が非零なら必ず `B` の中に親がある」で、これは

* 深さ 0 の列は `(0,0,0)`（だから末尾が非零なら深さ >= 1）
* 深さ >= 1 の列は行 0 の親を持ち、深さが厳密に減るので根まで辿れる
* 辿り着いた深さ 0 の列は行 1 が 0 なので、行 1 の親としても使える

から出る。行 2 ≡ 0 なので `srow <= 1`、すなわち `d1 = 0`（行 1 は持ち上がらない）。
順序数では `o(A) * o(B)` で、`o(B)` は 2 行 BMS の全域を走る。 -/

/-- 行 2 が恒等的に 0（＝埋め込まれた 2 行 BMS）。 -/
def Z2 (B : TrioSeq) : Prop := ∀ c ∈ B, c.2.2 = 0

/-- 深さ 0 の列は `(0,0,0)` に限る。 -/
def Zroot (B : TrioSeq) : Prop := ∀ c ∈ B, c.1 = 0 → c.2.1 = 0 ∧ c.2.2 = 0

theorem Flat_Z2 {B : TrioSeq} (h : Flat B) : Z2 B := fun c hc => (h c hc).2

theorem Flat_Zroot {B : TrioSeq} (h : Flat B) : Zroot B := fun c hc _ => h c hc

theorem Z2_entry {B : TrioSeq} (h : Z2 B) (j : ℕ) : entry B 2 j = 0 := by
  rcases Nat.lt_or_ge j B.length with hj | hj
  · have hg : B.getD j (0, 0, 0) = B[j] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    have hm := h _ (List.getElem_mem hj)
    show (B.getD j ((0, 0, 0) : ℕ × ℕ × ℕ)).2.2 = 0
    rw [hg]; exact hm
  · simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hj]

theorem Zroot_entry {B : TrioSeq} (h : Zroot B) {j : ℕ} (h0 : entry B 0 j = 0) :
    entry B 1 j = 0 ∧ entry B 2 j = 0 := by
  rcases Nat.lt_or_ge j B.length with hj | hj
  · have hg : B.getD j (0, 0, 0) = B[j] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    have hb0 : (B.getD j ((0, 0, 0) : ℕ × ℕ × ℕ)).1 = 0 := h0
    rw [hg] at hb0
    obtain ⟨e1, e2⟩ := h _ (List.getElem_mem hj) hb0
    refine ⟨?_, ?_⟩
    · show (B.getD j ((0, 0, 0) : ℕ × ℕ × ℕ)).2.1 = 0
      rw [hg]; exact e1
    · show (B.getD j ((0, 0, 0) : ℕ × ℕ × ℕ)).2.2 = 0
      rw [hg]; exact e2
  · constructor <;>
      simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hj]

theorem Z2_srow_le {B : TrioSeq} (h : Z2 B) (j : ℕ) : srow B j ≤ 1 := by
  unfold srow
  rw [if_neg (by rw [Z2_entry h j]; omega)]
  split <;> omega

theorem mem_of_mem_Pred {B : TrioSeq} {c : ℕ × ℕ × ℕ} (hc : c ∈ Pred B) : c ∈ B := by
  unfold Pred at hc
  by_cases h : B.length ≤ 1
  · rwa [if_pos h] at hc
  · rw [if_neg h] at hc; exact List.dropLast_subset _ hc

/-- **行 2 ≡ 0 と Zroot は展開で保たれる。** 行 1 の持ち上げ `d1` が 0 なのが要点。 -/
theorem Z2Zroot_oper {B : TrioSeq} (hz2 : Z2 B) (hzr : Zroot B) (n : ℕ) :
    Z2 (B⟦n⟧) ∧ Zroot (B⟦n⟧) := by
  by_cases hL : B.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]; exact ⟨hz2, hzr⟩
  by_cases hz : entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
      entry B 2 (B.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL hz]
    exact ⟨fun c hc => hz2 c (mem_of_mem_Pred hc),
      fun c hc => hzr c (mem_of_mem_Pred hc)⟩
  by_cases hp : hasParent B (srow B (B.length - 1)) (B.length - 1)
  · have hd1 : (0 : ℕ) = if 1 < srow B (B.length - 1) then
        entry B 1 (B.length - 1)
          - entry B 1 (parent B (srow B (B.length - 1)) (B.length - 1)) else 0 := by
      rw [if_neg (by have := Z2_srow_le hz2 (B.length - 1); omega)]
    rw [L53.oper_unfold (d1 := 0) rfl hL hz rfl hp rfl rfl hd1 n]
    simp only [Nat.mul_zero, ite_self, Nat.add_zero]
    constructor
    · intro c hc
      rcases List.mem_append.mp hc with hm | hm
      · exact hz2 c (List.mem_of_mem_take hm)
      · rw [List.mem_flatMap] at hm
        obtain ⟨k, -, hm2⟩ := hm
        rw [List.mem_map] at hm2
        obtain ⟨j, -, rfl⟩ := hm2
        exact Z2_entry hz2 j
    · intro c hc hc0
      rcases List.mem_append.mp hc with hm | hm
      · exact hzr c (List.mem_of_mem_take hm) hc0
      · rw [List.mem_flatMap] at hm
        obtain ⟨k, -, hm2⟩ := hm
        rw [List.mem_map] at hm2
        obtain ⟨j, -, rfl⟩ := hm2
        have hj0 : entry B 0 j = 0 := by dsimp only at hc0; omega
        exact Zroot_entry hzr hj0
  · rw [oper_eq_pred_of_noParent n hL hz hp]
    exact ⟨fun c hc => hz2 c (mem_of_mem_Pred hc),
      fun c hc => hzr c (mem_of_mem_Pred hc)⟩

/-- 行 0 の祖先を辿ると必ず深さ 0 の列に着く（根が深さ 0 だから途中で止まらない）。 -/
theorem rtg0_to_root {B : TrioSeq} (hroot : entry B 0 0 = 0) :
    ∀ v j, entry B 0 j = v → j < B.length →
      ∃ c, entry B 0 c = 0 ∧ Relation.ReflTransGen (nextrel0 B) c j := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro j hv hj
    rcases Nat.eq_zero_or_pos v with rfl | hpos
    · exact ⟨j, hv, Relation.ReflTransGen.refl⟩
    · have hj0 : 0 < j := by
        rcases Nat.eq_zero_or_pos j with rfl | h
        · omega
        · exact h
      have hpp : hasParent B 0 j := by
        rw [Wset.hasParent_zero_iff hj]
        exact ⟨0, hj0, by omega⟩
      have hn : nextrel0 B (parent B 0 j) j := by
        have h := parent_nextR hpp
        rwa [nextR, if_pos rfl] at h
      obtain ⟨c, hc0, hcr⟩ :=
        ih (entry B 0 (parent B 0 j)) (by have := hn.2.2.2.1; omega)
          (parent B 0 j) rfl hn.1
      exact ⟨c, hc0, hcr.tail hn⟩

/-- **末尾列が非零なら必ず `B` の中に親がある。** -/
theorem hasParent_of_Zroot {B : TrioSeq} (hz2 : Z2 B) (hzr : Zroot B)
    (hroot : entry B 0 0 = 0) (hlen : 2 ≤ B.length)
    (hnz : ¬ (entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
      entry B 2 (B.length - 1) = 0)) :
    hasParent B (srow B (B.length - 1)) (B.length - 1) := by
  have hj : B.length - 1 < B.length := by omega
  have h2 : entry B 2 (B.length - 1) = 0 := Z2_entry hz2 _
  have h0 : entry B 0 (B.length - 1) ≠ 0 := by
    intro hc
    obtain ⟨e1, e2⟩ := Zroot_entry hzr hc
    exact hnz ⟨hc, e1, e2⟩
  by_cases h1 : entry B 1 (B.length - 1) = 0
  · have hs : srow B (B.length - 1) = 0 := by
      unfold srow; rw [if_neg (by omega), if_neg (by omega)]
    rw [hs, Wset.hasParent_zero_iff hj]
    exact ⟨0, by omega, by omega⟩
  · have hs : srow B (B.length - 1) = 1 := by
      unfold srow; rw [if_neg (by omega), if_pos (by omega)]
    rw [hs]
    obtain ⟨c, hc0, hcr⟩ :=
      rtg0_to_root hroot (entry B 0 (B.length - 1)) (B.length - 1) rfl hj
    obtain ⟨e1, -⟩ := Zroot_entry hzr hc0
    exact H12Export.hasParent1_of_le0_witness hj hcr (by omega)

/-- **`A ++ bump B`（`B` は行 2 ≡ 0 ＋ Zroot）。** `Flat` 版の一般化。 -/
theorem bump_mem2 :
    ∀ B ∈ W 0, Z2 B → Zroot B → entry B 0 0 = 0 →
      ∀ A : TrioSeq, A ∈ W 0 → A ≠ [] → Deep A → A ++ bump B ∈ W 0 := by
  have key : W 0 ⊆ {B : TrioSeq | Z2 B → Zroot B → entry B 0 0 = 0 →
      ∀ A : TrioSeq, A ∈ W 0 → A ≠ [] → Deep A → A ++ bump B ∈ W 0} := by
    refine A2' ?_
    intro B hB
    simp only [Set.mem_setOf_eq]
    intro hz2 hzr hroot A hA hAne hAd
    by_cases hshort : B.length ≤ 1
    · rcases (by omega : B.length = 0 ∨ B.length = 1) with h0 | h1
      · have hnil : B = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        simpa [bump_nil] using hA
      · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
        have hc0 : c.1 = 0 := hroot
        obtain ⟨hc1, hc2⟩ := hzr c (by simp) hc0
        have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1 hc2)
        subst hcz
        have hb : bump [((0, 0, 0) : ℕ × ℕ × ℕ)] = [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
          simp [bump, shiftr01]
        rw [hb]
        exact snoc_one hA hAne hAd.1 hAd.2
    have hlen2 : 2 ≤ B.length := by omega
    have hBne : B ≠ [] := by
      intro hc; rw [hc] at hlen2; simp at hlen2
    rcases hB with ⟨hl, -⟩ | hnat | ⟨m, hm, -, -⟩
    · exact absurd hl hshort
    · by_cases hlast : entry B 0 (B.length - 1) = 0
      · -- 深さ 0 の末尾列は Zroot より `(0,0,0)`。展開は `dropLast`。
        obtain ⟨he1, he2⟩ := Zroot_entry hzr hlast
        have hz : entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
            entry B 2 (B.length - 1) = 0 := ⟨hlast, he1, he2⟩
        have hcol : B.getD (B.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ)
            = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hlast (Prod.ext he1 he2)
        have hgl : B.getLast hBne = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
          have h1 : B.getLast hBne = B.getD (B.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
            rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show B.length - 1 < B.length by omega)]
            rfl
          rw [h1, hcol]
        have hsplit : B = B.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
          rw [← hgl]
          exact (List.dropLast_append_getLast hBne).symm
        have hop : B⟦1⟧ = B.dropLast := by
          rw [oper_eq_pred_of_zero 1 (by omega) hz]
          unfold Pred
          rw [if_neg (by omega)]
        have hdl := hnat 1 le_rfl
        rw [hop] at hdl
        simp only [Set.mem_setOf_eq] at hdl
        have hdl0 : entry B.dropLast 0 0 = 0 := by
          rw [List.dropLast_eq_take,
            Wset.entry_take (show (0 : ℕ) < B.length - 1 by omega)]
          exact hroot
        have hIH := hdl (fun c hc => hz2 c (List.dropLast_subset _ hc))
          (fun c hc => hzr c (List.dropLast_subset _ hc)) hdl0 A hA hAne hAd
        have hDne : A ++ bump B.dropLast ≠ [] := by
          simp [List.append_eq_nil_iff, hAne]
        have hD : Deep (A ++ bump B.dropLast) :=
          Deep_append hAd hAne (fun c hc => bump_col c hc)
        have hbs : bump B = bump B.dropLast ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
          conv_lhs => rw [hsplit]
          simp [bump, shiftr01]
        rw [hbs, ← List.append_assoc]
        exact snoc_one hIH hDne hD.1 hD.2
      · have hnz : ¬ (entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
            entry B 2 (B.length - 1) = 0) := fun h => hlast h.1
        have hp := hasParent_of_Zroot hz2 hzr hroot hlen2 hnz
        refine A1_intro (Or.inr (Or.inl ?_))
        intro n hn
        rw [oper_bump A B n hlen2 hp]
        obtain ⟨hz2', hzr'⟩ := Z2Zroot_oper hz2 hzr n
        exact hnat n hn hz2' hzr' (by rw [Wset.oper_head_eq hn]; exact hroot) A hA hAne hAd
    · exact absurd hm (Nat.not_lt_zero m)
  intro B hB
  exact key hB

/-- 行 2 ≡ 0 ＋ Zroot ＋ 根が深さ 0 なら、`B ∈ W 0` は無条件。 -/
theorem Zroot_mem_W {B : TrioSeq} (hz2 : Z2 B) (hzr : Zroot B)
    (hroot : entry B 0 0 = 0) : B ∈ W 0 := by
  refine (mem_Wself_iff 0 B).mpr ⟨zeroRow2_mem_Wself hz2, ?_⟩
  obtain ⟨e1, e2⟩ := Zroot_entry hzr hroot
  simp [lev, e1, e2]

/-- **仮定は `B` の形だけ**: 行 2 ≡ 0・Zroot・根が深さ 0。 -/
theorem bump_z2 {B : TrioSeq} (hz2 : Z2 B) (hzr : Zroot B) (hroot : entry B 0 0 = 0)
    {A : TrioSeq} (hA : A ∈ W 0) (hAne : A ≠ []) (hAd : Deep A) :
    A ++ bump B ∈ W 0 :=
  bump_mem2 B (Zroot_mem_W hz2 hzr hroot) hz2 hzr hroot A hA hAne hAd

/-- **`X(1,0,0)(2,1,0) ∈ W 0`** — シートの行 278、`psi(Omega_omega) * eps_0`。
`srow = 1` なので旧来の緑の補題では届かなかった行列。 -/
theorem M278_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), (1, 1, 1), (1, 0, 0), (2, 1, 0)] ∈ W 0 := by
  have hz2 : Z2 [((0, 0, 0) : ℕ × ℕ × ℕ), (1, 1, 0)] := by
    intro c hc; simp at hc; rcases hc with rfl | rfl <;> rfl
  have hzr : Zroot [((0, 0, 0) : ℕ × ℕ × ℕ), (1, 1, 0)] := by
    intro c hc h0; simp at hc; rcases hc with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · simp at h0
  have h := bump_z2 hz2 hzr (by simp [entry]) Q_mem Q_ne Q_deep
  simpa [Q, bump, shiftr01] using h

/-! ## さらに一般化: 行 2 を許す（`Mono`）

`Z2`（行 2 ≡ 0）は「行 1 の親が根から取れる」ためだけに使っていた。行 2 まで
許すには行 2 の親も要るが、`Mono B`（行 2 <= 行 1）を足せば同じ論法で取れる:

  行 1 の親を辿ると行 1 = 0 の列に着く ⟹ `Mono` より行 2 も 0
  ⟹ その列が行 2 の親になる。

`Zroot` は行 2 があっても展開で保たれる（深さ 0 の写しは `k = 0` の分だけで、
それは元の列そのもの）。`Mono` も保たれる（行 1 しか持ち上がらない）。
ただし `B ∈ W 0` はここでは**本当の仮定**（行 2 があると `zeroRow2_mem_Wself`
が使えない）。それでも「`W 0` の元を 1 段深くして継げる」という閉包規則として
使える。 -/

/-- 行 2 <= 行 1。 -/
def Mono (B : TrioSeq) : Prop := ∀ c ∈ B, c.2.2 ≤ c.2.1

theorem Mono_entry {B : TrioSeq} (h : Mono B) (j : ℕ) : entry B 2 j ≤ entry B 1 j := by
  rcases Nat.lt_or_ge j B.length with hj | hj
  · have hg : B.getD j (0, 0, 0) = B[j] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    have hm := h _ (List.getElem_mem hj)
    show (B.getD j ((0, 0, 0) : ℕ × ℕ × ℕ)).2.2 ≤ (B.getD j ((0, 0, 0) : ℕ × ℕ × ℕ)).2.1
    rw [hg]; exact hm
  · simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hj]

theorem Z2_Mono {B : TrioSeq} (h : Z2 B) : Mono B := fun c hc => by rw [h c hc]; omega

open Classical in
/-- **深さ 0 の写しには行 1 の持ち上げが乗らない。** `Zroot` が展開で保たれる理由。 -/
theorem zroot_copy_key {B : TrioSeq} (hzr : Zroot B)
    (hz : ¬ (entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
      entry B 2 (B.length - 1) = 0))
    {i1 j0 j k d0 d1 : ℕ}
    (hi1 : i1 = srow B (B.length - 1)) (hj0 : j0 = parent B i1 (B.length - 1))
    (hd0 : d0 = if 0 < i1 then entry B 0 (B.length - 1) - entry B 0 j0 else 0)
    (hd1 : d1 = if 1 < i1 then entry B 1 (B.length - 1) - entry B 1 j0 else 0)
    (hj : entry B 0 j + (if le0 B j0 j then k * d0 else 0) = 0) :
    (if le1 B j0 j then k * d1 else 0) = 0 := by
  by_cases hle1 : le1 B j0 j
  · rw [if_pos hle1]
    have hle0 : le0 B j0 j := ⟨hle1.1, hle1.2.1, rtg1_to_rtg0 hle1.2.2⟩
    rw [if_pos hle0] at hj
    have hj0z : entry B 0 j = 0 := by omega
    have hkd0 : k * d0 = 0 := by omega
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hd0z : d0 = 0 := by
        rcases Nat.mul_eq_zero.mp hkd0 with h | h
        · omega
        · exact h
      rcases Nat.eq_zero_or_pos i1 with hi | hi
      · rw [hd1, if_neg (by omega)]; simp
      · exfalso
        have heq : j0 = j := rtg_to_root hj0z hle0.2.2
        have h0j0 : entry B 0 j0 = 0 := by rw [heq]; exact hj0z
        rw [hd0, if_pos hi] at hd0z
        have hlastz : entry B 0 (B.length - 1) = 0 := by omega
        obtain ⟨f1, f2⟩ := Zroot_entry hzr hlastz
        exact hz ⟨hlastz, f1, f2⟩
  · rw [if_neg hle1]

/-- **`Zroot` と `Mono` は展開で保たれる（行 2 の制限なし）。** -/
theorem ZM_oper {B : TrioSeq} (hzr : Zroot B) (hmo : Mono B) (n : ℕ) :
    Zroot (B⟦n⟧) ∧ Mono (B⟦n⟧) := by
  by_cases hL : B.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]; exact ⟨hzr, hmo⟩
  by_cases hz : entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
      entry B 2 (B.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL hz]
    exact ⟨fun c hc => hzr c (mem_of_mem_Pred hc),
      fun c hc => hmo c (mem_of_mem_Pred hc)⟩
  by_cases hp : hasParent B (srow B (B.length - 1)) (B.length - 1)
  · rw [L53.oper_unfold rfl hL hz rfl hp rfl rfl rfl n]
    constructor
    · intro c hc hc0
      rcases List.mem_append.mp hc with hm | hm
      · exact hzr c (List.mem_of_mem_take hm) hc0
      · rw [List.mem_flatMap] at hm
        obtain ⟨k, -, hm2⟩ := hm
        rw [List.mem_map] at hm2
        obtain ⟨j, -, rfl⟩ := hm2
        dsimp only at hc0 ⊢
        have hj0z : entry B 0 j = 0 := by omega
        obtain ⟨e1, e2⟩ := Zroot_entry hzr hj0z
        have hkey := zroot_copy_key (k := k) (j := j) hzr hz rfl rfl rfl rfl hc0
        exact ⟨by rw [e1, hkey], e2⟩
    · intro c hc
      rcases List.mem_append.mp hc with hm | hm
      · exact hmo c (List.mem_of_mem_take hm)
      · rw [List.mem_flatMap] at hm
        obtain ⟨k, -, hm2⟩ := hm
        rw [List.mem_map] at hm2
        obtain ⟨j, -, rfl⟩ := hm2
        dsimp only
        have := Mono_entry hmo j
        omega
  · rw [oper_eq_pred_of_noParent n hL hz hp]
    exact ⟨fun c hc => hzr c (mem_of_mem_Pred hc),
      fun c hc => hmo c (mem_of_mem_Pred hc)⟩

open Classical in
/-- **行 2 の親の存在**: `le1` 祖先に行 2 がより小さい列があれば親がある。 -/
theorem hasParent2_of_le1_witness {M : TrioSeq} {j y : ℕ} (hj : j < M.length)
    (hanc : Relation.ReflTransGen (nextrel1 M) y j) (hlt : entry M 2 y < entry M 2 j) :
    hasParent M 2 j := by
  classical
  have hyj : y < j := by
    rcases Relation.ReflTransGen.cases_tail hanc with h | ⟨c, hc1, hc2⟩
    · rw [h] at hlt; omega
    · exact lt_of_le_of_lt (rtg1_index_le hc1) hc2.2.2.1
  have hyle1 : le1 M y j := ⟨by omega, hj, hanc⟩
  obtain ⟨a, haj, halt, hale1, hamax⟩ :
      ∃ a, a < j ∧ entry M 2 a < entry M 2 j ∧ le1 M a j ∧
        ∀ x, a < x → le1 M x j → entry M 2 j ≤ entry M 2 x := by
    have hyT : y ∈ (Finset.range j).filter
        (fun x => entry M 2 x < entry M 2 j ∧ le1 M x j) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨hyj, hlt, hyle1⟩
    have hne : ((Finset.range j).filter
        (fun x => entry M 2 x < entry M 2 j ∧ le1 M x j)).Nonempty := ⟨y, hyT⟩
    have hmem := Finset.max'_mem _ hne
    simp only [Finset.mem_filter, Finset.mem_range] at hmem
    refine ⟨_, hmem.1, hmem.2.1, hmem.2.2, ?_⟩
    intro x hx1 hx2
    by_contra hc
    push Not at hc
    have hxj : x < j := lt_of_le_of_ne (rtg1_index_le hx2.2.2) (by rintro rfl; omega)
    have hxT : x ∈ (Finset.range j).filter
        (fun x => entry M 2 x < entry M 2 j ∧ le1 M x j) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨hxj, hc, hx2⟩
    exact absurd (Finset.le_max' _ x hxT) (by omega)
  have hstep : nextrel2 M a j :=
    ⟨by omega, hj, haj, halt, hale1, fun x hx => hamax x hx.1 hx.2⟩
  refine ⟨a, hstep, ?_⟩
  intro c hc
  have hc' : nextrel2 M c j := hc
  by_contra hne'
  rcases Nat.lt_or_ge c a with h | h
  · have h1 := hc'.2.2.2.2.2 a ⟨h, hale1⟩
    omega
  · have hgt : a < c := lt_of_le_of_ne h (Ne.symm hne')
    have h1 := hamax c hgt hc'.2.2.2.2.1
    have h2 := hc'.2.2.2.1
    omega

/-- 行 1 の祖先を辿ると必ず行 1 = 0 の列に着く。 -/
theorem le1_to_row1_zero {B : TrioSeq} (hzr : Zroot B) (hroot : entry B 0 0 = 0) :
    ∀ v j, entry B 1 j = v → j < B.length →
      ∃ c, entry B 1 c = 0 ∧ Relation.ReflTransGen (nextrel1 B) c j := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro j hv hj
    rcases Nat.eq_zero_or_pos v with rfl | hpos
    · exact ⟨j, hv, Relation.ReflTransGen.refl⟩
    · have h0j : entry B 0 j ≠ 0 := by
        intro hc
        obtain ⟨e1, -⟩ := Zroot_entry hzr hc
        omega
      obtain ⟨c0, hc00, hc0r⟩ := rtg0_to_root hroot (entry B 0 j) j rfl hj
      obtain ⟨e1, -⟩ := Zroot_entry hzr hc00
      have hp1 : hasParent B 1 j :=
        H12Export.hasParent1_of_le0_witness hj hc0r (by omega)
      have hn : nextrel1 B (parent B 1 j) j := parent_nextR hp1
      obtain ⟨c, hc1, hcr⟩ :=
        ih (entry B 1 (parent B 1 j)) (by have := hn.2.2.2.1; omega)
          (parent B 1 j) rfl hn.1
      exact ⟨c, hc1, hcr.tail hn⟩

/-- **末尾列が非零なら必ず `B` の中に親がある**（`Zroot` ＋ `Mono` 版）。 -/
theorem hasParent_of_ZrootMono {B : TrioSeq} (hzr : Zroot B) (hmo : Mono B)
    (hroot : entry B 0 0 = 0) (hlen : 2 ≤ B.length)
    (hnz : ¬ (entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
      entry B 2 (B.length - 1) = 0)) :
    hasParent B (srow B (B.length - 1)) (B.length - 1) := by
  have hj : B.length - 1 < B.length := by omega
  have h0 : entry B 0 (B.length - 1) ≠ 0 := by
    intro hc
    obtain ⟨e1, e2⟩ := Zroot_entry hzr hc
    exact hnz ⟨hc, e1, e2⟩
  have hm := Mono_entry hmo (B.length - 1)
  by_cases h2 : entry B 2 (B.length - 1) = 0
  · by_cases h1 : entry B 1 (B.length - 1) = 0
    · have hs : srow B (B.length - 1) = 0 := by
        unfold srow; rw [if_neg (by omega), if_neg (by omega)]
      rw [hs, Wset.hasParent_zero_iff hj]
      exact ⟨0, by omega, by omega⟩
    · have hs : srow B (B.length - 1) = 1 := by
        unfold srow; rw [if_neg (by omega), if_pos (by omega)]
      rw [hs]
      obtain ⟨c, hc0, hcr⟩ :=
        rtg0_to_root hroot (entry B 0 (B.length - 1)) (B.length - 1) rfl hj
      obtain ⟨e1, -⟩ := Zroot_entry hzr hc0
      exact H12Export.hasParent1_of_le0_witness hj hcr (by omega)
  · have hs : srow B (B.length - 1) = 2 := by
      unfold srow; rw [if_pos (by omega)]
    rw [hs]
    obtain ⟨c, hc1, hcr⟩ :=
      le1_to_row1_zero hzr hroot (entry B 1 (B.length - 1)) (B.length - 1) rfl hj
    have hc2 : entry B 2 c = 0 := by have := Mono_entry hmo c; omega
    exact hasParent2_of_le1_witness hj hcr (by omega)

/-- **`A ++ bump B`（`B` は `W 0` の元で `Zroot` ＋ `Mono`）。** 行 2 の制限なし。 -/
theorem bump_mem3 :
    ∀ B ∈ W 0, Zroot B → Mono B → entry B 0 0 = 0 →
      ∀ A : TrioSeq, A ∈ W 0 → A ≠ [] → Deep A → A ++ bump B ∈ W 0 := by
  have key : W 0 ⊆ {B : TrioSeq | Zroot B → Mono B → entry B 0 0 = 0 →
      ∀ A : TrioSeq, A ∈ W 0 → A ≠ [] → Deep A → A ++ bump B ∈ W 0} := by
    refine A2' ?_
    intro B hB
    simp only [Set.mem_setOf_eq]
    intro hzr hmo hroot A hA hAne hAd
    by_cases hshort : B.length ≤ 1
    · rcases (by omega : B.length = 0 ∨ B.length = 1) with h0 | h1
      · have hnil : B = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        simpa [bump_nil] using hA
      · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
        have hc0 : c.1 = 0 := hroot
        obtain ⟨hc1, hc2⟩ := hzr c (by simp) hc0
        have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1 hc2)
        subst hcz
        have hb : bump [((0, 0, 0) : ℕ × ℕ × ℕ)] = [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
          simp [bump, shiftr01]
        rw [hb]
        exact snoc_one hA hAne hAd.1 hAd.2
    have hlen2 : 2 ≤ B.length := by omega
    have hBne : B ≠ [] := by
      intro hc; rw [hc] at hlen2; simp at hlen2
    rcases hB with ⟨hl, -⟩ | hnat | ⟨m, hm, -, -⟩
    · exact absurd hl hshort
    · by_cases hlast : entry B 0 (B.length - 1) = 0
      · obtain ⟨he1, he2⟩ := Zroot_entry hzr hlast
        have hz : entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
            entry B 2 (B.length - 1) = 0 := ⟨hlast, he1, he2⟩
        have hcol : B.getD (B.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ)
            = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hlast (Prod.ext he1 he2)
        have hgl : B.getLast hBne = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
          have h1 : B.getLast hBne = B.getD (B.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
            rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show B.length - 1 < B.length by omega)]
            rfl
          rw [h1, hcol]
        have hsplit : B = B.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
          rw [← hgl]
          exact (List.dropLast_append_getLast hBne).symm
        have hop : B⟦1⟧ = B.dropLast := by
          rw [oper_eq_pred_of_zero 1 (by omega) hz]
          unfold Pred
          rw [if_neg (by omega)]
        have hdl := hnat 1 le_rfl
        rw [hop] at hdl
        simp only [Set.mem_setOf_eq] at hdl
        have hdl0 : entry B.dropLast 0 0 = 0 := by
          rw [List.dropLast_eq_take,
            Wset.entry_take (show (0 : ℕ) < B.length - 1 by omega)]
          exact hroot
        have hIH := hdl (fun c hc => hzr c (List.dropLast_subset _ hc))
          (fun c hc => hmo c (List.dropLast_subset _ hc)) hdl0 A hA hAne hAd
        have hDne : A ++ bump B.dropLast ≠ [] := by
          simp [List.append_eq_nil_iff, hAne]
        have hD : Deep (A ++ bump B.dropLast) :=
          Deep_append hAd hAne (fun c hc => bump_col c hc)
        have hbs : bump B = bump B.dropLast ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
          conv_lhs => rw [hsplit]
          simp [bump, shiftr01]
        rw [hbs, ← List.append_assoc]
        exact snoc_one hIH hDne hD.1 hD.2
      · have hnz : ¬ (entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
            entry B 2 (B.length - 1) = 0) := fun h => hlast h.1
        have hp := hasParent_of_ZrootMono hzr hmo hroot hlen2 hnz
        refine A1_intro (Or.inr (Or.inl ?_))
        intro n hn
        rw [oper_bump A B n hlen2 hp]
        obtain ⟨hzr', hmo'⟩ := ZM_oper hzr hmo n
        exact hnat n hn hzr' hmo' (by rw [Wset.oper_head_eq hn]; exact hroot) A hA hAne hAd
    · exact absurd hm (Nat.not_lt_zero m)
  intro B hB
  exact key hB

/-- 使いやすい形。 -/
theorem bump_zm {B : TrioSeq} (hB : B ∈ W 0) (hzr : Zroot B) (hmo : Mono B)
    (hroot : entry B 0 0 = 0)
    {A : TrioSeq} (hA : A ∈ W 0) (hAne : A ≠ []) (hAd : Deep A) :
    A ++ bump B ∈ W 0 :=
  bump_mem3 B hB hzr hmo hroot A hA hAne hAd

/-! ## 3 列の壁を 1 枚破る: `X(1,1,0) ∈ W 0`

`X(1,1,0) = (0,0,0)(1,1,1)(1,1,0)` は、旧来の緑の補題では届かなかった 7 個の
うちの 1 つ（末尾の `srow = 1` なので「シフト塔」が要ると思われていた）。
ところが展開は

    X(1,1,0)⟦n⟧ = (0,0,0)(1,1,1) (1,0,0)(2,1,1) (2,0,0)(3,1,1) ...
                = concat_{k<n} [(k,0,0), (k+1,1,1)]  =: Utow n

で、**`Utow (n+1) = Q ++ bump (Utow n)`**（`Q = (0,0,0)(1,1,1)`）という漸化式を
持つ。`Utow n` は `Zroot` かつ `Mono` かつ根が `(0,0,0)` なので `bump_zm` が
そのまま効き、`n` の帰納法で `Utow n ∈ W 0`。あとは節 2。

塔が `A ++ bump(塔)` の形をしている ── これが bump が塔に効く理由である。 -/

theorem entry_append_left {P B : TrioSeq} {i j : ℕ} (hj : j < P.length) :
    entry (P ++ B) i j = entry P i j := by
  simp [entry, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

/-- `X(1,1,0)` の展開の塔。 -/
def Utow : ℕ → TrioSeq
  | 0 => []
  | (n + 1) => Q ++ bump (Utow n)

theorem map_bump_flatMap (l : List ℕ) :
    bump (l.flatMap fun k => [((k, 0, 0) : ℕ × ℕ × ℕ), ((k + 1, 1, 1) : ℕ × ℕ × ℕ)])
      = (l.map Nat.succ).flatMap
        fun k => [((k, 0, 0) : ℕ × ℕ × ℕ), ((k + 1, 1, 1) : ℕ × ℕ × ℕ)] := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [bump, shiftr01, List.flatMap_cons, List.map_append, List.map_cons,
      List.map_nil] at ih ⊢
    rw [ih]

theorem Utow_eq (n : ℕ) : Utow n = (List.range n).flatMap
    fun k => [((k, 0, 0) : ℕ × ℕ × ℕ), ((k + 1, 1, 1) : ℕ × ℕ × ℕ)] := by
  induction n with
  | zero => simp [Utow]
  | succ n ih =>
    show Q ++ bump (Utow n) = _
    rw [ih, List.range_succ_eq_map, map_bump_flatMap]
    rfl

theorem Utow_col (n : ℕ) : ∀ c ∈ Utow n,
    (∃ k, c = ((k, 0, 0) : ℕ × ℕ × ℕ)) ∨ (∃ k, c = ((k + 1, 1, 1) : ℕ × ℕ × ℕ)) := by
  rw [Utow_eq]
  intro c hc
  rw [List.mem_flatMap] at hc
  obtain ⟨k, -, hc2⟩ := hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc2
  rcases hc2 with rfl | rfl
  · exact Or.inl ⟨k, rfl⟩
  · exact Or.inr ⟨k, rfl⟩

theorem Utow_zroot (n : ℕ) : Zroot (Utow n) := by
  intro c hc h0
  rcases Utow_col n c hc with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact absurd h0 (by simp)

theorem Utow_mono (n : ℕ) : Mono (Utow n) := by
  intro c hc
  rcases Utow_col n c hc with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> simp

theorem Utow_root (n : ℕ) : entry (Utow n) 0 0 = 0 := by
  cases n with
  | zero => simp [Utow, entry]
  | succ n =>
    show entry (Q ++ bump (Utow n)) 0 0 = 0
    rw [entry_append_left (by simp [Q])]
    simp [Q, entry]

theorem Utow_mem : ∀ n, Utow n ∈ W 0
  | 0 => by simpa [Utow] using W_nil 0
  | (n + 1) => by
      show Q ++ bump (Utow n) ∈ W 0
      exact bump_zm (Utow_mem n) (Utow_zroot n) (Utow_mono n) (Utow_root n)
        Q_mem Q_ne Q_deep

/-- `X(1,1,0) = (0,0,0)(1,1,1)(1,1,0)`。 -/
def X110 : TrioSeq := [(0, 0, 0), (1, 1, 1), (1, 1, 0)]

theorem X110_len : X110.length = 3 := by simp [X110]

theorem X110_srow : srow X110 2 = 1 := by simp [srow, X110, entry]

theorem nextrel0_X110_01 : nextrel0 X110 0 1 := by
  refine ⟨by simp [X110], by simp [X110], by omega, by simp [X110, entry], ?_⟩
  intro j hj; omega

theorem nextrel0_X110_02 : nextrel0 X110 0 2 := by
  refine ⟨by simp [X110], by simp [X110], by omega, by simp [X110, entry], ?_⟩
  intro j hj
  have : j = 1 := by omega
  subst this
  simp [X110, entry]

theorem le0_X110_00 : le0 X110 0 0 :=
  ⟨by simp [X110], by simp [X110], Relation.ReflTransGen.refl⟩

theorem le0_X110_01 : le0 X110 0 1 :=
  ⟨by simp [X110], by simp [X110], Relation.ReflTransGen.single nextrel0_X110_01⟩

theorem le0_X110_02 : le0 X110 0 2 :=
  ⟨by simp [X110], by simp [X110], Relation.ReflTransGen.single nextrel0_X110_02⟩

theorem X110_hasParent : hasParent X110 1 2 :=
  H12Export.hasParent1_of_le0_witness (by simp [X110]) le0_X110_02.2.2
    (by simp [X110, entry])

theorem nextrel1_X110_02 : nextrel1 X110 0 2 := by
  refine ⟨by simp [X110], by simp [X110], by omega, by simp [X110, entry],
    le0_X110_02, ?_⟩
  intro j hj
  have hjl : j < X110.length := hj.2.1
  rw [X110_len] at hjl
  have : j = 1 ∨ j = 2 := by omega
  rcases this with rfl | rfl <;> simp [X110, entry]

theorem X110_parent : parent X110 1 2 = 0 :=
  X110_hasParent.unique (parent_nextR X110_hasParent) nextrel1_X110_02

theorem oper_X110 (n : ℕ) : X110⟦n⟧ = Utow n := by
  rw [L53.oper_unfold (j1 := 2) (i1 := 1) (j0 := 0) (d0 := 1) (d1 := 0)
      (by simp [X110]) (by omega) (by simp [X110, entry]) X110_srow.symm
      X110_hasParent X110_parent.symm (by simp [X110, entry]) (by simp) n,
    Utow_eq]
  simp only [List.take_zero, Nat.sub_zero, List.nil_append]
  apply List.flatMap_congr
  intro k _
  have hr : List.range' 0 (2 - 0) = [0, 1] := rfl
  rw [hr]
  simp only [List.map_cons, List.map_nil, Nat.mul_zero, ite_self, Nat.add_zero,
    Nat.mul_one]
  rw [if_pos le0_X110_00, if_pos le0_X110_01]
  simp [X110, entry, Nat.add_comm]

/-- ★ **`X(1,1,0) = (0,0,0)(1,1,1)(1,1,0) ∈ W 0`** — 3 列の壁 7 個のうち 1 枚。 -/
theorem X110_mem : X110 ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_X110 n]
  exact Utow_mem n

/-! ## 一般化: 深さ 1 の列は行 1 が何でも継げる

`X(1,1,0)` の証明は `A = Q` に依っていない。`A ∈ W 0` が `Deep`・`Zroot`・`Mono`
なら、末尾に **`(1,e,0)`（深さ 1・行 2 は 0・行 1 は何でも）** を継げる。

理由: 継いだ列の行 1 の親は必ず `A` の根。`Deep` なので行 0 の祖先は根しかなく、
根の行 1 は 0（`Zroot`）だから。したがって

    (A ++ [(1,e,0)])⟦n⟧ = concat_{k<n} shiftr01 k 0 A  =: Tow A n
    Tow A (n+1) = A ++ bump (Tow A n)

で `bump_zm` の帰納法が回る。**`e` は結果に一切効かない。** -/

theorem bump_append (X Y : TrioSeq) : bump (X ++ Y) = bump X ++ bump Y := by
  simp [bump, shiftr01]

theorem shiftr01_succ (k : ℕ) (A : TrioSeq) :
    bump (shiftr01 k 0 A) = shiftr01 (k + 1) 0 A := by
  simp only [bump, shiftr01, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro p _
  simp [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]

/-- `A ++ [(1,e,0)]` の展開の塔。 -/
def Tow (A : TrioSeq) : ℕ → TrioSeq
  | 0 => []
  | (n + 1) => A ++ bump (Tow A n)

theorem map_bump_shift (A : TrioSeq) : ∀ l : List ℕ,
    bump (l.flatMap fun k => shiftr01 k 0 A)
      = (l.map (· + 1)).flatMap fun k => shiftr01 k 0 A
  | [] => by simp [bump, shiftr01]
  | (a :: t) => by
      rw [List.flatMap_cons, bump_append, map_bump_shift A t, List.map_cons,
        List.flatMap_cons, shiftr01_succ]

theorem Tow_eq (A : TrioSeq) (n : ℕ) :
    Tow A n = (List.range n).flatMap fun k => shiftr01 k 0 A := by
  induction n with
  | zero => simp [Tow]
  | succ n ih =>
    show A ++ bump (Tow A n) = _
    rw [ih, List.range_succ_eq_map, map_bump_shift, List.flatMap_cons, shiftr01_zero]

theorem Tow_col {A : TrioSeq} (n : ℕ) : ∀ c ∈ Tow A n, ∃ k, ∃ p ∈ A,
    c = ((p.1 + k, p.2.1 + 0, p.2.2) : ℕ × ℕ × ℕ) := by
  rw [Tow_eq]
  intro c hc
  rw [List.mem_flatMap] at hc
  obtain ⟨k, -, hc2⟩ := hc
  simp only [shiftr01, List.mem_map] at hc2
  obtain ⟨p, hp, rfl⟩ := hc2
  exact ⟨k, p, hp, rfl⟩

theorem Tow_zroot {A : TrioSeq} (hAz : Zroot A) (n : ℕ) : Zroot (Tow A n) := by
  intro c hc h0
  obtain ⟨k, p, hp, rfl⟩ := Tow_col n c hc
  have hp1 : p.1 = 0 := by dsimp only at h0; omega
  obtain ⟨e1, e2⟩ := hAz p hp hp1
  exact ⟨by dsimp only; omega, by dsimp only; exact e2⟩

theorem Tow_mono {A : TrioSeq} (hAm : Mono A) (n : ℕ) : Mono (Tow A n) := by
  intro c hc
  obtain ⟨k, p, hp, rfl⟩ := Tow_col n c hc
  have := hAm p hp
  dsimp only
  omega

theorem Tow_root {A : TrioSeq} (hAne : A ≠ []) (hAd : Deep A) (n : ℕ) :
    entry (Tow A n) 0 0 = 0 := by
  cases n with
  | zero => simp [Tow, entry]
  | succ n =>
    show entry (A ++ bump (Tow A n)) 0 0 = 0
    rw [entry_append_left (List.length_pos_iff.mpr hAne)]
    exact hAd.1

theorem Tow_mem {A : TrioSeq} (hA : A ∈ W 0) (hAne : A ≠ []) (hAd : Deep A)
    (hAz : Zroot A) (hAm : Mono A) : ∀ n, Tow A n ∈ W 0
  | 0 => by simpa [Tow] using W_nil 0
  | (n + 1) => by
      show A ++ bump (Tow A n) ∈ W 0
      exact bump_zm (Tow_mem hA hAne hAd hAz hAm n) (Tow_zroot hAz n)
        (Tow_mono hAm n) (Tow_root hAne hAd n) hA hAne hAd

theorem map_range'_shift (A : TrioSeq) (k : ℕ) :
    (List.range' 0 A.length).map
        (fun j => ((entry A 0 j + k, entry A 1 j, entry A 2 j) : ℕ × ℕ × ℕ))
      = shiftr01 k 0 A := by
  apply List.ext_getElem
  · simp [shiftr01]
  · intro i h1 h2
    have hi : i < A.length := by simpa using h1
    simp only [List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul,
      shiftr01]
    rw [← triple_entry A hi]
    rfl

theorem snoc_row1_oper {A : TrioSeq} (hAne : A ≠ []) (hAd : Deep A) (hAz : Zroot A)
    {e : ℕ} (he : 1 ≤ e) (n : ℕ) :
    (A ++ [((1, e, 0) : ℕ × ℕ × ℕ)])⟦n⟧ = Tow A n := by
  have hplen : 0 < A.length := List.length_pos_iff.mpr hAne
  have hlast := entry_append_last (P := A) (c := ((1, e, 0) : ℕ × ℕ × ℕ))
  have hpre : ∀ i j, j < A.length →
      entry (A ++ [((1, e, 0) : ℕ × ℕ × ℕ)]) i j = entry A i j :=
    fun i j hj => entry_append_lt hj
  have hMdeep : Deep (A ++ [((1, e, 0) : ℕ × ℕ × ℕ)]) :=
    Deep_snoc hAd hAne (le_refl 1)
  have hMlen : (A ++ [((1, e, 0) : ℕ × ℕ × ℕ)]).length = A.length + 1 := by simp
  set M : TrioSeq := A ++ [((1, e, 0) : ℕ × ℕ × ℕ)] with hM
  have hl0 : entry M 0 A.length = 1 := hlast.1
  have hl1 : entry M 1 A.length = e := hlast.2.1
  have hl2 : entry M 2 A.length = 0 := hlast.2.2
  have hsh : ∀ x, 0 < x → x < M.length → entry M 0 0 < entry M 0 x := by
    intro x hx0 hxl
    rw [hMdeep.1]
    exact hMdeep.2 x hx0 hxl
  have hle0 : ∀ j, j < M.length → le0 M 0 j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact ⟨by omega, by omega, Relation.ReflTransGen.refl⟩
    · exact H12Export.le0_root_of_shallow (by omega) hsh j hj0 hj
  have hroot1 : entry M 1 0 = 0 := by
    rw [hpre 1 0 hplen]
    exact (Zroot_entry hAz hAd.1).1
  have hsrow : srow M A.length = 1 := by
    unfold srow
    rw [if_neg (by rw [hl2]; omega), if_pos (by rw [hl1]; omega)]
  have hpar : hasParent M 1 A.length :=
    H12Export.hasParent1_of_le0_witness (by omega) (hle0 A.length (by omega)).2.2
      (by rw [hroot1, hl1]; omega)
  have hnr1 : nextrel1 M 0 A.length := by
    refine ⟨by omega, by omega, hplen, by rw [hroot1, hl1]; omega,
      hle0 A.length (by omega), ?_⟩
    intro j hj
    have hjeq : j = A.length := by
      rcases Relation.ReflTransGen.cases_tail hj.2.2.2 with h | ⟨c, hc1, hc2⟩
      · omega
      · exfalso
        have hc0 : entry M 0 c = 0 := by
          have := hc2.2.2.2.1
          rw [hl0] at this
          omega
        have hcz : c = 0 := by
          by_contra hcn
          have := hMdeep.2 c (by omega) hc2.1
          omega
        rw [hcz] at hc1
        have := H12Export.rtg0_index_le hc1
        omega
    rw [hjeq]
  have hj0 : parent M 1 A.length = 0 := hpar.unique (parent_nextR hpar) hnr1
  rw [L53.oper_unfold (j1 := A.length) (i1 := 1) (j0 := 0) (d0 := 1) (d1 := 0)
      (by omega) (by omega) (by rintro ⟨h, -, -⟩; rw [hl0] at h; omega)
      hsrow.symm hpar hj0.symm (by rw [if_pos (by omega), hl0, hMdeep.1]) (by simp) n,
    Tow_eq]
  simp only [List.take_zero, List.nil_append, Nat.sub_zero, Nat.mul_zero, ite_self,
    Nat.add_zero, Nat.mul_one]
  apply List.flatMap_congr
  intro k _
  rw [← map_range'_shift A k]
  apply List.map_congr_left
  intro j hj
  have hjl : j < A.length := by have := List.mem_range'_1.1 hj; omega
  rw [if_pos (hle0 j (by omega)), hpre 0 j hjl, hpre 1 j hjl, hpre 2 j hjl]

/-- ★ **`A ++ [(1,e,0)] ∈ W 0`** — `Deep`・`Zroot`・`Mono` な `W 0` の元には、
深さ 1・行 2 が 0 の列を、行 1 の値に関係なく継げる。 -/
theorem snoc_row1 {A : TrioSeq} (hA : A ∈ W 0) (hAne : A ≠ []) (hAd : Deep A)
    (hAz : Zroot A) (hAm : Mono A) {e : ℕ} (he : 1 ≤ e) :
    A ++ [((1, e, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [snoc_row1_oper hAne hAd hAz he n]
  exact Tow_mem hA hAne hAd hAz hAm n

/-! ## 積・冪の梯子: `o(A)^2` から `o(A)^o(A)` まで

`bump_mem3` は **`B` に `Deep` を要求しない**（`B ∈ W 0` ＋ `Zroot` ＋ `Mono` ＋
根が深さ 0 だけ）。この差がちょうど効く: `A ++ A` は根が 2 つあるので `Deep`
ではないが `B` 側の条件は満たすので、そのまま `bump` できる。

    Aok A := A ∈ W 0 ∧ A ≠ [] ∧ Deep A ∧ Zroot A ∧ Mono A   （左に置ける）
    Bok B := B ∈ W 0 ∧ Zroot B ∧ Mono B ∧ 根が深さ 0        （bump できる）

    Aok A → Bok B → Aok (A ++ bump B)     継いだ結果もまた左に置ける
    Aok A → Bok A                          （`Deep` を落とすだけ）
    Aok A → Bok (copies A n)               同じものを n 個並べても bump できる

順序数では（ユーザーの読み）:

    A ++ bump A                          o(A)^2
    A ++ bump (copies A n)               o(A)^(n+1)
    A ++ bump (A ++ bump [(0,0,0)])      o(A)^ω
    A ++ bump (A ++ bump ((0,0,0)(1,0,0)))  o(A)^(ω^ω)
    A ++ bump (A ++ bump B)              o(A)^o(B)
    A ++ bump (A ++ bump A)              o(A)^o(A)

いずれも標準形であることは `bms -s` で確認済み。 -/

/-- `bump` の左に置ける行列。 -/
structure Aok (A : TrioSeq) : Prop where
  mem : A ∈ W 0
  ne : A ≠ []
  deep : Deep A
  zroot : Zroot A
  mono : Mono A

/-- `bump` できる行列（`Deep` は要らない）。 -/
structure Bok (B : TrioSeq) : Prop where
  mem : B ∈ W 0
  zroot : Zroot B
  mono : Mono B
  root : entry B 0 0 = 0

theorem Aok.toBok {A : TrioSeq} (h : Aok A) : Bok A :=
  ⟨h.mem, h.zroot, h.mono, h.deep.1⟩

/-- **積**: `A ++ bump B ∈ W 0`。 -/
theorem Bok.append {A B : TrioSeq} (hA : Aok A) (hB : Bok B) : A ++ bump B ∈ W 0 :=
  bump_zm hB.mem hB.zroot hB.mono hB.root hA.mem hA.ne hA.deep

theorem bump_mono {B : TrioSeq} (h : Mono B) : Mono (bump B) := by
  intro c hc
  simp only [bump, shiftr01, List.mem_map] at hc
  obtain ⟨p, hp, rfl⟩ := hc
  have := h p hp
  dsimp only
  omega

/-- **継いだ結果もまた左に置ける** ⟹ いくらでも重ねられる。 -/
theorem Aok.append_bump {A B : TrioSeq} (hA : Aok A) (hB : Bok B) :
    Aok (A ++ bump B) := by
  refine ⟨Bok.append hA hB, by simp [List.append_eq_nil_iff, hA.ne],
    Deep_append hA.deep hA.ne (fun c hc => bump_col c hc), ?_, ?_⟩
  · intro c hc h0
    rcases List.mem_append.mp hc with hm | hm
    · exact hA.zroot c hm h0
    · have := bump_col c hm
      omega
  · intro c hc
    rcases List.mem_append.mp hc with hm | hm
    · exact hA.mono c hm
    · exact bump_mono hB.mono c hm

/-- `copies A n = A^n`。 -/
def copies (A : TrioSeq) (n : ℕ) : TrioSeq := (List.range n).flatMap fun _ => A

theorem copies_succ (A : TrioSeq) (n : ℕ) : copies A (n + 1) = A ++ copies A n := by
  simp [copies, List.range_succ_eq_map, List.flatMap_map, Function.comp_def]

theorem copies_mem_col {A : TrioSeq} {n : ℕ} : ∀ c ∈ copies A n, c ∈ A := by
  intro c hc
  simp only [copies, List.mem_flatMap] at hc
  obtain ⟨k, -, h⟩ := hc
  exact h

/-- **同じものを `n` 個並べたものも `bump` できる。** -/
theorem Aok.copies_Bok {A : TrioSeq} (hA : Aok A) (n : ℕ) : Bok (copies A n) := by
  refine ⟨W_flatMap_copies hA.mem (fun p _ => by rw [hA.deep.1]; omega) n,
    fun c hc => hA.zroot c (copies_mem_col c hc),
    fun c hc => hA.mono c (copies_mem_col c hc), ?_⟩
  cases n with
  | zero => simp [copies, entry]
  | succ n =>
    rw [copies_succ, entry_append_left (List.length_pos_iff.mpr hA.ne)]
    exact hA.deep.1

theorem Bok_nil : Bok ([] : TrioSeq) :=
  ⟨W_nil 0, by simp [Zroot], by simp [Mono], by simp [entry]⟩

theorem Bok_zero : Bok [((0, 0, 0) : ℕ × ℕ × ℕ)] :=
  ⟨Flat_mem_W (by intro c hc; simp at hc; subst hc; exact ⟨rfl, rfl⟩),
    by intro c hc _; simp at hc; subst hc; exact ⟨rfl, rfl⟩,
    by intro c hc; simp at hc; subst hc; simp,
    by simp [entry]⟩

/-- 平坦（行 1・行 2 が 0）で根が深さ 0 なら `Bok`。仮定は形だけ。 -/
theorem Bok_flat {B : TrioSeq} (hf : Flat B) (hroot : entry B 0 0 = 0) : Bok B :=
  ⟨Flat_mem_W hf, Flat_Zroot hf, Z2_Mono (Flat_Z2 hf), hroot⟩

theorem Aok_zero : Aok [((0, 0, 0) : ℕ × ℕ × ℕ)] :=
  ⟨Bok_zero.mem, by simp, ⟨by simp [entry], by intro j h1 h2; simp at h2; omega⟩,
    Bok_zero.zroot, Bok_zero.mono⟩

theorem Aok_Q : Aok Q := by
  refine ⟨Q_mem, Q_ne, Q_deep, ?_, ?_⟩
  · intro c hc h0; simp only [Q, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exact absurd h0 (by simp)
  · intro c hc; simp only [Q, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp

/-! ### 梯子（`o(A)^α`） -/

/-- `o(A)^2`。 -/
theorem pow_two {A : TrioSeq} (hA : Aok A) : A ++ bump A ∈ W 0 :=
  Bok.append hA hA.toBok

/-- `o(A)^(n+1)`。 -/
theorem pow_succ {A : TrioSeq} (hA : Aok A) (n : ℕ) :
    A ++ bump (copies A n) ∈ W 0 :=
  Bok.append hA (hA.copies_Bok n)

/-- `o(A)^o(B)`（`B` は `Bok` なら何でも）。 -/
theorem pow_gen {A B : TrioSeq} (hA : Aok A) (hB : Bok B) :
    A ++ bump (A ++ bump B) ∈ W 0 :=
  Bok.append hA (hA.append_bump hB).toBok

/-- `o(A)^ω`。 -/
theorem pow_omega {A : TrioSeq} (hA : Aok A) :
    A ++ bump (A ++ bump [((0, 0, 0) : ℕ × ℕ × ℕ)]) ∈ W 0 :=
  pow_gen hA Bok_zero

/-- `o(A)^(ω^ω)`。 -/
theorem pow_omega_omega {A : TrioSeq} (hA : Aok A) :
    A ++ bump (A ++ bump [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 0, 0) : ℕ × ℕ × ℕ)]) ∈ W 0 :=
  pow_gen hA (Bok_flat (by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact ⟨rfl, rfl⟩) (by simp [entry]))

/-- `o(A)^o(A)`。 -/
theorem pow_self {A : TrioSeq} (hA : Aok A) :
    A ++ bump (A ++ bump A) ∈ W 0 :=
  pow_gen hA hA.toBok

/-! ### 冪の塔とその極限

`powTow A m = A ++ bump (A ++ bump (... ++ bump A))`（`bump` が `m` 個）。
`bump` は `++` を通り抜けるので、これは実は**一様な写しの列**である:

    powTow A m = Tow A (m+1) = A ++ shiftr01 1 0 A ++ ... ++ shiftr01 m 0 A

そして `Tow A n` は `A ++ [(1,e,0)]` の基本列そのもの（`snoc_row1_oper`）。
したがって

    **冪の塔の極限は `A ++ [(1,1,0)]`。**

`A = X = (0,0,0)(1,1,1)` なら極限は `X(1,1,0)`（シート行 284, psi(W_w + W)）。
塔の各段はシートで
  m=0 行267 psi(W_w) / m=1 行280 psi(W_w)^2 / m=2 行283 psi(W_w)^psi(W_w)。 -/

/-- 冪の塔（`bump` を `m` 段）。 -/
def powTow (A : TrioSeq) : ℕ → TrioSeq
  | 0 => A
  | (m + 1) => A ++ bump (powTow A m)

theorem powTow_eq_Tow (A : TrioSeq) (m : ℕ) : powTow A m = Tow A (m + 1) := by
  induction m with
  | zero => show A = A ++ bump (Tow A 0); simp [Tow, bump_nil]
  | succ m ih => show A ++ bump (powTow A m) = _; rw [ih]; rfl

theorem powTow_Aok {A : TrioSeq} (hA : Aok A) : ∀ m, Aok (powTow A m)
  | 0 => hA
  | (m + 1) => hA.append_bump (powTow_Aok hA m).toBok

/-- **極限**: `A ++ [(1,e,0)]` の基本列がちょうど冪の塔。 -/
theorem powTow_is_fs {A : TrioSeq} (hAne : A ≠ []) (hAd : Deep A) (hAz : Zroot A)
    {e : ℕ} (he : 1 ≤ e) (m : ℕ) :
    (A ++ [((1, e, 0) : ℕ × ℕ × ℕ)])⟦m + 1⟧ = powTow A m := by
  rw [snoc_row1_oper hAne hAd hAz he, powTow_eq_Tow]

/-- `X = (0,0,0)(1,1,1)` の冪の塔の極限は `X(1,1,0)`。 -/
theorem X110_fs (m : ℕ) : X110⟦m + 1⟧ = powTow Q m := by
  have h : X110 = Q ++ [((1, 1, 0) : ℕ × ℕ × ℕ)] := by simp [X110, Q]
  rw [h, powTow_is_fs Q_ne Q_deep Aok_Q.zroot (le_refl 1)]

/-! ## シート行286 `X(1,1,0)(2,0,0) = psi(W_w + W*w)`

`snoc_row1` は `Aok` を保つので、`(1,e,0)` は**何段でも**継げる:

    snocR A e m = A ++ (1,e,0)^m  ∈ W 0

そして `A ++ [(1,e,0)(2,0,0)]` の展開はちょうどこの族:

    (A ++ [(1,e,0),(2,0,0)])⟦m⟧ = A ++ (1,e,0)^m

（末尾 `(2,0,0)` の行 0 の親は 1 つ前の `(1,e,0)`、`srow = 0` なので持ち上げ無し。）
したがって節 2 で落ちる。`A = X = (0,0,0)(1,1,1)`, `e = 1` がシート行286。 -/

theorem Aok.append_row1 {A : TrioSeq} (hA : Aok A) {e : ℕ} (he : 1 ≤ e) :
    Aok (A ++ [((1, e, 0) : ℕ × ℕ × ℕ)]) := by
  refine ⟨snoc_row1 hA.mem hA.ne hA.deep hA.zroot hA.mono he,
    by simp [List.append_eq_nil_iff, hA.ne],
    Deep_snoc hA.deep hA.ne (le_refl 1), ?_, ?_⟩
  · intro c hc h0
    rcases List.mem_append.mp hc with hm | hm
    · exact hA.zroot c hm h0
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      subst hm
      exact absurd h0 (by simp)
  · intro c hc
    rcases List.mem_append.mp hc with hm | hm
    · exact hA.mono c hm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      subst hm
      simp

/-- `A ++ (1,e,0)^m`。 -/
def snocR (A : TrioSeq) (e : ℕ) : ℕ → TrioSeq
  | 0 => A
  | (m + 1) => snocR A e m ++ [((1, e, 0) : ℕ × ℕ × ℕ)]

theorem snocR_eq (A : TrioSeq) (e m : ℕ) :
    snocR A e m = A ++ List.replicate m ((1, e, 0) : ℕ × ℕ × ℕ) := by
  induction m with
  | zero => simp [snocR]
  | succ m ih =>
    show snocR A e m ++ _ = _
    rw [ih, List.append_assoc, ← List.replicate_succ']

theorem snocR_Aok {A : TrioSeq} (hA : Aok A) {e : ℕ} (he : 1 ≤ e) :
    ∀ m, Aok (snocR A e m)
  | 0 => hA
  | (m + 1) => (snocR_Aok hA he m).append_row1 he

/-- **`(1,e,0)(2,0,0)` を継ぐ。** 展開は `(1,e,0)` を `m` 個並べたもの。 -/
theorem snoc_row1_two {A : TrioSeq} (hA : Aok A) {e : ℕ} (he : 1 ≤ e) :
    A ++ [((1, e, 0) : ℕ × ℕ × ℕ), ((2, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hne := hA.ne
  set M : TrioSeq := A ++ [((1, e, 0) : ℕ × ℕ × ℕ), ((2, 0, 0) : ℕ × ℕ × ℕ)] with hM
  have hplen : 0 < A.length := List.length_pos_iff.mpr hne
  have hlen : M.length - 1 = A.length + 1 := by rw [hM]; simp
  have hb : entry M 0 (A.length + 1) = 2 ∧ entry M 1 (A.length + 1) = 0 ∧
      entry M 2 (A.length + 1) = 0 := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [entry, hM, getD_app2_b]
  have ha : entry M 0 A.length = 1 := by simp [entry, hM, getD_app2_a]
  have hsr : srow M (A.length + 1) = 0 := by simp [srow, hb.2.1, hb.2.2]
  have hpar : hasParent M 0 (A.length + 1) := by
    rw [hasParent_zero_iff (by rw [hM]; simp)]
    exact ⟨A.length, by omega, by rw [ha, hb.1]; omega⟩
  have hj0 : parent M 0 (A.length + 1) = A.length := by
    have h := parent_nextR hpar
    rw [nextR, if_pos rfl] at h
    obtain ⟨-, -, hlt, -, hmin⟩ := h
    by_contra hne0
    have hlt' : parent M 0 (A.length + 1) < A.length := by omega
    have := hmin A.length ⟨hlt', by omega⟩
    rw [ha, hb.1] at this
    omega
  refine mem_of_oper_mem (fun m _ => ?_)
  have hop : M⟦m⟧ = A ++ List.replicate m ((1, e, 0) : ℕ × ℕ × ℕ) := by
    simp only [oper, hlen, hsr, hj0]
    rw [if_neg (by omega), if_neg (by rw [hb.1]; simp),
      if_neg (by rw [hlen, hsr]; exact not_not_intro hpar)]
    have htk : M.take A.length = A := by rw [hM, List.take_left]
    have hcol : ((entry M 0 A.length, entry M 1 A.length, entry M 2 A.length) : ℕ × ℕ × ℕ)
        = (1, e, 0) := by simp [entry, hM, getD_app2_a]
    rw [htk]
    congr 1
    simp only [show A.length + 1 - A.length = 1 from by omega,
      show (List.range' A.length 1) = [A.length] from rfl,
      List.map_cons, List.map_nil, lt_self_iff_false, if_false, Nat.not_lt_zero,
      Nat.mul_zero, ite_self, Nat.add_zero, hcol]
    exact flatMap_singleton_range _ m
  rw [hop, ← snocR_eq]
  exact (snocR_Aok hA he m).mem

/-- シート行285 `X(1,1,0)(1,1,0) = psi(W_w + W*2)`。 -/
theorem R285_mem :
    [((0, 0, 0) : ℕ × ℕ × ℕ), (1, 1, 1), (1, 1, 0), (1, 1, 0)] ∈ W 0 := by
  have h := (snocR_Aok Aok_Q (e := 1) (le_refl 1) 2).mem
  simpa [snocR, Q] using h

/-- ★ シート行286 `X(1,1,0)(2,0,0) = psi(W_w + W*w)`。 -/
theorem R286_mem :
    [((0, 0, 0) : ℕ × ℕ × ℕ), (1, 1, 1), (1, 1, 0), (2, 0, 0)] ∈ W 0 := by
  have h := snoc_row1_two Aok_Q (e := 1) (le_refl 1)
  simpa [Q] using h

/-! ## d=2 の bump: `A ++ Blk e B`

    Blk e B := (1,e,0) :: shiftr01 2 0 B

深さ 1 の列 1 本と、その下に深さ 2 以上のブロックを吊るした形。目標は

    Aok A → B ∈ W 0（Zroot ∧ Mono ∧ 根 0）→ 1 <= e  ⟹  A ++ Blk e B ∈ W 0

`B` の `W 0` 帰納法。枝は 2 つ:

* `B` の末尾が非零 ⟹ 親が `B` の中にあるので
  `(A ++ Blk e B)⟦n⟧ = A ++ Blk e (B⟦n⟧)`（`A` は不問）。
* `B` の末尾が `(0,0,0)` ⟹ `Blk e B = Blk e (B.dropLast) ++ [(2,0,0)]`。
  この `(2,0,0)` の行 0 の親は `(1,e,0)`（間の列は全部深さ 2 以上）。`srow = 0` で
  持ち上げも無いので `snoc_flat` が使え、要るのは**コピー族**

      A ++ (Blk e (B.dropLast))^n ∈ W 0

  だけ。これは「`Aok` な行列にはいつでも `Blk e (B.dropLast)` を継げる」という
  **帰納法の仮定を `n` 回使う**と出る。⟹ `A` を全称にしておくのが鍵。 -/

theorem oper_shift (A B : TrioSeq) (d n : ℕ) (hlen : 2 ≤ B.length)
    (hp : hasParent B (srow B (B.length - 1)) (B.length - 1)) :
    (A ++ shiftr01 d 0 B)⟦n⟧ = A ++ shiftr01 d 0 (B⟦n⟧) := by
  have h2 : 2 ≤ (shiftr01 d 0 B).length := by rw [shiftr01_length]; exact hlen
  have hp' : hasParent (shiftr01 d 0 B)
      (srow (shiftr01 d 0 B) ((shiftr01 d 0 B).length - 1))
      ((shiftr01 d 0 B).length - 1) := by
    rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hp
  rw [oper_append_right_of A _ n h2 hp', oper_shiftr01]

/-- 深さ 1 の列 1 本 ＋ 深さ 2 以上のブロック。 -/
def Blk (e : ℕ) (B : TrioSeq) : TrioSeq :=
  ((1, e, 0) : ℕ × ℕ × ℕ) :: shiftr01 2 0 B

theorem shift2_col {C : TrioSeq} : ∀ c ∈ shiftr01 2 0 C, 2 ≤ c.1 := by
  intro c hc
  simp only [shiftr01, List.mem_map] at hc
  obtain ⟨p, -, rfl⟩ := hc
  omega

theorem shift2_mono {C : TrioSeq} (h : Mono C) : Mono (shiftr01 2 0 C) := by
  intro c hc
  simp only [shiftr01, List.mem_map] at hc
  obtain ⟨p, hp, rfl⟩ := hc
  have := h p hp
  dsimp only
  omega

theorem Blk_len (e : ℕ) (B : TrioSeq) : (Blk e B).length = B.length + 1 := by
  simp [Blk, shiftr01]

theorem Blk_col {e : ℕ} {B : TrioSeq} : ∀ c ∈ Blk e B, 1 ≤ c.1 := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hm
  · dsimp only; omega
  · have := shift2_col c hm; omega

theorem Blk_mono {e : ℕ} {B : TrioSeq} (h : Mono B) : Mono (Blk e B) := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hm
  · dsimp only; omega
  · exact shift2_mono h c hm

theorem Blk_nil (e : ℕ) : Blk e [] = [((1, e, 0) : ℕ × ℕ × ℕ)] := by
  simp [Blk, shiftr01]

theorem Blk_one (e : ℕ) :
    Blk e [((0, 0, 0) : ℕ × ℕ × ℕ)]
      = [((1, e, 0) : ℕ × ℕ × ℕ), ((2, 0, 0) : ℕ × ℕ × ℕ)] := by
  simp [Blk, shiftr01]

theorem Blk_snoc (e : ℕ) (B : TrioSeq) :
    Blk e (B ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])
      = Blk e B ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] := by
  simp [Blk, shiftr01]

theorem Blk_app (A B : TrioSeq) (e : ℕ) :
    A ++ Blk e B = (A ++ [((1, e, 0) : ℕ × ℕ × ℕ)]) ++ shiftr01 2 0 B := by
  simp [Blk]

theorem Aok_append_Blk {A B : TrioSeq} {e : ℕ} (hmem : A ++ Blk e B ∈ W 0)
    (hA : Aok A) (hmo : Mono B) : Aok (A ++ Blk e B) := by
  refine ⟨hmem, by simp [List.append_eq_nil_iff, hA.ne],
    Deep_append hA.deep hA.ne (fun c hc => Blk_col c hc), ?_, ?_⟩
  · intro c hc h0
    rcases List.mem_append.mp hc with hm | hm
    · exact hA.zroot c hm h0
    · have := Blk_col c hm; omega
  · intro c hc
    rcases List.mem_append.mp hc with hm | hm
    · exact hA.mono c hm
    · exact Blk_mono hmo c hm

/-- `A ++ X^n`（右から継ぐ形）。 -/
def Yseq (A X : TrioSeq) : ℕ → TrioSeq
  | 0 => A
  | (n + 1) => Yseq A X n ++ X

theorem Yseq_eq (A X : TrioSeq) (n : ℕ) :
    Yseq A X n = A ++ (List.range n).flatMap fun _ => X := by
  induction n with
  | zero => simp [Yseq]
  | succ n ih =>
    show Yseq A X n ++ X = _
    rw [ih, List.append_assoc, List.range_succ, List.flatMap_append]
    simp

theorem Yseq_Aok {A C : TrioSeq} {e : ℕ} (hA : Aok A) (hmoC : Mono C)
    (hIH : ∀ A' : TrioSeq, Aok A' → A' ++ Blk e C ∈ W 0) :
    ∀ n, Aok (Yseq A (Blk e C) n)
  | 0 => hA
  | (n + 1) =>
      Aok_append_Blk (hIH _ (Yseq_Aok hA hmoC hIH n)) (Yseq_Aok hA hmoC hIH n) hmoC

theorem Blk_entry_zero {e : ℕ} {C : TrioSeq} : entry (Blk e C) 0 0 = 1 := rfl

theorem Blk_entry_pos {e : ℕ} {C : TrioSeq} (s : ℕ) (hs : s < C.length) :
    2 ≤ entry (Blk e C) 0 (s + 1) := by
  have hg : (Blk e C).getD (s + 1) ((0, 0, 0) : ℕ × ℕ × ℕ)
      = (shiftr01 2 0 C).getD s (0, 0, 0) := rfl
  have hm : (shiftr01 2 0 C).getD s ((0, 0, 0) : ℕ × ℕ × ℕ) ∈ shiftr01 2 0 C :=
    getD_mem_of_lt (by rw [shiftr01_length]; exact hs)
  show 2 ≤ ((Blk e C).getD (s + 1) ((0, 0, 0) : ℕ × ℕ × ℕ)).1
  rw [hg]
  exact shift2_col _ hm

/-- **(S2)**: コピー族が済めば `(2,0,0)` を継げる。 -/
theorem blk_snoc_two {C A : TrioSeq} {e : ℕ} (hmoC : Mono C) (hA : Aok A)
    (hIH : ∀ A' : TrioSeq, Aok A' → A' ++ Blk e C ∈ W 0) :
    (A ++ Blk e C) ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hAlen : 0 < A.length := List.length_pos_iff.mpr hA.ne
  set P : TrioSeq := A ++ Blk e C with hP
  have hPlen : P.length = A.length + (C.length + 1) := by
    rw [hP]; simp [Blk_len]
  have hPne : P ≠ [] := by rw [hP]; simp [List.append_eq_nil_iff, hA.ne]
  have hcolA : entry P 0 A.length = 1 := by
    rw [hP, show A.length = A.length + 0 from rfl, entry_append_right]
    exact Blk_entry_zero
  have hcolmid : ∀ j, A.length < j → j < P.length → 2 ≤ entry P 0 j := by
    intro j h1 h2
    obtain ⟨s, rfl⟩ : ∃ s, j = A.length + (s + 1) := ⟨j - A.length - 1, by omega⟩
    rw [hP, entry_append_right]
    exact Blk_entry_pos s (by omega)
  have hlast2 : entry (P ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) 0 P.length = 2 :=
    entry_append_last.1
  have hpar : hasParent (P ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) 0 P.length := by
    rw [hasParent_zero_iff (by simp)]
    refine ⟨A.length, by omega, ?_⟩
    rw [entry_append_lt (show A.length < P.length by omega), hcolA, hlast2]
    omega
  have hj0 : parent (P ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) 0 P.length = A.length := by
    have h := parent_nextR hpar
    rw [nextR, if_pos rfl] at h
    obtain ⟨-, -, hlt, hval, hmin⟩ := h
    by_contra hne0
    rcases Nat.lt_or_ge (parent (P ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) 0 P.length) A.length
      with hc | hc
    · have hmm := hmin A.length ⟨hc, by omega⟩
      rw [entry_append_lt (show A.length < P.length by omega), hcolA, hlast2] at hmm
      omega
    · have hgt : A.length < parent (P ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) 0 P.length :=
        lt_of_le_of_ne hc (Ne.symm hne0)
      have hmm := hcolmid _ hgt (by omega)
      rw [entry_append_lt (show parent (P ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) 0 P.length
        < P.length by omega), hlast2] at hval
      omega
  refine snoc_flat (A := P) (b := ((2, 0, 0) : ℕ × ℕ × ℕ)) (j0 := A.length) hPne
    (by simp) rfl rfl hpar hj0 ?_
  intro n
  have h1 : P.take A.length = A := by rw [hP, List.take_left]
  have h2 : P.drop A.length = Blk e C := by rw [hP, List.drop_left]
  rw [h1, h2, ← Yseq_eq]
  exact (Yseq_Aok hA hmoC hIH n).mem

/-- ★ **d=2 の bump**: `Aok A` の上に `(1,e,0)` ＋ 深さ 2 のブロックを吊るせる。 -/
theorem blk_mem :
    ∀ B ∈ W 0, Zroot B → Mono B → entry B 0 0 = 0 →
      ∀ A : TrioSeq, Aok A → ∀ e : ℕ, 1 ≤ e → A ++ Blk e B ∈ W 0 := by
  have key : W 0 ⊆ {B : TrioSeq | Zroot B → Mono B → entry B 0 0 = 0 →
      ∀ A : TrioSeq, Aok A → ∀ e : ℕ, 1 ≤ e → A ++ Blk e B ∈ W 0} := by
    refine A2' ?_
    intro B hB
    simp only [Set.mem_setOf_eq]
    intro hzr hmo hroot A hA e he
    by_cases hshort : B.length ≤ 1
    · rcases (by omega : B.length = 0 ∨ B.length = 1) with h0 | h1
      · have hnil : B = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        rw [Blk_nil]
        exact snoc_row1 hA.mem hA.ne hA.deep hA.zroot hA.mono he
      · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
        have hc0 : c.1 = 0 := hroot
        obtain ⟨hc1, hc2⟩ := hzr c (by simp) hc0
        have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1 hc2)
        subst hcz
        rw [Blk_one]
        exact snoc_row1_two hA he
    have hlen2 : 2 ≤ B.length := by omega
    have hBne : B ≠ [] := by
      intro hc; rw [hc] at hlen2; simp at hlen2
    rcases hB with ⟨hl, -⟩ | hnat | ⟨m, hm, -, -⟩
    · exact absurd hl hshort
    · by_cases hlast : entry B 0 (B.length - 1) = 0
      · obtain ⟨he1, he2⟩ := Zroot_entry hzr hlast
        have hz : entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
            entry B 2 (B.length - 1) = 0 := ⟨hlast, he1, he2⟩
        have hcol : B.getD (B.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ)
            = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hlast (Prod.ext he1 he2)
        have hgl : B.getLast hBne = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
          have h1 : B.getLast hBne = B.getD (B.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
            rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show B.length - 1 < B.length by omega)]
            rfl
          rw [h1, hcol]
        have hsplit : B = B.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
          rw [← hgl]; exact (List.dropLast_append_getLast hBne).symm
        have hop : B⟦1⟧ = B.dropLast := by
          rw [oper_eq_pred_of_zero 1 (by omega) hz]
          unfold Pred
          rw [if_neg (by omega)]
        have hdl := hnat 1 le_rfl
        rw [hop] at hdl
        simp only [Set.mem_setOf_eq] at hdl
        have hdl0 : entry B.dropLast 0 0 = 0 := by
          rw [List.dropLast_eq_take,
            Wset.entry_take (show (0 : ℕ) < B.length - 1 by omega)]
          exact hroot
        have hIH : ∀ A' : TrioSeq, Aok A' → A' ++ Blk e B.dropLast ∈ W 0 :=
          fun A' hA' => hdl (fun c hc => hzr c (List.dropLast_subset _ hc))
            (fun c hc => hmo c (List.dropLast_subset _ hc)) hdl0 A' hA' e he
        have hgoal := blk_snoc_two (C := B.dropLast) (e := e)
          (fun c hc => hmo c (List.dropLast_subset _ hc)) hA hIH
        have heq : A ++ Blk e B = (A ++ Blk e B.dropLast) ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] := by
          conv_lhs => rw [hsplit]
          rw [Blk_snoc, List.append_assoc]
        rw [heq]
        exact hgoal
      · have hnz : ¬ (entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
            entry B 2 (B.length - 1) = 0) := fun h => hlast h.1
        have hp := hasParent_of_ZrootMono hzr hmo hroot hlen2 hnz
        refine A1_intro (Or.inr (Or.inl ?_))
        intro n hn
        rw [Blk_app, oper_shift _ _ 2 n hlen2 hp, ← Blk_app]
        obtain ⟨hzr', hmo'⟩ := ZM_oper hzr hmo n
        exact hnat n hn hzr' hmo' (by rw [Wset.oper_head_eq hn]; exact hroot) A hA e he
    · exact absurd hm (Nat.not_lt_zero m)
  intro B hB
  exact key hB

/-- 使いやすい形。 -/
theorem blk_zm {B : TrioSeq} (hB : B ∈ W 0) (hzr : Zroot B) (hmo : Mono B)
    (hroot : entry B 0 0 = 0) {A : TrioSeq} (hA : Aok A) {e : ℕ} (he : 1 ≤ e) :
    A ++ Blk e B ∈ W 0 :=
  blk_mem B hB hzr hmo hroot A hA e he

/-! ## シート行287 `X(1,1,0)(2,0,0)(3,1,1) = psi(W_w + W*psi(W_w))`

    287⟦n⟧ = X(1,1,0) ++ (2,0,0)(3,1,0)(4,2,0)... = Q ++ Blk 1 (Diag n)

（末尾 `(3,1,1)` は `srow = 2`、行 2 の親は `(2,0,0)`、`d0 = d1 = 1`、
ブロックは 1 列 `(2,0,0)`。）`Diag n = (0,0,0)(1,1,0)...(n-1,n-1,0)` は行 2 ≡ 0 で
`Zroot` ＋ `Mono` ＋ 根 0 なので `blk_zm` がそのまま効く。 -/

/-- 行 0・行 1 の対角 `(0,0,0)(1,1,0)...(n-1,n-1,0)`。 -/
def Diag (n : ℕ) : TrioSeq := (List.range n).map fun k => ((k, k, 0) : ℕ × ℕ × ℕ)

theorem Diag_col (n : ℕ) : ∀ c ∈ Diag n, ∃ k, c = ((k, k, 0) : ℕ × ℕ × ℕ) := by
  intro c hc
  simp only [Diag, List.mem_map] at hc
  obtain ⟨k, -, rfl⟩ := hc
  exact ⟨k, rfl⟩

theorem Diag_Z2 (n : ℕ) : Z2 (Diag n) := by
  intro c hc; obtain ⟨k, rfl⟩ := Diag_col n c hc; rfl

theorem Diag_zroot (n : ℕ) : Zroot (Diag n) := by
  intro c hc h0
  obtain ⟨k, rfl⟩ := Diag_col n c hc
  have hk : k = 0 := h0
  subst hk
  exact ⟨rfl, rfl⟩

theorem Diag_mono (n : ℕ) : Mono (Diag n) := by
  intro c hc; obtain ⟨k, rfl⟩ := Diag_col n c hc; dsimp only; omega

theorem Diag_root (n : ℕ) : entry (Diag n) 0 0 = 0 := by
  cases n with
  | zero => simp [Diag, entry]
  | succ n => simp [Diag, entry, List.range_succ_eq_map]

theorem Diag_mem (n : ℕ) : Diag n ∈ W 0 :=
  Zroot_mem_W (Diag_Z2 n) (Diag_zroot n) (Diag_root n)

/-- シート行287。 -/
def R287 : TrioSeq := [(0, 0, 0), (1, 1, 1), (1, 1, 0), (2, 0, 0), (3, 1, 1)]

theorem R287_len : R287.length = 5 := by simp [R287]

theorem nextrel0_R287_34 : nextrel0 R287 3 4 := by
  refine ⟨by simp [R287], by simp [R287], by omega, by simp [R287, entry], ?_⟩
  intro j hj; omega

theorem le0_R287_34 : le0 R287 3 4 :=
  ⟨by simp [R287], by simp [R287], Relation.ReflTransGen.single nextrel0_R287_34⟩

theorem nextrel1_R287_34 : nextrel1 R287 3 4 := by
  refine ⟨by simp [R287], by simp [R287], by omega, by simp [R287, entry],
    le0_R287_34, ?_⟩
  intro j hj
  have hjl := hj.2.1
  rw [R287_len] at hjl
  have hj4 : j = 4 := by omega
  subst hj4
  omega

theorem nextrel2_R287_34 : nextrel2 R287 3 4 := by
  refine ⟨by simp [R287], by simp [R287], by omega, by simp [R287, entry],
    ⟨by simp [R287], by simp [R287], Relation.ReflTransGen.single nextrel1_R287_34⟩, ?_⟩
  intro j hj
  have hjl := hj.2.1
  rw [R287_len] at hjl
  have hj4 : j = 4 := by omega
  subst hj4
  omega

theorem R287_hasParent : hasParent R287 2 4 :=
  hasParent2_of_le1_witness (by rw [R287_len]; omega)
    (Relation.ReflTransGen.single nextrel1_R287_34) (by simp [R287, entry])

theorem R287_parent : parent R287 2 4 = 3 :=
  R287_hasParent.unique (parent_nextR R287_hasParent) nextrel2_R287_34

theorem R287_srow : srow R287 4 = 2 := by simp [srow, R287, entry]

theorem le0_R287_33 : le0 R287 3 3 :=
  ⟨by simp [R287], by simp [R287], Relation.ReflTransGen.refl⟩

theorem le1_R287_33 : le1 R287 3 3 :=
  ⟨by simp [R287], by simp [R287], Relation.ReflTransGen.refl⟩

theorem flatMap_singleton_map {α β : Type _} (f : α → β) (l : List α) :
    l.flatMap (fun x => [f x]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

open Classical in
theorem oper_R287 (n : ℕ) : R287⟦n⟧ = Q ++ Blk 1 (Diag n) := by
  rw [L53.oper_unfold (j1 := 4) (i1 := 2) (j0 := 3) (d0 := 1) (d1 := 1)
      (by simp [R287]) (by omega) (by simp [R287, entry]) R287_srow.symm
      R287_hasParent R287_parent.symm (by simp [R287, entry]) (by simp [R287, entry]) n]
  have hr : List.range' 3 (4 - 3) = [3] := rfl
  have htk : R287.take 3 = [((0, 0, 0) : ℕ × ℕ × ℕ), (1, 1, 1), (1, 1, 0)] := rfl
  rw [hr, htk]
  have hbody : ∀ k : ℕ, ([3] : List ℕ).map
      (fun j => ((entry R287 0 j + (if le0 R287 3 j then k * 1 else 0),
        entry R287 1 j + (if le1 R287 3 j then k * 1 else 0),
        entry R287 2 j) : ℕ × ℕ × ℕ))
      = [((k + 2, k, 0) : ℕ × ℕ × ℕ)] := by
    intro k
    simp only [List.map_cons, List.map_nil]
    rw [if_pos le0_R287_33, if_pos le1_R287_33]
    simp [R287, entry, Nat.add_comm]
  rw [List.flatMap_congr (fun k _ => hbody k)]
  simp [Q, Blk, Diag, shiftr01, flatMap_singleton_map, Function.comp_def, Nat.add_comm]

/-- ★ シート行287 `X(1,1,0)(2,0,0)(3,1,1) ∈ W 0`。 -/
theorem R287_mem : R287 ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_R287 n]
  exact blk_zm (Diag_mem n) (Diag_zroot n) (Diag_mono n) (Diag_root n) Aok_Q (le_refl 1)

/-! ## シート行288 `X(1,1,0)(2,1,0) = psi(W_w + W^2)`

    288⟦n⟧ = concat_{k<n} shiftr01 (2k) 0 X(1,1,0)  =: Tw2 n

（末尾 `(2,1,0)` は `srow = 1`、行 1 の親は根、`d0 = 2`、ブロックは `X(1,1,0)` 全体。）
そして

    Tw2 (n+1) = X(1,1,0) ++ shiftr01 2 0 (Tw2 n) = Q ++ Blk 1 (Tw2 n)

なので `blk_zm` を `n` の帰納法で回すだけ。**d=2 の bump が塔の漸化式そのもの。** -/

theorem shiftr01_append0 (d : ℕ) (X Y : TrioSeq) :
    shiftr01 d 0 (X ++ Y) = shiftr01 d 0 X ++ shiftr01 d 0 Y := by
  simp [shiftr01]

theorem shiftr01_add0 (a b : ℕ) (X : TrioSeq) :
    shiftr01 a 0 (shiftr01 b 0 X) = shiftr01 (b + a) 0 X := by
  simp only [shiftr01, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro p _
  simp [Nat.add_assoc]

theorem shift_flatMap0 (d : ℕ) (f : ℕ → TrioSeq) : ∀ l : List ℕ,
    shiftr01 d 0 (l.flatMap f) = l.flatMap fun x => shiftr01 d 0 (f x)
  | [] => by simp [shiftr01]
  | (a :: t) => by
      rw [List.flatMap_cons, shiftr01_append0, shift_flatMap0 d f t, List.flatMap_cons]

theorem X110_eq : X110 = Q ++ [((1, 1, 0) : ℕ × ℕ × ℕ)] := by simp [X110, Q]

/-- `288` の展開の塔。 -/
def Tw2 (n : ℕ) : TrioSeq := (List.range n).flatMap fun k => shiftr01 (2 * k) 0 X110

theorem Tw2_succ (n : ℕ) : Tw2 (n + 1) = Q ++ Blk 1 (Tw2 n) := by
  rw [Blk_app, ← X110_eq]
  show (List.range (n + 1)).flatMap _ = _
  rw [List.range_succ_eq_map, List.flatMap_cons]
  have h0 : shiftr01 (2 * 0) 0 X110 = X110 := by simp [shiftr01]
  rw [h0, Tw2, shift_flatMap0, List.flatMap_map]
  congr 1

theorem Tw2_mono : ∀ n, Mono (Tw2 n)
  | 0 => by intro c hc; simp [Tw2] at hc
  | (n + 1) => by
      rw [Tw2_succ]
      intro c hc
      rcases List.mem_append.mp hc with hm | hm
      · exact Aok_Q.mono c hm
      · exact Blk_mono (Tw2_mono n) c hm

theorem Tw2_zroot : ∀ n, Zroot (Tw2 n)
  | 0 => by intro c hc; simp [Tw2] at hc
  | (n + 1) => by
      rw [Tw2_succ]
      intro c hc h0
      rcases List.mem_append.mp hc with hm | hm
      · exact Aok_Q.zroot c hm h0
      · have := Blk_col c hm; omega

theorem Tw2_root : ∀ n, entry (Tw2 n) 0 0 = 0
  | 0 => by simp [Tw2, entry]
  | (n + 1) => by
      rw [Tw2_succ, entry_append_left (by simp [Q])]
      exact Aok_Q.deep.1

theorem Tw2_mem : ∀ n, Tw2 n ∈ W 0
  | 0 => by simpa [Tw2] using W_nil 0
  | (n + 1) => by
      rw [Tw2_succ]
      exact blk_zm (Tw2_mem n) (Tw2_zroot n) (Tw2_mono n) (Tw2_root n) Aok_Q (le_refl 1)

/-- シート行288。 -/
def R288 : TrioSeq := [(0, 0, 0), (1, 1, 1), (1, 1, 0), (2, 1, 0)]

theorem R288_len : R288.length = 4 := by simp [R288]

theorem R288_srow : srow R288 3 = 1 := by simp [srow, R288, entry]

theorem nextrel0_R288_01 : nextrel0 R288 0 1 := by
  refine ⟨by simp [R288], by simp [R288], by omega, by simp [R288, entry], ?_⟩
  intro x hx; omega

theorem nextrel0_R288_02 : nextrel0 R288 0 2 := by
  refine ⟨by simp [R288], by simp [R288], by omega, by simp [R288, entry], ?_⟩
  intro x hx
  have : x = 1 := by omega
  subst this
  simp [R288, entry]

theorem nextrel0_R288_23 : nextrel0 R288 2 3 := by
  refine ⟨by simp [R288], by simp [R288], by omega, by simp [R288, entry], ?_⟩
  intro x hx; omega

theorem le0_R288_0 : le0 R288 0 0 :=
  ⟨by simp [R288], by simp [R288], Relation.ReflTransGen.refl⟩

theorem le0_R288_1 : le0 R288 0 1 :=
  ⟨by simp [R288], by simp [R288], Relation.ReflTransGen.single nextrel0_R288_01⟩

theorem le0_R288_2 : le0 R288 0 2 :=
  ⟨by simp [R288], by simp [R288], Relation.ReflTransGen.single nextrel0_R288_02⟩

theorem le0_R288_3 : le0 R288 0 3 :=
  ⟨by simp [R288], by simp [R288],
    (Relation.ReflTransGen.single nextrel0_R288_02).tail nextrel0_R288_23⟩

theorem nextrel1_R288 : nextrel1 R288 0 3 := by
  refine ⟨by simp [R288], by simp [R288], by omega, by simp [R288, entry],
    le0_R288_3, ?_⟩
  intro j hj
  have hjl := hj.2.1
  rw [R288_len] at hjl
  have hcase : j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hcase with rfl | rfl | rfl <;> simp [R288, entry]

theorem R288_hasParent : hasParent R288 1 3 :=
  H12Export.hasParent1_of_le0_witness (by rw [R288_len]; omega)
    le0_R288_3.2.2 (by simp [R288, entry])

theorem R288_parent : parent R288 1 3 = 0 :=
  R288_hasParent.unique (parent_nextR R288_hasParent) nextrel1_R288

open Classical in
theorem oper_R288 (n : ℕ) : R288⟦n⟧ = Tw2 n := by
  rw [L53.oper_unfold (j1 := 3) (i1 := 1) (j0 := 0) (d0 := 2) (d1 := 0)
      (by simp [R288]) (by omega) (by simp [R288, entry]) R288_srow.symm
      R288_hasParent R288_parent.symm (by simp [R288, entry]) (by simp) n]
  have hr : List.range' 0 (3 - 0) = [0, 1, 2] := rfl
  have htk : R288.take 0 = [] := rfl
  rw [hr, htk, List.nil_append]
  have hbody : ∀ k : ℕ, ([0, 1, 2] : List ℕ).map
      (fun j => ((entry R288 0 j + (if le0 R288 0 j then k * 2 else 0),
        entry R288 1 j + (if le1 R288 0 j then k * 0 else 0),
        entry R288 2 j) : ℕ × ℕ × ℕ))
      = shiftr01 (2 * k) 0 X110 := by
    intro k
    simp only [List.map_cons, List.map_nil, Nat.mul_zero, ite_self, Nat.add_zero]
    rw [if_pos le0_R288_0, if_pos le0_R288_1, if_pos le0_R288_2]
    simp [R288, entry, X110, shiftr01, Nat.mul_comm, Nat.add_comm]
  rw [List.flatMap_congr (fun k _ => hbody k)]
  rfl

/-- ★ シート行288 `X(1,1,0)(2,1,0) ∈ W 0`。 -/
theorem R288_mem : R288 ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_R288 n]
  exact Tw2_mem n

#print axioms Tw2_mem
#print axioms R288_mem

#print axioms oper_R287
#print axioms R287_mem

#print axioms blk_snoc_two
#print axioms blk_mem

#print axioms snoc_row1_two
#print axioms R285_mem
#print axioms R286_mem

#print axioms powTow_eq_Tow
#print axioms X110_fs

/-- 具体例: `X = (0,0,0)(1,1,1)` について `X ++ bump X = X(1,0,0)(2,1,1) ∈ W 0`。 -/
theorem QQ_mem : [((0, 0, 0) : ℕ × ℕ × ℕ), (1, 1, 1), (1, 0, 0), (2, 1, 1)] ∈ W 0 := by
  have h := pow_two Aok_Q
  simpa [Q, bump, shiftr01] using h

/-- 具体例: `X ++ bump (X ++ bump X) = X(1,0,0)(2,1,1)(2,0,0)(3,1,1) ∈ W 0`。 -/
theorem QQQ_mem :
    [((0, 0, 0) : ℕ × ℕ × ℕ), (1, 1, 1), (1, 0, 0), (2, 1, 1), (2, 0, 0), (3, 1, 1)]
      ∈ W 0 := by
  have h := pow_self Aok_Q
  simpa [Q, bump, shiftr01] using h

#print axioms Aok.append_bump
#print axioms pow_gen
#print axioms QQQ_mem

#print axioms snoc_row1_oper
#print axioms snoc_row1

#print axioms Utow_mem
#print axioms X110_mem

#print axioms ZM_oper
#print axioms hasParent2_of_le1_witness
#print axioms bump_mem3

#print axioms Z2Zroot_oper
#print axioms bump_mem2
#print axioms M278_mem

#print axioms Flat_mem_W
#print axioms chain_mem
#print axioms M3_mem'

#print axioms Flat_oper
#print axioms bump_mem

#print axioms oper_append_right_of
#print axioms oper_bump
#print axioms Flat_srow

/-! ## 中間セグメント付きの d=2 bump（`BlkM`）

`Blk e B = (1,e,0) :: B⇑2` は、深さ 1 の**列 1 本**の後ろにブロックを吊るす形
だった。行 289 以上では、深さ 1 の列の後ろに深さ 2 の列が何本か挟まった形

    A ++ M ++ B⇑2        M = (1,e,0)(2,*,*)...(2,*,*)

が要る。`(2,0,0)` を継ぐときの行 0 の親は「深さ 2 未満の最後の列」＝ `M` の
先頭なので、`Blk` の議論はそのまま通る。底だけが `A ++ M ∈ W 0` に変わる。

さらに `(2,1,0)` を継ぐ規則（`snoc21_mem`）が要るので、「**根以外の浅い列
（深さ ≤ 1）の行 1 は 1 以上**」という条件 `Sh1` を一緒に運ぶ。`Sh1` は
`A ↦ A ++ BlkM M B` で保たれる（`M` の先頭以外は深さ 2 以上だから）。 -/

/-- 根以外の深さ ≤ 1 の列は行 1 が 1 以上。 -/
def Sh1 (Y : TrioSeq) : Prop :=
  ∀ j, 0 < j → j < Y.length → entry Y 0 j ≤ 1 → 1 ≤ entry Y 1 j

/-- 中間セグメント用（根も含める）。 -/
def Sh1M (M : TrioSeq) : Prop :=
  ∀ j, j < M.length → entry M 0 j ≤ 1 → 1 ≤ entry M 1 j

/-- 中間セグメント: 先頭が深さ 1・行 1 が 1 以上、残りは深さ 2 以上。 -/
structure Mid (M : TrioSeq) : Prop where
  ne : M ≠ []
  col : ∀ c ∈ M, 1 ≤ c.1
  head : entry M 0 0 = 1
  head1 : 1 ≤ entry M 1 0
  tail : ∀ j, 1 ≤ j → j < M.length → 2 ≤ entry M 0 j
  mono : Mono M

theorem Mid.sh1M {M : TrioSeq} (hM : Mid M) : Sh1M M := by
  intro j hj hsh
  rcases Nat.eq_zero_or_pos j with rfl | h
  · exact hM.head1
  · have := hM.tail j h hj; omega

/-- `M` ＋ 深さ 2 以上のブロック。 -/
def BlkM (M B : TrioSeq) : TrioSeq := M ++ shiftr01 2 0 B

theorem BlkM_col {M B : TrioSeq} (hM : ∀ c ∈ M, 1 ≤ c.1) :
    ∀ c ∈ BlkM M B, 1 ≤ c.1 := by
  intro c hc
  rcases List.mem_append.mp hc with hm | hm
  · exact hM c hm
  · have := shift2_col c hm; omega

theorem BlkM_mono {M B : TrioSeq} (hM : Mono M) (hB : Mono B) : Mono (BlkM M B) := by
  intro c hc
  rcases List.mem_append.mp hc with hm | hm
  · exact hM c hm
  · exact shift2_mono hB c hm

theorem BlkM_nil (M : TrioSeq) : BlkM M [] = M := by simp [BlkM, shiftr01]

theorem BlkM_snoc (M B : TrioSeq) :
    BlkM M (B ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])
      = BlkM M B ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] := by
  simp [BlkM, shiftr01]

theorem BlkM_app (A M B : TrioSeq) :
    A ++ BlkM M B = (A ++ M) ++ shiftr01 2 0 B := by
  simp [BlkM]

theorem BlkM_len (M B : TrioSeq) : (BlkM M B).length = M.length + B.length := by
  simp [BlkM, shiftr01]

theorem Aok_append_BlkM {A M B : TrioSeq} (hmem : A ++ BlkM M B ∈ W 0)
    (hA : Aok A) (hM : Mid M) (hmo : Mono B) : Aok (A ++ BlkM M B) := by
  refine ⟨hmem, by simp [List.append_eq_nil_iff, hA.ne],
    Deep_append hA.deep hA.ne (fun c hc => BlkM_col hM.col c hc), ?_, ?_⟩
  · intro c hc h0
    rcases List.mem_append.mp hc with hm | hm
    · exact hA.zroot c hm h0
    · have := BlkM_col hM.col c hm; omega
  · intro c hc
    rcases List.mem_append.mp hc with hm | hm
    · exact hA.mono c hm
    · exact BlkM_mono hM.mono hmo c hm

/-- `Sh1` は `BlkM` の継ぎ足しで保たれる。 -/
theorem Sh1_append_BlkM {A M B : TrioSeq} (hne : A ≠ []) (hA : Sh1 A) (hMs : Sh1M M) :
    Sh1 (A ++ BlkM M B) := by
  intro j hj0 hjl hsh
  have hAlen : 0 < A.length := List.length_pos_iff.mpr hne
  rcases Nat.lt_or_ge j A.length with h | h
  · rw [entry_append_left h] at hsh ⊢
    exact hA j hj0 h hsh
  · obtain ⟨t, rfl⟩ : ∃ t, j = A.length + t := ⟨j - A.length, by omega⟩
    rw [entry_append_right] at hsh ⊢
    have htl : t < M.length + B.length := by
      simp only [List.length_append, BlkM_len] at hjl; omega
    rcases Nat.lt_or_ge t M.length with h2 | h2
    · rw [BlkM, entry_append_left h2] at hsh ⊢
      exact hMs t h2 hsh
    · exfalso
      obtain ⟨s, rfl⟩ : ∃ s, t = M.length + s := ⟨t - M.length, by omega⟩
      have hm : (shiftr01 2 0 B).getD s ((0, 0, 0) : ℕ × ℕ × ℕ) ∈ shiftr01 2 0 B :=
        getD_mem_of_lt (by rw [shiftr01_length]; omega)
      have h3 := shift2_col _ hm
      rw [BlkM, entry_append_right, entry0_eq] at hsh
      omega

theorem Yseq_Aok_M {A M C : TrioSeq} (hA : Aok A) (hsA : Sh1 A) (hM : Mid M)
    (hmoC : Mono C)
    (hIH : ∀ A' : TrioSeq, Aok A' → Sh1 A' → A' ++ BlkM M C ∈ W 0) :
    ∀ n, Aok (Yseq A (BlkM M C) n) ∧ Sh1 (Yseq A (BlkM M C) n)
  | 0 => ⟨hA, hsA⟩
  | (n + 1) =>
      ⟨Aok_append_BlkM
          (hIH _ (Yseq_Aok_M hA hsA hM hmoC hIH n).1 (Yseq_Aok_M hA hsA hM hmoC hIH n).2)
          (Yseq_Aok_M hA hsA hM hmoC hIH n).1 hM hmoC,
       Sh1_append_BlkM (Yseq_Aok_M hA hsA hM hmoC hIH n).1.ne
         (Yseq_Aok_M hA hsA hM hmoC hIH n).2 hM.sh1M⟩

theorem BlkM_entry_zero {M C : TrioSeq} (hM : Mid M) : entry (BlkM M C) 0 0 = 1 := by
  have hlen : 0 < M.length := List.length_pos_iff.mpr hM.ne
  rw [BlkM, entry_append_left hlen]
  exact hM.head

theorem BlkM_entry_pos {M C : TrioSeq} (hM : Mid M) (s : ℕ) (hs1 : 1 ≤ s)
    (hs : s < M.length + C.length) : 2 ≤ entry (BlkM M C) 0 s := by
  rcases Nat.lt_or_ge s M.length with h | h
  · rw [BlkM, entry_append_left h]
    exact hM.tail s hs1 h
  · obtain ⟨t, rfl⟩ : ∃ t, s = M.length + t := ⟨s - M.length, by omega⟩
    have hm : (shiftr01 2 0 C).getD t ((0, 0, 0) : ℕ × ℕ × ℕ) ∈ shiftr01 2 0 C :=
      getD_mem_of_lt (by rw [shiftr01_length]; omega)
    show 2 ≤ entry (M ++ shiftr01 2 0 C) 0 (M.length + t)
    rw [entry_append_right, entry0_eq]
    exact shift2_col _ hm

/-- **(S2')**: コピー族が済めば `(2,0,0)` を継げる。 -/
theorem blkM_snoc_two {C A M : TrioSeq} (hM : Mid M) (hmoC : Mono C) (hA : Aok A)
    (hsA : Sh1 A)
    (hIH : ∀ A' : TrioSeq, Aok A' → Sh1 A' → A' ++ BlkM M C ∈ W 0) :
    (A ++ BlkM M C) ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hAlen : 0 < A.length := List.length_pos_iff.mpr hA.ne
  have hMlen : 0 < M.length := List.length_pos_iff.mpr hM.ne
  set P : TrioSeq := A ++ BlkM M C with hP
  have hPlen : P.length = A.length + (M.length + C.length) := by
    rw [hP]; simp [BlkM_len]
  have hPne : P ≠ [] := by rw [hP]; simp [List.append_eq_nil_iff, hA.ne]
  have hcolA : entry P 0 A.length = 1 := by
    rw [hP, show A.length = A.length + 0 from rfl, entry_append_right]
    exact BlkM_entry_zero hM
  have hcolmid : ∀ j, A.length < j → j < P.length → 2 ≤ entry P 0 j := by
    intro j h1 h2
    obtain ⟨s, rfl⟩ : ∃ s, j = A.length + (s + 1) := ⟨j - A.length - 1, by omega⟩
    rw [hP, entry_append_right]
    exact BlkM_entry_pos hM (s + 1) (by omega) (by omega)
  have hlast2 : entry (P ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) 0 P.length = 2 :=
    entry_append_last.1
  have hpar : hasParent (P ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) 0 P.length := by
    rw [hasParent_zero_iff (by simp)]
    refine ⟨A.length, by omega, ?_⟩
    rw [entry_append_lt (show A.length < P.length by omega), hcolA, hlast2]
    omega
  have hj0 : parent (P ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) 0 P.length = A.length := by
    have h := parent_nextR hpar
    rw [nextR, if_pos rfl] at h
    obtain ⟨-, -, hlt, hval, hmin⟩ := h
    by_contra hne0
    rcases Nat.lt_or_ge (parent (P ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) 0 P.length) A.length
      with hc | hc
    · have hmm := hmin A.length ⟨hc, by omega⟩
      rw [entry_append_lt (show A.length < P.length by omega), hcolA, hlast2] at hmm
      omega
    · have hgt : A.length < parent (P ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) 0 P.length :=
        lt_of_le_of_ne hc (Ne.symm hne0)
      have hmm := hcolmid _ hgt (by omega)
      rw [entry_append_lt (show parent (P ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) 0 P.length
        < P.length by omega), hlast2] at hval
      omega
  refine snoc_flat (A := P) (b := ((2, 0, 0) : ℕ × ℕ × ℕ)) (j0 := A.length) hPne
    (by simp) rfl rfl hpar hj0 ?_
  intro n
  have h1 : P.take A.length = A := by rw [hP, List.take_left]
  have h2 : P.drop A.length = BlkM M C := by rw [hP, List.drop_left]
  rw [h1, h2, ← Yseq_eq]
  exact (Yseq_Aok_M hA hsA hM hmoC hIH n).1.mem

/-- ★ **中間セグメント付き d=2 bump**。底は `∀ Aok A, Sh1 A → A ++ M ∈ W 0`。 -/
theorem blkM_mem (M : TrioSeq) (hM : Mid M)
    (hbase : ∀ A : TrioSeq, Aok A → Sh1 A → A ++ M ∈ W 0) :
    ∀ B ∈ W 0, Zroot B → Mono B → entry B 0 0 = 0 →
      ∀ A : TrioSeq, Aok A → Sh1 A → A ++ BlkM M B ∈ W 0 := by
  have key : W 0 ⊆ {B : TrioSeq | Zroot B → Mono B → entry B 0 0 = 0 →
      ∀ A : TrioSeq, Aok A → Sh1 A → A ++ BlkM M B ∈ W 0} := by
    refine A2' ?_
    intro B hB
    simp only [Set.mem_setOf_eq]
    intro hzr hmo hroot A hA hsA
    by_cases hshort : B.length ≤ 1
    · rcases (by omega : B.length = 0 ∨ B.length = 1) with h0 | h1
      · have hnil : B = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        rw [BlkM_nil]
        exact hbase A hA hsA
      · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
        have hc0 : c.1 = 0 := hroot
        obtain ⟨hc1, hc2⟩ := hzr c (by simp) hc0
        have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1 hc2)
        subst hcz
        have heq : A ++ BlkM M [((0, 0, 0) : ℕ × ℕ × ℕ)]
            = (A ++ BlkM M []) ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] := by
          simp [BlkM, shiftr01]
        rw [heq]
        refine blkM_snoc_two hM (by intro c hc; simp at hc) hA hsA ?_
        intro A' hA' hsA'
        rw [BlkM_nil]
        exact hbase A' hA' hsA'
    have hlen2 : 2 ≤ B.length := by omega
    have hBne : B ≠ [] := by
      intro hc; rw [hc] at hlen2; simp at hlen2
    rcases hB with ⟨hl, -⟩ | hnat | ⟨m, hm, -, -⟩
    · exact absurd hl hshort
    · by_cases hlast : entry B 0 (B.length - 1) = 0
      · obtain ⟨he1, he2⟩ := Zroot_entry hzr hlast
        have hz : entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
            entry B 2 (B.length - 1) = 0 := ⟨hlast, he1, he2⟩
        have hcol : B.getD (B.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ)
            = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hlast (Prod.ext he1 he2)
        have hgl : B.getLast hBne = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
          have h1 : B.getLast hBne = B.getD (B.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
            rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show B.length - 1 < B.length by omega)]
            rfl
          rw [h1, hcol]
        have hsplit : B = B.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
          rw [← hgl]; exact (List.dropLast_append_getLast hBne).symm
        have hop : B⟦1⟧ = B.dropLast := by
          rw [oper_eq_pred_of_zero 1 (by omega) hz]
          unfold Pred
          rw [if_neg (by omega)]
        have hdl := hnat 1 le_rfl
        rw [hop] at hdl
        simp only [Set.mem_setOf_eq] at hdl
        have hdl0 : entry B.dropLast 0 0 = 0 := by
          rw [List.dropLast_eq_take,
            Wset.entry_take (show (0 : ℕ) < B.length - 1 by omega)]
          exact hroot
        have hIH : ∀ A' : TrioSeq, Aok A' → Sh1 A' → A' ++ BlkM M B.dropLast ∈ W 0 :=
          fun A' hA' hsA' => hdl (fun c hc => hzr c (List.dropLast_subset _ hc))
            (fun c hc => hmo c (List.dropLast_subset _ hc)) hdl0 A' hA' hsA'
        have hgoal := blkM_snoc_two (C := B.dropLast) hM
          (fun c hc => hmo c (List.dropLast_subset _ hc)) hA hsA hIH
        have heq : A ++ BlkM M B
            = (A ++ BlkM M B.dropLast) ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] := by
          conv_lhs => rw [hsplit]
          rw [BlkM_snoc, List.append_assoc]
        rw [heq]
        exact hgoal
      · have hnz : ¬ (entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
            entry B 2 (B.length - 1) = 0) := fun h => hlast h.1
        have hp := hasParent_of_ZrootMono hzr hmo hroot hlen2 hnz
        refine A1_intro (Or.inr (Or.inl ?_))
        intro n hn
        rw [BlkM_app, oper_shift _ _ 2 n hlen2 hp, ← BlkM_app]
        obtain ⟨hzr', hmo'⟩ := ZM_oper hzr hmo n
        exact hnat n hn hzr' hmo' (by rw [Wset.oper_head_eq hn]; exact hroot) A hA hsA
    · exact absurd hm (Nat.not_lt_zero m)
  intro B hB
  exact key hB

#print axioms blkM_snoc_two
#print axioms blkM_mem

/-! ## `(2,1,0)` の継ぎ足しと シート行289 `X(1,1,0)(2,1,0)(3,0,0) = psi(W_w + W^w)`

`Y` の末尾に `(2,1,0)` を継ぐと、バッドルートは行 1（`srow = 1`）、行 1 の親は
根（深さ 0）で `d0 = 2`、`d1 = 0`（`i1 = 1` なので行 1 は上昇しない）。よって

    (Y ++ [(2,1,0)])⟦n⟧ = Y ++ Y⇑2 ++ Y⇑4 ++ ... （n 個）=: Tw Y n
    Tw Y (n+1) = Y ++ (Tw Y n)⇑2

で、`Y = A ++ Mseq m` なら右辺は `A ++ BlkM (Mseq m) (Tw Y n)`。
これで `m` についての帰納法が回る（`(I)_0 → (II)_0 → (I)_1 → ...`）。 -/

/-- `Y` の d=2 の塔。 -/
def Tw (Y : TrioSeq) (n : ℕ) : TrioSeq :=
  (List.range n).flatMap fun k => shiftr01 (2 * k) 0 Y

theorem Tw_succ (Y : TrioSeq) (n : ℕ) :
    Tw Y (n + 1) = Y ++ shiftr01 2 0 (Tw Y n) := by
  show (List.range (n + 1)).flatMap _ = _
  rw [List.range_succ_eq_map, List.flatMap_cons]
  have h0 : shiftr01 (2 * 0) 0 Y = Y := by simp [shiftr01]
  rw [h0, Tw, shift_flatMap0, List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro x _
  rw [shiftr01_add0, Nat.mul_succ]

theorem Tw_mono {Y : TrioSeq} (h : Mono Y) : ∀ n, Mono (Tw Y n)
  | 0 => by intro c hc; simp [Tw] at hc
  | (n + 1) => by
      rw [Tw_succ]
      intro c hc
      rcases List.mem_append.mp hc with hm | hm
      · exact h c hm
      · exact shift2_mono (Tw_mono h n) c hm

theorem Tw_zroot {Y : TrioSeq} (h : Zroot Y) : ∀ n, Zroot (Tw Y n)
  | 0 => by intro c hc; simp [Tw] at hc
  | (n + 1) => by
      rw [Tw_succ]
      intro c hc h0
      rcases List.mem_append.mp hc with hm | hm
      · exact h c hm h0
      · have := shift2_col c hm; omega

theorem Tw_root {Y : TrioSeq} (hne : Y ≠ []) (h : entry Y 0 0 = 0) :
    ∀ n, entry (Tw Y n) 0 0 = 0
  | 0 => by simp [Tw, entry]
  | (n + 1) => by
      rw [Tw_succ, entry_append_left (List.length_pos_iff.mpr hne)]
      exact h

/-- 行 0 の祖先関係は行 0 の値について単調。 -/
theorem rtg0_entry_le {M : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 M) a b) : entry M 0 a ≤ entry M 0 b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact le_trans ih (le_of_lt hstep.2.2.2.1)

open Classical in
/-- ★ `(2,1,0)` を継いだときの展開は `Y` の d=2 の塔。 -/
theorem oper_snoc21 {Y : TrioSeq} (hne : Y ≠ []) (hd : Deep Y) (hz : Zroot Y)
    (hs1 : Sh1 Y) (n : ℕ) :
    (Y ++ [((2, 1, 0) : ℕ × ℕ × ℕ)])⟦n⟧ = Tw Y n := by
  have hplen : 0 < Y.length := List.length_pos_iff.mpr hne
  have hlast := entry_append_last (P := Y) (c := ((2, 1, 0) : ℕ × ℕ × ℕ))
  have hpre : ∀ i j, j < Y.length →
      entry (Y ++ [((2, 1, 0) : ℕ × ℕ × ℕ)]) i j = entry Y i j :=
    fun i j hj => entry_append_lt hj
  have hMdeep : Deep (Y ++ [((2, 1, 0) : ℕ × ℕ × ℕ)]) := Deep_snoc hd hne (by omega)
  set M : TrioSeq := Y ++ [((2, 1, 0) : ℕ × ℕ × ℕ)] with hM
  have hMlen : M.length = Y.length + 1 := by rw [hM]; simp
  have hl0 : entry M 0 Y.length = 2 := hlast.1
  have hl1 : entry M 1 Y.length = 1 := hlast.2.1
  have hl2 : entry M 2 Y.length = 0 := hlast.2.2
  have hsh : ∀ x, 0 < x → x < M.length → entry M 0 0 < entry M 0 x := by
    intro x hx0 hxl
    rw [hMdeep.1]
    exact hMdeep.2 x hx0 hxl
  have hle0 : ∀ j, j < M.length → le0 M 0 j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact ⟨by omega, by omega, Relation.ReflTransGen.refl⟩
    · exact H12Export.le0_root_of_shallow (by omega) hsh j hj0 hj
  have hroot1 : entry M 1 0 = 0 := by
    rw [hpre 1 0 hplen]
    exact (Zroot_entry hz hd.1).1
  have hsrow : srow M Y.length = 1 := by
    unfold srow
    rw [if_neg (by rw [hl2]; omega), if_pos (by rw [hl1]; omega)]
  have hpar : hasParent M 1 Y.length :=
    H12Export.hasParent1_of_le0_witness (by omega) (hle0 Y.length (by omega)).2.2
      (by rw [hroot1, hl1]; omega)
  have hnr1 : nextrel1 M 0 Y.length := by
    refine ⟨by omega, by omega, hplen, by rw [hroot1, hl1]; omega,
      hle0 Y.length (by omega), ?_⟩
    rintro j ⟨hj0, hjle⟩
    rw [hl1]
    rcases Nat.lt_or_ge j Y.length with h | h
    · -- `j` は `Y` の中。祖先なので行 0 は 2 未満 ⟹ 深さ ≤ 1 ⟹ `Sh1`。
      have hjne : j ≠ Y.length := by omega
      obtain ⟨c, hc1, hc2⟩ :=
        (Relation.ReflTransGen.cases_head hjle.2.2).resolve_left (by
          intro hcon; exact hjne hcon)
      have hlt : entry M 0 j < entry M 0 c := hc1.2.2.2.1
      have hle : entry M 0 c ≤ entry M 0 Y.length := rtg0_entry_le hc2
      rw [hl0] at hle
      rw [hpre 1 j h]
      refine hs1 j hj0 h ?_
      rw [← hpre 0 j h]
      omega
    · have hjeq : j = Y.length := by
        have := H12Export.rtg0_index_le hjle.2.2
        omega
      rw [hjeq, hl1]
  have hj0 : parent M 1 Y.length = 0 := hpar.unique (parent_nextR hpar) hnr1
  rw [L53.oper_unfold (j1 := Y.length) (i1 := 1) (j0 := 0) (d0 := 2) (d1 := 0)
      (by omega) (by omega) (by rintro ⟨h, -, -⟩; rw [hl0] at h; omega)
      hsrow.symm hpar hj0.symm (by rw [if_pos (by omega), hl0, hMdeep.1]) (by simp) n,
    Tw]
  simp only [List.take_zero, List.nil_append, Nat.sub_zero, Nat.mul_zero, ite_self,
    Nat.add_zero]
  apply List.flatMap_congr
  intro k _
  rw [← map_range'_shift Y (2 * k)]
  apply List.map_congr_left
  intro j hj
  have hjl : j < Y.length := by have := List.mem_range'_1.1 hj; omega
  rw [if_pos (hle0 j (by omega)), hpre 0 j hjl, hpre 1 j hjl, hpre 2 j hjl,
    Nat.mul_comm k 2]

/-- ★ 塔が済めば `(2,1,0)` を継げる。 -/
theorem snoc21_mem {Y : TrioSeq} (hne : Y ≠ []) (hd : Deep Y) (hz : Zroot Y)
    (hs1 : Sh1 Y) (htw : ∀ n, Tw Y n ∈ W 0) :
    Y ++ [((2, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_snoc21 hne hd hz hs1 n]
  exact htw n

/-! ### 中間セグメント `Mseq m = (1,1,0)(2,1,0)^m` -/

def Rep21 (m : ℕ) : TrioSeq := List.replicate m ((2, 1, 0) : ℕ × ℕ × ℕ)

def Mseq (m : ℕ) : TrioSeq := ((1, 1, 0) : ℕ × ℕ × ℕ) :: Rep21 m

theorem Rep21_len (m : ℕ) : (Rep21 m).length = m := by simp [Rep21]

theorem Rep21_mem {m : ℕ} {c : ℕ × ℕ × ℕ} (h : c ∈ Rep21 m) :
    c = ((2, 1, 0) : ℕ × ℕ × ℕ) := List.eq_of_mem_replicate h

theorem Mseq_len (m : ℕ) : (Mseq m).length = m + 1 := by simp [Mseq, Rep21]

theorem Mseq_zero : Mseq 0 = [((1, 1, 0) : ℕ × ℕ × ℕ)] := by simp [Mseq, Rep21]

theorem Mseq_succ (m : ℕ) :
    Mseq (m + 1) = Mseq m ++ [((2, 1, 0) : ℕ × ℕ × ℕ)] := by
  simp [Mseq, Rep21, List.replicate_succ']

theorem Mseq_mem_col {m : ℕ} {c : ℕ × ℕ × ℕ} (h : c ∈ Mseq m) :
    1 ≤ c.1 ∧ c.2.2 ≤ c.2.1 := by
  rcases List.mem_cons.mp h with rfl | hm
  · exact ⟨by decide, by decide⟩
  · rw [Rep21_mem hm]; exact ⟨by decide, by decide⟩

theorem Mseq_entry {m t : ℕ} (h : t < m) :
    entry (Mseq m) 0 (t + 1) = 2 := by
  have hg : (Mseq m).getD (t + 1) ((0, 0, 0) : ℕ × ℕ × ℕ)
      = (Rep21 m).getD t ((0, 0, 0) : ℕ × ℕ × ℕ) := rfl
  have h2 : (Rep21 m).getD t ((0, 0, 0) : ℕ × ℕ × ℕ) = ((2, 1, 0) : ℕ × ℕ × ℕ) :=
    Rep21_mem (getD_mem_of_lt (by rw [Rep21_len]; exact h))
  show ((Mseq m).getD (t + 1) ((0, 0, 0) : ℕ × ℕ × ℕ)).1 = 2
  rw [hg, h2]

theorem Mid_Mseq (m : ℕ) : Mid (Mseq m) := by
  refine ⟨by simp [Mseq], fun c hc => (Mseq_mem_col hc).1, rfl, le_refl 1, ?_, ?_⟩
  · intro j h1 h2
    obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
    rw [Mseq_len] at h2
    exact le_of_eq (Mseq_entry (by omega)).symm
  · intro c hc
    exact (Mseq_mem_col hc).2

theorem Aok_append_Mseq {A : TrioSeq} (hA : Aok A) (m : ℕ)
    (hmem : A ++ Mseq m ∈ W 0) : Aok (A ++ Mseq m) := by
  have h := Aok_append_BlkM (M := Mseq m) (B := []) (by rw [BlkM_nil]; exact hmem) hA
    (Mid_Mseq m) (by intro c hc; simp at hc)
  rw [BlkM_nil] at h
  exact h

theorem Sh1_append_Mseq {A : TrioSeq} (hne : A ≠ []) (hsA : Sh1 A) (m : ℕ) :
    Sh1 (A ++ Mseq m) := by
  have h := Sh1_append_BlkM (M := Mseq m) (B := []) hne hsA (Mid_Mseq m).sh1M
  rw [BlkM_nil] at h
  exact h

/-- `Tw (A ++ Mseq m)` の塔（`m` の段の帰納法の仮定 `hbase` を使う）。 -/
theorem tw_mseq_mem (m : ℕ)
    (hbase : ∀ A : TrioSeq, Aok A → Sh1 A → A ++ Mseq m ∈ W 0)
    {A : TrioSeq} (hA : Aok A) (hsA : Sh1 A) : ∀ n, Tw (A ++ Mseq m) n ∈ W 0
  | 0 => by simpa [Tw] using W_nil 0
  | (n + 1) => by
      have hY : Aok (A ++ Mseq m) := Aok_append_Mseq hA m (hbase A hA hsA)
      have heq : Tw (A ++ Mseq m) (n + 1)
          = A ++ BlkM (Mseq m) (Tw (A ++ Mseq m) n) := by
        rw [Tw_succ, BlkM, List.append_assoc]
      rw [heq]
      exact blkM_mem (Mseq m) (Mid_Mseq m) hbase _
        (tw_mseq_mem m hbase hA hsA n) (Tw_zroot hY.zroot n) (Tw_mono hY.mono n)
        (Tw_root hY.ne hY.deep.1 n) A hA hsA

/-- ★★ `A ++ (1,1,0)(2,1,0)^m ∈ W 0`。 -/
theorem mseq_mem : ∀ m : ℕ, ∀ A : TrioSeq, Aok A → Sh1 A → A ++ Mseq m ∈ W 0
  | 0 => by
      intro A hA hsA
      rw [Mseq_zero]
      exact snoc_row1 hA.mem hA.ne hA.deep hA.zroot hA.mono (le_refl 1)
  | (m + 1) => by
      intro A hA hsA
      have hY : Aok (A ++ Mseq m) := Aok_append_Mseq hA m (mseq_mem m A hA hsA)
      have hsY : Sh1 (A ++ Mseq m) := Sh1_append_Mseq hA.ne hsA m
      rw [Mseq_succ, ← List.append_assoc]
      exact snoc21_mem hY.ne hY.deep hY.zroot hsY (tw_mseq_mem m (mseq_mem m) hA hsA)

/-! ### シート行289 -/

theorem Sh1_Q : Sh1 Q := by
  intro j hj0 hjl hsh
  have hj : j = 1 := by simp [Q] at hjl; omega
  subst hj
  simp [Q, entry]

def R289 : TrioSeq := [(0, 0, 0), (1, 1, 1), (1, 1, 0), (2, 1, 0), (3, 0, 0)]

theorem R289_eq : R289 = R288 ++ [((3, 0, 0) : ℕ × ℕ × ℕ)] := by simp [R289, R288]

theorem R289_cop (n : ℕ) :
    R288.take 3 ++ (List.range n).flatMap (fun _ => R288.drop 3) ∈ W 0 := by
  have h1 : R288.take 3 = X110 := rfl
  have h2 : R288.drop 3 = [((2, 1, 0) : ℕ × ℕ × ℕ)] := rfl
  have h3 : (List.range n).flatMap (fun _ => [((2, 1, 0) : ℕ × ℕ × ℕ)]) = Rep21 n := by
    induction n with
    | zero => simp [Rep21]
    | succ n ih =>
        rw [List.range_succ, List.flatMap_append, ih]
        simp [Rep21, List.replicate_succ']
  rw [h1, h2, h3, X110_eq, List.append_assoc]
  exact mseq_mem n Q Aok_Q Sh1_Q

/-- ★ シート行289 `X(1,1,0)(2,1,0)(3,0,0) ∈ W 0`。 -/
theorem R289_mem : R289 ∈ W 0 := by
  rw [R289_eq]
  have hnr0 : nextrel0 (R288 ++ [((3, 0, 0) : ℕ × ℕ × ℕ)]) 3 4 := by
    refine ⟨by simp [R288], by simp [R288], by omega, by simp [R288, entry], ?_⟩
    intro j hj; omega
  have hpar4 : hasParent (R288 ++ [((3, 0, 0) : ℕ × ℕ × ℕ)]) 0 4 := by
    rw [hasParent_zero_iff (by simp [R288])]
    exact ⟨3, by omega, by simp [R288, entry]⟩
  have hj04 : parent (R288 ++ [((3, 0, 0) : ℕ × ℕ × ℕ)]) 0 4 = 3 :=
    hpar4.unique (parent_nextR hpar4) (by rw [nextR, if_pos rfl]; exact hnr0)
  have hpar : hasParent (R288 ++ [((3, 0, 0) : ℕ × ℕ × ℕ)]) 0 R288.length := by
    rw [R288_len]; exact hpar4
  have hj0 : parent (R288 ++ [((3, 0, 0) : ℕ × ℕ × ℕ)]) 0 R288.length = 3 := by
    rw [R288_len]; exact hj04
  exact snoc_flat (A := R288) (b := ((3, 0, 0) : ℕ × ℕ × ℕ)) (j0 := 3)
    (by simp [R288]) (by simp) rfl rfl hpar hj0 R289_cop

#print axioms oper_snoc21
#print axioms mseq_mem
#print axioms R289_mem

end Small
end TRIO
