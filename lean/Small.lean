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

#print axioms M_mem
#print axioms Mm_mem
#print axioms snoc_flat
#print axioms snoc_two
#print axioms Rep_mem
#print axioms Rep_one_mem
#print axioms M2_mem
#print axioms snoc_one

end Small
end TRIO
