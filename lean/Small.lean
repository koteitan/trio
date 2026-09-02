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

/-- 親は根。行 1 の列 `(1,1,1)` は高さ 1 なので候補から外れる。 -/
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

/-! ## 一般化した 1 段: 根の直上に `(1,0,0)` を継ぐ

`Mm` の各段でやったことは、行列に固有ではない。**根が `(0,0,0)` で、他の列が全部
高さ 1 以上**なら、末尾に `(1,0,0)` を継いでよい（親が必ず根なので
`mem_W_of_flat_root`）。これで梯子の (1,0,0) 方向は何段でも伸びる。 -/

/-- **根の直上に `(1,0,0)` を継ぐのは無料**（`P` の根が高さ 0、他が高さ 1 以上のとき）。 -/
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

`snoc_one` の仮定「根が高さ 0・他は高さ 1 以上」は継ぎ足しで保たれる。名前を付けて
おくと、梯子を何段でも回せる。 -/

/-- 根が高さ 0 で、他の列は高さ 1 以上。 -/
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

`Deep` が見るのは行 0 だけなので、継ぎ足す列が全部高さ 1 以上なら保たれる。 -/

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
間の列は全部高さ 2 なので最小性を邪魔しない。 -/

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
と言っている。だから次の性質が閉じれば、梯子は高さに関係なく全部回る。

    Iterable P := ∀ q < |P|, ∀ n, P.take q ++ (P.drop q)^n ∈ W 0

`Deep`（根が高さ 0・他は高さ 1 以上）は、これの**高さ 1 に特化した弱い版**である。
高さ 1 でだけ `Deep` で足りたのは、継ぎ足す塊の親が必ず根で、`take 0 = []` に
なってコピー族が `W_flatMap_copies` で無料になるから。高さ 2 以上では
`take q ≠ []` になり、`PrefixCopiesOpen` の開いている場合に入る。

計測（`tools/probe_iterable.py`、上界は `r49.Wup` で False が健全）:
梯子が生成する形 `X ++ (1,0,0)^a1 (2,0,0)^a2 … (d,0,0)^ad`（d ≤ 4, a ≤ 3）で
**判定 3219 件・反例 0**。 -/

/-- どの接尾辞も繰り返せる。`snoc_flat` の仮定をまとめたもの。 -/
def Iterable (P : TrioSeq) : Prop :=
  ∀ q, q < P.length → ∀ n,
    P.take q ++ (List.range n).flatMap (fun _ => P.drop q) ∈ W 0

/-! ### なぜ高さ 1 で止まるか（再帰を追った結果）

`snoc_flat` で末尾 1 列を剥がすと、親の位置 `j0` で

    P ++ Q^n  ⟶  (P ++ Q^(n-1) ++ Q[:r]) ++ (Q[r : |Q|-1])^m

となる。**高さ 1 の梯子**では `Q = App k = (1,0,0)(2,0,0)^k` で、親は必ず `Q` の
先頭の `(1,0,0)`（`r = 0`）なので

    P ++ (App k)^n  ⟶  P ++ (App (k-1))^m

と **`k` が 1 つ減る**。底の `App 0 = [(1,0,0)]` では親が根に落ちて `take 0 = []` に
なり、`W_flatMap_copies` で無料。だから `app_iter` は回る。

**高さ 2 では底が変わる**。`AppAt2 k = (2,0,0)(3,0,0)^k` の底 `[(2,0,0)]` を継ぐと、
親は根ではなく `(1,0,0)` になり

    (X ++ (1,0,0) ++ S) ++ (2,0,0)^m
      ⟶  X ++ [(1,0,0) ++ S ++ (2,0,0)^(m-1)]^i

で、ブロックが **`S` を巻き込んで伸びる**。`S` は再帰のたびに育つので、
ブロックの長さでも高さでも整礎な測度が取れない。

⟹ **高さ 1 が特別だったのは「親が根に落ちて `take` が空になる」からで、
高さ 2 以上ではそこが閉じない。** 止まる理由は順序数の減少しかなく、それは `W`
そのもの。つまりここが `PrefixCopiesOpen` が開いている理由の、梯子から見た姿である。

計測（両側とも健全、`tools/probe_pcdeep.py`）:

    P in W 0, Deep P, Q の根が高さ 1, Q の全列が高さ 1 以上  ==>  P ++ Q^n in W 0
    判定 12870 件 / 反例 0

`Mm` / `Rep` / `app_iter` は全部この特殊ケースで、梯子の 4 段目以降は
一般形を要求する。 -/

/-! ## bump: 接頭辞を不問にする

`B` の末尾列が `B` の中に親を持つなら、`A ++ bump B` のバッドルートも `bump B` の
中で止まるので、**`A` が何であってもよい**（`bump B` = 行 0 に一律 +1）。

`Column.oper_append_right` はこれを `entry T 0 0 = 0` で実現しているが、`bump B` の
根は高さ 1 なので使えない。`Wset.nextR_src_ge`（アンカー仮定なしで「接頭辞は親を
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

`B` が平坦（行 1・行 2 が 0）で根が高さ 0 なら、`A ++ bump B` の**バッドルートは
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
      · -- 末尾列は非零。根が高さ 0 なので `B` の中に親がある。
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

`Chain k = (0,0,0)(1,0,0)…(k,0,0)` は平坦で根が高さ 0。`bump` すると
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

`Flat`（行 1 も 0）は「行 2 ≡ 0 ＋ **高さ 0 の列は `(0,0,0)` に限る**」まで緩められ
る。同じ帰納法が回る理由は「末尾列が非零なら必ず `B` の中に親がある」で、これは

* 高さ 0 の列は `(0,0,0)`（だから末尾が非零なら高さ >= 1）
* 高さ >= 1 の列は行 0 の親を持ち、高さが厳密に減るので根まで辿れる
* 辿り着いた高さ 0 の列は行 1 が 0 なので、行 1 の親としても使える

から出る。行 2 ≡ 0 なので `srow <= 1`、すなわち `d1 = 0`（行 1 は持ち上がらない）。
順序数では `o(A) * o(B)` で、`o(B)` は 2 行 BMS の全域を走る。 -/

/-- 行 2 が恒等的に 0（＝埋め込まれた 2 行 BMS）。 -/
def Z2 (B : TrioSeq) : Prop := ∀ c ∈ B, c.2.2 = 0

/-- 高さ 0 の列は `(0,0,0)` に限る。 -/
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

/-- 行 0 の祖先を辿ると必ず高さ 0 の列に着く（根が高さ 0 だから途中で止まらない）。 -/
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
      · -- 高さ 0 の末尾列は Zroot より `(0,0,0)`。展開は `dropLast`。
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

/-- 行 2 ≡ 0 ＋ Zroot ＋ 根が高さ 0 なら、`B ∈ W 0` は無条件。 -/
theorem Zroot_mem_W {B : TrioSeq} (hz2 : Z2 B) (hzr : Zroot B)
    (hroot : entry B 0 0 = 0) : B ∈ W 0 := by
  refine (mem_Wself_iff 0 B).mpr ⟨zeroRow2_mem_Wself hz2, ?_⟩
  obtain ⟨e1, e2⟩ := Zroot_entry hzr hroot
  simp [lev, e1, e2]

/-- **仮定は `B` の形だけ**: 行 2 ≡ 0・Zroot・根が高さ 0。 -/
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

`Zroot` は行 2 があっても展開で保たれる（高さ 0 の写しは `k = 0` の分だけで、
それは元の列そのもの）。`Mono` も保たれる（行 1 しか持ち上がらない）。
ただし `B ∈ W 0` はここでは**本当の仮定**（行 2 があると `zeroRow2_mem_Wself`
が使えない）。それでも「`W 0` の元を 1 段高くして継げる」という閉包規則として
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
/-- **高さ 0 の写しには行 1 の持ち上げが乗らない。** `Zroot` が展開で保たれる理由。 -/
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

/-! ## 一般化: 高さ 1 の列は行 1 が何でも継げる

`X(1,1,0)` の証明は `A = Q` に依っていない。`A ∈ W 0` が `Deep`・`Zroot`・`Mono`
なら、末尾に **`(1,e,0)`（高さ 1・行 2 は 0・行 1 は何でも）** を継げる。

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
高さ 1・行 2 が 0 の列を、行 1 の値に関係なく継げる。 -/
theorem snoc_row1 {A : TrioSeq} (hA : A ∈ W 0) (hAne : A ≠ []) (hAd : Deep A)
    (hAz : Zroot A) (hAm : Mono A) {e : ℕ} (he : 1 ≤ e) :
    A ++ [((1, e, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [snoc_row1_oper hAne hAd hAz he n]
  exact Tow_mem hA hAne hAd hAz hAm n

/-! ## 積・冪の梯子: `o(A)^2` から `o(A)^o(A)` まで

`bump_mem3` は **`B` に `Deep` を要求しない**（`B ∈ W 0` ＋ `Zroot` ＋ `Mono` ＋
根が高さ 0 だけ）。この差がちょうど効く: `A ++ A` は根が 2 つあるので `Deep`
ではないが `B` 側の条件は満たすので、そのまま `bump` できる。

    Aok A := A ∈ W 0 ∧ A ≠ [] ∧ Deep A ∧ Zroot A ∧ Mono A   （左に置ける）
    Bok B := B ∈ W 0 ∧ Zroot B ∧ Mono B ∧ 根が高さ 0        （bump できる）

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

/-- 平坦（行 1・行 2 が 0）で根が高さ 0 なら `Bok`。仮定は形だけ。 -/
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

高さ 1 の列 1 本と、その下に高さ 2 以上のブロックを吊るした形。目標は

    Aok A → B ∈ W 0（Zroot ∧ Mono ∧ 根 0）→ 1 <= e  ⟹  A ++ Blk e B ∈ W 0

`B` の `W 0` 帰納法。枝は 2 つ:

* `B` の末尾が非零 ⟹ 親が `B` の中にあるので
  `(A ++ Blk e B)⟦n⟧ = A ++ Blk e (B⟦n⟧)`（`A` は不問）。
* `B` の末尾が `(0,0,0)` ⟹ `Blk e B = Blk e (B.dropLast) ++ [(2,0,0)]`。
  この `(2,0,0)` の行 0 の親は `(1,e,0)`（間の列は全部高さ 2 以上）。`srow = 0` で
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

/-- 高さ 1 の列 1 本 ＋ 高さ 2 以上のブロック。 -/
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

/-- ★ **d=2 の bump**: `Aok A` の上に `(1,e,0)` ＋ 高さ 2 のブロックを吊るせる。 -/
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

/-! ## 高さ `d` の一般 bump（`BlkD`）

`Blk e B = (1,e,0) :: B⇑2` を二方向に一般化する。

* アンカーを**セグメント** `M` にする（先頭は高さ < d、残りは高さ ≥ d）。
* シフト量を `2` から一般の `d` にする。

    BlkD d M B = M ++ B⇑d

`(d,0,0)` を継ぐときの行 0 の親は「高さ < d の最後の列」＝ `M` の先頭なので、
`Blk` の議論はそのまま通る。底は `A ++ M ∈ W 0`。

さらに `A` 側に**不変量 `P`** を運ぶ。`P` は「`A` の上に高さ `d` のブロックを
吊るせる」という情報を持てるので、高さの梯子（`d → d+1`）が登れる。`P` の
閉包条件には**その段の帰納法の仮定そのもの**を渡す（`hclose` の第 4 引数）。 -/

theorem shiftD_col {d : ℕ} {C : TrioSeq} : ∀ c ∈ shiftr01 d 0 C, d ≤ c.1 := by
  intro c hc
  simp only [shiftr01, List.mem_map] at hc
  obtain ⟨p, -, rfl⟩ := hc
  omega

theorem shiftD_mono {d : ℕ} {C : TrioSeq} (h : Mono C) : Mono (shiftr01 d 0 C) := by
  intro c hc
  simp only [shiftr01, List.mem_map] at hc
  obtain ⟨p, hp, rfl⟩ := hc
  have := h p hp
  dsimp only
  omega

/-- 根以外の**高さ < d** の列は行 1 が 1 以上。 -/
def Shd (d : ℕ) (Y : TrioSeq) : Prop :=
  ∀ j, 0 < j → j < Y.length → entry Y 0 j < d → 1 ≤ entry Y 1 j

/-- 中間セグメント用（根も含める）。 -/
def ShdM (d : ℕ) (M : TrioSeq) : Prop :=
  ∀ j, j < M.length → entry M 0 j < d → 1 ≤ entry M 1 j

/-- 高さ `d` 用の中間セグメント: 先頭が高さ < d・行 1 が 1 以上、残りは高さ ≥ d。 -/
structure MidD (d : ℕ) (M : TrioSeq) : Prop where
  ne : M ≠ []
  col : ∀ c ∈ M, 1 ≤ c.1
  head : entry M 0 0 + 1 = d
  head1 : 1 ≤ entry M 1 0
  tail : ∀ j, 1 ≤ j → j < M.length → d ≤ entry M 0 j
  mono : Mono M

theorem MidD.shdM {d : ℕ} {M : TrioSeq} (hM : MidD d M) : ShdM d M := by
  intro j hj hlt
  rcases Nat.eq_zero_or_pos j with rfl | h
  · exact hM.head1
  · have := hM.tail j h hj; omega

/-- `M` ＋ 高さ `d` 以上のブロック。 -/
def BlkD (d : ℕ) (M B : TrioSeq) : TrioSeq := M ++ shiftr01 d 0 B

theorem BlkD_col {d : ℕ} (hd : 1 ≤ d) {M B : TrioSeq} (hM : ∀ c ∈ M, 1 ≤ c.1) :
    ∀ c ∈ BlkD d M B, 1 ≤ c.1 := by
  intro c hc
  rcases List.mem_append.mp hc with hm | hm
  · exact hM c hm
  · have := shiftD_col c hm; omega

theorem BlkD_mono {d : ℕ} {M B : TrioSeq} (hM : Mono M) (hB : Mono B) :
    Mono (BlkD d M B) := by
  intro c hc
  rcases List.mem_append.mp hc with hm | hm
  · exact hM c hm
  · exact shiftD_mono hB c hm

theorem BlkD_nil (d : ℕ) (M : TrioSeq) : BlkD d M [] = M := by simp [BlkD, shiftr01]

theorem BlkD_snoc (d : ℕ) (M B : TrioSeq) :
    BlkD d M (B ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])
      = BlkD d M B ++ [((d, 0, 0) : ℕ × ℕ × ℕ)] := by
  simp [BlkD, shiftr01]

theorem BlkD_app (d : ℕ) (A M B : TrioSeq) :
    A ++ BlkD d M B = (A ++ M) ++ shiftr01 d 0 B := by
  simp [BlkD]

theorem BlkD_len (d : ℕ) (M B : TrioSeq) :
    (BlkD d M B).length = M.length + B.length := by
  simp [BlkD, shiftr01]

theorem Aok_append_BlkD {d : ℕ} (hd : 1 ≤ d) {A M B : TrioSeq}
    (hmem : A ++ BlkD d M B ∈ W 0) (hA : Aok A) (hM : MidD d M) (hmo : Mono B) :
    Aok (A ++ BlkD d M B) := by
  refine ⟨hmem, by simp [List.append_eq_nil_iff, hA.ne],
    Deep_append hA.deep hA.ne (fun c hc => BlkD_col hd hM.col c hc), ?_, ?_⟩
  · intro c hc h0
    rcases List.mem_append.mp hc with hm | hm
    · exact hA.zroot c hm h0
    · have := BlkD_col hd hM.col c hm; omega
  · intro c hc
    rcases List.mem_append.mp hc with hm | hm
    · exact hA.mono c hm
    · exact BlkD_mono hM.mono hmo c hm

/-- `Shd d` は `BlkD d` の継ぎ足しで保たれる。 -/
theorem Shd_append_BlkD {d : ℕ} {A M B : TrioSeq} (hne : A ≠ []) (hA : Shd d A)
    (hMs : ShdM d M) : Shd d (A ++ BlkD d M B) := by
  intro j hj0 hjl hsh
  have hAlen : 0 < A.length := List.length_pos_iff.mpr hne
  rcases Nat.lt_or_ge j A.length with h | h
  · rw [entry_append_left h] at hsh ⊢
    exact hA j hj0 h hsh
  · obtain ⟨t, rfl⟩ : ∃ t, j = A.length + t := ⟨j - A.length, by omega⟩
    rw [entry_append_right] at hsh ⊢
    have htl : t < M.length + B.length := by
      simp only [List.length_append, BlkD_len] at hjl; omega
    rcases Nat.lt_or_ge t M.length with h2 | h2
    · rw [BlkD, entry_append_left h2] at hsh ⊢
      exact hMs t h2 hsh
    · exfalso
      obtain ⟨s, rfl⟩ : ∃ s, t = M.length + s := ⟨t - M.length, by omega⟩
      have hm : (shiftr01 d 0 B).getD s ((0, 0, 0) : ℕ × ℕ × ℕ) ∈ shiftr01 d 0 B :=
        getD_mem_of_lt (by rw [shiftr01_length]; omega)
      have h3 := shiftD_col _ hm
      rw [BlkD, entry_append_right, entry0_eq] at hsh
      omega

theorem BlkD_entry_zero {d : ℕ} {M C : TrioSeq} (hM : MidD d M) :
    entry (BlkD d M C) 0 0 = entry M 0 0 := by
  have hlen : 0 < M.length := List.length_pos_iff.mpr hM.ne
  rw [BlkD, entry_append_left hlen]

theorem BlkD_entry_pos {d : ℕ} {M C : TrioSeq} (hM : MidD d M) (s : ℕ) (hs1 : 1 ≤ s)
    (hs : s < M.length + C.length) : d ≤ entry (BlkD d M C) 0 s := by
  rcases Nat.lt_or_ge s M.length with h | h
  · rw [BlkD, entry_append_left h]
    exact hM.tail s hs1 h
  · obtain ⟨t, rfl⟩ : ∃ t, s = M.length + t := ⟨s - M.length, by omega⟩
    have hm : (shiftr01 d 0 C).getD t ((0, 0, 0) : ℕ × ℕ × ℕ) ∈ shiftr01 d 0 C :=
      getD_mem_of_lt (by rw [shiftr01_length]; omega)
    show d ≤ entry (M ++ shiftr01 d 0 C) 0 (M.length + t)
    rw [entry_append_right, entry0_eq]
    exact shiftD_col _ hm

theorem Yseq_Aok_D {d : ℕ} (hd : 1 ≤ d) {A M C : TrioSeq} (hA : Aok A) (hM : MidD d M)
    (hmoC : Mono C) {P : TrioSeq → Prop} (hP : P A)
    (hclose : ∀ A' C' : TrioSeq, Aok A' → P A' → Mono C' →
        (∀ A'' : TrioSeq, Aok A'' → P A'' → A'' ++ BlkD d M C' ∈ W 0) →
        P (A' ++ BlkD d M C'))
    (hIH : ∀ A' : TrioSeq, Aok A' → P A' → A' ++ BlkD d M C ∈ W 0) :
    ∀ n, Aok (Yseq A (BlkD d M C) n) ∧ P (Yseq A (BlkD d M C) n) := by
  intro n
  induction n with
  | zero => exact ⟨hA, hP⟩
  | succ n ih =>
      refine ⟨?_, ?_⟩
      · show Aok (Yseq A (BlkD d M C) n ++ BlkD d M C)
        exact Aok_append_BlkD hd (hIH _ ih.1 ih.2) ih.1 hM hmoC
      · show P (Yseq A (BlkD d M C) n ++ BlkD d M C)
        exact hclose _ C ih.1 ih.2 hmoC hIH

/-- **(S2'')**: コピー族が済めば `(d,0,0)` を継げる。 -/
theorem blkD_snoc_two {d : ℕ} (hd : 1 ≤ d) {C A M : TrioSeq} (hM : MidD d M)
    (hmoC : Mono C) (hA : Aok A) {P : TrioSeq → Prop} (hP : P A)
    (hclose : ∀ A' C' : TrioSeq, Aok A' → P A' → Mono C' →
        (∀ A'' : TrioSeq, Aok A'' → P A'' → A'' ++ BlkD d M C' ∈ W 0) →
        P (A' ++ BlkD d M C'))
    (hIH : ∀ A' : TrioSeq, Aok A' → P A' → A' ++ BlkD d M C ∈ W 0) :
    (A ++ BlkD d M C) ++ [((d, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hAlen : 0 < A.length := List.length_pos_iff.mpr hA.ne
  have hMlen : 0 < M.length := List.length_pos_iff.mpr hM.ne
  set P0 : TrioSeq := A ++ BlkD d M C with hP0
  have hPlen : P0.length = A.length + (M.length + C.length) := by
    rw [hP0]; simp [BlkD_len]
  have hPne : P0 ≠ [] := by rw [hP0]; simp [List.append_eq_nil_iff, hA.ne]
  have hcolA : entry P0 0 A.length = entry M 0 0 := by
    rw [hP0, show A.length = A.length + 0 from rfl, entry_append_right]
    exact BlkD_entry_zero hM
  have hcolmid : ∀ j, A.length < j → j < P0.length → d ≤ entry P0 0 j := by
    intro j h1 h2
    obtain ⟨s, rfl⟩ : ∃ s, j = A.length + (s + 1) := ⟨j - A.length - 1, by omega⟩
    rw [hP0, entry_append_right]
    exact BlkD_entry_pos hM (s + 1) (by omega) (by omega)
  have hlast2 : entry (P0 ++ [((d, 0, 0) : ℕ × ℕ × ℕ)]) 0 P0.length = d :=
    entry_append_last.1
  have hhd : entry M 0 0 < d := by have := hM.head; omega
  have hpar : hasParent (P0 ++ [((d, 0, 0) : ℕ × ℕ × ℕ)]) 0 P0.length := by
    rw [hasParent_zero_iff (by simp)]
    refine ⟨A.length, by omega, ?_⟩
    rw [entry_append_lt (show A.length < P0.length by omega), hcolA, hlast2]
    omega
  have hj0 : parent (P0 ++ [((d, 0, 0) : ℕ × ℕ × ℕ)]) 0 P0.length = A.length := by
    have h := parent_nextR hpar
    rw [nextR, if_pos rfl] at h
    obtain ⟨-, -, hlt, hval, hmin⟩ := h
    by_contra hne0
    rcases Nat.lt_or_ge (parent (P0 ++ [((d, 0, 0) : ℕ × ℕ × ℕ)]) 0 P0.length) A.length
      with hc | hc
    · have hmm := hmin A.length ⟨hc, by omega⟩
      rw [entry_append_lt (show A.length < P0.length by omega), hcolA, hlast2] at hmm
      omega
    · have hgt : A.length < parent (P0 ++ [((d, 0, 0) : ℕ × ℕ × ℕ)]) 0 P0.length :=
        lt_of_le_of_ne hc (Ne.symm hne0)
      have hmm := hcolmid _ hgt (by omega)
      rw [entry_append_lt (show parent (P0 ++ [((d, 0, 0) : ℕ × ℕ × ℕ)]) 0 P0.length
        < P0.length by omega), hlast2] at hval
      omega
  refine snoc_flat (A := P0) (b := ((d, 0, 0) : ℕ × ℕ × ℕ)) (j0 := A.length) hPne
    (by simp; omega) rfl rfl hpar hj0 ?_
  intro n
  have h1 : P0.take A.length = A := by rw [hP0, List.take_left]
  have h2 : P0.drop A.length = BlkD d M C := by rw [hP0, List.drop_left]
  rw [h1, h2, ← Yseq_eq]
  exact (Yseq_Aok_D hd hA hM hmoC hP hclose hIH n).1.mem

/-- ★★ **高さ `d` の一般 bump**。`P` は `A` 側の不変量。 -/
theorem blkD_mem {d : ℕ} (hd : 1 ≤ d) (M : TrioSeq) (hM : MidD d M)
    {P : TrioSeq → Prop}
    (hbase : ∀ A : TrioSeq, Aok A → P A → A ++ M ∈ W 0)
    (hclose : ∀ A' C' : TrioSeq, Aok A' → P A' → Mono C' →
        (∀ A'' : TrioSeq, Aok A'' → P A'' → A'' ++ BlkD d M C' ∈ W 0) →
        P (A' ++ BlkD d M C')) :
    ∀ B ∈ W 0, Zroot B → Mono B → entry B 0 0 = 0 →
      ∀ A : TrioSeq, Aok A → P A → A ++ BlkD d M B ∈ W 0 := by
  have key : W 0 ⊆ {B : TrioSeq | Zroot B → Mono B → entry B 0 0 = 0 →
      ∀ A : TrioSeq, Aok A → P A → A ++ BlkD d M B ∈ W 0} := by
    refine A2' ?_
    intro B hB
    simp only [Set.mem_setOf_eq]
    intro hzr hmo hroot A hA hPA
    by_cases hshort : B.length ≤ 1
    · rcases (by omega : B.length = 0 ∨ B.length = 1) with h0 | h1
      · have hnil : B = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        rw [BlkD_nil]
        exact hbase A hA hPA
      · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
        have hc0 : c.1 = 0 := hroot
        obtain ⟨hc1, hc2⟩ := hzr c (by simp) hc0
        have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1 hc2)
        subst hcz
        have heq : A ++ BlkD d M [((0, 0, 0) : ℕ × ℕ × ℕ)]
            = (A ++ BlkD d M []) ++ [((d, 0, 0) : ℕ × ℕ × ℕ)] := by
          simp [BlkD, shiftr01]
        rw [heq]
        refine blkD_snoc_two hd hM (by intro c hc; simp at hc) hA hPA hclose ?_
        intro A' hA' hP'
        rw [BlkD_nil]
        exact hbase A' hA' hP'
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
        have hIH : ∀ A' : TrioSeq, Aok A' → P A' → A' ++ BlkD d M B.dropLast ∈ W 0 :=
          fun A' hA' hP' => hdl (fun c hc => hzr c (List.dropLast_subset _ hc))
            (fun c hc => hmo c (List.dropLast_subset _ hc)) hdl0 A' hA' hP'
        have hgoal := blkD_snoc_two (C := B.dropLast) hd hM
          (fun c hc => hmo c (List.dropLast_subset _ hc)) hA hPA hclose hIH
        have heq : A ++ BlkD d M B
            = (A ++ BlkD d M B.dropLast) ++ [((d, 0, 0) : ℕ × ℕ × ℕ)] := by
          conv_lhs => rw [hsplit]
          rw [BlkD_snoc, List.append_assoc]
        rw [heq]
        exact hgoal
      · have hnz : ¬ (entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
            entry B 2 (B.length - 1) = 0) := fun h => hlast h.1
        have hp := hasParent_of_ZrootMono hzr hmo hroot hlen2 hnz
        refine A1_intro (Or.inr (Or.inl ?_))
        intro n hn
        rw [BlkD_app, oper_shift _ _ d n hlen2 hp, ← BlkD_app]
        obtain ⟨hzr', hmo'⟩ := ZM_oper hzr hmo n
        exact hnat n hn hzr' hmo' (by rw [Wset.oper_head_eq hn]; exact hroot) A hA hPA
    · exact absurd hm (Nat.not_lt_zero m)
  intro B hB
  exact key hB

/-! ## 高さ `d` の塔と `(d,1,0)` の継ぎ足し -/

/-- `Y` の高さ `d` の塔。 -/
def TwD (d : ℕ) (Y : TrioSeq) (n : ℕ) : TrioSeq :=
  (List.range n).flatMap fun k => shiftr01 (d * k) 0 Y

theorem TwD_succ (d : ℕ) (Y : TrioSeq) (n : ℕ) :
    TwD d Y (n + 1) = Y ++ shiftr01 d 0 (TwD d Y n) := by
  show (List.range (n + 1)).flatMap _ = _
  rw [List.range_succ_eq_map, List.flatMap_cons]
  have h0 : shiftr01 (d * 0) 0 Y = Y := by simp [shiftr01]
  rw [h0, TwD, shift_flatMap0, List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro x _
  rw [shiftr01_add0, Nat.mul_succ]

theorem TwD_mono {d : ℕ} {Y : TrioSeq} (h : Mono Y) : ∀ n, Mono (TwD d Y n)
  | 0 => by intro c hc; simp [TwD] at hc
  | (n + 1) => by
      rw [TwD_succ]
      intro c hc
      rcases List.mem_append.mp hc with hm | hm
      · exact h c hm
      · exact shiftD_mono (TwD_mono h n) c hm

theorem TwD_zroot {d : ℕ} (hd : 1 ≤ d) {Y : TrioSeq} (h : Zroot Y) :
    ∀ n, Zroot (TwD d Y n)
  | 0 => by intro c hc; simp [TwD] at hc
  | (n + 1) => by
      rw [TwD_succ]
      intro c hc h0
      rcases List.mem_append.mp hc with hm | hm
      · exact h c hm h0
      · have := shiftD_col c hm; omega

theorem TwD_root {d : ℕ} {Y : TrioSeq} (hne : Y ≠ []) (h : entry Y 0 0 = 0) :
    ∀ n, entry (TwD d Y n) 0 0 = 0
  | 0 => by simp [TwD, entry]
  | (n + 1) => by
      rw [TwD_succ, entry_append_left (List.length_pos_iff.mpr hne)]
      exact h

/-- 「右から見た狭義最小記録」の列にだけ行 1 の下界を課す（`Shd` の弱化）。
最後の列に高さ `d` の列を継いだときの `le0` 祖先は、ちょうどこの形。 -/
def Ancd (d : ℕ) (Y : TrioSeq) : Prop :=
  ∀ j, 0 < j → j < Y.length → entry Y 0 j < d →
    (∀ i, j < i → i < Y.length → entry Y 0 j < entry Y 0 i) → 1 ≤ entry Y 1 j

theorem Shd_Ancd {d : ℕ} {Y : TrioSeq} (h : Shd d Y) : Ancd d Y :=
  fun j hj0 hjl hlt _ => h j hj0 hjl hlt

/-- ★ 行 0 の祖先 `a` は、`a` と `b` の間の全ての列より真に低い。 -/
theorem rtg0_rec {M : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 M) a b) :
    ∀ i, a < i → i ≤ b → entry M 0 a < entry M 0 i := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro i h1 h2; omega
  | head hac _ ih =>
      rename_i a c _
      intro i h1 h2
      rcases Nat.lt_trichotomy i c with hi | hi | hi
      · have hm := hac.2.2.2.2 i ⟨h1, hi⟩
        have hv := hac.2.2.2.1
        omega
      · subst hi; exact hac.2.2.2.1
      · have hv := hac.2.2.2.1
        have := ih i hi h2
        omega

/-- 行 0 の祖先関係は行 0 の値について単調。 -/
theorem rtg0_entry_le {M : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 M) a b) : entry M 0 a ≤ entry M 0 b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact le_trans ih (le_of_lt hstep.2.2.2.1)

open Classical in
/-- ★ `(d,1,0)` を継いだときの展開は `Y` の高さ `d` の塔。 -/
theorem oper_snocd {Y : TrioSeq} {d : ℕ} (hd : 1 ≤ d) (hne : Y ≠ []) (hdp : Deep Y)
    (hz : Zroot Y) (hsh : Ancd d Y) (n : ℕ) :
    (Y ++ [((d, 1, 0) : ℕ × ℕ × ℕ)])⟦n⟧ = TwD d Y n := by
  have hplen : 0 < Y.length := List.length_pos_iff.mpr hne
  have hlast := entry_append_last (P := Y) (c := ((d, 1, 0) : ℕ × ℕ × ℕ))
  have hpre : ∀ i j, j < Y.length →
      entry (Y ++ [((d, 1, 0) : ℕ × ℕ × ℕ)]) i j = entry Y i j :=
    fun i j hj => entry_append_lt hj
  have hMdeep : Deep (Y ++ [((d, 1, 0) : ℕ × ℕ × ℕ)]) := Deep_snoc hdp hne (by exact hd)
  set M : TrioSeq := Y ++ [((d, 1, 0) : ℕ × ℕ × ℕ)] with hM
  have hMlen : M.length = Y.length + 1 := by rw [hM]; simp
  have hl0 : entry M 0 Y.length = d := hlast.1
  have hl1 : entry M 1 Y.length = 1 := hlast.2.1
  have hl2 : entry M 2 Y.length = 0 := hlast.2.2
  have hsh0 : ∀ x, 0 < x → x < M.length → entry M 0 0 < entry M 0 x := by
    intro x hx0 hxl
    rw [hMdeep.1]
    exact hMdeep.2 x hx0 hxl
  have hle0 : ∀ j, j < M.length → le0 M 0 j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact ⟨by omega, by omega, Relation.ReflTransGen.refl⟩
    · exact H12Export.le0_root_of_shallow (by omega) hsh0 j hj0 hj
  have hroot1 : entry M 1 0 = 0 := by
    rw [hpre 1 0 hplen]
    exact (Zroot_entry hz hdp.1).1
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
    · have hrec := rtg0_rec hjle.2.2
      rw [hpre 1 j h]
      refine hsh j hj0 h ?_ ?_
      · have h1 := hrec Y.length (by omega) le_rfl
        rw [hl0, hpre 0 j h] at h1
        exact h1
      · intro i hi1 hi2
        have h1 := hrec i hi1 (by omega)
        rw [hpre 0 j h, hpre 0 i hi2] at h1
        exact h1
    · have hjeq : j = Y.length := by
        have := H12Export.rtg0_index_le hjle.2.2
        omega
      rw [hjeq, hl1]
  have hj0 : parent M 1 Y.length = 0 := hpar.unique (parent_nextR hpar) hnr1
  rw [L53.oper_unfold (j1 := Y.length) (i1 := 1) (j0 := 0) (d0 := d) (d1 := 0)
      (by omega) (by omega) (by rintro ⟨h, -, -⟩; rw [hl0] at h; omega)
      hsrow.symm hpar hj0.symm (by rw [if_pos (by omega), hl0, hMdeep.1]; omega) (by simp) n,
    TwD]
  simp only [List.take_zero, List.nil_append, Nat.sub_zero, Nat.mul_zero, ite_self,
    Nat.add_zero]
  apply List.flatMap_congr
  intro k _
  rw [← map_range'_shift Y (d * k)]
  apply List.map_congr_left
  intro j hj
  have hjl : j < Y.length := by have := List.mem_range'_1.1 hj; omega
  rw [if_pos (hle0 j (by omega)), hpre 0 j hjl, hpre 1 j hjl, hpre 2 j hjl,
    Nat.mul_comm k d]

/-- ★ 塔が済めば `(d,1,0)` を継げる。 -/
theorem snocd_mem {Y : TrioSeq} {d : ℕ} (hd : 1 ≤ d) (hne : Y ≠ []) (hdp : Deep Y)
    (hz : Zroot Y) (hsh : Ancd d Y) (htw : ∀ n, TwD d Y n ∈ W 0) :
    Y ++ [((d, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_snocd hd hne hdp hz hsh n]
  exact htw n

#print axioms blkD_mem
#print axioms oper_snocd

/-! ## `P = Shd d` の場合（不変量に何も足さない）

`Shd d` はそれ自身 `BlkD d` で閉じているので、`hclose` は追加の帰納法の仮定を
使わない。 -/

theorem hclose_Shd {d : ℕ} {M : TrioSeq} (hM : MidD d M) :
    ∀ A' C' : TrioSeq, Aok A' → Shd d A' → Mono C' →
      (∀ A'' : TrioSeq, Aok A'' → Shd d A'' → A'' ++ BlkD d M C' ∈ W 0) →
      Shd d (A' ++ BlkD d M C') :=
  fun A' _ hA' hs' _ _ => Shd_append_BlkD hA'.ne hs' hM.shdM

theorem Aok_append_Mid {d : ℕ} (hd : 1 ≤ d) {A M : TrioSeq} (hA : Aok A)
    (hM : MidD d M) (hmem : A ++ M ∈ W 0) : Aok (A ++ M) := by
  have h := Aok_append_BlkD (d := d) (B := []) hd (by rw [BlkD_nil]; exact hmem) hA hM
    (by intro c hc; simp at hc)
  rw [BlkD_nil] at h
  exact h

theorem Shd_append_Mid {d : ℕ} {A M : TrioSeq} (hne : A ≠ []) (hsA : Shd d A)
    (hM : MidD d M) : Shd d (A ++ M) := by
  have h := Shd_append_BlkD (d := d) (B := []) hne hsA hM.shdM
  rw [BlkD_nil] at h
  exact h

/-! ### 中間セグメント `Mseq m = (1,1,0)(2,1,0)^m` と シート行289 -/

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

theorem Mseq_entry {m t : ℕ} (h : t < m) : entry (Mseq m) 0 (t + 1) = 2 := by
  have hg : (Mseq m).getD (t + 1) ((0, 0, 0) : ℕ × ℕ × ℕ)
      = (Rep21 m).getD t ((0, 0, 0) : ℕ × ℕ × ℕ) := rfl
  have h2 : (Rep21 m).getD t ((0, 0, 0) : ℕ × ℕ × ℕ) = ((2, 1, 0) : ℕ × ℕ × ℕ) :=
    Rep21_mem (getD_mem_of_lt (by rw [Rep21_len]; exact h))
  show ((Mseq m).getD (t + 1) ((0, 0, 0) : ℕ × ℕ × ℕ)).1 = 2
  rw [hg, h2]

theorem MidD_Mseq (m : ℕ) : MidD 2 (Mseq m) := by
  refine ⟨by simp [Mseq], fun c hc => (Mseq_mem_col hc).1, ?_, le_refl 1, ?_, ?_⟩
  · have h0 : entry (Mseq m) 0 0 = 1 := rfl
    omega
  · intro j h1 h2
    obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
    rw [Mseq_len] at h2
    exact le_of_eq (Mseq_entry (by omega)).symm
  · intro c hc
    exact (Mseq_mem_col hc).2

/-- `Tw` の各段（`m` の段の帰納法の仮定 `hbase` を使う）。 -/
theorem tw_mseq_mem (m : ℕ)
    (hbase : ∀ A : TrioSeq, Aok A → Shd 2 A → A ++ Mseq m ∈ W 0)
    {A : TrioSeq} (hA : Aok A) (hsA : Shd 2 A) :
    ∀ n, TwD 2 (A ++ Mseq m) n ∈ W 0
  | 0 => by simpa [TwD] using W_nil 0
  | (n + 1) => by
      have hY : Aok (A ++ Mseq m) :=
        Aok_append_Mid (by omega) hA (MidD_Mseq m) (hbase A hA hsA)
      have heq : TwD 2 (A ++ Mseq m) (n + 1)
          = A ++ BlkD 2 (Mseq m) (TwD 2 (A ++ Mseq m) n) := by
        rw [TwD_succ, BlkD, List.append_assoc]
      rw [heq]
      exact blkD_mem (by omega) (Mseq m) (MidD_Mseq m) hbase
        (hclose_Shd (MidD_Mseq m)) _ (tw_mseq_mem m hbase hA hsA n)
        (TwD_zroot (by omega) hY.zroot n) (TwD_mono hY.mono n)
        (TwD_root hY.ne hY.deep.1 n) A hA hsA

/-- ★★ `A ++ (1,1,0)(2,1,0)^m ∈ W 0`。 -/
theorem mseq_mem : ∀ m : ℕ, ∀ A : TrioSeq, Aok A → Shd 2 A → A ++ Mseq m ∈ W 0
  | 0 => by
      intro A hA _
      rw [Mseq_zero]
      exact snoc_row1 hA.mem hA.ne hA.deep hA.zroot hA.mono (le_refl 1)
  | (m + 1) => by
      intro A hA hsA
      have hY : Aok (A ++ Mseq m) :=
        Aok_append_Mid (by omega) hA (MidD_Mseq m) (mseq_mem m A hA hsA)
      have hsY : Shd 2 (A ++ Mseq m) := Shd_append_Mid hA.ne hsA (MidD_Mseq m)
      rw [Mseq_succ, ← List.append_assoc]
      exact snocd_mem (by omega) hY.ne hY.deep hY.zroot (Shd_Ancd hsY)
        (tw_mseq_mem m (mseq_mem m) hA hsA)

theorem Shd_Q (d : ℕ) (hd : 2 ≤ d) : Shd d Q := by
  intro j hj0 hjl _
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
  exact mseq_mem n Q Aok_Q (Shd_Q 2 (by omega))

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

#print axioms mseq_mem
#print axioms R289_mem

/-! ## 高さの梯子 `Lv r a`（ランク付き・シフト付き）

`Lv r a A` ＝「`A` は高さ `r` 以下の梯子を持ち、高さ `a+1` のブロックを吊るせる」
（アンカーは高さ `a`）。

    Lv 0 a A       = Aok A ∧ a = 0
    Lv (r+1) 0 A   = Aok A                        アンカーは根（`bump`）
    Lv (r+1) (a+1) A = Aok A ∧ ∃ A0 M, A = A0 ++ M ∧ Lv r a A0 ∧ MidD (a+2) M
                       ∧ (∀ s A', Lv r (a+s) A' → A' ++ M↑s ∈ W 0)

最後が**シフト付きの再継ぎ性**。`M↑s` はアンカーが高さ `a+1+s` なので、`Lv r (a+s)`
な行列になら誰にでも継げる、という意味。

ランク `r` が要る理由: 再継ぎ性は `Lv` を**仮定の側**で、しかも `a+s ≥ a` の
段で参照する。段だけでは再帰が停止しないので、ランクを 1 つ下げて参照する。 -/

theorem entry1_eq {M : TrioSeq} {j : ℕ} :
    entry M 1 j = (M.getD j ((0, 0, 0) : ℕ × ℕ × ℕ)).2.1 := rfl

theorem entry_shift0 {s : ℕ} {M : TrioSeq} {j : ℕ} (hj : j < M.length) :
    entry (shiftr01 s 0 M) 0 j = entry M 0 j + s := by
  rw [entry0_eq, entry0_eq, shiftr01_getD hj]

theorem entry_shift1 {s : ℕ} {M : TrioSeq} {j : ℕ} (hj : j < M.length) :
    entry (shiftr01 s 0 M) 1 j = entry M 1 j := by
  rw [entry1_eq, entry1_eq, shiftr01_getD hj]
  simp

theorem MidD_col_ge {d : ℕ} {M : TrioSeq} (hM : MidD d M) : ∀ c ∈ M, d - 1 ≤ c.1 := by
  intro c hc
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
  have hg : entry M 0 j = M[j].1 := by
    rw [entry0_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  rcases Nat.eq_zero_or_pos j with rfl | h
  · have := hM.head; omega
  · have := hM.tail j h hj; omega

theorem MidD_append {d : ℕ} {M N : TrioSeq} (hM : MidD d M)
    (hN : ∀ c ∈ N, d ≤ c.1) (hNm : Mono N) : MidD d (M ++ N) := by
  have hMlen : 0 < M.length := List.length_pos_iff.mpr hM.ne
  refine ⟨by simp [List.append_eq_nil_iff, hM.ne], ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hM.col c h
    · have h1 := hN c h
      have h2 := hM.head
      omega
  · rw [entry_append_left hMlen]; exact hM.head
  · rw [entry_append_left hMlen]; exact hM.head1
  · intro j h1 h2
    rcases Nat.lt_or_ge j M.length with h | h
    · rw [entry_append_left h]; exact hM.tail j h1 h
    · obtain ⟨t, rfl⟩ : ∃ t, j = M.length + t := ⟨j - M.length, by omega⟩
      rw [entry_append_right, entry0_eq]
      refine hN _ (getD_mem_of_lt ?_)
      simp only [List.length_append] at h2; omega
  · intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hM.mono c h
    · exact hNm c h

theorem MidD_one (d : ℕ) (hd : 1 ≤ d) :
    MidD (d + 1) [((d, 1, 0) : ℕ × ℕ × ℕ)] := by
  refine ⟨by simp, ?_, rfl, le_refl 1, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact hd
  · intro j h1 h2
    simp only [List.length_singleton] at h2
    omega
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    dsimp only
    omega

theorem MidD_shift {d : ℕ} {M : TrioSeq} (hM : MidD d M) (s : ℕ) :
    MidD (d + s) (shiftr01 s 0 M) := by
  have hlen : 0 < M.length := List.length_pos_iff.mpr hM.ne
  have hlen' : (shiftr01 s 0 M).length = M.length := shiftr01_length s 0 M
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hc
    have h0 : (shiftr01 s 0 M).length = 0 := by rw [hc]; rfl
    rw [hlen'] at h0; omega
  · intro c hc
    simp only [shiftr01, List.mem_map] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    have := hM.col p hp
    dsimp only; omega
  · rw [entry_shift0 hlen]
    have := hM.head; omega
  · rw [entry_shift1 hlen]
    exact hM.head1
  · intro j h1 h2
    rw [hlen'] at h2
    rw [entry_shift0 h2]
    have := hM.tail j h1 h2; omega
  · intro c hc
    simp only [shiftr01, List.mem_map] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    have := hM.mono p hp
    dsimp only; omega

/-! ### シフト付きの `blkD_mem` -/

theorem Yseq_Aok_S {d : ℕ} (hd : 1 ≤ d) {A M C : TrioSeq} {s : ℕ} (hA : Aok A)
    (hM : MidD d M) (hmoC : Mono C) {P : ℕ → TrioSeq → Prop} (hP : P s A)
    (hclose : ∀ (s' : ℕ) (A' C' : TrioSeq), Aok A' → P s' A' → Mono C' →
        (∀ (t : ℕ) (A'' : TrioSeq), Aok A'' → P t A'' →
          A'' ++ BlkD (d + t) (shiftr01 t 0 M) C' ∈ W 0) →
        P s' (A' ++ BlkD (d + s') (shiftr01 s' 0 M) C'))
    (hIH : ∀ (t : ℕ) (A'' : TrioSeq), Aok A'' → P t A'' →
        A'' ++ BlkD (d + t) (shiftr01 t 0 M) C ∈ W 0) :
    ∀ n, Aok (Yseq A (BlkD (d + s) (shiftr01 s 0 M) C) n) ∧
      P s (Yseq A (BlkD (d + s) (shiftr01 s 0 M) C) n) := by
  intro n
  induction n with
  | zero => exact ⟨hA, hP⟩
  | succ n ih =>
      refine ⟨?_, ?_⟩
      · show Aok (Yseq A (BlkD (d + s) (shiftr01 s 0 M) C) n
          ++ BlkD (d + s) (shiftr01 s 0 M) C)
        exact Aok_append_BlkD (by omega) (hIH s _ ih.1 ih.2) ih.1 (MidD_shift hM s) hmoC
      · show P s (Yseq A (BlkD (d + s) (shiftr01 s 0 M) C) n
          ++ BlkD (d + s) (shiftr01 s 0 M) C)
        exact hclose s _ C ih.1 ih.2 hmoC hIH

theorem blkD_snoc_twoS {d : ℕ} (hd : 1 ≤ d) {C A M : TrioSeq} {s : ℕ}
    (hM : MidD d M) (hmoC : Mono C) (hA : Aok A) {P : ℕ → TrioSeq → Prop} (hP : P s A)
    (hclose : ∀ (s' : ℕ) (A' C' : TrioSeq), Aok A' → P s' A' → Mono C' →
        (∀ (t : ℕ) (A'' : TrioSeq), Aok A'' → P t A'' →
          A'' ++ BlkD (d + t) (shiftr01 t 0 M) C' ∈ W 0) →
        P s' (A' ++ BlkD (d + s') (shiftr01 s' 0 M) C'))
    (hIH : ∀ (t : ℕ) (A'' : TrioSeq), Aok A'' → P t A'' →
        A'' ++ BlkD (d + t) (shiftr01 t 0 M) C ∈ W 0) :
    (A ++ BlkD (d + s) (shiftr01 s 0 M) C) ++ [((d + s, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  set Ms : TrioSeq := shiftr01 s 0 M with hMs0
  have hMs : MidD (d + s) Ms := MidD_shift hM s
  have hAlen : 0 < A.length := List.length_pos_iff.mpr hA.ne
  have hMlen : 0 < Ms.length := List.length_pos_iff.mpr hMs.ne
  set P0 : TrioSeq := A ++ BlkD (d + s) Ms C with hP0
  have hPlen : P0.length = A.length + (Ms.length + C.length) := by
    rw [hP0]; simp [BlkD_len]
  have hPne : P0 ≠ [] := by rw [hP0]; simp [List.append_eq_nil_iff, hA.ne]
  have hcolA : entry P0 0 A.length = entry Ms 0 0 := by
    rw [hP0, show A.length = A.length + 0 from rfl, entry_append_right]
    exact BlkD_entry_zero hMs
  have hcolmid : ∀ j, A.length < j → j < P0.length → d + s ≤ entry P0 0 j := by
    intro j h1 h2
    obtain ⟨t, rfl⟩ : ∃ t, j = A.length + (t + 1) := ⟨j - A.length - 1, by omega⟩
    rw [hP0, entry_append_right]
    exact BlkD_entry_pos hMs (t + 1) (by omega) (by omega)
  have hlast2 : entry (P0 ++ [((d + s, 0, 0) : ℕ × ℕ × ℕ)]) 0 P0.length = d + s :=
    entry_append_last.1
  have hhd : entry Ms 0 0 < d + s := by have := hMs.head; omega
  have hpar : hasParent (P0 ++ [((d + s, 0, 0) : ℕ × ℕ × ℕ)]) 0 P0.length := by
    rw [hasParent_zero_iff (by simp)]
    refine ⟨A.length, by omega, ?_⟩
    rw [entry_append_lt (show A.length < P0.length by omega), hcolA, hlast2]
    omega
  have hj0 : parent (P0 ++ [((d + s, 0, 0) : ℕ × ℕ × ℕ)]) 0 P0.length = A.length := by
    have h := parent_nextR hpar
    rw [nextR, if_pos rfl] at h
    obtain ⟨-, -, hlt, hval, hmin⟩ := h
    by_contra hne0
    rcases Nat.lt_or_ge
        (parent (P0 ++ [((d + s, 0, 0) : ℕ × ℕ × ℕ)]) 0 P0.length) A.length with hc | hc
    · have hmm := hmin A.length ⟨hc, by omega⟩
      rw [entry_append_lt (show A.length < P0.length by omega), hcolA, hlast2] at hmm
      omega
    · have hgt : A.length
          < parent (P0 ++ [((d + s, 0, 0) : ℕ × ℕ × ℕ)]) 0 P0.length :=
        lt_of_le_of_ne hc (Ne.symm hne0)
      have hmm := hcolmid _ hgt (by omega)
      rw [entry_append_lt (show parent (P0 ++ [((d + s, 0, 0) : ℕ × ℕ × ℕ)]) 0 P0.length
        < P0.length by omega), hlast2] at hval
      omega
  refine snoc_flat (A := P0) (b := ((d + s, 0, 0) : ℕ × ℕ × ℕ)) (j0 := A.length) hPne
    (by simp; omega) rfl rfl hpar hj0 ?_
  intro n
  have h1 : P0.take A.length = A := by rw [hP0, List.take_left]
  have h2 : P0.drop A.length = BlkD (d + s) Ms C := by rw [hP0, List.drop_left]
  rw [h1, h2, ← Yseq_eq]
  exact (Yseq_Aok_S hd hA hM hmoC hP hclose hIH n).1.mem

/-- ★★ シフト付きの高さ `d` 一般 bump。帰納法の仮定を**全てのシフトで**渡す。 -/
theorem blkD_memS {d : ℕ} (hd : 1 ≤ d) (M : TrioSeq) (hM : MidD d M)
    {P : ℕ → TrioSeq → Prop}
    (hbase : ∀ (s : ℕ) (A : TrioSeq), Aok A → P s A → A ++ shiftr01 s 0 M ∈ W 0)
    (hclose : ∀ (s : ℕ) (A' C' : TrioSeq), Aok A' → P s A' → Mono C' →
        (∀ (t : ℕ) (A'' : TrioSeq), Aok A'' → P t A'' →
          A'' ++ BlkD (d + t) (shiftr01 t 0 M) C' ∈ W 0) →
        P s (A' ++ BlkD (d + s) (shiftr01 s 0 M) C')) :
    ∀ B ∈ W 0, Zroot B → Mono B → entry B 0 0 = 0 →
      ∀ (s : ℕ) (A : TrioSeq), Aok A → P s A →
        A ++ BlkD (d + s) (shiftr01 s 0 M) B ∈ W 0 := by
  have key : W 0 ⊆ {B : TrioSeq | Zroot B → Mono B → entry B 0 0 = 0 →
      ∀ (s : ℕ) (A : TrioSeq), Aok A → P s A →
        A ++ BlkD (d + s) (shiftr01 s 0 M) B ∈ W 0} := by
    refine A2' ?_
    intro B hB
    simp only [Set.mem_setOf_eq]
    intro hzr hmo hroot s A hA hPA
    by_cases hshort : B.length ≤ 1
    · rcases (by omega : B.length = 0 ∨ B.length = 1) with h0 | h1
      · have hnil : B = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        rw [BlkD_nil]
        exact hbase s A hA hPA
      · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
        have hc0 : c.1 = 0 := hroot
        obtain ⟨hc1, hc2⟩ := hzr c (by simp) hc0
        have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1 hc2)
        subst hcz
        have heq : A ++ BlkD (d + s) (shiftr01 s 0 M) [((0, 0, 0) : ℕ × ℕ × ℕ)]
            = (A ++ BlkD (d + s) (shiftr01 s 0 M) [])
              ++ [((d + s, 0, 0) : ℕ × ℕ × ℕ)] := by
          simp [BlkD, shiftr01]
        rw [heq]
        refine blkD_snoc_twoS hd hM (by intro c hc; simp at hc) hA hPA hclose ?_
        intro t A' hA' hP'
        rw [BlkD_nil]
        exact hbase t A' hA' hP'
    have hlen2 : 2 ≤ B.length := by omega
    have hBne : B ≠ [] := by intro hc; rw [hc] at hlen2; simp at hlen2
    rcases hB with ⟨hl, -⟩ | hnat | ⟨m, hm, -, -⟩
    · exact absurd hl hshort
    · by_cases hlast : entry B 0 (B.length - 1) = 0
      · obtain ⟨he1, he2⟩ := Zroot_entry hzr hlast
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
          rw [oper_eq_pred_of_zero 1 (by omega) ⟨hlast, he1, he2⟩]
          unfold Pred
          rw [if_neg (by omega)]
        have hdl := hnat 1 le_rfl
        rw [hop] at hdl
        simp only [Set.mem_setOf_eq] at hdl
        have hdl0 : entry B.dropLast 0 0 = 0 := by
          rw [List.dropLast_eq_take,
            Wset.entry_take (show (0 : ℕ) < B.length - 1 by omega)]
          exact hroot
        have hIH : ∀ (t : ℕ) (A' : TrioSeq), Aok A' → P t A' →
            A' ++ BlkD (d + t) (shiftr01 t 0 M) B.dropLast ∈ W 0 :=
          fun t A' hA' hP' => hdl (fun c hc => hzr c (List.dropLast_subset _ hc))
            (fun c hc => hmo c (List.dropLast_subset _ hc)) hdl0 t A' hA' hP'
        have hgoal := blkD_snoc_twoS (C := B.dropLast) hd hM
          (fun c hc => hmo c (List.dropLast_subset _ hc)) hA hPA hclose hIH
        have heq : A ++ BlkD (d + s) (shiftr01 s 0 M) B
            = (A ++ BlkD (d + s) (shiftr01 s 0 M) B.dropLast)
              ++ [((d + s, 0, 0) : ℕ × ℕ × ℕ)] := by
          conv_lhs => rw [hsplit]
          rw [BlkD_snoc, List.append_assoc]
        rw [heq]
        exact hgoal
      · have hnz : ¬ (entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
            entry B 2 (B.length - 1) = 0) := fun h => hlast h.1
        have hp := hasParent_of_ZrootMono hzr hmo hroot hlen2 hnz
        refine A1_intro (Or.inr (Or.inl ?_))
        intro n hn
        rw [BlkD_app, oper_shift _ _ (d + s) n hlen2 hp, ← BlkD_app]
        obtain ⟨hzr', hmo'⟩ := ZM_oper hzr hmo n
        exact hnat n hn hzr' hmo' (by rw [Wset.oper_head_eq hn]; exact hroot) s A hA hPA
    · exact absurd hm (Nat.not_lt_zero m)
  intro B hB
  exact key hB

/-! ### 梯子本体 -/

/-- 高さ `r` 以下の梯子で、高さ `a+1` のブロックを吊るせる行列。 -/
def Lv : ℕ → ℕ → TrioSeq → Prop
  | 0, a, A => Aok A ∧ a = 0
  | (_ + 1), 0, A => Aok A
  | (r + 1), (a + 1), A => Aok A ∧ ∃ A0 M : TrioSeq, A = A0 ++ M ∧ Lv r a A0 ∧
      MidD (a + 2) M ∧
      (∀ (s : ℕ) (A' : TrioSeq), Lv r (a + s) A' → A' ++ shiftr01 s 0 M ∈ W 0)

theorem Lv_Aok : ∀ (r a : ℕ) (A : TrioSeq), Lv r a A → Aok A
  | 0, _, _, h => h.1
  | (_ + 1), 0, _, h => h
  | (_ + 1), (_ + 1), _, h => h.1

theorem Lv_Ancd : ∀ (r a : ℕ) (A : TrioSeq), Lv r a A → Ancd (a + 1) A
  | 0, a, A, h => by
      obtain ⟨hA, ha⟩ := h
      subst ha
      intro j hj0 hjl hlt _
      have := hA.deep.2 j hj0 hjl
      omega
  | (_ + 1), 0, A, h => by
      have hA : Aok A := h
      intro j hj0 hjl hlt _
      have := hA.deep.2 j hj0 hjl
      omega
  | (r + 1), (a + 1), A, h => by
      obtain ⟨hAok, A0, M, rfl, hA0, hM, -⟩ := h
      have hA0ok : Aok A0 := Lv_Aok r a A0 hA0
      have hA0len : 0 < A0.length := List.length_pos_iff.mpr hA0ok.ne
      have hMlen : 0 < M.length := List.length_pos_iff.mpr hM.ne
      have hhead0 : entry (A0 ++ M) 0 A0.length = entry M 0 0 := by
        rw [show A0.length = A0.length + 0 from rfl, entry_append_right]
      have hhead1 : entry (A0 ++ M) 1 A0.length = entry M 1 0 := by
        rw [show A0.length = A0.length + 0 from rfl, entry_append_right]
      have hMh : entry M 0 0 = a + 1 := by have := hM.head; omega
      intro j hj0 hjl hlt hrec
      have hlen : (A0 ++ M).length = A0.length + M.length := by simp
      rcases Nat.lt_trichotomy j A0.length with hj | hj | hj
      · have hcmp : entry (A0 ++ M) 0 j < entry (A0 ++ M) 0 A0.length :=
          hrec A0.length hj (by omega)
        rw [hhead0, hMh] at hcmp
        rw [entry_append_left hj] at hcmp ⊢
        refine Lv_Ancd r a A0 hA0 j hj0 hj hcmp ?_
        intro i hi1 hi2
        have := hrec i hi1 (by omega)
        rw [entry_append_left hj, entry_append_left hi2] at this
        exact this
      · subst hj
        rw [hhead1]
        exact hM.head1
      · exfalso
        obtain ⟨t, rfl⟩ : ∃ t, j = A0.length + t := ⟨j - A0.length, by omega⟩
        rw [entry_append_right] at hlt
        have := hM.tail t (by omega) (by omega)
        omega

/-- シフト閉包: 再継ぎ可能なセグメントを `s` だけ高くして継いでも梯子が 1 段上がる。 -/
theorem Lv_shift {r a : ℕ} {M : TrioSeq} (hM : MidD (a + 2) M)
    (hre : ∀ (t : ℕ) (A' : TrioSeq), Lv r (a + t) A' → A' ++ shiftr01 t 0 M ∈ W 0)
    (s : ℕ) {A' : TrioSeq} (hA' : Lv r (a + s) A') :
    Lv (r + 1) (a + s + 1) (A' ++ shiftr01 s 0 M) := by
  have hA'ok : Aok A' := Lv_Aok _ _ _ hA'
  have hmem : A' ++ shiftr01 s 0 M ∈ W 0 := hre s A' hA'
  have hMs0 : MidD (a + 2 + s) (shiftr01 s 0 M) := MidD_shift hM s
  have heq : a + 2 + s = a + s + 2 := by omega
  rw [heq] at hMs0
  refine ⟨Aok_append_Mid (by omega) hA'ok hMs0 hmem, A', shiftr01 s 0 M, rfl, hA',
    hMs0, ?_⟩
  intro t A'' hA''
  rw [shiftr01_add0]
  refine hre (s + t) A'' ?_
  have h2 : a + (s + t) = a + s + t := by omega
  rw [h2]
  exact hA''

theorem Lv_hang : ∀ (r a : ℕ) (A : TrioSeq), Lv r a A → ∀ B : TrioSeq, Bok B →
    A ++ shiftr01 (a + 1) 0 B ∈ W 0
  | 0, a, A, h, B, hB => by
      obtain ⟨hA, ha⟩ := h
      subst ha
      show A ++ bump B ∈ W 0
      exact bump_zm hB.mem hB.zroot hB.mono hB.root hA.mem hA.ne hA.deep
  | (_ + 1), 0, A, h, B, hB => by
      have hA : Aok A := h
      show A ++ bump B ∈ W 0
      exact bump_zm hB.mem hB.zroot hB.mono hB.root hA.mem hA.ne hA.deep
  | (r + 1), (a + 1), A, h, B, hB => by
      obtain ⟨hAok, A0, M, rfl, hA0, hM, hre⟩ := h
      have hA0ok : Aok A0 := Lv_Aok r a A0 hA0
      have hbase : ∀ (s : ℕ) (A' : TrioSeq), Aok A' → Lv r (a + s) A' →
          A' ++ shiftr01 s 0 M ∈ W 0 := fun s A' _ h' => hre s A' h'
      have hclose : ∀ (s : ℕ) (A' C' : TrioSeq), Aok A' → Lv r (a + s) A' → Mono C' →
          (∀ (t : ℕ) (A'' : TrioSeq), Aok A'' → Lv r (a + t) A'' →
            A'' ++ BlkD (a + 2 + t) (shiftr01 t 0 M) C' ∈ W 0) →
          Lv r (a + s) (A' ++ BlkD (a + 2 + s) (shiftr01 s 0 M) C') := by
        intro s A' C' hA'ok hA' hmoC' hIH
        have hXmem := hIH s A' hA'ok hA'
        have hMs : MidD (a + 2 + s) (shiftr01 s 0 M) := MidD_shift hM s
        have hXok : Aok (A' ++ BlkD (a + 2 + s) (shiftr01 s 0 M) C') :=
          Aok_append_BlkD (by omega) hXmem hA'ok hMs hmoC'
        rcases Nat.eq_zero_or_pos (a + s) with hz | hpos
        · have ha : a = 0 := by omega
          have hs : s = 0 := by omega
          subst ha; subst hs
          match r with
          | 0 => exact ⟨hXok, rfl⟩
          | (_ + 1) => exact hXok
        · obtain ⟨e, he⟩ : ∃ e, a + s = e + 1 := ⟨a + s - 1, by omega⟩
          rw [he] at hA'
          match r, hA' with
          | 0, hA' => exact absurd hA'.2 (by omega)
          | (r' + 1), hA' =>
              obtain ⟨-, A0', M', hsp, hA0', hM', hre'⟩ := hA'
              subst hsp
              have hNcol : ∀ c ∈ BlkD (a + 2 + s) (shiftr01 s 0 M) C', e + 2 ≤ c.1 := by
                intro c hc
                rcases List.mem_append.mp hc with hh | hh
                · have := MidD_col_ge hMs c hh; omega
                · have := shiftD_col c hh; omega
              have hNmo : Mono (BlkD (a + 2 + s) (shiftr01 s 0 M) C') :=
                BlkD_mono hMs.mono hmoC'
              have hgoal : Lv (r' + 1) (e + 1)
                  ((A0' ++ M') ++ BlkD (a + 2 + s) (shiftr01 s 0 M) C') := by
                refine ⟨by rw [List.append_assoc] at hXok ⊢; exact hXok,
                  A0', M' ++ BlkD (a + 2 + s) (shiftr01 s 0 M) C',
                  by rw [List.append_assoc], hA0', MidD_append hM' hNcol hNmo, ?_⟩
                intro t A'' hA''
                have hm1 : A'' ++ shiftr01 t 0 M' ∈ W 0 := hre' t A'' hA''
                have hlv1 : Lv (r' + 1) (e + t + 1) (A'' ++ shiftr01 t 0 M') :=
                  Lv_shift hM' hre' t hA''
                have hok1 : Aok (A'' ++ shiftr01 t 0 M') := Lv_Aok _ _ _ hlv1
                have hlv2 : Lv (r' + 1) (a + (s + t)) (A'' ++ shiftr01 t 0 M') := by
                  have h3 : a + (s + t) = e + t + 1 := by omega
                  rw [h3]; exact hlv1
                have hres := hIH (s + t) _ hok1 hlv2
                have hshift : shiftr01 t 0 (M' ++ BlkD (a + 2 + s) (shiftr01 s 0 M) C')
                    = shiftr01 t 0 M' ++ BlkD (a + 2 + (s + t))
                        (shiftr01 (s + t) 0 M) C' := by
                  simp only [BlkD, shiftr01_append0, shiftr01_add0]
                  rw [show a + 2 + s + t = a + 2 + (s + t) from by omega]
                rw [hshift, ← List.append_assoc]
                exact hres
              rw [he]
              exact hgoal
      have hkey := blkD_memS (d := a + 2) (by omega) M hM hbase hclose B hB.mem
        hB.zroot hB.mono hB.root 0 A0 hA0ok (by simpa using hA0)
      simp only [shiftr01_zero, Nat.add_zero] at hkey
      rw [BlkD_app] at hkey
      exact hkey

theorem Lv_tw (r a : ℕ) (A : TrioSeq) (hA : Lv r a A) :
    ∀ n, TwD (a + 1) A n ∈ W 0
  | 0 => by simpa [TwD] using W_nil 0
  | (n + 1) => by
      have hAok : Aok A := Lv_Aok r a A hA
      rw [TwD_succ]
      exact Lv_hang r a A hA (TwD (a + 1) A n)
        ⟨Lv_tw r a A hA n, TwD_zroot (by omega) hAok.zroot n, TwD_mono hAok.mono n,
          TwD_root hAok.ne hAok.deep.1 n⟩

/-- ★★ `Lv r a A` なら `(a+1,1,0)` を継げる。 -/
theorem Lv_snoc (r a : ℕ) (A : TrioSeq) (hA : Lv r a A) :
    A ++ [((a + 1, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hAok : Aok A := Lv_Aok r a A hA
  exact snocd_mem (by omega) hAok.ne hAok.deep hAok.zroot (Lv_Ancd r a A hA)
    (Lv_tw r a A hA)

/-! ### 対角 `Dg k = X(1,1,0)(2,1,0)...(k,1,0)` と シート行290/291/292 -/

def Dg : ℕ → TrioSeq
  | 0 => Q
  | (k + 1) => Dg k ++ [((k + 1, 1, 0) : ℕ × ℕ × ℕ)]

theorem Lv_Dg : ∀ k : ℕ, Lv k k (Dg k)
  | 0 => ⟨(Aok_Q : Aok Q), rfl⟩
  | (k + 1) => by
      have hprev : Lv k k (Dg k) := Lv_Dg k
      have hM : MidD (k + 2) [((k + 1, 1, 0) : ℕ × ℕ × ℕ)] :=
        MidD_one (k + 1) (by omega)
      have hre : ∀ (s : ℕ) (A' : TrioSeq), Lv k (k + s) A' →
          A' ++ shiftr01 s 0 [((k + 1, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
        intro s A' hA'
        have h := Lv_snoc k (k + s) A' hA'
        have heq : shiftr01 s 0 [((k + 1, 1, 0) : ℕ × ℕ × ℕ)]
            = [((k + s + 1, 1, 0) : ℕ × ℕ × ℕ)] := by
          simp [shiftr01]; omega
        rw [heq]
        exact h
      have hmem : Dg k ++ [((k + 1, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
        have h := hre 0 (Dg k) (by simpa using hprev)
        simpa using h
      exact ⟨Aok_append_Mid (by omega) (Lv_Aok _ _ _ hprev) hM hmem,
        Dg k, [((k + 1, 1, 0) : ℕ × ℕ × ℕ)], rfl, hprev, hM, hre⟩

theorem Dg_mem (k : ℕ) : Dg k ∈ W 0 := (Lv_Aok _ _ _ (Lv_Dg k)).mem

theorem Dg_eq : ∀ n : ℕ,
    Dg n = Q ++ (List.range n).flatMap fun k => [((k + 1, 1, 0) : ℕ × ℕ × ℕ)]
  | 0 => by simp [Dg]
  | (n + 1) => by
      show Dg n ++ _ = _
      rw [Dg_eq n, List.range_succ, List.flatMap_append, List.append_assoc]
      simp

#print axioms Lv_hang
#print axioms Lv_snoc
#print axioms Dg_mem

/-- ★ シート行290 `X(1,1,0)(2,1,0)(3,1,0) = psi(W_w + W^W)`。 -/
def R290 : TrioSeq := [(0, 0, 0), (1, 1, 1), (1, 1, 0), (2, 1, 0), (3, 1, 0)]

theorem R290_eq : R290 = Dg 3 := by rfl

theorem R290_mem : R290 ∈ W 0 := by rw [R290_eq]; exact Dg_mem 3

/-- ★ シート行291 `psi(W_w + W^W^W)`。 -/
def R291 : TrioSeq := [(0, 0, 0), (1, 1, 1), (1, 1, 0), (2, 1, 0), (3, 1, 0), (4, 1, 0)]

theorem R291_eq : R291 = Dg 4 := by rfl

theorem R291_mem : R291 ∈ W 0 := by rw [R291_eq]; exact Dg_mem 4

/-! ### シート行292 `X(1,1,0)(2,2,0) = psi(W_w + psi_1(W_2))`

`292⟦n⟧ = Dg n`（バッドルートは行 1、親は `(1,1,0)`、`d0 = 1`、ブロックは 1 列）。 -/

def R292 : TrioSeq := [(0, 0, 0), (1, 1, 1), (1, 1, 0), (2, 2, 0)]

theorem R292_len : R292.length = 4 := by simp [R292]

theorem R292_srow : srow R292 3 = 1 := by simp [srow, R292, entry]

theorem nextrel0_R292_23 : nextrel0 R292 2 3 := by
  refine ⟨by simp [R292], by simp [R292], by omega, by simp [R292, entry], ?_⟩
  intro j hj; omega

theorem le0_R292_22 : le0 R292 2 2 :=
  ⟨by simp [R292], by simp [R292], Relation.ReflTransGen.refl⟩

theorem le0_R292_23 : le0 R292 2 3 :=
  ⟨by simp [R292], by simp [R292], Relation.ReflTransGen.single nextrel0_R292_23⟩

theorem R292_hasParent : hasParent R292 1 3 :=
  H12Export.hasParent1_of_le0_witness (by rw [R292_len]; omega) le0_R292_23.2.2
    (by simp [R292, entry])

theorem nextrel1_R292 : nextrel1 R292 2 3 := by
  refine ⟨by simp [R292], by simp [R292], by omega, by simp [R292, entry],
    le0_R292_23, ?_⟩
  intro j hj
  obtain ⟨hj2, hjle⟩ := hj
  have hjl : j < R292.length := hjle.1
  rw [R292_len] at hjl
  have hj3 : j = 3 := by omega
  subst hj3
  omega

theorem R292_parent : parent R292 1 3 = 2 :=
  R292_hasParent.unique (parent_nextR R292_hasParent) nextrel1_R292

open Classical in
theorem oper_R292 (n : ℕ) : R292⟦n⟧ = Dg n := by
  rw [L53.oper_unfold (j1 := 3) (i1 := 1) (j0 := 2) (d0 := 1) (d1 := 0)
      (by simp [R292]) (by omega) (by simp [R292, entry]) R292_srow.symm
      R292_hasParent R292_parent.symm (by simp [R292, entry]) (by simp) n,
    Dg_eq]
  have htk : R292.take 2 = Q := rfl
  rw [htk]
  apply congrArg
  apply List.flatMap_congr
  intro k _
  have hr : List.range' 2 (3 - 2) = [2] := rfl
  rw [hr]
  simp only [List.map_cons, List.map_nil, Nat.mul_zero, ite_self, Nat.add_zero,
    Nat.mul_one]
  rw [if_pos le0_R292_22]
  simp [R292, entry, Nat.add_comm]

/-- ★ シート行292 `X(1,1,0)(2,2,0) ∈ W 0`。 -/
theorem R292_mem : R292 ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_R292 n]
  exact Dg_mem n

#print axioms R290_mem
#print axioms R291_mem
#print axioms R292_mem

/-! ## 段 `u` 版の `blkD_mem` — 残るのは 2 枝だけ

`blkD_mem` は `B ∈ W 0` の帰納法だった。`W 0` では `Aop` の節3 が空で、しかも
`Zroot B` のおかげで「末尾が孤児」の枝が現れない。段を上げると、この 2 つが
生きた枝として出る。

    節1              |B| ≤ 1 ∧ lev B 0 = 0            ← 既存の議論で済む
    節2 ＋ 全零末尾                                     ← 既存（blkD_snoc_two）
    節2 ＋ B の中に親あり                                ← 既存（oper_shift の恒等式）
    節2 ＋ B の中では孤児   ★ hSnoc                     ← 文脈が孤児を復活させる
    節3（graft）           ★ hGraft                    ← 残核 (GC) の顔

下の定理は `sorry` 無しで通る。残っているのは仮定 `hSnoc` / `hGraft` の 2 本
だけで、どちらも**その枝で使える帰納法の仮定を引数として受け取る**形にしてある
（`RESIDUE-PROBLEM.md` §4.5 の「呼び出し地点にあるのに捨てられているパッケージ」）。 -/

theorem blkD_stage {d u : ℕ} (hd : 1 ≤ d) (M : TrioSeq) (hM : MidD d M)
    {P Pb : TrioSeq → Prop}
    (hPbOper : ∀ B : TrioSeq, Pb B → ∀ n, 1 ≤ n → Pb (B⟦n⟧))
    (hPbMono : ∀ B : TrioSeq, Pb B → Mono B)
    (hPbRoot : ∀ B : TrioSeq, Pb B → entry B 0 0 = 0)
    (hbase : ∀ A : TrioSeq, Aok A → P A → A ++ M ∈ W 0)
    (hclose : ∀ A' C' : TrioSeq, Aok A' → P A' → Mono C' →
        (∀ A'' : TrioSeq, Aok A'' → P A'' → A'' ++ BlkD d M C' ∈ W 0) →
        P (A' ++ BlkD d M C'))
    (hSnoc : ∀ B : TrioSeq, 2 ≤ B.length → Pb B →
        ¬ (entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
           entry B 2 (B.length - 1) = 0) →
        ¬ hasParent B (srow B (B.length - 1)) (B.length - 1) →
        (∀ A : TrioSeq, Aok A → P A → A ++ BlkD d M B.dropLast ∈ W 0) →
        ∀ A : TrioSeq, Aok A → P A → A ++ BlkD d M B ∈ W 0)
    (hGraft : ∀ (B : TrioSeq) (m : ℕ), m < u → domT B m → Pb B →
        (∀ z ∈ W m, based z → Pb (graft B z) →
          ∀ A : TrioSeq, Aok A → P A → A ++ BlkD d M (graft B z) ∈ W 0) →
        ∀ A : TrioSeq, Aok A → P A → A ++ BlkD d M B ∈ W 0) :
    ∀ B ∈ W u, Pb B → ∀ A : TrioSeq, Aok A → P A → A ++ BlkD d M B ∈ W 0 := by
  have key : W u ⊆ {B : TrioSeq |
      Pb B → ∀ A : TrioSeq, Aok A → P A → A ++ BlkD d M B ∈ W 0} := by
    refine A2' ?_
    intro B hB
    simp only [Set.mem_setOf_eq]
    intro hPb A hA hPA
    have hroot : entry B 0 0 = 0 := hPbRoot B hPb
    have hmo : Mono B := hPbMono B hPb
    rcases hB with ⟨hl, hlev0⟩ | hnat | ⟨m, hm, hdom, hgr⟩
    · -- 節1
      rcases (by omega : B.length = 0 ∨ B.length = 1) with h0 | h1
      · have hnil : B = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        rw [BlkD_nil]
        exact hbase A hA hPA
      · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
        have hc0 : c.1 = 0 := hroot
        have hc1 : c.2.1 = 0 ∧ c.2.2 = 0 := by
          have : 2 * c.2.1 + c.2.2 = 0 := hlev0
          omega
        have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1.1 hc1.2)
        subst hcz
        have heq : A ++ BlkD d M [((0, 0, 0) : ℕ × ℕ × ℕ)]
            = (A ++ BlkD d M []) ++ [((d, 0, 0) : ℕ × ℕ × ℕ)] := by
          simp [BlkD, shiftr01]
        rw [heq]
        refine blkD_snoc_two hd hM (by intro c hc; simp at hc) hA hPA hclose ?_
        intro A' hA' hP'
        rw [BlkD_nil]
        exact hbase A' hA' hP'
    · -- 節2
      by_cases hshort : B.length ≤ 1
      · have hself : B⟦1⟧ = B := oper_eq_self_of_short 1 (by omega)
        have := hnat 1 le_rfl
        rw [hself] at this
        simp only [Set.mem_setOf_eq] at this
        exact this hPb A hA hPA
      have hlen2 : 2 ≤ B.length := by omega
      have hBne : B ≠ [] := by intro hc; rw [hc] at hlen2; simp at hlen2
      -- dropLast 版の帰納法の仮定を先に作る
      by_cases hzero : entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
          entry B 2 (B.length - 1) = 0
      · -- 全零末尾 ⟹ dropLast、ブロック側は (d,0,0) を継ぐだけ
        obtain ⟨hz0, hz1, hz2⟩ := hzero
        have hcol : B.getD (B.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ)
            = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hz0 (Prod.ext hz1 hz2)
        have hgl : B.getLast hBne = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
          have h1 : B.getLast hBne = B.getD (B.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
            rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show B.length - 1 < B.length by omega)]
            rfl
          rw [h1, hcol]
        have hsplit : B = B.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
          rw [← hgl]; exact (List.dropLast_append_getLast hBne).symm
        have hop : B⟦1⟧ = B.dropLast := by
          rw [oper_eq_pred_of_zero 1 (by omega) ⟨hz0, hz1, hz2⟩]
          unfold Pred
          rw [if_neg (by omega)]
        have hdl := hnat 1 le_rfl
        rw [hop] at hdl
        simp only [Set.mem_setOf_eq] at hdl
        have hPbdl : Pb B.dropLast := by
          have := hPbOper B hPb 1 le_rfl
          rwa [hop] at this
        have hIH : ∀ A' : TrioSeq, Aok A' → P A' → A' ++ BlkD d M B.dropLast ∈ W 0 :=
          fun A' hA' hP' => hdl hPbdl A' hA' hP'
        have hgoal := blkD_snoc_two (C := B.dropLast) hd hM
          (hPbMono _ hPbdl) hA hPA hclose hIH
        have heq : A ++ BlkD d M B
            = (A ++ BlkD d M B.dropLast) ++ [((d, 0, 0) : ℕ × ℕ × ℕ)] := by
          conv_lhs => rw [hsplit]
          rw [BlkD_snoc, List.append_assoc]
        rw [heq]
        exact hgoal
      · by_cases hp : hasParent B (srow B (B.length - 1)) (B.length - 1)
        · -- B の中に親がある ⟹ 恒等式で n の帰納法に落ちる
          refine A1_intro (Or.inr (Or.inl ?_))
          intro n hn
          rw [BlkD_app, oper_shift _ _ d n hlen2 hp, ← BlkD_app]
          exact hnat n hn (hPbOper B hPb n hn) A hA hPA
        · -- ★ 孤児枝: B の中では親が無いが、文脈 A ++ M が親を与える
          have hop : B⟦1⟧ = B.dropLast := by
            rw [oper_eq_pred_of_noParent 1 (by omega) hzero hp]
            unfold Pred
            rw [if_neg (by omega)]
          have hdl := hnat 1 le_rfl
          rw [hop] at hdl
          simp only [Set.mem_setOf_eq] at hdl
          have hPbdl : Pb B.dropLast := by
            have := hPbOper B hPb 1 le_rfl
            rwa [hop] at this
          exact hSnoc B hlen2 hPb hzero hp
            (fun A' hA' hP' => hdl hPbdl A' hA' hP') A hA hPA
    · -- ★ 節3（graft）
      refine hGraft B m hm hdom hPb ?_ A hA hPA
      intro z hz hbz hPbg A' hA' hP'
      have := hgr z hz hbz
      simp only [Set.mem_setOf_eq] at this
      exact this hPbg A' hA' hP'
  intro B hB
  exact key hB

/-- **検算**: `u = 0` では `hSnoc` も `hGraft` も空になり、`blkD_stage` から
`blkD_mem` がそのまま出る（＝ 一般化が忠実であることの確認）。 -/
theorem blkD_mem_of_stage {d : ℕ} (hd : 1 ≤ d) (M : TrioSeq) (hM : MidD d M)
    {P : TrioSeq → Prop}
    (hbase : ∀ A : TrioSeq, Aok A → P A → A ++ M ∈ W 0)
    (hclose : ∀ A' C' : TrioSeq, Aok A' → P A' → Mono C' →
        (∀ A'' : TrioSeq, Aok A'' → P A'' → A'' ++ BlkD d M C' ∈ W 0) →
        P (A' ++ BlkD d M C')) :
    ∀ B ∈ W 0, Zroot B → Mono B → entry B 0 0 = 0 →
      ∀ A : TrioSeq, Aok A → P A → A ++ BlkD d M B ∈ W 0 := by
  intro B hB hzr hmo hroot A hA hPA
  refine blkD_stage (Pb := fun X => Zroot X ∧ Mono X ∧ entry X 0 0 = 0)
    hd M hM ?_ ?_ ?_ hbase hclose ?_ ?_ B hB ⟨hzr, hmo, hroot⟩ A hA hPA
  · rintro B' ⟨h1, h2, h3⟩ n hn
    obtain ⟨h1', h2'⟩ := ZM_oper h1 h2 n
    exact ⟨h1', h2', by rw [Wset.oper_head_eq hn]; exact h3⟩
  · rintro B' ⟨-, h2, -⟩; exact h2
  · rintro B' ⟨-, -, h3⟩; exact h3
  · rintro B' hlen2 ⟨h1, h2, h3⟩ hnz hp - A' hA' hP'
    exact absurd (hasParent_of_ZrootMono h1 h2 h3 hlen2 hnz) hp
  · rintro B' m hm - - - A' hA' hP'
    exact absurd hm (Nat.not_lt_zero m)

#print axioms blkD_stage
#print axioms blkD_mem_of_stage

/-! ## 内部アンカーの継ぎ足し `snocY`

`Lv_snoc` は「行 1 の親が**根**」の場合だった。行293 以降では

    Y0 ++ M ++ [(L+1, y, 0)]        M の先頭は高さ L・行 1 = e < y

の形が出る。行 1 の親は `M` の先頭（内部）で、`d0 = (L+1) - L = 1`、ブロックは
`M` そのもの。よって展開は `M` を 1 ずつ高くしたコピーの列:

    (Y0 ++ M ++ [(L+1,y,0)])[n] = Y0 ++ M ++ M↑1 ++ ... ++ M↑(n-1)  =: Mtw Y0 M n

`M` の尻尾が高さ `L+1` 以上（`MidD (L+1) M`）なので、`M` の中には行 1 が `y`
未満の `le0` 祖先が無く、親が `M` の先頭に固定される。 -/

def Mtw (Y0 M : TrioSeq) (n : ℕ) : TrioSeq :=
  Y0 ++ (List.range n).flatMap fun k => shiftr01 k 0 M

theorem Mtw_zero (Y0 M : TrioSeq) : Mtw Y0 M 0 = Y0 := by simp [Mtw]

theorem Mtw_succ (Y0 M : TrioSeq) (n : ℕ) :
    Mtw Y0 M (n + 1) = Mtw Y0 M n ++ shiftr01 n 0 M := by
  simp [Mtw, List.range_succ, List.flatMap_append, List.append_assoc]

theorem map_range'_shift_at {T M : TrioSeq} {q k : ℕ}
    (hq : ∀ i t, t < M.length → entry T i (q + t) = entry M i t) :
    (List.range' q M.length).map
        (fun j => ((entry T 0 j + k, entry T 1 j, entry T 2 j) : ℕ × ℕ × ℕ))
      = shiftr01 k 0 M := by
  apply List.ext_getElem
  · simp [shiftr01]
  · intro i h1 h2
    have hi : i < M.length := by simpa using h1
    simp only [List.getElem_map, List.getElem_range', Nat.one_mul, shiftr01]
    rw [hq 0 i hi, hq 1 i hi, hq 2 i hi, ← triple_entry M hi]
    rfl

open Classical in
/-- ★ 内部アンカーでの継ぎ足しの展開。 -/
theorem oper_snocY {Y0 M : TrioSeq} {L y : ℕ} (hY0ne : Y0 ≠ [])
    (hM : MidD (L + 1) M) (hMe : entry M 1 0 < y) (hy : 1 ≤ y) (n : ℕ) :
    ((Y0 ++ M) ++ [((L + 1, y, 0) : ℕ × ℕ × ℕ)])⟦n⟧ = Mtw Y0 M n := by
  have hY0len : 0 < Y0.length := List.length_pos_iff.mpr hY0ne
  have hMlen : 0 < M.length := List.length_pos_iff.mpr hM.ne
  set Y : TrioSeq := Y0 ++ M with hY
  set T : TrioSeq := Y ++ [((L + 1, y, 0) : ℕ × ℕ × ℕ)] with hT
  have hYlen : Y.length = Y0.length + M.length := by rw [hY]; simp
  have hTlen : T.length = Y.length + 1 := by rw [hT]; simp
  have hpreY : ∀ i j, j < Y.length → entry T i j = entry Y i j :=
    fun i j hj => entry_append_lt hj
  have hpreM : ∀ i t, t < M.length → entry Y i (Y0.length + t) = entry M i t := by
    intro i t _
    rw [hY, entry_append_right]
  have hlast := entry_append_last (P := Y) (c := ((L + 1, y, 0) : ℕ × ℕ × ℕ))
  have hl0 : entry T 0 Y.length = L + 1 := hlast.1
  have hl1 : entry T 1 Y.length = y := hlast.2.1
  have hl2 : entry T 2 Y.length = 0 := hlast.2.2
  have hanchor0 : entry T 0 Y0.length = L := by
    rw [hpreY 0 Y0.length (by omega),
      show Y0.length = Y0.length + 0 from rfl, hpreM 0 0 hMlen]
    have := hM.head; omega
  have hanchor1 : entry T 1 Y0.length = entry M 1 0 := by
    rw [hpreY 1 Y0.length (by omega),
      show Y0.length = Y0.length + 0 from rfl, hpreM 1 0 hMlen]
  have hdeeper : ∀ x, Y0.length < x → x < T.length → L + 1 ≤ entry T 0 x := by
    intro x h1 h2
    rcases Nat.lt_or_ge x Y.length with h | h
    · obtain ⟨t, rfl⟩ : ∃ t, x = Y0.length + t := ⟨x - Y0.length, by omega⟩
      rw [hpreY 0 _ h, hpreM 0 t (by omega)]
      exact hM.tail t (by omega) (by omega)
    · have : x = Y.length := by omega
      rw [this, hl0]
  have hsh : ∀ x, Y0.length < x → x < T.length → entry T 0 Y0.length < entry T 0 x := by
    intro x h1 h2
    have := hdeeper x h1 h2
    rw [hanchor0]; omega
  have hle0 : ∀ j, Y0.length ≤ j → j < T.length → le0 T Y0.length j := by
    intro j h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · exact ⟨by omega, by omega, Relation.ReflTransGen.refl⟩
    · exact H12Export.le0_root_of_shallow (by omega) hsh j h h2
  have hsrow : srow T Y.length = 1 := by
    unfold srow
    rw [if_neg (by rw [hl2]; omega), if_pos (by rw [hl1]; omega)]
  have hpar : hasParent T 1 Y.length :=
    H12Export.hasParent1_of_le0_witness (by omega)
      (hle0 Y.length (by omega) (by omega)).2.2
      (by rw [hanchor1, hl1]; exact hMe)
  have hnr1 : nextrel1 T Y0.length Y.length := by
    refine ⟨by omega, by omega, by omega, by rw [hanchor1, hl1]; exact hMe,
      hle0 Y.length (by omega) (by omega), ?_⟩
    rintro j ⟨hj0, hjle⟩
    rw [hl1]
    rcases Nat.lt_or_ge j Y.length with h | h
    · exfalso
      have hrec := rtg0_rec hjle.2.2 Y.length (by omega) le_rfl
      rw [hl0] at hrec
      have := hdeeper j hj0 (by omega)
      omega
    · have : j = Y.length := by
        have := H12Export.rtg0_index_le hjle.2.2
        omega
      rw [this, hl1]
  have hj0 : parent T 1 Y.length = Y0.length :=
    hpar.unique (parent_nextR hpar) hnr1
  rw [L53.oper_unfold (j1 := Y.length) (i1 := 1) (j0 := Y0.length) (d0 := 1) (d1 := 0)
      (by omega) (by omega) (by rintro ⟨h, -, -⟩; rw [hl0] at h; omega)
      hsrow.symm hpar hj0.symm (by rw [if_pos (by omega), hl0, hanchor0]; omega)
      (by simp) n, Mtw]
  have htk : T.take Y0.length = Y0 := by
    rw [hT, hY, List.append_assoc]
    exact List.take_left
  have hrlen : Y.length - Y0.length = M.length := by omega
  rw [htk, hrlen]
  simp only [Nat.mul_zero, ite_self, Nat.add_zero, Nat.mul_one]
  congr 1
  apply List.flatMap_congr
  intro k _
  rw [← map_range'_shift_at (T := T) (M := M) (q := Y0.length) (k := k)
    (fun i t ht => by
      rw [hpreY i _ (by omega), hpreM i t ht])]
  apply List.map_congr_left
  intro j hj
  have hjr := List.mem_range'_1.1 hj
  rw [if_pos (hle0 j (by omega) (by omega))]

/-- ★ 塔が済めば内部アンカーで継げる。 -/
theorem snocY_mem {Y0 M : TrioSeq} {L y : ℕ} (hY0ne : Y0 ≠ [])
    (hM : MidD (L + 1) M) (hMe : entry M 1 0 < y) (hy : 1 ≤ y)
    (htw : ∀ n, Mtw Y0 M n ∈ W 0) :
    (Y0 ++ M) ++ [((L + 1, y, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_snocY hY0ne hM hMe hy n]
  exact htw n

#print axioms oper_snocY
#print axioms snocY_mem

theorem Mtw_Q_eq (n : ℕ) : Mtw Q [((1, 1, 0) : ℕ × ℕ × ℕ)] n = Dg n := by
  rw [Mtw, Dg_eq]
  congr 1
  apply List.flatMap_congr
  intro k _
  simp only [shiftr01, List.map_cons, List.map_nil]
  congr 2
  omega

/-- **検算**: `snocY_mem` から行292 が出る（`Y0 = Q`, `M = [(1,1,0)]`, `y = 2`）。 -/
theorem R292_mem_of_snocY : R292 ∈ W 0 := by
  have h : R292 = (Q ++ [((1, 1, 0) : ℕ × ℕ × ℕ)]) ++ [((2, 2, 0) : ℕ × ℕ × ℕ)] := by
    simp [R292, Q]
  rw [h]
  refine snocY_mem (L := 1) (y := 2) (by simp [Q]) (MidD_one 1 (by omega)) ?_ (by omega) ?_
  · show (1 : ℕ) < 2
    omega
  · intro n
    rw [Mtw_Q_eq]
    exact Dg_mem n

#print axioms R292_mem_of_snocY

/-! ### `Lv` の梯子 ×`Mtw` の塔

`Lv_snoc` は 1 本だけ `(a+1,1,0)` を継ぐ。ここではそれを **n 本連ねた鎖**
`A(a+1,1,0)(a+2,1,0)...(a+n,1,0)` が `W 0` に入ることを示す。ランクは 1 段ごとに
1 つ上がるが、`n` ごとに別のランクでよいので問題にならない。 -/

theorem Mtw_one_succ (A : TrioSeq) (a n : ℕ) :
    Mtw A [((a + 1, 1, 0) : ℕ × ℕ × ℕ)] (n + 1)
      = Mtw A [((a + 1, 1, 0) : ℕ × ℕ × ℕ)] n ++ [((a + n + 1, 1, 0) : ℕ × ℕ × ℕ)] := by
  rw [Mtw_succ]
  congr 1
  simp only [shiftr01, List.map_cons, List.map_nil]
  congr 2
  omega

/-- 鎖の各段が梯子の 1 段になる。 -/
theorem Lv_chain_lv (r a : ℕ) (A : TrioSeq) (hA : Lv r a A) :
    ∀ n : ℕ, Lv (r + n) (a + n) (Mtw A [((a + 1, 1, 0) : ℕ × ℕ × ℕ)] n)
  | 0 => by simpa [Mtw_zero] using hA
  | (n + 1) => by
      have ih := Lv_chain_lv r a A hA n
      rw [Mtw_one_succ]
      have hM : MidD (a + n + 2) [((a + n + 1, 1, 0) : ℕ × ℕ × ℕ)] :=
        MidD_one (a + n + 1) (by omega)
      have hre : ∀ (t : ℕ) (A' : TrioSeq), Lv (r + n) (a + n + t) A' →
          A' ++ shiftr01 t 0 [((a + n + 1, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
        intro t A' hA'
        have h := Lv_snoc (r + n) (a + n + t) A' hA'
        have heq : shiftr01 t 0 [((a + n + 1, 1, 0) : ℕ × ℕ × ℕ)]
            = [((a + n + t + 1, 1, 0) : ℕ × ℕ × ℕ)] := by
          simp only [shiftr01, List.map_cons, List.map_nil]
          congr 2
          omega
        rw [heq]
        exact h
      have h := Lv_shift (r := r + n) (a := a + n) hM hre 0
        (A' := Mtw A [((a + 1, 1, 0) : ℕ × ℕ × ℕ)] n) (by simpa using ih)
      simp only [shiftr01_zero, Nat.add_zero] at h
      have h1 : r + n + 1 = r + (n + 1) := by omega
      have h2 : a + n + 1 = a + (n + 1) := by omega
      rw [h1, h2] at h
      exact h

/-- ★ `Lv r a A` なら鎖 `A(a+1,1,0)(a+2,1,0)...` はどこまでも `W 0`。 -/
theorem Lv_chain (r a : ℕ) (A : TrioSeq) (hA : Lv r a A) (n : ℕ) :
    Mtw A [((a + 1, 1, 0) : ℕ × ℕ × ℕ)] n ∈ W 0 :=
  (Lv_Aok _ _ _ (Lv_chain_lv r a A hA n)).mem

/-- ★★ `Lv r a A` なら **2 列** `(a+1,1,0)(a+2,2,0)` を継げる。

`(a+2,2,0)` の行 1 の親は直前の `(a+1,1,0)`（内部アンカー）なので、塔は
`Mtw A [(a+1,1,0)]` すなわち鎖。 -/
theorem Lv_snoc2 (r a : ℕ) (A : TrioSeq) (hA : Lv r a A) :
    A ++ [((a + 1, 1, 0) : ℕ × ℕ × ℕ), ((a + 2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hAok : Aok A := Lv_Aok _ _ _ hA
  have h := snocY_mem (Y0 := A) (M := [((a + 1, 1, 0) : ℕ × ℕ × ℕ)]) (L := a + 1)
    (y := 2) hAok.ne (MidD_one (a + 1) (by omega)) (by show (1 : ℕ) < 2; omega)
    (by omega) (Lv_chain r a A hA)
  simpa using h

#print axioms Lv_chain
#print axioms Lv_snoc2

/-! ### 内部アンカーの継ぎ足し（歩幅 `delta` 版）

`oper_snocY` はアンカーと末尾列の高さの差が 1 の場合。ここでは差を `dl` に一般化する。
写しの歩幅がそのまま `dl` になるので、塔は `Mtwd dl Y0 M n = Y0 ++ M ++ M↑dl ++ M↑2dl ++ ...`。

差が 2 以上のときは「アンカーより後ろで末尾列の行 0 の祖先になる列」が実在しうるので、
`nextrel1` の最小性は仮定 `hMy`（`M` の頭以外は行 1 が `y` 以上）で押さえる。 -/

def Mtwd (dl : ℕ) (Y0 M : TrioSeq) (n : ℕ) : TrioSeq :=
  Y0 ++ (List.range n).flatMap fun k => shiftr01 (dl * k) 0 M

theorem Mtwd_zero (dl : ℕ) (Y0 M : TrioSeq) : Mtwd dl Y0 M 0 = Y0 := by simp [Mtwd]

theorem Mtwd_one (dl : ℕ) (Y0 M : TrioSeq) : Mtwd dl Y0 M 1 = Y0 ++ M := by
  simp [Mtwd, shiftr01_zero]

theorem Mtwd_succ (dl : ℕ) (Y0 M : TrioSeq) (n : ℕ) :
    Mtwd dl Y0 M (n + 1) = Mtwd dl Y0 M n ++ shiftr01 (dl * n) 0 M := by
  simp [Mtwd, List.range_succ, List.flatMap_append, List.append_assoc]

open Classical in
/-- ★ 内部アンカーでの継ぎ足しの展開（歩幅 `dl`）。 -/
theorem oper_snocYd {Y0 M : TrioSeq} {L y dl : ℕ} (hY0ne : Y0 ≠ [])
    (hM : MidD (L + 1) M) (hMe : entry M 1 0 < y)
    (hMy : ∀ t, 1 ≤ t → t < M.length → entry M 0 t < L + dl →
      (∀ i, t < i → i < M.length → entry M 0 t < entry M 0 i) → y ≤ entry M 1 t)
    (hy : 1 ≤ y) (hdl : 1 ≤ dl) (n : ℕ) :
    ((Y0 ++ M) ++ [((L + dl, y, 0) : ℕ × ℕ × ℕ)])⟦n⟧ = Mtwd dl Y0 M n := by
  have hY0len : 0 < Y0.length := List.length_pos_iff.mpr hY0ne
  have hMlen : 0 < M.length := List.length_pos_iff.mpr hM.ne
  set Y : TrioSeq := Y0 ++ M with hY
  set T : TrioSeq := Y ++ [((L + dl, y, 0) : ℕ × ℕ × ℕ)] with hT
  have hYlen : Y.length = Y0.length + M.length := by rw [hY]; simp
  have hTlen : T.length = Y.length + 1 := by rw [hT]; simp
  have hpreY : ∀ i j, j < Y.length → entry T i j = entry Y i j :=
    fun i j hj => entry_append_lt hj
  have hpreM : ∀ i t, t < M.length → entry Y i (Y0.length + t) = entry M i t := by
    intro i t _
    rw [hY, entry_append_right]
  have hlast := entry_append_last (P := Y) (c := ((L + dl, y, 0) : ℕ × ℕ × ℕ))
  have hl0 : entry T 0 Y.length = L + dl := hlast.1
  have hl1 : entry T 1 Y.length = y := hlast.2.1
  have hl2 : entry T 2 Y.length = 0 := hlast.2.2
  have hanchor0 : entry T 0 Y0.length = L := by
    rw [hpreY 0 Y0.length (by omega),
      show Y0.length = Y0.length + 0 from rfl, hpreM 0 0 hMlen]
    have := hM.head; omega
  have hanchor1 : entry T 1 Y0.length = entry M 1 0 := by
    rw [hpreY 1 Y0.length (by omega),
      show Y0.length = Y0.length + 0 from rfl, hpreM 1 0 hMlen]
  have hdeeper : ∀ x, Y0.length < x → x < T.length → L + 1 ≤ entry T 0 x := by
    intro x h1 h2
    rcases Nat.lt_or_ge x Y.length with h | h
    · obtain ⟨t, rfl⟩ : ∃ t, x = Y0.length + t := ⟨x - Y0.length, by omega⟩
      rw [hpreY 0 _ h, hpreM 0 t (by omega)]
      exact hM.tail t (by omega) (by omega)
    · have : x = Y.length := by omega
      rw [this, hl0]; omega
  have hsh : ∀ x, Y0.length < x → x < T.length → entry T 0 Y0.length < entry T 0 x := by
    intro x h1 h2
    have := hdeeper x h1 h2
    rw [hanchor0]; omega
  have hle0 : ∀ j, Y0.length ≤ j → j < T.length → le0 T Y0.length j := by
    intro j h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · exact ⟨by omega, by omega, Relation.ReflTransGen.refl⟩
    · exact H12Export.le0_root_of_shallow (by omega) hsh j h h2
  have hsrow : srow T Y.length = 1 := by
    unfold srow
    rw [if_neg (by rw [hl2]; omega), if_pos (by rw [hl1]; omega)]
  have hpar : hasParent T 1 Y.length :=
    H12Export.hasParent1_of_le0_witness (by omega)
      (hle0 Y.length (by omega) (by omega)).2.2
      (by rw [hanchor1, hl1]; exact hMe)
  have hnr1 : nextrel1 T Y0.length Y.length := by
    refine ⟨by omega, by omega, by omega, by rw [hanchor1, hl1]; exact hMe,
      hle0 Y.length (by omega) (by omega), ?_⟩
    rintro j ⟨hj0, hjle⟩
    rw [hl1]
    rcases Nat.lt_or_ge j Y.length with h | h
    · obtain ⟨t, rfl⟩ : ∃ t, j = Y0.length + t := ⟨j - Y0.length, by omega⟩
      have hlow : entry M 0 t < L + dl := by
        have hlt := rtg0_rec hjle.2.2 Y.length (by omega) (le_refl _)
        rw [hl0] at hlt
        rwa [hpreY 0 _ h, hpreM 0 t (by omega)] at hlt
      have hrec : ∀ i, t < i → i < M.length → entry M 0 t < entry M 0 i := by
        intro i hti hiM
        have hlt := rtg0_rec hjle.2.2 (Y0.length + i) (by omega) (by omega)
        rwa [hpreY 0 _ h, hpreM 0 t (by omega),
          hpreY 0 _ (by omega), hpreM 0 i hiM] at hlt
      rw [hpreY 1 _ h, hpreM 1 t (by omega)]
      exact hMy t (by omega) (by omega) hlow hrec
    · have : j = Y.length := by
        have := H12Export.rtg0_index_le hjle.2.2
        omega
      rw [this, hl1]
  have hj0 : parent T 1 Y.length = Y0.length :=
    hpar.unique (parent_nextR hpar) hnr1
  rw [L53.oper_unfold (j1 := Y.length) (i1 := 1) (j0 := Y0.length) (d0 := dl) (d1 := 0)
      (by omega) (by omega) (by rintro ⟨h, -, -⟩; rw [hl0] at h; omega)
      hsrow.symm hpar hj0.symm (by rw [if_pos (by omega), hl0, hanchor0]; omega)
      (by simp) n, Mtwd]
  have htk : T.take Y0.length = Y0 := by
    rw [hT, hY, List.append_assoc]
    exact List.take_left
  have hrlen : Y.length - Y0.length = M.length := by omega
  rw [htk, hrlen]
  simp only [Nat.mul_zero, ite_self, Nat.add_zero]
  congr 1
  apply List.flatMap_congr
  intro k _
  rw [← map_range'_shift_at (T := T) (M := M) (q := Y0.length) (k := dl * k)
    (fun i t ht => by
      rw [hpreY i _ (by omega), hpreM i t ht])]
  apply List.map_congr_left
  intro j hj
  have hjr := List.mem_range'_1.1 hj
  rw [if_pos (hle0 j (by omega) (by omega)), Nat.mul_comm k dl]

/-- ★ 塔が済めば内部アンカーで歩幅 `dl` の列を継げる。 -/
theorem snocYd_mem {Y0 M : TrioSeq} {L y dl : ℕ} (hY0ne : Y0 ≠ [])
    (hM : MidD (L + 1) M) (hMe : entry M 1 0 < y)
    (hMy : ∀ t, 1 ≤ t → t < M.length → entry M 0 t < L + dl →
      (∀ i, t < i → i < M.length → entry M 0 t < entry M 0 i) → y ≤ entry M 1 t)
    (hy : 1 ≤ y) (hdl : 1 ≤ dl) (htw : ∀ n, Mtwd dl Y0 M n ∈ W 0) :
    (Y0 ++ M) ++ [((L + dl, y, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_snocYd hY0ne hM hMe hMy hy hdl n]
  exact htw n

#print axioms oper_snocYd
#print axioms snocYd_mem

/-! ### シート行293 `X(1,1,0)(2,2,0)(3,2,0) = psi(W_w + psi_1(W_2^2))`

`N293 = (1,1,0)(2,2,0)` を歩幅 2 で積んだ塔が `W 0` に入れば行293 が出る。 -/

def N293 : TrioSeq := [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ)]

def R293 : TrioSeq := [(0, 0, 0), (1, 1, 1), (1, 1, 0), (2, 2, 0), (3, 2, 0)]

theorem MidD_N293 : MidD 2 N293 where
  ne := by simp [N293]
  col := by
    intro c hc
    simp only [N293, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> decide
  head := rfl
  head1 := le_refl 1
  tail := by
    intro j h1 h2
    simp only [N293, List.length_cons, List.length_nil] at h2
    have hj : j = 1 := by omega
    subst hj
    have hv : entry N293 0 1 = 2 := rfl
    omega
  mono := by
    intro c hc
    simp only [N293, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> decide

/-- ★ 塔 `Q ++ N293 ++ N293↑2 ++ N293↑4 ++ ...` が済めば行293。 -/
theorem R293_mem_of_tower (htw : ∀ n, Mtwd 2 Q N293 n ∈ W 0) : R293 ∈ W 0 := by
  have h : R293 = (Q ++ N293) ++ [((1 + 2, 2, 0) : ℕ × ℕ × ℕ)] := by
    simp [R293, Q, N293]
  rw [h]
  refine snocYd_mem (L := 1) (y := 2) (dl := 2) (by simp [Q]) MidD_N293 ?_ ?_
    (by omega) (by omega) htw
  · show (1 : ℕ) < 2
    omega
  · intro t h1 h2 _ _
    simp only [N293, List.length_cons, List.length_nil] at h2
    have ht : t = 1 := by omega
    subst ht
    have hv : entry N293 1 1 = 2 := rfl
    omega

#print axioms R293_mem_of_tower

/-! ### ランクを消す（`Lw`）と、再継ぎ可能セグメント `Seg`

`Lv r a A` の `r` は定義を停止させるための燃料で、`Lv r a A → r ≥ a` が成り立つ。
そのため `hre` の仮定 `Lv r (a+s) A'` は `s > r - a` では空になり、ランクは上げられない
（`Lv r a A → Lv (r+1) a A` は偽: `Lv 1 1 A → Lv 0 1 A` は `False` になる）。

**逃げ道**: ランクを ∃ で包んだ `Lw c A := ∃ r, Lv r c A` を使う。
`Lv r' c A' → Lw c A'` は自明なので、「`Lw` の頭すべてに継げる」という**定理**があれば、
それは任意のランクの記録の `hre` として使える。`Lv_snoc` はまさにその形。 -/

def Lw (c : ℕ) (A : TrioSeq) : Prop := ∃ r, Lv r c A

theorem Lw_Aok {c : ℕ} {A : TrioSeq} (h : Lw c A) : Aok A := by
  obtain ⟨r, hr⟩ := h
  exact Lv_Aok r c A hr

theorem Lw_mem {c : ℕ} {A : TrioSeq} (h : Lw c A) : A ∈ W 0 := (Lw_Aok h).mem

theorem Lw_Q : Lw 0 Q := ⟨0, (Aok_Q : Aok Q), rfl⟩

/-- ★ 高さ `a+1` から始まる、`Lw` の頭ならどこへでも（シフトして）継げるセグメント。 -/
structure Seg (a : ℕ) (M : TrioSeq) : Prop where
  mid : MidD (a + 2) M
  head1 : entry M 1 0 < 2
  reapp : ∀ (s : ℕ) (A' : TrioSeq), Lw (a + s) A' → A' ++ shiftr01 s 0 M ∈ W 0

theorem Seg_shift {a : ℕ} {M : TrioSeq} (hS : Seg a M) (u : ℕ) :
    Seg (a + u) (shiftr01 u 0 M) where
  mid := by
    have h := MidD_shift hS.mid u
    rwa [show a + 2 + u = a + u + 2 from by omega] at h
  head1 := by
    rw [entry_shift1 (List.length_pos_iff.mpr hS.mid.ne)]
    exact hS.head1
  reapp := by
    intro s A' hA'
    rw [shiftr01_add0]
    refine hS.reapp (u + s) A' ?_
    rwa [show a + (u + s) = a + u + s from by omega]

/-- ★★ セグメントの塔。ランクは 1 段ごとに上がるが、`Seg.reapp` は
`Lw`（ランクは ∃）の頭に対する主張なので、どの段でも使える。 -/
theorem Lw_tower {a : ℕ} {A0 M : TrioSeq} (hS : Seg a M) (h0 : Lw a A0) :
    ∀ n : ℕ, Lw (a + n) (Mtw A0 M n)
  | 0 => by simpa [Mtw_zero] using h0
  | (n + 1) => by
      obtain ⟨r, hr⟩ := Lw_tower hS h0 n
      rw [Mtw_succ]
      have hmem : Mtw A0 M n ++ shiftr01 n 0 M ∈ W 0 := hS.reapp n _ ⟨r, hr⟩
      have hMn : MidD (a + n + 2) (shiftr01 n 0 M) := by
        have h := MidD_shift hS.mid n
        rwa [show a + 2 + n = a + n + 2 from by omega] at h
      refine ⟨r + 1, Aok_append_Mid (by omega) (Lv_Aok _ _ _ hr) hMn hmem,
        Mtw A0 M n, shiftr01 n 0 M, rfl, hr, hMn, ?_⟩
      intro t A' hA'
      rw [shiftr01_add0]
      refine hS.reapp (n + t) A' ⟨r, ?_⟩
      rwa [show a + (n + t) = a + n + t from by omega]

theorem Lw_tower_mem {a : ℕ} {A0 M : TrioSeq} (hS : Seg a M) (h0 : Lw a A0) (n : ℕ) :
    Mtw A0 M n ∈ W 0 := Lw_mem (Lw_tower hS h0 n)

/-- ★★ セグメントの直後に `(a+2,2,0)` を継げる（内部アンカー、歩幅 1）。 -/
theorem Seg_snoc2 {a : ℕ} {A0 M : TrioSeq} (hS : Seg a M) (h0 : Lw a A0) :
    (A0 ++ M) ++ [((a + 2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  snocY_mem (L := a + 1) (y := 2) (Lw_Aok h0).ne hS.mid hS.head1 (by omega)
    (Lw_tower_mem hS h0)

/-- `(a+1,1,0)` は `Seg`（再継ぎは `Lv_snoc`）。 -/
theorem Seg_one (a : ℕ) : Seg a [((a + 1, 1, 0) : ℕ × ℕ × ℕ)] where
  mid := MidD_one (a + 1) (by omega)
  head1 := by show (1 : ℕ) < 2; omega
  reapp := by
    intro s A' hA'
    obtain ⟨r, hr⟩ := hA'
    have h := Lv_snoc r (a + s) A' hr
    have heq : shiftr01 s 0 [((a + 1, 1, 0) : ℕ × ℕ × ℕ)]
        = [((a + s + 1, 1, 0) : ℕ × ℕ × ℕ)] := by
      simp only [shiftr01, List.map_cons, List.map_nil]
      congr 2
      omega
    rw [heq]
    exact h

/-- **検算**: `Lv_snoc2` は `Seg_one` ＋ `Seg_snoc2` の特別な場合。 -/
theorem Lv_snoc2' (r a : ℕ) (A : TrioSeq) (hA : Lv r a A) :
    A ++ [((a + 1, 1, 0) : ℕ × ℕ × ℕ), ((a + 2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := Seg_snoc2 (Seg_one a) (A0 := A) ⟨r, hA⟩
  simpa using h

#print axioms Lw_tower
#print axioms Seg_snoc2
#print axioms Lv_snoc2'

/-! ### ★★ `(a+2,2,0)` を継いだ頭も吊るせる（`hang2`）

`Lv` の梯子は「最後のセグメントの頭の高さ」＝レベルなので、`(a+2,2,0)` を継いだ
行列のレベルは `a+2` になってほしいが、その記録には `(a+2,2,0)` の再継ぎ
（＝任意の `Lw` の頭に `(·,2,0)` を継ぐ）が要り、それは循環する。

ここでは記録を作らず、**吊るしだけ**を直接示す。`blkD_memS` の中身 `Mid` を
`(a+2,2,0)` そのものにして、`P s X := X が「Lw の頭 ++ Seg」に分かれる` を不変量に取る。
`hbase` は `Seg_snoc2`、`hclose` は「セグメントを `Blk` で伸ばす」で閉じる。 -/

theorem MidD_col (d v : ℕ) (hd : 1 ≤ d) (hv : 1 ≤ v) :
    MidD (d + 1) [((d, v, 0) : ℕ × ℕ × ℕ)] := by
  refine ⟨by simp, ?_, rfl, hv, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    exact hd
  · intro j h1 h2
    simp only [List.length_cons, List.length_nil] at h2
    omega
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    dsimp only
    omega

theorem shift_col (d v s : ℕ) :
    shiftr01 s 0 [((d, v, 0) : ℕ × ℕ × ℕ)] = [((d + s, v, 0) : ℕ × ℕ × ℕ)] := by
  simp [shiftr01]

/-- `Seg` の頭は空でない。 -/
theorem Seg_ne {a : ℕ} {M : TrioSeq} (hS : Seg a M) : 0 < M.length :=
  List.length_pos_iff.mpr hS.mid.ne

theorem hang2 {a : ℕ} {A0 M : TrioSeq} (hS : Seg a M) (h0 : Lw a A0)
    (B : TrioSeq) (hB : Bok B) :
    ((A0 ++ M) ++ [((a + 2, 2, 0) : ℕ × ℕ × ℕ)]) ++ shiftr01 (a + 3) 0 B ∈ W 0 := by
  have hMdD : MidD (a + 3) [((a + 2, 2, 0) : ℕ × ℕ × ℕ)] := by
    have h := MidD_col (a + 2) 2 (by omega) (by omega)
    rwa [show a + 2 + 1 = a + 3 from by omega] at h
  have hbase : ∀ (s : ℕ) (X : TrioSeq), Aok X →
      (∃ X0 M', X = X0 ++ M' ∧ Lw (a + s) X0 ∧ Seg (a + s) M') →
      X ++ shiftr01 s 0 [((a + 2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
    rintro s X - ⟨X0, M', rfl, hX0, hM'⟩
    rw [shift_col]
    have h := Seg_snoc2 hM' hX0
    rwa [show a + s + 2 = a + 2 + s from by omega] at h
  have hclose : ∀ (s : ℕ) (X C' : TrioSeq), Aok X →
      (∃ X0 M', X = X0 ++ M' ∧ Lw (a + s) X0 ∧ Seg (a + s) M') → Mono C' →
      (∀ (t : ℕ) (Y : TrioSeq), Aok Y →
        (∃ Y0 M'', Y = Y0 ++ M'' ∧ Lw (a + t) Y0 ∧ Seg (a + t) M'') →
        Y ++ BlkD (a + 3 + t) (shiftr01 t 0 [((a + 2, 2, 0) : ℕ × ℕ × ℕ)]) C' ∈ W 0) →
      (∃ Z0 M'',
        X ++ BlkD (a + 3 + s) (shiftr01 s 0 [((a + 2, 2, 0) : ℕ × ℕ × ℕ)]) C'
          = Z0 ++ M'' ∧ Lw (a + s) Z0 ∧ Seg (a + s) M'') := by
    rintro s X C' - ⟨X0, M', rfl, hX0, hM'⟩ hmoC' hIH
    set Blk : TrioSeq :=
      BlkD (a + 3 + s) (shiftr01 s 0 [((a + 2, 2, 0) : ℕ × ℕ × ℕ)]) C' with hBlk
    have hMs : MidD (a + 3 + s) (shiftr01 s 0 [((a + 2, 2, 0) : ℕ × ℕ × ℕ)]) :=
      MidD_shift hMdD s
    have hBlkcol : ∀ c ∈ Blk, a + s + 2 ≤ c.1 := by
      intro c hc
      rcases List.mem_append.mp hc with h | h
      · rw [shift_col] at h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        subst h
        dsimp only
        omega
      · have := shiftD_col c h
        omega
    have hBlkmo : Mono Blk := BlkD_mono hMs.mono hmoC'
    refine ⟨X0, M' ++ Blk, by rw [List.append_assoc], hX0, ?_, ?_, ?_⟩
    · exact MidD_append hM'.mid hBlkcol hBlkmo
    · rw [entry_append_left (Seg_ne hM')]
      exact hM'.head1
    · intro u A' hA'
      rw [shiftr01_append0]
      have h1 : A' ++ shiftr01 u 0 M' ∈ W 0 := hM'.reapp u A' hA'
      have hSu : Seg (a + s + u) (shiftr01 u 0 M') := Seg_shift hM' u
      have hAok : Aok (A' ++ shiftr01 u 0 M') :=
        Aok_append_Mid (by omega) (Lw_Aok hA') hSu.mid h1
      have hP : ∃ Y0 M'', A' ++ shiftr01 u 0 M' = Y0 ++ M'' ∧
          Lw (a + (s + u)) Y0 ∧ Seg (a + (s + u)) M'' := by
        refine ⟨A', shiftr01 u 0 M', rfl, ?_, ?_⟩
        · rwa [show a + (s + u) = a + s + u from by omega]
        · rwa [show a + (s + u) = a + s + u from by omega]
      have h2 := hIH (s + u) _ hAok hP
      have heq : shiftr01 u 0 Blk
          = BlkD (a + 3 + (s + u))
              (shiftr01 (s + u) 0 [((a + 2, 2, 0) : ℕ × ℕ × ℕ)]) C' := by
        rw [hBlk, BlkD, BlkD, shiftr01_append0, shiftr01_add0, shiftr01_add0]
        congr 2
        omega
      rw [heq, ← List.append_assoc]
      exact h2
  have hmemAM : A0 ++ M ∈ W 0 := by
    have h := hS.reapp 0 A0 (by simpa using h0)
    simpa using h
  have hAokAM : Aok (A0 ++ M) := Aok_append_Mid (by omega) (Lw_Aok h0) hS.mid hmemAM
  have hP0 : ∃ X0 M', A0 ++ M = X0 ++ M' ∧ Lw (a + 0) X0 ∧ Seg (a + 0) M' := by
    refine ⟨A0, M, rfl, ?_, ?_⟩
    · simpa using h0
    · simpa using hS
  have hkey := blkD_memS (d := a + 3) (by omega) [((a + 2, 2, 0) : ℕ × ℕ × ℕ)] hMdD
    hbase hclose B hB.mem hB.zroot hB.mono hB.root 0 (A0 ++ M) hAokAM hP0
  rw [BlkD_app] at hkey
  simpa using hkey

#print axioms hang2

/-! ### `hang2` の系: 塔と `(a+3,1,0)` の継ぎ足し -/

theorem Lw_Ancd {c : ℕ} {A : TrioSeq} (h : Lw c A) : Ancd (c + 1) A := by
  obtain ⟨r, hr⟩ := h
  exact Lv_Ancd r c A hr

theorem hang2_Aok {a : ℕ} {A0 M : TrioSeq} (hS : Seg a M) (h0 : Lw a A0) :
    Aok ((A0 ++ M) ++ [((a + 2, 2, 0) : ℕ × ℕ × ℕ)]) := by
  have hmemAM : A0 ++ M ∈ W 0 := by
    have h := hS.reapp 0 A0 (by simpa using h0)
    simpa using h
  have hAokAM : Aok (A0 ++ M) := Aok_append_Mid (by omega) (Lw_Aok h0) hS.mid hmemAM
  have hMdD : MidD (a + 3) [((a + 2, 2, 0) : ℕ × ℕ × ℕ)] := by
    have h := MidD_col (a + 2) 2 (by omega) (by omega)
    rwa [show a + 2 + 1 = a + 3 from by omega] at h
  exact Aok_append_Mid (by omega) hAokAM hMdD (Seg_snoc2 hS h0)

theorem hang2_Ancd {a : ℕ} {A0 M : TrioSeq} (hS : Seg a M) (h0 : Lw a A0) :
    Ancd (a + 3) ((A0 ++ M) ++ [((a + 2, 2, 0) : ℕ × ℕ × ℕ)]) := by
  set c : ℕ × ℕ × ℕ := ((a + 2, 2, 0) : ℕ × ℕ × ℕ) with hc
  set Y : TrioSeq := (A0 ++ M) ++ [c] with hY
  have hL0 : 0 < A0.length := List.length_pos_iff.mpr (Lw_Aok h0).ne
  have hLM : 0 < M.length := Seg_ne hS
  have hPlen : (A0 ++ M).length = A0.length + M.length := by simp
  have hYlen : Y.length = A0.length + M.length + 1 := by rw [hY]; simp; omega
  have hpre : ∀ i j, j < (A0 ++ M).length → entry Y i j = entry (A0 ++ M) i j :=
    fun i j hj => entry_append_left hj
  have hlast := entry_append_last (P := A0 ++ M) (c := c)
  have hl0 : entry Y 0 (A0 ++ M).length = a + 2 := hlast.1
  have hl1 : entry Y 1 (A0 ++ M).length = 2 := hlast.2.1
  have hMh0 : entry M 0 0 = a + 1 := by have := hS.mid.head; omega
  intro j hj0 hjl hlt hrec
  rcases Nat.lt_or_ge j (A0 ++ M).length with hj | hj
  · -- j は A0 ++ M の中
    rcases Nat.lt_or_ge j A0.length with hjA | hjA
    · -- A0 の中: M の頭より低いことが記録最小から出る
      have hcmp : entry Y 0 j < entry Y 0 A0.length :=
        hrec A0.length hjA (by omega)
      have hMhY : entry Y 0 A0.length = a + 1 := by
        rw [hpre 0 A0.length (by omega),
          show A0.length = A0.length + 0 from rfl, entry_append_right, hMh0]
      rw [hMhY] at hcmp
      rw [hpre 0 j (by omega), entry_append_left hjA] at hcmp
      rw [hpre 1 j (by omega), entry_append_left hjA]
      refine Lw_Ancd h0 j hj0 hjA hcmp ?_
      intro i hi1 hi2
      have h := hrec i hi1 (by omega)
      rw [hpre 0 j (by omega), entry_append_left hjA, hpre 0 i (by omega),
        entry_append_left hi2] at h
      exact h
    · -- M の中
      obtain ⟨t, rfl⟩ : ∃ t, j = A0.length + t := ⟨j - A0.length, by omega⟩
      have ht : t < M.length := by omega
      rw [hpre 1 _ (by omega), entry_append_right]
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · exact hS.mid.head1
      · exfalso
        have hdeep := hS.mid.tail t htpos ht
        have h := hrec (A0 ++ M).length (by omega) (by omega)
        rw [hpre 0 _ (by omega), entry_append_right, hl0] at h
        omega
  · -- j は末尾
    have : j = (A0 ++ M).length := by omega
    rw [this, hl1]
    omega

theorem hang2_tw {a : ℕ} {A0 M : TrioSeq} (hS : Seg a M) (h0 : Lw a A0) :
    ∀ n : ℕ, TwD (a + 3) ((A0 ++ M) ++ [((a + 2, 2, 0) : ℕ × ℕ × ℕ)]) n ∈ W 0
  | 0 => by simpa [TwD] using W_nil 0
  | (n + 1) => by
      have hAok := hang2_Aok hS h0
      rw [TwD_succ]
      exact hang2 hS h0 _
        ⟨hang2_tw hS h0 n, TwD_zroot (by omega) hAok.zroot n, TwD_mono hAok.mono n,
          TwD_root hAok.ne hAok.deep.1 n⟩

/-- ★★ `(a+2,2,0)` の上に `(a+3,1,0)` を継げる。 -/
theorem hang2_snoc {a : ℕ} {A0 M : TrioSeq} (hS : Seg a M) (h0 : Lw a A0) :
    ((A0 ++ M) ++ [((a + 2, 2, 0) : ℕ × ℕ × ℕ)]) ++ [((a + 3, 1, 0) : ℕ × ℕ × ℕ)]
      ∈ W 0 := by
  have hAok := hang2_Aok hS h0
  exact snocd_mem (by omega) hAok.ne hAok.deep hAok.zroot (hang2_Ancd hS h0)
    (hang2_tw hS h0)

#print axioms hang2_snoc

/-- **検算**: 行292 の上に `(3,1,0)` を継げる（行293 の塔の第 1 段）。 -/
theorem R292_snoc310 : R292 ++ [((3, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := hang2_snoc (a := 0) (A0 := Q) (M := [((1, 1, 0) : ℕ × ℕ × ℕ)])
    (Seg_one 0) Lw_Q
  have heq : ((Q ++ [((1, 1, 0) : ℕ × ℕ × ℕ)]) ++ [((0 + 2, 2, 0) : ℕ × ℕ × ℕ)])
      ++ [((0 + 3, 1, 0) : ℕ × ℕ × ℕ)] = R292 ++ [((3, 1, 0) : ℕ × ℕ × ℕ)] := by
    simp [R292, Q]
  rwa [heq] at h

#print axioms R292_snoc310

/-! ### 行293 のブロック `N293 = (1,1,0)(2,2,0)` は `Seg`

再継ぎ性はちょうど `Lv_snoc2`。したがって
`Lw_tower` で**歩幅 1** の塔 `Mtw Q N293 n` は全段 `Lw` に入る。

行293 が要るのは**歩幅 2** の塔 `Mtwd 2 Q N293 n`（チャットでは `T_n`）。歩幅 `dl` の塔は
段ごとにレベルが `dl` 上がる必要があるが、`Lv` のレベルは
「最後のセグメントの頭の高さ」なので 1 しか上がらない。この 1 のずれが
`LADDER-PROBLEM.md` §3 の (G2)。 -/

theorem Seg_N293 : Seg 0 N293 where
  mid := MidD_N293
  head1 := by show (1 : ℕ) < 2; omega
  reapp := by
    intro s A' hA'
    obtain ⟨r, hr⟩ := hA'
    have h := Lv_snoc2 r (0 + s) A' hr
    have heq : shiftr01 s 0 N293
        = [((0 + s + 1, 1, 0) : ℕ × ℕ × ℕ), ((0 + s + 2, 2, 0) : ℕ × ℕ × ℕ)] := by
      simp only [N293, shiftr01, List.map_cons, List.map_nil, List.cons.injEq,
        Prod.mk.injEq, and_true]
      omega
    rw [heq]
    exact h

/-- 歩幅 1 の塔なら全段 `Lw`。（行293 に要るのは歩幅 2。） -/
theorem Mtw_N293_mem (n : ℕ) : Mtw Q N293 n ∈ W 0 :=
  Lw_tower_mem Seg_N293 Lw_Q n

#print axioms Seg_N293
#print axioms Mtw_N293_mem

/-! ### 行292 と 行293 の間を埋める

`X = (0,0,0)(1,1,1)(1,1,0)(2,2,0)` に 1 列継いだ 8 個。順序は

```
X(1,0,0) < X(1,1,0) < X(2,0,0) < X(2,1,0) < X(2,2,0) < X(3,0,0) < X(3,1,0) < X(3,2,0)
                                                                              = 行293
```

切り方は 3 族:

```
bad root 0（X 全体を写す）   (1,0,0) (1,1,0) (2,1,0) (3,1,0)   delta 0,1,2,3
bad root 2（尻尾を写す）     (2,0,0) (2,2,0) (3,2,0)           delta 0,1,2
bad root 3（(2,2,0) を写す） (3,0,0)                           delta 0
```
-/

theorem R292_eq_QN : R292 = Q ++ N293 := by simp [R292, Q, N293]

theorem Aok_R292 : Aok R292 := by
  rw [R292_eq_QN]
  exact Aok_append_Mid (by omega) Aok_Q MidD_N293 (by rw [← R292_eq_QN]; exact R292_mem)

/-- `X` はレベル 0 の土台。 -/
theorem Lv0_R292 : Lv 1 0 R292 := Aok_R292

/-- `X` はレベル 1 の土台（最後のセグメントは `(1,1,0)(2,2,0)`、再継ぎは `Lv_snoc2`）。 -/
theorem Lv1_R292 : Lv 1 1 R292 := by
  have hre : ∀ (t : ℕ) (A' : TrioSeq), Lv 0 (0 + t) A' →
      A' ++ shiftr01 t 0 N293 ∈ W 0 := by
    intro t A' hA'
    obtain ⟨hAok, ht⟩ := hA'
    have ht0 : t = 0 := by omega
    subst ht0
    have h := Lv_snoc2 1 0 A' hAok
    simpa [N293] using h
  have h := Lv_shift (r := 0) (a := 0) MidD_N293 hre 0 (A' := Q)
    (by exact ⟨(Aok_Q : Aok Q), rfl⟩)
  simpa [R292_eq_QN] using h

/-- ★ `X(1,1,0)`（族 A・delta 1）。 -/
theorem R292_snoc110 : R292 ++ [((1, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  Lv_snoc 1 0 R292 Lv0_R292

/-- ★ `X(2,1,0)`（族 A・delta 2）。 -/
theorem R292_snoc210 : R292 ++ [((2, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  Lv_snoc 1 1 R292 Lv1_R292

#print axioms R292_snoc110
#print axioms R292_snoc210

/-! #### 族 B の delta 0 と 族 C: `X(2,0,0)` と `X(3,0,0)`

どちらも末尾が `(h,0,0)` なので `snoc_flat`。写しは **verbatim**（delta 0）。 -/

theorem copies_snoc (A : TrioSeq) (n : ℕ) : copies A (n + 1) = copies A n ++ A := by
  simp [copies, List.range_succ, List.flatMap_append]

/-- `A` が `Aok` なら `(1,1,0)(2,2,0)` を何個でも継げる。 -/
theorem Aok_append_copies_N293 : ∀ (n : ℕ) (A : TrioSeq), Aok A →
    Aok (A ++ copies N293 n)
  | 0, A, hA => by simpa [copies] using hA
  | (n + 1), A, hA => by
      have hmem : A ++ N293 ∈ W 0 := by
        have h := Lv_snoc2 1 0 A hA
        simpa [N293] using h
      have hAok : Aok (A ++ N293) := Aok_append_Mid (by omega) hA MidD_N293 hmem
      have h := Aok_append_copies_N293 n (A ++ N293) hAok
      rw [copies_succ, ← List.append_assoc]
      exact h

/-- `(1,1,0)(2,2,0)^k`。 -/
def Rep220 (k : ℕ) : TrioSeq :=
  [((1, 1, 0) : ℕ × ℕ × ℕ)] ++ copies [((2, 2, 0) : ℕ × ℕ × ℕ)] k

theorem Rep220_zero : Rep220 0 = [((1, 1, 0) : ℕ × ℕ × ℕ)] := by simp [Rep220, copies]

theorem Rep220_succ (k : ℕ) :
    Rep220 (k + 1) = Rep220 k ++ [((2, 2, 0) : ℕ × ℕ × ℕ)] := by
  simp [Rep220, copies_snoc, List.append_assoc]

theorem Rep220_mid : ∀ k, MidD 2 (Rep220 k)
  | 0 => by rw [Rep220_zero]; exact MidD_one 1 (by omega)
  | (k + 1) => by
      rw [Rep220_succ]
      refine MidD_append (Rep220_mid k) ?_ ?_ <;> intro c hc <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc <;> subst hc <;> decide

theorem Rep220_head : ∀ k, entry (Rep220 k) 1 0 = 1
  | 0 => by rw [Rep220_zero]; rfl
  | (k + 1) => by
      rw [Rep220_succ, entry_append_left (List.length_pos_iff.mpr (Rep220_mid k).ne)]
      exact Rep220_head k

/-- ★ `(1,1,0)(2,2,0)^k` は `Seg`（再継ぎは `Seg_snoc2` の反復）。 -/
theorem Seg_Rep220 : ∀ k, Seg 0 (Rep220 k)
  | 0 => by rw [Rep220_zero]; simpa using Seg_one 0
  | (k + 1) => by
      refine ⟨Rep220_mid (k + 1), by rw [Rep220_head]; omega, ?_⟩
      intro s A' hA'
      rw [Rep220_succ, shiftr01_append0, ← List.append_assoc]
      have hSs : Seg (0 + s) (shiftr01 s 0 (Rep220 k)) := Seg_shift (Seg_Rep220 k) s
      have h := Seg_snoc2 hSs (A0 := A') (by simpa using hA')
      have heq : shiftr01 s 0 [((2, 2, 0) : ℕ × ℕ × ℕ)]
          = [((0 + s + 2, 2, 0) : ℕ × ℕ × ℕ)] := by
        simp only [shiftr01, List.map_cons, List.map_nil]
        congr 2
        omega
      rw [heq]
      exact h

theorem Q_append_Rep220 (k : ℕ) : Q ++ Rep220 k ∈ W 0 := by
  have h := (Seg_Rep220 k).reapp 0 Q (by simpa using Lw_Q)
  simpa using h

#print axioms Seg_Rep220

theorem R292_len4 : R292.length = 4 := by simp [R292]

/-- ★ `X(2,0,0)`（族 B・delta 0）。写しは尻尾 `(1,1,0)(2,2,0)` の verbatim 反復。 -/
theorem R292_snoc200 : R292 ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hpar : hasParent (R292 ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) 0 R292.length := by
    rw [R292_len4, hasParent_zero_iff (by simp [R292])]
    exact ⟨2, by omega, by decide⟩
  have hnr : nextrel0 (R292 ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) 2 R292.length := by
    rw [R292_len4]
    refine ⟨by simp [R292], by simp [R292], by omega, by decide, ?_⟩
    intro j hj
    have hj3 : j = 3 := by omega
    subst hj3
    decide
  refine snoc_flat (A := R292) (j0 := 2) (by simp [R292]) (by decide) rfl rfl hpar
    (hpar.unique (parent_nextR hpar) (by rw [R292_len4] at hnr ⊢; exact hnr)) ?_
  intro n
  have h1 : R292.take 2 = Q := by simp [R292, Q]
  have h2 : R292.drop 2 = N293 := by simp [R292, N293]
  rw [h1, h2]
  exact (Aok_append_copies_N293 n Q Aok_Q).mem

/-- ★ `X(3,0,0)`（族 C）。写しは `(2,2,0)` の verbatim 反復。 -/
theorem R292_snoc300 : R292 ++ [((3, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hpar : hasParent (R292 ++ [((3, 0, 0) : ℕ × ℕ × ℕ)]) 0 R292.length := by
    rw [R292_len4, hasParent_zero_iff (by simp [R292])]
    exact ⟨3, by omega, by decide⟩
  have hnr : nextrel0 (R292 ++ [((3, 0, 0) : ℕ × ℕ × ℕ)]) 3 R292.length := by
    rw [R292_len4]
    refine ⟨by simp [R292], by simp [R292], by omega, by decide, ?_⟩
    intro j hj
    omega
  refine snoc_flat (A := R292) (j0 := 3) (by simp [R292]) (by decide) rfl rfl hpar
    (hpar.unique (parent_nextR hpar) (by rw [R292_len4] at hnr ⊢; exact hnr)) ?_
  intro n
  have h1 : R292.take 3 ++ (List.range n).flatMap
      (fun _ => R292.drop 3) = Q ++ Rep220 n := by
    have hd : R292.drop 3 = [((2, 2, 0) : ℕ × ℕ × ℕ)] := by simp [R292]
    have ht : R292.take 3 = Q ++ [((1, 1, 0) : ℕ × ℕ × ℕ)] := by simp [R292, Q]
    rw [hd, ht, Rep220, ← List.append_assoc]
    rfl
  rw [h1]
  exact Q_append_Rep220 n

#print axioms R292_snoc200
#print axioms R292_snoc300

/-! #### 族 A の delta 0: `X(1,0,0)` -/

theorem copies_R292_mem : ∀ n, copies R292 n ∈ W 0
  | 0 => by simpa [copies] using W_nil 0
  | (n + 1) => by
      rw [copies_snoc]
      refine W_add (copies_R292_mem n) R292_mem ?_
      intro p _
      have h : entry R292 0 0 = 0 := rfl
      omega

/-- ★ `X(1,0,0)`（族 A・delta 0）。写しは `X` 全体の verbatim 反復。 -/
theorem R292_snoc100 : R292 ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hpar : hasParent (R292 ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) 0 R292.length := by
    rw [R292_len4, hasParent_zero_iff (by simp [R292])]
    exact ⟨0, by omega, by decide⟩
  have hnr : nextrel0 (R292 ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) 0 R292.length := by
    rw [R292_len4]
    refine ⟨by simp [R292], by simp [R292], by omega, by decide, ?_⟩
    intro j hj
    have hj3 : j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj3 with rfl | rfl | rfl <;> decide
  refine snoc_flat (A := R292) (j0 := 0) (by simp [R292]) (by decide) rfl rfl hpar
    (hpar.unique (parent_nextR hpar) (by rw [R292_len4] at hnr ⊢; exact hnr)) ?_
  intro n
  simpa [copies] using copies_R292_mem n

#print axioms R292_snoc100

/-- ★ `X(2,2,0)`（族 B・delta 1）。`Seg_snoc2` の直接の帰結。 -/
theorem R292_snoc220 : R292 ++ [((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := Seg_snoc2 Seg_N293 Lw_Q
  rw [R292_eq_QN]
  simpa using h

#print axioms R292_snoc220

/-! #### まとめ: 行292 と 行293 の間の 8 個

```
X(1,0,0)  R292_snoc100   ✅   族 A delta 0
X(1,1,0)  R292_snoc110   ✅   族 A delta 1
X(2,0,0)  R292_snoc200   ✅   族 B delta 0
X(2,1,0)  R292_snoc210   ✅   族 A delta 2
X(2,2,0)  R292_snoc220   ✅   族 B delta 1
X(3,0,0)  R292_snoc300   ✅   族 C
X(3,1,0)  R292_snoc310   ✅   族 A delta 3
X(3,2,0)  = 行293        ❌   族 B delta 2   ← 残り 1 個
```
-/

/-! ## ★★★ セグメントの本数で階層を作る（`Hd k c Z`）

これまでの `Lv` は**高さ**で階層を作っていたので、再継ぎ性が `Lv` を
高さ `a+s`（上）で参照し、定義できなかった。

**本数 `k` で階層を作る**と、再継ぎ性が参照するのは `Hd k`（同じ `k`・高さは上）だけ
なので、`k` についての構造再帰で定義できる。

```
Hd 0 c Z = Lw c Z                            レベル c の土台
Hd (k+1) c Z = Z0 ++ N,  Hd k c Z0,
               N の 1 列目の高さ = c+k+1,
               N は Hd k の頭すべてに（ずらして）継げる
```

`Hd k c Z` なら高さ `c+k+1` にブロックを吊るせる。 -/

def Hd : ℕ → ℕ → TrioSeq → Prop
  | 0, c, Z => Lw c Z
  | (k + 1), c, Z => ∃ Z0 N : TrioSeq, Z = Z0 ++ N ∧ Hd k c Z0 ∧
      MidD (c + k + 2) N ∧ (k = 0 → entry N 1 0 < 2) ∧
      (∀ (u : ℕ) (Y : TrioSeq), Hd k (c + u) Y → Y ++ shiftr01 u 0 N ∈ W 0)

theorem Hd_Aok : ∀ (k c : ℕ) (Z : TrioSeq), Hd k c Z → Aok Z
  | 0, c, Z, h => Lw_Aok h
  | (k + 1), c, Z, h => by
      obtain ⟨Z0, N, rfl, h0, hN, hN1, hre⟩ := h
      have hmem : Z0 ++ N ∈ W 0 := by
        have := hre 0 Z0 (by simpa using h0)
        simpa using this
      exact Aok_append_Mid (by omega) (Hd_Aok k c Z0 h0) hN hmem

theorem Hd_mem {k c : ℕ} {Z : TrioSeq} (h : Hd k c Z) : Z ∈ W 0 := (Hd_Aok k c Z h).mem

theorem Hd_Ancd : ∀ (k c : ℕ) (Z : TrioSeq), Hd k c Z → Ancd (c + k + 1) Z
  | 0, c, Z, h => by simpa using Lw_Ancd h
  | (k + 1), c, Z, h => by
      obtain ⟨Z0, N, rfl, h0, hN, hN1, hre⟩ := h
      have hZ0ok : Aok Z0 := Hd_Aok k c Z0 h0
      have hZ0len : 0 < Z0.length := List.length_pos_iff.mpr hZ0ok.ne
      have hNlen : 0 < N.length := List.length_pos_iff.mpr hN.ne
      have hhead0 : entry (Z0 ++ N) 0 Z0.length = entry N 0 0 := by
        rw [show Z0.length = Z0.length + 0 from rfl, entry_append_right]
      have hhead1 : entry (Z0 ++ N) 1 Z0.length = entry N 1 0 := by
        rw [show Z0.length = Z0.length + 0 from rfl, entry_append_right]
      have hNh : entry N 0 0 = c + k + 1 := by have := hN.head; omega
      intro j hj0 hjl hlt hrec
      have hlen : (Z0 ++ N).length = Z0.length + N.length := by simp
      rcases Nat.lt_trichotomy j Z0.length with hj | hj | hj
      · have hcmp : entry (Z0 ++ N) 0 j < entry (Z0 ++ N) 0 Z0.length :=
          hrec Z0.length hj (by omega)
        rw [hhead0, hNh] at hcmp
        rw [entry_append_left hj] at hcmp ⊢
        refine Hd_Ancd k c Z0 h0 j hj0 hj (by omega) ?_
        intro i hi1 hi2
        have := hrec i hi1 (by omega)
        rw [entry_append_left hj, entry_append_left hi2] at this
        exact this
      · subst hj
        rw [hhead1]
        exact hN.head1
      · exfalso
        obtain ⟨t, rfl⟩ : ∃ t, j = Z0.length + t := ⟨j - Z0.length, by omega⟩
        rw [entry_append_right] at hlt
        have := hN.tail t (by omega) (by omega)
        omega

#print axioms Hd_Ancd

/-- ★ `Hd k` は「高さ `c+k+1` 以上のブロックを継ぐ」で閉じる。
`blkD_memS` の `hclose` の中身。 -/
theorem Hd_close : ∀ (k c : ℕ) (Y Blk : TrioSeq), Hd k c Y →
    (∀ x ∈ Blk, c + k + 1 ≤ x.1) → Mono Blk →
    (∀ (t : ℕ) (Y' : TrioSeq), Hd k (c + t) Y' → Y' ++ shiftr01 t 0 Blk ∈ W 0) →
    Hd k c (Y ++ Blk)
  | 0, c, Y, Blk, hY, hBcol, hBmo, hre => by
      -- `Hd 0 c Y = Lw c Y`。Lv の記録の最後のセグメントを `Blk` で伸ばす。
      obtain ⟨r, hr⟩ := hY
      have hmem : Y ++ Blk ∈ W 0 := by
        have := hre 0 Y ⟨r, by simpa using hr⟩
        simpa using this
      have hYok : Aok Y := Lv_Aok r c Y hr
      match c, hr with
      | 0, hr =>
          refine ⟨r, ?_⟩
          have hAok : Aok (Y ++ Blk) := by
            refine ⟨hmem, by simp [List.append_eq_nil_iff, hYok.ne], ?_, ?_, ?_⟩
            · refine ⟨?_, ?_⟩
              · rw [entry_append_left (List.length_pos_iff.mpr hYok.ne)]
                exact hYok.deep.1
              · intro j hj1 hj2
                rcases Nat.lt_or_ge j Y.length with h | h
                · rw [entry_append_left h]; exact hYok.deep.2 j hj1 h
                · obtain ⟨t, rfl⟩ : ∃ t, j = Y.length + t := ⟨j - Y.length, by omega⟩
                  rw [entry_append_right, entry0_eq]
                  have ht : t < Blk.length := by simp at hj2; omega
                  have := hBcol _ (List.getElem_mem ht)
                  rw [List.getD_eq_getElem?_getD,
                    List.getElem?_eq_getElem ht]
                  simpa using by omega
            · intro x hx hx0
              rcases List.mem_append.mp hx with h | h
              · exact hYok.zroot x h hx0
              · exact absurd hx0 (by have := hBcol x h; omega)
            · intro x hx
              rcases List.mem_append.mp hx with h | h
              · exact hYok.mono x h
              · exact hBmo x h
          match r with
          | 0 => exact ⟨hAok, rfl⟩
          | (_ + 1) => exact hAok
      | (e + 1), hr =>
          match r, hr with
          | 0, hr => exact absurd hr.2 (by omega)
          | (r' + 1), hr =>
              obtain ⟨-, Y0, M', hsp, hY0, hM', hre'⟩ := hr
              subst hsp
              have hBcol' : ∀ x ∈ Blk, e + 2 ≤ x.1 := by
                intro x hx; have := hBcol x hx; omega
              refine ⟨r' + 1, ?_, Y0, M' ++ Blk, by rw [List.append_assoc],
                hY0, MidD_append hM' hBcol' hBmo, ?_⟩
              · have h : Y0 ++ (M' ++ Blk) ∈ W 0 := by
                  rw [← List.append_assoc]; exact hmem
                rw [List.append_assoc]
                exact Aok_append_Mid (d := e + 2) (by omega) (Lv_Aok _ _ _ hY0)
                  (MidD_append hM' hBcol' hBmo) h
              · intro t A'' hA''
                rw [shiftr01_append0, ← List.append_assoc]
                have h1 : A'' ++ shiftr01 t 0 M' ∈ W 0 := hre' t A'' hA''
                have hlv : Lv (r' + 1) (e + t + 1) (A'' ++ shiftr01 t 0 M') :=
                  Lv_shift hM' hre' t hA''
                refine hre t _ ⟨r' + 1, ?_⟩
                rwa [show e + 1 + t = e + t + 1 from by omega]
  | (k + 1), c, Y, Blk, hY, hBcol, hBmo, hre => by
      obtain ⟨Y0, N', rfl, hY0, hN', hN1', hreN⟩ := hY
      have hBcol' : ∀ x ∈ Blk, c + k + 2 ≤ x.1 := by
        intro x hx; have := hBcol x hx; omega
      refine ⟨Y0, N' ++ Blk, by rw [List.append_assoc], hY0,
        MidD_append hN' hBcol' hBmo, ?_, ?_⟩
      · intro hk
        rw [entry_append_left (List.length_pos_iff.mpr hN'.ne)]
        exact hN1' hk
      intro u Y'' hY''
      rw [shiftr01_append0, ← List.append_assoc]
      have h1 : Y'' ++ shiftr01 u 0 N' ∈ W 0 := hreN u Y'' hY''
      have hMu : MidD (c + u + k + 2) (shiftr01 u 0 N') := by
        have h := MidD_shift hN' u
        rwa [show c + k + 2 + u = c + u + k + 2 from by omega] at h
      have hstep : Hd (k + 1) (c + u) (Y'' ++ shiftr01 u 0 N') := by
        refine ⟨Y'', shiftr01 u 0 N', rfl, hY'', hMu, ?_, ?_⟩
        · intro hk
          rw [entry_shift1 (List.length_pos_iff.mpr hN'.ne)]
          exact hN1' hk
        intro v Y3 hY3
        rw [shiftr01_add0]
        refine hreN (u + v) Y3 ?_
        rwa [show c + (u + v) = c + u + v from by omega]
      exact hre u _ hstep

#print axioms Hd_close

/-- ★★ `Hd k c Z` なら高さ `c+k+1` にブロックを吊るせる。 -/
theorem Hd_hang : ∀ (k c : ℕ) (Z : TrioSeq), Hd k c Z → ∀ B : TrioSeq, Bok B →
    Z ++ shiftr01 (c + k + 1) 0 B ∈ W 0
  | 0, c, Z, h, B, hB => by
      obtain ⟨r, hr⟩ := h
      simpa using Lv_hang r c Z hr B hB
  | (k + 1), c, Z, h, B, hB => by
      obtain ⟨Z0, N, rfl, h0, hN, hN1, hre⟩ := h
      have hbase : ∀ (s : ℕ) (Y : TrioSeq), Aok Y → Hd k (c + s) Y →
          Y ++ shiftr01 s 0 N ∈ W 0 := fun s Y _ hY => hre s Y hY
      have hclose : ∀ (s : ℕ) (Y C' : TrioSeq), Aok Y → Hd k (c + s) Y → Mono C' →
          (∀ (t : ℕ) (Y' : TrioSeq), Aok Y' → Hd k (c + t) Y' →
            Y' ++ BlkD (c + k + 2 + t) (shiftr01 t 0 N) C' ∈ W 0) →
          Hd k (c + s) (Y ++ BlkD (c + k + 2 + s) (shiftr01 s 0 N) C') := by
        intro s Y C' _ hY hmoC' hIH
        have hNs : MidD (c + k + 2 + s) (shiftr01 s 0 N) := MidD_shift hN s
        refine Hd_close k (c + s) Y _ hY ?_ (BlkD_mono hNs.mono hmoC') ?_
        · intro x hx
          rcases List.mem_append.mp hx with hh | hh
          · have := MidD_col_ge hNs x hh; omega
          · have := shiftD_col x hh; omega
        · intro t Y' hY'
          have heq : shiftr01 t 0 (BlkD (c + k + 2 + s) (shiftr01 s 0 N) C')
              = BlkD (c + k + 2 + (s + t)) (shiftr01 (s + t) 0 N) C' := by
            simp only [BlkD, shiftr01_append0, shiftr01_add0]
            congr 2
            omega
          rw [heq]
          refine hIH (s + t) Y' (Hd_Aok k (c + (s + t)) Y' ?_) ?_ <;>
            rwa [show c + (s + t) = c + s + t from by omega]
      have hkey := blkD_memS (d := c + k + 2) (by omega) N hN hbase hclose
        B hB.mem hB.zroot hB.mono hB.root 0 Z0 (Hd_Aok k c Z0 h0) (by simpa using h0)
      rw [BlkD_app] at hkey
      simp only [shiftr01_zero, Nat.add_zero] at hkey
      have heq : c + (k + 1) + 1 = c + k + 2 := by omega
      rw [heq]
      exact hkey

theorem Hd_tw (k c : ℕ) (Z : TrioSeq) (hZ : Hd k c Z) :
    ∀ n, TwD (c + k + 1) Z n ∈ W 0
  | 0 => by simpa [TwD] using W_nil 0
  | (n + 1) => by
      have hAok : Aok Z := Hd_Aok k c Z hZ
      rw [TwD_succ]
      exact Hd_hang k c Z hZ (TwD (c + k + 1) Z n)
        ⟨Hd_tw k c Z hZ n, TwD_zroot (by omega) hAok.zroot n, TwD_mono hAok.mono n,
          TwD_root hAok.ne hAok.deep.1 n⟩

/-- ★★ `Hd k c Z` なら `(c+k+1,1,0)` を継げる。 -/
theorem Hd_snoc (k c : ℕ) (Z : TrioSeq) (hZ : Hd k c Z) :
    Z ++ [((c + k + 1, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hAok : Aok Z := Hd_Aok k c Z hZ
  exact snocd_mem (by omega) hAok.ne hAok.deep hAok.zroot (Hd_Ancd k c Z hZ)
    (Hd_tw k c Z hZ)

/-- ★★ `(c+k+1,1,0)` を継ぐと段が 1 つ上がる。これで鎖がいくらでも伸びる。 -/
theorem Hd_step (k c : ℕ) (Z : TrioSeq) (hZ : Hd k c Z) :
    Hd (k + 1) c (Z ++ [((c + k + 1, 1, 0) : ℕ × ℕ × ℕ)]) := by
  refine ⟨Z, [((c + k + 1, 1, 0) : ℕ × ℕ × ℕ)], rfl, hZ, ?_, ?_, ?_⟩
  · have h := MidD_one (c + k + 1) (by omega)
    rwa [show c + k + 1 + 1 = c + k + 2 from by omega] at h
  · intro _
    show (1 : ℕ) < 2
    omega
  · intro u Y hY
    have h := Hd_snoc k (c + u) Y hY
    have heq : shiftr01 u 0 [((c + k + 1, 1, 0) : ℕ × ℕ × ℕ)]
        = [((c + u + k + 1, 1, 0) : ℕ × ℕ × ℕ)] := by
      simp only [shiftr01, List.map_cons, List.map_nil]
      congr 2
      omega
    rw [heq]
    exact h

#print axioms Hd_hang
#print axioms Hd_step

/-! ### `Hd` を行292 に当てる -/

theorem Hd_zero_iff (c : ℕ) (Z : TrioSeq) : Hd 0 c Z ↔ Lw c Z := Iff.rfl

theorem Hd1_Dg1 : Hd 1 0 (Q ++ [((1, 1, 0) : ℕ × ℕ × ℕ)]) := by
  have h := Hd_step 0 0 Q Lw_Q
  simpa using h

/-- ★★ `X = (0,0,0)(1,1,1)(1,1,0)(2,2,0)` は 2 段（`(1,1,0)` と `(2,2,0)`）。
`(2,2,0)` の再継ぎはちょうど `Seg_snoc2`。 -/
theorem Hd2_R292 : Hd 2 0 R292 := by
  refine ⟨Q ++ [((1, 1, 0) : ℕ × ℕ × ℕ)], [((2, 2, 0) : ℕ × ℕ × ℕ)],
    by simp [R292, Q], Hd1_Dg1, MidD_col 2 2 (by omega) (by omega), ?_, ?_⟩
  · intro hk
    simp at hk
  · intro u Y hY
    obtain ⟨Y0, N, rfl, hY0, hN, hN1, hre⟩ := hY
    simp only [Nat.zero_add, Nat.add_zero] at hN hY0 hre
    have hSeg : Seg u N := ⟨hN, hN1 rfl, fun v Y' hY' => hre v Y' hY'⟩
    have h := Seg_snoc2 hSeg (A0 := Y0) hY0
    have heq : shiftr01 u 0 [((2, 2, 0) : ℕ × ℕ × ℕ)]
        = [((u + 2, 2, 0) : ℕ × ℕ × ℕ)] := by
      simp only [shiftr01, List.map_cons, List.map_nil, List.cons.injEq,
        Prod.mk.injEq, and_true]
      omega
    rw [heq]
    exact h

/-- ★ `X` に高さ 3 から `(k,1,0)` の鎖を継ぐと、継いだ本数だけ段が上がる。 -/
theorem Hd_chain_R292 : ∀ n : ℕ,
    Hd (2 + n) 0 (Mtw R292 [((3, 1, 0) : ℕ × ℕ × ℕ)] n)
  | 0 => by simpa [Mtw_zero] using Hd2_R292
  | (n + 1) => by
      have h := Hd_step (2 + n) 0 _ (Hd_chain_R292 n)
      simp only [Nat.zero_add] at h
      rw [Mtw_one_succ R292 2 n, show 2 + (n + 1) = 2 + n + 1 from by omega]
      exact h

theorem Mtw_R292_310_mem (n : ℕ) : Mtw R292 [((3, 1, 0) : ℕ × ℕ × ℕ)] n ∈ W 0 :=
  Hd_mem (Hd_chain_R292 n)

/-- ★★★ 行293 の基本列の 2 項目 `R293[1] = X(3,1,0)(4,2,0)`。 -/
theorem R293_1_mem :
    (R292 ++ [((3, 1, 0) : ℕ × ℕ × ℕ)]) ++ [((4, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := snocY_mem (Y0 := R292) (M := [((3, 1, 0) : ℕ × ℕ × ℕ)]) (L := 3) (y := 2)
    (by simp [R292]) (MidD_one 3 (by omega)) (by show (1 : ℕ) < 2; omega) (by omega)
    Mtw_R292_310_mem
  simpa using h

#print axioms Hd2_R292
#print axioms R293_1_mem

/-! ## ★★★ 台座を差し替えられる梯子 `LvB`（行293 への道）

`Lv` の底は「`Aok A` かつレベル 0」に固定で、1 ランク ＝ 1 レベルだった。
行293 の基本列
`X_n = (0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,1,0)(4,2,0)...(2n-1,1,0)(2n,2,0)`
は `(·,2,0)` を継ぐたびにレベルが 2 上がるので、`Lv` では表せない。

そこで**底 `P`（レベルと行列の述語）を引数**にして梯子を作り直し、
`(·,2,0)` の本数 `j` について底を取り替える:

```
Basef 0     h A = Aok A ∧ h = 0
Basef (j+1)     = NxtB (Basef j)   -- 「Basef j の梯子の頭 ++ セグメント ++ (·,2,0) の塊」
```

各段の梯子 `LvB (Basef j)` の中ではランクが自由に伸びる（`LwB` でランクを ∃ で潰す）
ので塔が作れる。定義の再帰は `j` について構造的。 -/

/-- 底に要る性質。`close` は `blkD_memS` の `hclose` で使う。 -/
structure BaseOk (P : ℕ → TrioSeq → Prop) : Prop where
  aok : ∀ (h : ℕ) (A : TrioSeq), P h A → Aok A
  ancd : ∀ (h : ℕ) (A : TrioSeq), P h A → Ancd (h + 1) A
  hang : ∀ (h : ℕ) (A : TrioSeq), P h A → ∀ B : TrioSeq, Bok B →
      A ++ shiftr01 (h + 1) 0 B ∈ W 0
  close : ∀ (h : ℕ) (A Blk : TrioSeq), P h A → (∀ x ∈ Blk, h + 1 ≤ x.1) → Mono Blk →
      (∀ (t : ℕ) (A' : TrioSeq), P (h + t) A' → A' ++ shiftr01 t 0 Blk ∈ W 0) →
      P h (A ++ Blk)

/-- 底 `P` の上の梯子。`r` はランク、`h` はレベル。 -/
def LvB (P : ℕ → TrioSeq → Prop) : ℕ → ℕ → TrioSeq → Prop
  | 0, h, A => P h A
  | (r + 1), h, A => Aok A ∧ (P h A ∨ ∃ (b : ℕ) (A0 M : TrioSeq), h = b + 1 ∧
      A = A0 ++ M ∧ LvB P r b A0 ∧ MidD (b + 2) M ∧
      (∀ (s : ℕ) (A' : TrioSeq), LvB P r (b + s) A' → A' ++ shiftr01 s 0 M ∈ W 0))

/-- 「頭 `A` の右に中間セグメント `N` を継ぐと祖先条件が 1 段上がる」。 -/
theorem Ancd_append_Mid {d : ℕ} {A N : TrioSeq} (hAne : A ≠ []) (hA : Ancd d A)
    (hN : MidD (d + 1) N) : Ancd (d + 1) (A ++ N) := by
  have hAlen : 0 < A.length := List.length_pos_iff.mpr hAne
  have hNlen : 0 < N.length := List.length_pos_iff.mpr hN.ne
  have hhead0 : entry (A ++ N) 0 A.length = entry N 0 0 := by
    rw [show A.length = A.length + 0 from rfl, entry_append_right]
  have hhead1 : entry (A ++ N) 1 A.length = entry N 1 0 := by
    rw [show A.length = A.length + 0 from rfl, entry_append_right]
  have hNh : entry N 0 0 = d := by have := hN.head; omega
  intro j hj0 hjl hlt hrec
  have hlen : (A ++ N).length = A.length + N.length := by simp
  rcases Nat.lt_trichotomy j A.length with hj | hj | hj
  · have hcmp : entry (A ++ N) 0 j < entry (A ++ N) 0 A.length :=
      hrec A.length hj (by omega)
    rw [hhead0, hNh] at hcmp
    rw [entry_append_left hj] at hcmp ⊢
    refine hA j hj0 hj hcmp ?_
    intro i hi1 hi2
    have := hrec i hi1 (by omega)
    rw [entry_append_left hj, entry_append_left hi2] at this
    exact this
  · subst hj
    rw [hhead1]
    exact hN.head1
  · exfalso
    obtain ⟨t, rfl⟩ : ∃ t, j = A.length + t := ⟨j - A.length, by omega⟩
    rw [entry_append_right] at hlt
    have := hN.tail t (by omega) (by omega)
    omega

theorem LvB_Aok {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) :
    ∀ (r h : ℕ) (A : TrioSeq), LvB P r h A → Aok A
  | 0, h, A, hA => hP.aok h A hA
  | (_ + 1), _, _, hA => hA.1

theorem LvB_of_base {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) :
    ∀ (r h : ℕ) (A : TrioSeq), P h A → LvB P r h A
  | 0, _, _, hA => hA
  | (_ + 1), h, A, hA => ⟨hP.aok h A hA, Or.inl hA⟩

theorem LvB_Ancd {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) :
    ∀ (r h : ℕ) (A : TrioSeq), LvB P r h A → Ancd (h + 1) A
  | 0, h, A, hA => hP.ancd h A hA
  | (r + 1), h, A, hA => by
      rcases hA.2 with h1 | ⟨b, A0, M, rfl, rfl, hA0, hM, -⟩
      · exact hP.ancd h A h1
      · exact Ancd_append_Mid (LvB_Aok hP r b A0 hA0).ne (LvB_Ancd hP r b A0 hA0) hM

/-- シフト閉包: 再継ぎ可能なセグメントを `s` だけ高くして継いでも梯子が 1 段上がる。 -/
theorem LvB_shift {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) {r b : ℕ} {M : TrioSeq}
    (hM : MidD (b + 2) M)
    (hre : ∀ (t : ℕ) (A' : TrioSeq), LvB P r (b + t) A' → A' ++ shiftr01 t 0 M ∈ W 0)
    (s : ℕ) {A' : TrioSeq} (hA' : LvB P r (b + s) A') :
    LvB P (r + 1) (b + s + 1) (A' ++ shiftr01 s 0 M) := by
  have hA'ok : Aok A' := LvB_Aok hP _ _ _ hA'
  have hmem : A' ++ shiftr01 s 0 M ∈ W 0 := hre s A' hA'
  have hMs0 : MidD (b + s + 2) (shiftr01 s 0 M) := by
    have h := MidD_shift hM s
    rwa [show b + 2 + s = b + s + 2 from by omega] at h
  refine ⟨Aok_append_Mid (by omega) hA'ok hMs0 hmem,
    Or.inr ⟨b + s, A', shiftr01 s 0 M, rfl, rfl, hA', hMs0, ?_⟩⟩
  intro t A'' hA''
  rw [shiftr01_add0]
  refine hre (s + t) A'' ?_
  rwa [show b + (s + t) = b + s + t from by omega]

theorem LvB_hang {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) :
    ∀ (r h : ℕ) (A : TrioSeq), LvB P r h A → ∀ B : TrioSeq, Bok B →
      A ++ shiftr01 (h + 1) 0 B ∈ W 0
  | 0, h, A, hA, B, hB => hP.hang h A hA B hB
  | (r + 1), h, A, hA, B, hB => by
      rcases hA.2 with h1 | ⟨b, A0, M, rfl, rfl, hA0, hM, hre⟩
      · exact hP.hang h A h1 B hB
      have hA0ok : Aok A0 := LvB_Aok hP r b A0 hA0
      have hbase : ∀ (s : ℕ) (A' : TrioSeq), Aok A' → LvB P r (b + s) A' →
          A' ++ shiftr01 s 0 M ∈ W 0 := fun s A' _ h' => hre s A' h'
      have hclose : ∀ (s : ℕ) (A' C' : TrioSeq), Aok A' → LvB P r (b + s) A' → Mono C' →
          (∀ (t : ℕ) (A'' : TrioSeq), Aok A'' → LvB P r (b + t) A'' →
            A'' ++ BlkD (b + 2 + t) (shiftr01 t 0 M) C' ∈ W 0) →
          LvB P r (b + s) (A' ++ BlkD (b + 2 + s) (shiftr01 s 0 M) C') := by
        intro s A' C' hA'ok hA' hmoC' hIH
        have hMs : MidD (b + 2 + s) (shiftr01 s 0 M) := MidD_shift hM s
        have hXmem := hIH s A' hA'ok hA'
        have hXok : Aok (A' ++ BlkD (b + 2 + s) (shiftr01 s 0 M) C') :=
          Aok_append_BlkD (by omega) hXmem hA'ok hMs hmoC'
        have hBlkcol : ∀ x ∈ BlkD (b + 2 + s) (shiftr01 s 0 M) C', b + s + 1 ≤ x.1 := by
          intro x hx
          rcases List.mem_append.mp hx with hh | hh
          · have := MidD_col_ge hMs x hh; omega
          · have := shiftD_col x hh; omega
        have hBlkmo : Mono (BlkD (b + 2 + s) (shiftr01 s 0 M) C') :=
          BlkD_mono hMs.mono hmoC'
        have hshiftBlk : ∀ t : ℕ,
            shiftr01 t 0 (BlkD (b + 2 + s) (shiftr01 s 0 M) C')
              = BlkD (b + 2 + (s + t)) (shiftr01 (s + t) 0 M) C' := by
          intro t
          simp only [BlkD, shiftr01_append0, shiftr01_add0]
          congr 2
          omega
        have hBlkre : ∀ (t : ℕ) (A'' : TrioSeq), P (b + s + t) A'' →
            A'' ++ shiftr01 t 0 (BlkD (b + 2 + s) (shiftr01 s 0 M) C') ∈ W 0 := by
          intro t A'' hA''
          rw [hshiftBlk t]
          refine hIH (s + t) A'' (hP.aok _ _ hA'') ?_
          refine LvB_of_base hP r _ _ ?_
          rwa [show b + (s + t) = b + s + t from by omega]
        rcases Nat.eq_zero_or_pos r with rfl | hrpos
        · exact hP.close (b + s) A' _ hA' hBlkcol hBlkmo hBlkre
        obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        refine ⟨hXok, ?_⟩
        rcases hA'.2 with hp | ⟨e, A0', M', he, hsp, hA0', hM', hre'⟩
        · exact Or.inl (hP.close (b + s) A' _ hp hBlkcol hBlkmo hBlkre)
        subst hsp
        have hNcol : ∀ x ∈ BlkD (b + 2 + s) (shiftr01 s 0 M) C', e + 2 ≤ x.1 := by
          intro x hx
          have := hBlkcol x hx
          omega
        refine Or.inr ⟨e, A0', M' ++ BlkD (b + 2 + s) (shiftr01 s 0 M) C', he,
          by rw [List.append_assoc], hA0', MidD_append hM' hNcol hBlkmo, ?_⟩
        intro t A'' hA''
        have hm1 : A'' ++ shiftr01 t 0 M' ∈ W 0 := hre' t A'' hA''
        have hlv1 : LvB P (r' + 1) (e + t + 1) (A'' ++ shiftr01 t 0 M') :=
          LvB_shift hP hM' hre' t hA''
        have hok1 : Aok (A'' ++ shiftr01 t 0 M') := LvB_Aok hP _ _ _ hlv1
        have hlv2 : LvB P (r' + 1) (b + (s + t)) (A'' ++ shiftr01 t 0 M') := by
          rw [show b + (s + t) = e + t + 1 from by omega]
          exact hlv1
        have hres := hIH (s + t) _ hok1 hlv2
        rw [shiftr01_append0, hshiftBlk t, ← List.append_assoc]
        exact hres
      have hkey := blkD_memS (d := b + 2) (by omega) M hM hbase hclose B hB.mem
        hB.zroot hB.mono hB.root 0 A0 hA0ok (by simpa using hA0)
      simp only [shiftr01_zero, Nat.add_zero] at hkey
      rw [BlkD_app] at hkey
      exact hkey

theorem LvB_tw {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) (r h : ℕ) (A : TrioSeq)
    (hA : LvB P r h A) : ∀ n, TwD (h + 1) A n ∈ W 0
  | 0 => by simpa [TwD] using W_nil 0
  | (n + 1) => by
      have hAok : Aok A := LvB_Aok hP r h A hA
      rw [TwD_succ]
      exact LvB_hang hP r h A hA (TwD (h + 1) A n)
        ⟨LvB_tw hP r h A hA n, TwD_zroot (by omega) hAok.zroot n, TwD_mono hAok.mono n,
          TwD_root hAok.ne hAok.deep.1 n⟩

theorem LvB_snoc {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) (r h : ℕ) (A : TrioSeq)
    (hA : LvB P r h A) : A ++ [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hAok : Aok A := LvB_Aok hP r h A hA
  exact snocd_mem (by omega) hAok.ne hAok.deep hAok.zroot (LvB_Ancd hP r h A hA)
    (LvB_tw hP r h A hA)

/-- ランクを ∃ で潰したクラス。塔はこの中で回る。 -/
def LwB (P : ℕ → TrioSeq → Prop) (h : ℕ) (A : TrioSeq) : Prop := ∃ r, LvB P r h A

theorem LwB_Aok {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) {h : ℕ} {A : TrioSeq}
    (hA : LwB P h A) : Aok A := by
  obtain ⟨r, hr⟩ := hA
  exact LvB_Aok hP r h A hr

theorem LwB_mem {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) {h : ℕ} {A : TrioSeq}
    (hA : LwB P h A) : A ∈ W 0 := (LwB_Aok hP hA).mem

theorem LwB_Ancd {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) {h : ℕ} {A : TrioSeq}
    (hA : LwB P h A) : Ancd (h + 1) A := by
  obtain ⟨r, hr⟩ := hA
  exact LvB_Ancd hP r h A hr

theorem LwB_of_base {P : ℕ → TrioSeq → Prop} {h : ℕ} {A : TrioSeq} (hA : P h A) :
    LwB P h A := ⟨0, hA⟩

/-- 高さ `h+1` から始まる、`LwB` の頭ならどこへでも（シフトして）継げるセグメント。 -/
structure SegB (P : ℕ → TrioSeq → Prop) (h : ℕ) (M : TrioSeq) : Prop where
  mid : MidD (h + 2) M
  head1 : entry M 1 0 < 2
  reapp : ∀ (s : ℕ) (A' : TrioSeq), LwB P (h + s) A' → A' ++ shiftr01 s 0 M ∈ W 0

theorem SegB_shift {P : ℕ → TrioSeq → Prop} {h : ℕ} {M : TrioSeq} (hS : SegB P h M)
    (u : ℕ) : SegB P (h + u) (shiftr01 u 0 M) where
  mid := by
    have h1 := MidD_shift hS.mid u
    rwa [show h + 2 + u = h + u + 2 from by omega] at h1
  head1 := by
    rw [entry_shift1 (List.length_pos_iff.mpr hS.mid.ne)]
    exact hS.head1
  reapp := by
    intro s A' hA'
    rw [shiftr01_add0]
    refine hS.reapp (u + s) A' ?_
    rwa [show h + (u + s) = h + u + s from by omega]

theorem LwB_tower {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) {h : ℕ} {A0 M : TrioSeq}
    (hS : SegB P h M) (h0 : LwB P h A0) : ∀ n : ℕ, LwB P (h + n) (Mtw A0 M n)
  | 0 => by simpa [Mtw_zero] using h0
  | (n + 1) => by
      obtain ⟨r, hr⟩ := LwB_tower hP hS h0 n
      rw [Mtw_succ]
      have hmem : Mtw A0 M n ++ shiftr01 n 0 M ∈ W 0 := hS.reapp n _ ⟨r, hr⟩
      have hMn : MidD (h + n + 2) (shiftr01 n 0 M) := by
        have h1 := MidD_shift hS.mid n
        rwa [show h + 2 + n = h + n + 2 from by omega] at h1
      refine ⟨r + 1, Aok_append_Mid (by omega) (LvB_Aok hP _ _ _ hr) hMn hmem,
        Or.inr ⟨h + n, Mtw A0 M n, shiftr01 n 0 M, rfl, rfl, hr, hMn, ?_⟩⟩
      intro t A' hA'
      rw [shiftr01_add0]
      refine hS.reapp (n + t) A' ⟨r, ?_⟩
      rwa [show h + (n + t) = h + n + t from by omega]

theorem LwB_tower_mem {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) {h : ℕ} {A0 M : TrioSeq}
    (hS : SegB P h M) (h0 : LwB P h A0) (n : ℕ) : Mtw A0 M n ∈ W 0 :=
  LwB_mem hP (LwB_tower hP hS h0 n)

/-- ★★ セグメントの直後に `(h+2,2,0)` を継げる。 -/
theorem SegB_snoc2 {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) {h : ℕ} {A0 M : TrioSeq}
    (hS : SegB P h M) (h0 : LwB P h A0) :
    (A0 ++ M) ++ [((h + 2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  snocY_mem (L := h + 1) (y := 2) (LwB_Aok hP h0).ne hS.mid hS.head1 (by omega)
    (LwB_tower_mem hP hS h0)

/-- `(h+1,1,0)` は `SegB`。 -/
theorem SegB_one {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) (h : ℕ) :
    SegB P h [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] where
  mid := MidD_one (h + 1) (by omega)
  head1 := by show (1 : ℕ) < 2; omega
  reapp := by
    intro s A' hA'
    obtain ⟨r, hr⟩ := hA'
    have h1 := LvB_snoc hP r (h + s) A' hr
    have heq : shiftr01 s 0 [((h + 1, 1, 0) : ℕ × ℕ × ℕ)]
        = [((h + s + 1, 1, 0) : ℕ × ℕ × ℕ)] := by
      simp only [shiftr01, List.map_cons, List.map_nil]
      congr 2
      omega
    rw [heq]
    exact h1

/-! ### `(·,2,0)` を 1 本足した新しい底 `NxtB` -/

/-- 「`LwB` の頭 ++ `SegB`」。`blkD_memS` の不変量。 -/
def InvB (P : ℕ → TrioSeq → Prop) (b s : ℕ) (Y : TrioSeq) : Prop :=
  ∃ Y0 M : TrioSeq, Y = Y0 ++ M ∧ LwB P (b + s) Y0 ∧ SegB P (b + s) M

/-- `P` の梯子の頭に `SegB` を継ぎ、さらに `(b+2,2,0)` から始まる塊 `N` を継いだもの。 -/
def NxtB (P : ℕ → TrioSeq → Prop) : ℕ → TrioSeq → Prop := fun h A =>
  ∃ (b : ℕ) (Y0 M N : TrioSeq), h = b + 2 ∧ A = (Y0 ++ M) ++ N ∧
    LwB P b Y0 ∧ SegB P b M ∧ MidD (b + 3) N ∧
    (∀ (s : ℕ) (Y : TrioSeq), InvB P b s Y → Y ++ shiftr01 s 0 N ∈ W 0)

theorem NxtB_aok {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) (h : ℕ) (A : TrioSeq)
    (hA : NxtB P h A) : Aok A := by
  obtain ⟨b, Y0, M, N, rfl, rfl, hY0, hM, hN, hNre⟩ := hA
  have hYM : Y0 ++ M ∈ W 0 := by
    have h1 := hM.reapp 0 Y0 (by simpa using hY0)
    simpa using h1
  have hYMok : Aok (Y0 ++ M) := Aok_append_Mid (by omega) (LwB_Aok hP hY0) hM.mid hYM
  have hmem : (Y0 ++ M) ++ N ∈ W 0 := by
    have h1 := hNre 0 (Y0 ++ M) ⟨Y0, M, rfl, by simpa using hY0, by simpa using hM⟩
    simpa using h1
  exact Aok_append_Mid (by omega) hYMok hN hmem

theorem NxtB_ancd {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) (h : ℕ) (A : TrioSeq)
    (hA : NxtB P h A) : Ancd (h + 1) A := by
  obtain ⟨b, Y0, M, N, rfl, rfl, hY0, hM, hN, hNre⟩ := hA
  have hYM1 : LwB P (b + 1) (Y0 ++ M) := by
    have h1 := LwB_tower hP hM hY0 1
    rwa [Mtw_succ, Mtw_zero, shiftr01_zero] at h1
  have hAnc : Ancd (b + 2) (Y0 ++ M) := LwB_Ancd hP hYM1
  exact Ancd_append_Mid (LwB_Aok hP hYM1).ne hAnc hN

theorem NxtB_hang {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) (h : ℕ) (A : TrioSeq)
    (hA : NxtB P h A) (B : TrioSeq) (hB : Bok B) :
    A ++ shiftr01 (h + 1) 0 B ∈ W 0 := by
  obtain ⟨b, Y0, M, N, rfl, rfl, hY0, hM, hN, hNre⟩ := hA
  have hbase : ∀ (s : ℕ) (X : TrioSeq), Aok X → InvB P b s X →
      X ++ shiftr01 s 0 N ∈ W 0 := fun s X _ hX => hNre s X hX
  have hclose : ∀ (s : ℕ) (X C' : TrioSeq), Aok X → InvB P b s X → Mono C' →
      (∀ (t : ℕ) (Y : TrioSeq), Aok Y → InvB P b t Y →
        Y ++ BlkD (b + 3 + t) (shiftr01 t 0 N) C' ∈ W 0) →
      InvB P b s (X ++ BlkD (b + 3 + s) (shiftr01 s 0 N) C') := by
    rintro s X C' - ⟨X0, M', rfl, hX0, hM'⟩ hmoC' hIH
    set Blk : TrioSeq := BlkD (b + 3 + s) (shiftr01 s 0 N) C' with hBlk
    have hNs : MidD (b + 3 + s) (shiftr01 s 0 N) := MidD_shift hN s
    have hBlkcol : ∀ c ∈ Blk, b + s + 2 ≤ c.1 := by
      intro c hc
      rcases List.mem_append.mp hc with hh | hh
      · have := MidD_col_ge hNs c hh; omega
      · have := shiftD_col c hh; omega
    have hBlkmo : Mono Blk := BlkD_mono hNs.mono hmoC'
    refine ⟨X0, M' ++ Blk, by rw [List.append_assoc], hX0, ?_, ?_, ?_⟩
    · exact MidD_append hM'.mid hBlkcol hBlkmo
    · rw [entry_append_left (List.length_pos_iff.mpr hM'.mid.ne)]
      exact hM'.head1
    · intro u A' hA'
      rw [shiftr01_append0]
      have h1 : A' ++ shiftr01 u 0 M' ∈ W 0 := hM'.reapp u A' hA'
      have hSu : SegB P (b + s + u) (shiftr01 u 0 M') := SegB_shift hM' u
      have hAok : Aok (A' ++ shiftr01 u 0 M') :=
        Aok_append_Mid (by omega) (LwB_Aok hP hA') hSu.mid h1
      have hP2 : InvB P b (s + u) (A' ++ shiftr01 u 0 M') := by
        refine ⟨A', shiftr01 u 0 M', rfl, ?_, ?_⟩
        · rwa [show b + (s + u) = b + s + u from by omega]
        · rwa [show b + (s + u) = b + s + u from by omega]
      have h2 := hIH (s + u) _ hAok hP2
      have heq : shiftr01 u 0 Blk
          = BlkD (b + 3 + (s + u)) (shiftr01 (s + u) 0 N) C' := by
        rw [hBlk, BlkD, BlkD, shiftr01_append0, shiftr01_add0, shiftr01_add0]
        congr 2
        omega
      rw [heq, ← List.append_assoc]
      exact h2
  have hYM : Y0 ++ M ∈ W 0 := by
    have h1 := hM.reapp 0 Y0 (by simpa using hY0)
    simpa using h1
  have hYMok : Aok (Y0 ++ M) := Aok_append_Mid (by omega) (LwB_Aok hP hY0) hM.mid hYM
  have hkey := blkD_memS (d := b + 3) (by omega) N hN hbase hclose B hB.mem
    hB.zroot hB.mono hB.root 0 (Y0 ++ M) hYMok
    ⟨Y0, M, rfl, by simpa using hY0, by simpa using hM⟩
  simp only [shiftr01_zero, Nat.add_zero] at hkey
  rw [BlkD_app] at hkey
  exact hkey

theorem NxtB_close {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) (h : ℕ) (A Blk : TrioSeq)
    (hA : NxtB P h A) (hcol : ∀ x ∈ Blk, h + 1 ≤ x.1) (hmo : Mono Blk)
    (hre : ∀ (t : ℕ) (A' : TrioSeq), NxtB P (h + t) A' → A' ++ shiftr01 t 0 Blk ∈ W 0) :
    NxtB P h (A ++ Blk) := by
  obtain ⟨b, Y0, M, N, rfl, rfl, hY0, hM, hN, hNre⟩ := hA
  refine ⟨b, Y0, M, N ++ Blk, rfl, by rw [List.append_assoc], hY0, hM,
    MidD_append hN (by intro x hx; have := hcol x hx; omega) hmo, ?_⟩
  intro s Y hY
  rw [shiftr01_append0, ← List.append_assoc]
  have h1 : Y ++ shiftr01 s 0 N ∈ W 0 := hNre s Y hY
  obtain ⟨Y0', M', rfl, hY0', hM'⟩ := hY
  have hstep : NxtB P (b + 2 + s) ((Y0' ++ M') ++ shiftr01 s 0 N) := by
    refine ⟨b + s, Y0', M', shiftr01 s 0 N, by omega, rfl, hY0', hM', ?_, ?_⟩
    · have h2 := MidD_shift hN s
      rwa [show b + 3 + s = b + s + 3 from by omega] at h2
    · intro t Z hZ
      rw [shiftr01_add0]
      refine hNre (s + t) Z ?_
      obtain ⟨Z0, M'', rfl, hZ0, hM''⟩ := hZ
      exact ⟨Z0, M'', rfl, by rwa [show b + (s + t) = b + s + t from by omega],
        by rwa [show b + (s + t) = b + s + t from by omega]⟩
  exact hre s _ hstep

theorem NxtB_BaseOk {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) : BaseOk (NxtB P) where
  aok := NxtB_aok hP
  ancd := NxtB_ancd hP
  hang := NxtB_hang hP
  close := NxtB_close hP

/-! ### 底の列 `Basef j`（`(·,2,0)` の本数 `j`） -/

theorem BaseOk_zero : BaseOk (fun (h : ℕ) (A : TrioSeq) => Aok A ∧ h = 0) where
  aok := fun _ _ hA => hA.1
  ancd := by
    rintro h A ⟨hA, rfl⟩
    intro j hj0 hjl hlt _
    have := hA.deep.2 j hj0 hjl
    omega
  hang := by
    rintro h A ⟨hA, rfl⟩ B hB
    show A ++ bump B ∈ W 0
    exact bump_zm hB.mem hB.zroot hB.mono hB.root hA.mem hA.ne hA.deep
  close := by
    rintro h A Blk ⟨hA, rfl⟩ hcol hmo hre
    have hmem : A ++ Blk ∈ W 0 := by
      have h1 := hre 0 A ⟨hA, rfl⟩
      simpa using h1
    refine ⟨⟨hmem, by simp [List.append_eq_nil_iff, hA.ne], ?_, ?_, ?_⟩, rfl⟩
    · exact Deep_append hA.deep hA.ne (fun c hc => by have := hcol c hc; omega)
    · intro x hx hx0
      rcases List.mem_append.mp hx with hh | hh
      · exact hA.zroot x hh hx0
      · exact absurd hx0 (by have := hcol x hh; omega)
    · intro x hx
      rcases List.mem_append.mp hx with hh | hh
      · exact hA.mono x hh
      · exact hmo x hh

def Basef : ℕ → ℕ → TrioSeq → Prop
  | 0 => fun h A => Aok A ∧ h = 0
  | (j + 1) => NxtB (Basef j)

theorem BaseOk_Basef : ∀ j : ℕ, BaseOk (Basef j)
  | 0 => BaseOk_zero
  | (j + 1) => NxtB_BaseOk (BaseOk_Basef j)

/-! ### 行293 の基本列 -/

/-- `Xs n = (0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,1,0)(4,2,0)...(2n-1,1,0)(2n,2,0)`。 -/
def Xs : ℕ → TrioSeq
  | 0 => Q
  | (n + 1) => Xs n ++ [((2 * n + 1, 1, 0) : ℕ × ℕ × ℕ), ((2 * n + 2, 2, 0) : ℕ × ℕ × ℕ)]

theorem Basef_Xs : ∀ n : ℕ, Basef n (2 * n) (Xs n)
  | 0 => ⟨(Aok_Q : Aok Q), rfl⟩
  | (n + 1) => by
      have hP := BaseOk_Basef n
      have hLw : LwB (Basef n) (2 * n) (Xs n) := LwB_of_base (Basef_Xs n)
      have hSeg : SegB (Basef n) (2 * n) [((2 * n + 1, 1, 0) : ℕ × ℕ × ℕ)] :=
        SegB_one hP (2 * n)
      have hMid : MidD (2 * n + 3) [((2 * n + 2, 2, 0) : ℕ × ℕ × ℕ)] := by
        have h1 := MidD_col (2 * n + 2) 2 (by omega) (by omega)
        rwa [show 2 * n + 2 + 1 = 2 * n + 3 from by omega] at h1
      show NxtB (Basef n) (2 * (n + 1)) (Xs (n + 1))
      refine ⟨2 * n, Xs n, [((2 * n + 1, 1, 0) : ℕ × ℕ × ℕ)],
        [((2 * n + 2, 2, 0) : ℕ × ℕ × ℕ)], by omega, ?_, hLw, hSeg, hMid, ?_⟩
      · show Xs n ++ [((2 * n + 1, 1, 0) : ℕ × ℕ × ℕ), ((2 * n + 2, 2, 0) : ℕ × ℕ × ℕ)]
          = (Xs n ++ [((2 * n + 1, 1, 0) : ℕ × ℕ × ℕ)])
            ++ [((2 * n + 2, 2, 0) : ℕ × ℕ × ℕ)]
        simp
      · rintro s Y ⟨Y0, M', rfl, hY0, hM'⟩
        rw [shift_col]
        have h1 := SegB_snoc2 hP hM' hY0
        rwa [show 2 * n + s + 2 = 2 * n + 2 + s from by omega] at h1

theorem Xs_mem (n : ℕ) : Xs n ∈ W 0 :=
  ((BaseOk_Basef n).aok _ _ (Basef_Xs n)).mem

theorem Xs_eq_Mtwd : ∀ n : ℕ, Xs n = Mtwd 2 Q N293 n
  | 0 => by rw [Mtwd_zero]; rfl
  | (n + 1) => by
      rw [Mtwd_succ, ← Xs_eq_Mtwd n]
      show Xs n ++ [((2 * n + 1, 1, 0) : ℕ × ℕ × ℕ), ((2 * n + 2, 2, 0) : ℕ × ℕ × ℕ)]
        = Xs n ++ shiftr01 (2 * n) 0 N293
      congr 1
      simp only [N293, shiftr01, List.map_cons, List.map_nil, List.cons.injEq,
        Prod.mk.injEq, and_true]
      omega

/-- ★★★ シート行293 `(0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,2,0) ∈ W 0`。 -/
theorem R293_mem : R293 ∈ W 0 :=
  R293_mem_of_tower (fun n => by rw [← Xs_eq_Mtwd n]; exact Xs_mem n)

#print axioms R293_mem

/-! ## ★★★ 走りの梯子 `RunA`（行294 への道）

行294 の基本列は `(·,2,0)` が 1 本ずつ伸びる:

```
294[n] = (0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,2,0)...(n+1,2,0)
```

その各項の展開は**歩幅 `m` の塔**で、繰り返す塊が
`Uu m b = (b+1,1,0)(b+2,2,0)...(b+m,2,0)` と長くなる。

塔を作るには「塊の各部品を、**より大きな台座の上でも**継げる」ことが要る。
そこで再継ぎ性を台座について ∀ で取った `SegA`（絶対セグメント）を使い、
台座は ∃ で包む（`LwA`）。`SegA` はブロックを飲み込んでも `SegA` のまま
（飲み込むときに使う仮定も台座 ∀ の形で来るため）。 -/

/-- どれかの良い台座の上の梯子の頭。 -/
def LwA (h : ℕ) (A : TrioSeq) : Prop :=
  ∃ P : ℕ → TrioSeq → Prop, BaseOk P ∧ LwB P h A

theorem LwA_Aok {h : ℕ} {A : TrioSeq} (hA : LwA h A) : Aok A := by
  obtain ⟨P, hP, hL⟩ := hA
  exact LwB_Aok hP hL

/-- 台座に依らないセグメント。`SegB` の台座 ∀ 版。 -/
structure SegA (h : ℕ) (M : TrioSeq) : Prop where
  mid : MidD (h + 2) M
  head1 : entry M 1 0 < 2
  reapp : ∀ (P : ℕ → TrioSeq → Prop), BaseOk P → ∀ (s : ℕ) (A' : TrioSeq),
      LwB P (h + s) A' → A' ++ shiftr01 s 0 M ∈ W 0

theorem SegA_toSegB {h : ℕ} {M : TrioSeq} (hM : SegA h M)
    {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) : SegB P h M where
  mid := hM.mid
  head1 := hM.head1
  reapp := fun s A' hA' => hM.reapp P hP s A' hA'

theorem SegA_shift {h : ℕ} {M : TrioSeq} (hM : SegA h M) (u : ℕ) :
    SegA (h + u) (shiftr01 u 0 M) where
  mid := by
    have h1 := MidD_shift hM.mid u
    rwa [show h + 2 + u = h + u + 2 from by omega] at h1
  head1 := by
    rw [entry_shift1 (List.length_pos_iff.mpr hM.mid.ne)]
    exact hM.head1
  reapp := by
    intro P hP s A' hA'
    rw [shiftr01_add0]
    refine hM.reapp P hP (u + s) A' ?_
    rwa [show h + (u + s) = h + u + s from by omega]

/-- `(h+1,1,0)` は絶対セグメント（`LvB_snoc` はどの台座でも通る）。 -/
theorem SegA_one (h : ℕ) : SegA h [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] where
  mid := MidD_one (h + 1) (by omega)
  head1 := by show (1 : ℕ) < 2; omega
  reapp := by
    intro P hP s A' hA'
    obtain ⟨r, hr⟩ := hA'
    have h1 := LvB_snoc hP r (h + s) A' hr
    have heq : shiftr01 s 0 [((h + 1, 1, 0) : ℕ × ℕ × ℕ)]
        = [((h + s + 1, 1, 0) : ℕ × ℕ × ℕ)] := by
      simp only [shiftr01, List.map_cons, List.map_nil]
      congr 2
      omega
    rw [heq]
    exact h1

/-- `RunA j h A`: 梯子の頭の上に `(·,1,0)` 1 本と `(·,2,0)` を `j` 本
（それぞれ上にブロックを飲み込んでよい）。レベルは `h`。 -/
def RunA : ℕ → ℕ → TrioSeq → Prop
  | 0, h, A => ∃ (b : ℕ) (Y0 M : TrioSeq), h = b + 1 ∧ A = Y0 ++ M ∧
      LwA b Y0 ∧ SegA b M
  | (j + 1), h, A => ∃ (b : ℕ) (A0 N : TrioSeq), h = b + 1 ∧ A = A0 ++ N ∧
      RunA j b A0 ∧ MidD (b + 2) N ∧ 2 ≤ entry N 1 0 ∧
      (∀ (s : ℕ) (X : TrioSeq), RunA j (b + s) X → X ++ shiftr01 s 0 N ∈ W 0)

/-- `RunA 0` の頭は梯子の頭（レベルが 1 上がっている）。 -/
theorem RunA0_LwA {h : ℕ} {A : TrioSeq} (hA : RunA 0 h A) : LwA h A := by
  obtain ⟨b, Y0, M, rfl, rfl, ⟨P, hP, hY0⟩, hM⟩ := hA
  refine ⟨P, hP, ?_⟩
  have h1 := LwB_tower hP (SegA_toSegB hM hP) hY0 1
  rwa [Mtw_succ, Mtw_zero, shiftr01_zero] at h1

theorem BaseOk_RunA : ∀ j : ℕ, BaseOk (RunA j)
  | 0 => by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h A hA
        exact LwA_Aok (RunA0_LwA hA)
      · intro h A hA
        obtain ⟨P, hP, hL⟩ := RunA0_LwA hA
        exact LwB_Ancd hP hL
      · intro h A hA B hB
        obtain ⟨P, hP, r, hr⟩ := RunA0_LwA hA
        exact LvB_hang hP r h A hr B hB
      · rintro h A Blk ⟨b, Y0, M, rfl, rfl, hY0, hM⟩ hcol hmo hre
        refine ⟨b, Y0, M ++ Blk, rfl, by rw [List.append_assoc], hY0, ?_, ?_, ?_⟩
        · exact MidD_append hM.mid (by intro x hx; have := hcol x hx; omega) hmo
        · rw [entry_append_left (List.length_pos_iff.mpr hM.mid.ne)]
          exact hM.head1
        · intro P hP u A' hA'
          rw [shiftr01_append0, ← List.append_assoc]
          have h1 : A' ++ shiftr01 u 0 M ∈ W 0 := hM.reapp P hP u A' hA'
          have hstep : RunA 0 (b + 1 + u) (A' ++ shiftr01 u 0 M) := by
            refine ⟨b + u, A', shiftr01 u 0 M, by omega, rfl, ⟨P, hP, hA'⟩,
              SegA_shift hM u⟩
          exact hre u _ hstep
  | (j + 1) => by
      have hIHj := BaseOk_RunA j
      refine ⟨?_, ?_, ?_, ?_⟩
      · rintro h A ⟨b, A0, N, rfl, rfl, hA0, hN, hN2, hre⟩
        have hmem : A0 ++ N ∈ W 0 := by
          have h1 := hre 0 A0 (by simpa using hA0)
          simpa using h1
        exact Aok_append_Mid (by omega) (hIHj.aok b A0 hA0) hN hmem
      · rintro h A ⟨b, A0, N, rfl, rfl, hA0, hN, hN2, hre⟩
        exact Ancd_append_Mid (hIHj.aok b A0 hA0).ne (hIHj.ancd b A0 hA0) hN
      · rintro h A ⟨b, A0, N, rfl, rfl, hA0, hN, hN2, hre⟩ B hB
        have hbase : ∀ (s : ℕ) (X : TrioSeq), Aok X → RunA j (b + s) X →
            X ++ shiftr01 s 0 N ∈ W 0 := fun s X _ hX => hre s X hX
        have hclose : ∀ (s : ℕ) (X C' : TrioSeq), Aok X → RunA j (b + s) X → Mono C' →
            (∀ (t : ℕ) (Y : TrioSeq), Aok Y → RunA j (b + t) Y →
              Y ++ BlkD (b + 2 + t) (shiftr01 t 0 N) C' ∈ W 0) →
            RunA j (b + s) (X ++ BlkD (b + 2 + s) (shiftr01 s 0 N) C') := by
          intro s X C' _ hX hmoC' hIH
          have hNs : MidD (b + 2 + s) (shiftr01 s 0 N) := MidD_shift hN s
          refine hIHj.close (b + s) X _ hX ?_ (BlkD_mono hNs.mono hmoC') ?_
          · intro x hx
            rcases List.mem_append.mp hx with hh | hh
            · have := MidD_col_ge hNs x hh; omega
            · have := shiftD_col x hh; omega
          · intro t Y hY
            have heq : shiftr01 t 0 (BlkD (b + 2 + s) (shiftr01 s 0 N) C')
                = BlkD (b + 2 + (s + t)) (shiftr01 (s + t) 0 N) C' := by
              simp only [BlkD, shiftr01_append0, shiftr01_add0]
              congr 2
              omega
            rw [heq]
            have hY' : RunA j (b + (s + t)) Y := by
              rwa [show b + (s + t) = b + s + t from by omega]
            exact hIH (s + t) Y (hIHj.aok _ _ hY') hY'
        have hkey := blkD_memS (d := b + 2) (by omega) N hN hbase hclose B hB.mem
          hB.zroot hB.mono hB.root 0 A0 (hIHj.aok b A0 hA0) (by simpa using hA0)
        simp only [shiftr01_zero, Nat.add_zero] at hkey
        rw [BlkD_app] at hkey
        exact hkey
      · rintro h A Blk ⟨b, A0, N, rfl, rfl, hA0, hN, hN2, hre⟩ hcol hmo hcl
        refine ⟨b, A0, N ++ Blk, rfl, by rw [List.append_assoc], hA0,
          MidD_append hN (by intro x hx; have := hcol x hx; omega) hmo, ?_, ?_⟩
        · rw [entry_append_left (List.length_pos_iff.mpr hN.ne)]
          exact hN2
        · intro s X hX
          rw [shiftr01_append0, ← List.append_assoc]
          have h1 : X ++ shiftr01 s 0 N ∈ W 0 := hre s X hX
          have hstep : RunA (j + 1) (b + 1 + s) (X ++ shiftr01 s 0 N) := by
            refine ⟨b + s, X, shiftr01 s 0 N, by omega, rfl, hX, ?_, ?_, ?_⟩
            · have h2 := MidD_shift hN s
              rwa [show b + 2 + s = b + s + 2 from by omega] at h2
            · rw [entry_shift1 (List.length_pos_iff.mpr hN.ne)]
              exact hN2
            · intro t Z hZ
              rw [shiftr01_add0]
              refine hre (s + t) Z ?_
              rwa [show b + (s + t) = b + s + t from by omega]
          exact hcl s _ hstep

#print axioms BaseOk_RunA

/-! ### 走りの塊 `RunU` と、その塔 -/

/-- `RunA j` の頭はどの `j` でも梯子の頭（台座に `RunA j` 自身を取る）。 -/
theorem RunA_LwA (j h : ℕ) (Z : TrioSeq) (hZ : RunA j h Z) : LwA h Z :=
  ⟨RunA j, BaseOk_RunA j, 0, hZ⟩

/-- 走りの塊。`RunU j c U`: `U = (c+1,1,0)` のセグメント ++ `(·,2,0)` を `j` 本
（各段の上のブロック込み）。 -/
def RunU : ℕ → ℕ → TrioSeq → Prop
  | 0, c, U => SegA c U
  | (j + 1), c, U => ∃ U0 N : TrioSeq, U = U0 ++ N ∧ RunU j c U0 ∧
      MidD (c + j + 3) N ∧ 2 ≤ entry N 1 0 ∧
      (∀ (s : ℕ) (X : TrioSeq), RunA j (c + 1 + j + s) X → X ++ shiftr01 s 0 N ∈ W 0)

theorem RunU_mid : ∀ (j c : ℕ) (U : TrioSeq), RunU j c U → MidD (c + 2) U
  | 0, c, U, hU => hU.mid
  | (j + 1), c, U, hU => by
      obtain ⟨U0, N, rfl, hU0, hN, hN2, hre⟩ := hU
      refine MidD_append (RunU_mid j c U0 hU0) ?_ hN.mono
      intro x hx
      have := MidD_col_ge hN x hx
      omega

theorem RunU_head1 : ∀ (j c : ℕ) (U : TrioSeq), RunU j c U → entry U 1 0 < 2
  | 0, _, _, hU => hU.head1
  | (j + 1), c, U, hU => by
      obtain ⟨U0, N, rfl, hU0, hN, hN2, hre⟩ := hU
      rw [entry_append_left (List.length_pos_iff.mpr (RunU_mid j c U0 hU0).ne)]
      exact RunU_head1 j c U0 hU0

theorem RunU_shift : ∀ (j c : ℕ) (U : TrioSeq), RunU j c U → ∀ v : ℕ,
    RunU j (c + v) (shiftr01 v 0 U)
  | 0, c, U, hU, v => SegA_shift hU v
  | (j + 1), c, U, hU, v => by
      obtain ⟨U0, N, rfl, hU0, hN, hN2, hre⟩ := hU
      refine ⟨shiftr01 v 0 U0, shiftr01 v 0 N, by rw [shiftr01_append0],
        RunU_shift j c U0 hU0 v, ?_, ?_, ?_⟩
      · have h1 := MidD_shift hN v
        rwa [show c + j + 3 + v = c + v + j + 3 from by omega] at h1
      · rw [entry_shift1 (List.length_pos_iff.mpr hN.ne)]
        exact hN2
      · intro s X hX
        rw [shiftr01_add0]
        refine hre (v + s) X ?_
        rwa [show c + 1 + j + (v + s) = c + v + 1 + j + s from by omega]

/-- `snocYd_mem` の `hMy`: 継ぐ列より低い記録の行 1 は 2 以上。 -/
theorem RunU_rec : ∀ (j c : ℕ) (U : TrioSeq), RunU j c U →
    ∀ t, 1 ≤ t → t < U.length → entry U 0 t < c + j + 2 →
      (∀ i, t < i → i < U.length → entry U 0 t < entry U 0 i) → 2 ≤ entry U 1 t
  | 0, c, U, hU, t, ht1, htl, hlt, _ => by
      have := hU.mid.tail t ht1 htl
      omega
  | (j + 1), c, U, hU, t, ht1, htl, hlt, hrec => by
      obtain ⟨U0, N, rfl, hU0, hN, hN2, hre⟩ := hU
      have hU0mid := RunU_mid j c U0 hU0
      have hU0len : 0 < U0.length := List.length_pos_iff.mpr hU0mid.ne
      have hNlen : 0 < N.length := List.length_pos_iff.mpr hN.ne
      have hlen : (U0 ++ N).length = U0.length + N.length := by simp
      have hNh : entry (U0 ++ N) 0 U0.length = c + j + 2 := by
        rw [show U0.length = U0.length + 0 from rfl, entry_append_right]
        have := hN.head; omega
      rcases Nat.lt_trichotomy t U0.length with h | h | h
      · rw [entry_append_left h] at hlt ⊢
        have hlt' : entry U0 0 t < c + j + 2 := by
          have := hrec U0.length h (by omega)
          rw [entry_append_left h, hNh] at this
          omega
        refine RunU_rec j c U0 hU0 t ht1 h hlt' ?_
        intro i hti hiU
        have := hrec i hti (by omega)
        rw [entry_append_left h, entry_append_left hiU] at this
        exact this
      · subst h
        rw [show U0.length = U0.length + 0 from rfl, entry_append_right]
        exact hN2
      · exfalso
        obtain ⟨q, rfl⟩ : ∃ q, t = U0.length + q := ⟨t - U0.length, by omega⟩
        rw [entry_append_right] at hlt
        have := hN.tail q (by omega) (by omega)
        omega

theorem RunA_of : ∀ (j c : ℕ) (Y0 U : TrioSeq), LwA c Y0 → RunU j c U →
    RunA j (c + 1 + j) (Y0 ++ U)
  | 0, c, Y0, U, hY0, hU => ⟨c, Y0, U, rfl, rfl, hY0, hU⟩
  | (j + 1), c, Y0, U, hY0, hU => by
      obtain ⟨U0, N, rfl, hU0, hN, hN2, hre⟩ := hU
      refine ⟨c + 1 + j, Y0 ++ U0, N, by omega, by rw [List.append_assoc],
        RunA_of j c Y0 U0 hY0 hU0, ?_, hN2, ?_⟩
      · rwa [show c + 1 + j + 2 = c + j + 3 from by omega]
      · exact hre

theorem RunA_to : ∀ (j h : ℕ) (X : TrioSeq), RunA j h X →
    ∃ (c : ℕ) (Y0 U : TrioSeq), h = c + 1 + j ∧ X = Y0 ++ U ∧ LwA c Y0 ∧ RunU j c U
  | 0, h, X, hX => by
      obtain ⟨b, Y0, M, rfl, rfl, hY0, hM⟩ := hX
      exact ⟨b, Y0, M, rfl, rfl, hY0, hM⟩
  | (j + 1), h, X, hX => by
      obtain ⟨b, A0, N, rfl, rfl, hA0, hN, hN2, hre⟩ := hX
      obtain ⟨c, Y0, U0, rfl, rfl, hY0, hU0⟩ := RunA_to j b A0 hA0
      refine ⟨c, Y0, U0 ++ N, by omega, by rw [List.append_assoc], hY0,
        ⟨U0, N, rfl, hU0, ?_, hN2, ?_⟩⟩
      · rwa [show c + 1 + j + 2 = c + j + 3 from by omega] at hN
      · exact hre

/-- ★★ 走りの塊の塔（歩幅 `j+1`）。段が上がっても `RunA j` のまま。 -/
theorem RunU_tower {j c : ℕ} {Y0 U : TrioSeq} (hY0 : LwA c Y0) (hU : RunU j c U) :
    ∀ n : ℕ, RunA j (c + n * (j + 1) + 1 + j) (Mtwd (j + 1) Y0 U (n + 1))
  | 0 => by
      rw [Mtwd_one]
      simpa using RunA_of j c Y0 U hY0 hU
  | (n + 1) => by
      have hprev := RunU_tower hY0 hU n
      rw [Mtwd_succ]
      have hL : LwA (c + n * (j + 1) + 1 + j) (Mtwd (j + 1) Y0 U (n + 1)) :=
        RunA_LwA j _ _ hprev
      have hmul1 : (j + 1) * (n + 1) = n * (j + 1) + 1 + j := by
        rw [Nat.mul_succ, Nat.mul_comm (j + 1) n]
        omega
      have hmul2 : (n + 1) * (j + 1) = n * (j + 1) + 1 + j := by
        rw [Nat.succ_mul]
        omega
      have hUs : RunU j (c + n * (j + 1) + 1 + j) (shiftr01 ((j + 1) * (n + 1)) 0 U) := by
        have h1 := RunU_shift j c U hU ((j + 1) * (n + 1))
        rwa [show c + (j + 1) * (n + 1) = c + n * (j + 1) + 1 + j from by omega] at h1
      have h2 := RunA_of j _ _ _ hL hUs
      rwa [show c + n * (j + 1) + 1 + j + 1 + j = c + (n + 1) * (j + 1) + 1 + j from by
        omega] at h2

theorem RunU_tower_mem {j c : ℕ} {Y0 U : TrioSeq} (hY0 : LwA c Y0) (hU : RunU j c U) :
    ∀ n : ℕ, Mtwd (j + 1) Y0 U n ∈ W 0
  | 0 => by rw [Mtwd_zero]; exact (LwA_Aok hY0).mem
  | (n + 1) => ((BaseOk_RunA j).aok _ _ (RunU_tower hY0 hU n)).mem

/-- ★★★ 走りの上に `(·,2,0)` をもう 1 本継げる。 -/
theorem RunA_snoc2 (j h : ℕ) (X : TrioSeq) (hX : RunA j h X) :
    X ++ [((h + 1, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  obtain ⟨c, Y0, U, rfl, rfl, hY0, hU⟩ := RunA_to j _ X hX
  have hmid : MidD (c + 2) U := RunU_mid j c U hU
  have hne : Y0 ≠ [] := (LwA_Aok hY0).ne
  have h1 := snocYd_mem (Y0 := Y0) (M := U) (L := c + 1) (y := 2) (dl := j + 1)
    hne (by rwa [show c + 1 + 1 = c + 2 from by omega]) (RunU_head1 j c U hU)
    ?_ (by omega) (by omega) (RunU_tower_mem hY0 hU)
  · rwa [show c + 1 + (j + 1) = c + 1 + j + 1 from by omega] at h1
  · intro t ht1 htl hlt hrec
    refine RunU_rec j c U hU t ht1 htl ?_ hrec
    omega

#print axioms RunA_snoc2

/-! ### シート行294 `X(1,1,0)(2,2,0)(3,3,0) = psi(W_w + psi_1(W_3))`

基本列は `(·,2,0)` が 1 本ずつ伸びる列。塊 `Uu n = (1,1,0)(2,2,0)...(n+1,2,0)` を
`RunU n 0` に入れれば `Q ++ Uu n ∈ W 0` が出る。 -/

/-- `Uu n = (1,1,0)(2,2,0)(3,2,0)...(n+1,2,0)`（`(·,2,0)` が `n` 本）。 -/
def Uu : ℕ → TrioSeq
  | 0 => [((1, 1, 0) : ℕ × ℕ × ℕ)]
  | (n + 1) => Uu n ++ [((n + 2, 2, 0) : ℕ × ℕ × ℕ)]

theorem LwA_Q : LwA 0 Q :=
  ⟨fun h A => Aok A ∧ h = 0, BaseOk_zero, 0, ⟨(Aok_Q : Aok Q), rfl⟩⟩

theorem RunU_Uu : ∀ n : ℕ, RunU n 0 (Uu n)
  | 0 => by
      have h := SegA_one 0
      simpa [Uu] using h
  | (n + 1) => by
      refine ⟨Uu n, [((n + 2, 2, 0) : ℕ × ℕ × ℕ)], rfl, RunU_Uu n, ?_, ?_, ?_⟩
      · have h := MidD_col (n + 2) 2 (by omega) (by omega)
        rwa [show n + 2 + 1 = 0 + n + 3 from by omega] at h
      · show (2 : ℕ) ≤ 2
        omega
      · intro s X hX
        have h := RunA_snoc2 n (0 + 1 + n + s) X hX
        rw [shift_col]
        rwa [show 0 + 1 + n + s + 1 = n + 2 + s from by omega] at h

theorem RunA_Uu (n : ℕ) : RunA n (0 + 1 + n) (Q ++ Uu n) :=
  RunA_of n 0 Q (Uu n) LwA_Q (RunU_Uu n)

theorem Uu_mem (n : ℕ) : Q ++ Uu n ∈ W 0 :=
  ((BaseOk_RunA n).aok _ _ (RunA_Uu n)).mem

theorem Mtw_Dg1_Uu : ∀ n : ℕ,
    Mtw (Q ++ [((1, 1, 0) : ℕ × ℕ × ℕ)]) [((2, 2, 0) : ℕ × ℕ × ℕ)] n = Q ++ Uu n
  | 0 => by rw [Mtw_zero]; rfl
  | (n + 1) => by
      rw [Mtw_succ, Mtw_Dg1_Uu n, shift_col]
      show (Q ++ Uu n) ++ [((2 + n, 2, 0) : ℕ × ℕ × ℕ)]
        = Q ++ (Uu n ++ [((n + 2, 2, 0) : ℕ × ℕ × ℕ)])
      rw [List.append_assoc, show 2 + n = n + 2 from by omega]

/-- シート行294。 -/
def R294 : TrioSeq := [(0, 0, 0), (1, 1, 1), (1, 1, 0), (2, 2, 0), (3, 3, 0)]

/-- ★★★ 行294 `(0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0) ∈ W 0`。 -/
theorem R294_mem : R294 ∈ W 0 := by
  have h : R294 = ((Q ++ [((1, 1, 0) : ℕ × ℕ × ℕ)]) ++ [((2, 2, 0) : ℕ × ℕ × ℕ)])
      ++ [((2 + 1, 3, 0) : ℕ × ℕ × ℕ)] := by
    simp [R294, Q]
  rw [h]
  refine snocY_mem (L := 2) (y := 3) (by simp [Q]) ?_ ?_ (by omega) ?_
  · have hM := MidD_col 2 2 (by omega) (by omega)
    rwa [show 2 + 1 = 2 + 1 from rfl] at hM
  · show (2 : ℕ) < 3
    omega
  · intro n
    rw [Mtw_Dg1_Uu n]
    exact Uu_mem n

#print axioms R294_mem

/-! ## ★★★ 段の階段 `Vis`（行295/296 への道）

`RunA j` は「LwA の台座 ++ `(·,1,0)` の頭 ++ `(·,≥2,0)` のブロック `j` 本」だった。
`(·,3,0)` を継ぐには「`(·,2,0)` の頭 ++ `(·,≥3,0)` のブロック列」を、`(·,2,0)` を継げる台座
（`∃ j', RunA j'`）の上に置く。塔の各段はこの台座に戻る必要があるが、上段のユニット
`n ++ N_1..N_j` は `j+1` 段ぶん高さを使うので、下段のブロックを **群**（`MidD` ブロックの列、
レベルはブロック数ぶん上がる）にしておく。上段のユニットは平坦化して下段の 1 群になる。

* `VU E hl bl j c U`: 群。`U = M0 ++ N_1 ++ ... ++ N_j`、`M0` は `MidD (c+2)` で頭の行 1 が `hl` 以上、
  再継ぎは `E` の上。`N_i` は `MidD (c+i+2)` で頭の行 1 が `bl` 以上、再継ぎは
  「`E` の元 ++ 同じ群の先頭 `i-1` 本」の上。
* `VisG E Hd g j h A`: 台座 `E` の元 ++ 頭（述語 `Hd`）++ 群 `j` 個（行 1 は `g` 以上）。
  群 `i` の再継ぎは `VisG E Hd g (i-1)` の上。 -/

/-- 群。 -/
def VU (E : ℕ → TrioSeq → Prop) (hl bl : ℕ) : ℕ → ℕ → TrioSeq → Prop
  | 0, c, U => MidD (c + 2) U ∧ hl ≤ entry U 1 0 ∧
      (∀ (s : ℕ) (X : TrioSeq), E (c + s) X → X ++ shiftr01 s 0 U ∈ W 0)
  | (j + 1), c, U => ∃ U0 N : TrioSeq, U = U0 ++ N ∧ VU E hl bl j c U0 ∧
      MidD (c + j + 3) N ∧ bl ≤ entry N 1 0 ∧
      (∀ (s : ℕ) (X : TrioSeq),
        (∃ (c' : ℕ) (Y0 U' : TrioSeq), c + s = c' ∧ X = Y0 ++ U' ∧ E c' Y0 ∧ VU E hl bl j c' U') →
        X ++ shiftr01 s 0 N ∈ W 0)

/-- 群の頭つきクラス: 台座の元 ++ 群（`j+1` 本）。レベルは `c + 1 + j`。 -/
def VUC (E : ℕ → TrioSeq → Prop) (hl bl j : ℕ) (h : ℕ) (A : TrioSeq) : Prop :=
  ∃ (c : ℕ) (Y0 U : TrioSeq), h = c + 1 + j ∧ A = Y0 ++ U ∧ E c Y0 ∧ VU E hl bl j c U

theorem VU_mid {E : ℕ → TrioSeq → Prop} {hl bl : ℕ} :
    ∀ (j c : ℕ) (U : TrioSeq), VU E hl bl j c U → MidD (c + 2) U
  | 0, _, _, hU => hU.1
  | (j + 1), c, U, hU => by
      obtain ⟨U0, N, rfl, hU0, hN, -, -⟩ := hU
      refine MidD_append (VU_mid j c U0 hU0) ?_ hN.mono
      intro x hx
      have := MidD_col_ge hN x hx
      omega

theorem VU_head {E : ℕ → TrioSeq → Prop} {hl bl : ℕ} :
    ∀ (j c : ℕ) (U : TrioSeq), VU E hl bl j c U → hl ≤ entry U 1 0
  | 0, _, _, hU => hU.2.1
  | (j + 1), c, U, hU => by
      obtain ⟨U0, N, rfl, hU0, -, -, -⟩ := hU
      rw [entry_append_left (List.length_pos_iff.mpr (VU_mid j c U0 hU0).ne)]
      exact VU_head j c U0 hU0

theorem VU_shift {E : ℕ → TrioSeq → Prop} {hl bl : ℕ} :
    ∀ (j c : ℕ) (U : TrioSeq), VU E hl bl j c U → ∀ v : ℕ,
      VU E hl bl j (c + v) (shiftr01 v 0 U)
  | 0, c, U, hU, v => by
      obtain ⟨hM, hh, hre⟩ := hU
      refine ⟨?_, ?_, ?_⟩
      · have h1 := MidD_shift hM v
        rwa [show c + 2 + v = c + v + 2 from by omega] at h1
      · rw [entry_shift1 (List.length_pos_iff.mpr hM.ne)]
        exact hh
      · intro s X hX
        rw [shiftr01_add0]
        refine hre (v + s) X ?_
        rwa [show c + (v + s) = c + v + s from by omega]
  | (j + 1), c, U, hU, v => by
      obtain ⟨U0, N, rfl, hU0, hN, hN2, hre⟩ := hU
      refine ⟨shiftr01 v 0 U0, shiftr01 v 0 N, by rw [shiftr01_append0],
        VU_shift j c U0 hU0 v, ?_, ?_, ?_⟩
      · have h1 := MidD_shift hN v
        rwa [show c + j + 3 + v = c + v + j + 3 from by omega] at h1
      · rw [entry_shift1 (List.length_pos_iff.mpr hN.ne)]
        exact hN2
      · rintro s X ⟨c', Y0, U', hc, rfl, hY0, hU'⟩
        rw [shiftr01_add0]
        exact hre (v + s) (Y0 ++ U') ⟨c', Y0, U', by omega, rfl, hY0, hU'⟩

/-- 群の記録: 継ぐ高さより低い記録の行 1 は `bl` 以上（頭を除く）。 -/
theorem VU_rec {E : ℕ → TrioSeq → Prop} {hl bl : ℕ} :
    ∀ (j c : ℕ) (U : TrioSeq), VU E hl bl j c U →
    ∀ t, 1 ≤ t → t < U.length → entry U 0 t < c + j + 2 →
      (∀ i, t < i → i < U.length → entry U 0 t < entry U 0 i) → bl ≤ entry U 1 t
  | 0, c, U, hU, t, ht1, htl, hlt, _ => by
      have := hU.1.tail t ht1 htl
      omega
  | (j + 1), c, U, hU, t, ht1, htl, hlt, hrec => by
      obtain ⟨U0, N, rfl, hU0, hN, hN2, -⟩ := hU
      have hU0mid := VU_mid j c U0 hU0
      have hU0len : 0 < U0.length := List.length_pos_iff.mpr hU0mid.ne
      have hNlen : 0 < N.length := List.length_pos_iff.mpr hN.ne
      have hlen : (U0 ++ N).length = U0.length + N.length := by simp
      have hNh : entry (U0 ++ N) 0 U0.length = c + j + 2 := by
        rw [show U0.length = U0.length + 0 from rfl, entry_append_right]
        have := hN.head; omega
      rcases Nat.lt_trichotomy t U0.length with h | h | h
      · rw [entry_append_left h] at hlt ⊢
        have hlt' : entry U0 0 t < c + j + 2 := by
          have := hrec U0.length h (by omega)
          rw [entry_append_left h, hNh] at this
          omega
        refine VU_rec j c U0 hU0 t ht1 h hlt' ?_
        intro i hti hiU
        have := hrec i hti (by omega)
        rw [entry_append_left h, entry_append_left hiU] at this
        exact this
      · subst h
        rw [show U0.length = U0.length + 0 from rfl, entry_append_right]
        exact hN2
      · exfalso
        obtain ⟨q, rfl⟩ : ∃ q, t = U0.length + q := ⟨t - U0.length, by omega⟩
        rw [entry_append_right] at hlt
        have := hN.tail q (by omega) (by omega)
        omega

/-- 群は台座のどの元にも（シフトして）継げる。 -/
theorem VU_reapp {E : ℕ → TrioSeq → Prop} {hl bl : ℕ} :
    ∀ (j c : ℕ) (U : TrioSeq), VU E hl bl j c U →
    ∀ (s : ℕ) (X : TrioSeq), E (c + s) X → X ++ shiftr01 s 0 U ∈ W 0
  | 0, _, _, hU, s, X, hX => hU.2.2 s X hX
  | (j + 1), c, U, hU, s, X, hX => by
      obtain ⟨U0, N, rfl, hU0, -, -, hre⟩ := hU
      rw [shiftr01_append0, ← List.append_assoc]
      exact hre s (X ++ shiftr01 s 0 U0)
        ⟨c + s, X, shiftr01 s 0 U0, rfl, rfl, hX, VU_shift j c U0 hU0 s⟩

theorem VUC_mem {E : ℕ → TrioSeq → Prop} {hl bl j h : ℕ} {A : TrioSeq}
    (hA : VUC E hl bl j h A) : A ∈ W 0 := by
  obtain ⟨c, Y0, U, rfl, rfl, hY0, hU⟩ := hA
  have h1 := VU_reapp j c U hU 0 Y0 (by simpa using hY0)
  simpa using h1

/-! ### 群の頭つきクラス `VisG` -/

/-- 頭の述語 `Hd` に要る性質。 -/
structure HdOk (E : ℕ → TrioSeq → Prop) (Hd : ℕ → TrioSeq → Prop) : Prop where
  mid : ∀ (c : ℕ) (M : TrioSeq), Hd c M → MidD (c + 2) M
  reapp : ∀ (c : ℕ) (M : TrioSeq), Hd c M → ∀ (s : ℕ) (X : TrioSeq), E (c + s) X →
      X ++ shiftr01 s 0 M ∈ W 0
  shift : ∀ (c : ℕ) (M : TrioSeq), Hd c M → ∀ v : ℕ, Hd (c + v) (shiftr01 v 0 M)

/-- 台座 `E` の元 ++ 頭 ++ 群 `j` 個。 -/
def VisG (E : ℕ → TrioSeq → Prop) (Hd : ℕ → TrioSeq → Prop) (g : ℕ) :
    ℕ → ℕ → TrioSeq → Prop
  | 0, h, A => ∃ (c : ℕ) (Y0 M : TrioSeq), h = c + 1 ∧ A = Y0 ++ M ∧ E c Y0 ∧ Hd c M
  | (j + 1), h, A => ∃ (b r : ℕ) (A0 G : TrioSeq), h = b + 1 + r ∧ A = A0 ++ G ∧
      VisG E Hd g j b A0 ∧ VU (VisG E Hd g j) g g r b G

/-- ユニット（頭 ++ 群 `j` 個）。`VUn j c e U`: レベル `c` の上、高さ `e` ぶん（頂上はレベル `c+e`）。 -/
def VUn (E : ℕ → TrioSeq → Prop) (Hd : ℕ → TrioSeq → Prop) (g : ℕ) :
    ℕ → ℕ → ℕ → TrioSeq → Prop
  | 0, c, e, U => e = 1 ∧ Hd c U
  | (j + 1), c, e, U => ∃ (e0 r : ℕ) (U0 G : TrioSeq), U = U0 ++ G ∧ e = e0 + 1 + r ∧
      VUn E Hd g j c e0 U0 ∧ VU (VisG E Hd g j) g g r (c + e0) G

theorem VisG_of {E Hd : ℕ → TrioSeq → Prop} {g : ℕ} :
    ∀ (j c e : ℕ) (Y0 U : TrioSeq), E c Y0 → VUn E Hd g j c e U →
      VisG E Hd g j (c + e) (Y0 ++ U)
  | 0, c, e, Y0, U, hY0, hU => by
      obtain ⟨rfl, hU⟩ := hU
      exact ⟨c, Y0, U, rfl, rfl, hY0, hU⟩
  | (j + 1), c, e, Y0, U, hY0, hU => by
      obtain ⟨e0, r, U0, G, rfl, rfl, hU0, hG⟩ := hU
      exact ⟨c + e0, r, Y0 ++ U0, G, by omega, by rw [List.append_assoc],
        VisG_of j c e0 Y0 U0 hY0 hU0, hG⟩

theorem VisG_to {E Hd : ℕ → TrioSeq → Prop} {g : ℕ} :
    ∀ (j h : ℕ) (A : TrioSeq), VisG E Hd g j h A →
      ∃ (c e : ℕ) (Y0 U : TrioSeq), h = c + e ∧ A = Y0 ++ U ∧ E c Y0 ∧ VUn E Hd g j c e U
  | 0, h, A, hA => by
      obtain ⟨c, Y0, M, rfl, rfl, hY0, hM⟩ := hA
      exact ⟨c, 1, Y0, M, rfl, rfl, hY0, rfl, hM⟩
  | (j + 1), h, A, hA => by
      obtain ⟨b, r, A0, G, rfl, rfl, hA0, hG⟩ := hA
      obtain ⟨c, e0, Y0, U0, rfl, rfl, hY0, hU0⟩ := VisG_to j b A0 hA0
      exact ⟨c, e0 + 1 + r, Y0, U0 ++ G, by omega, by rw [List.append_assoc], hY0,
        ⟨e0, r, U0, G, rfl, rfl, hU0, hG⟩⟩

theorem VUn_pos {E Hd : ℕ → TrioSeq → Prop} {g : ℕ} :
    ∀ (j c e : ℕ) (U : TrioSeq), VUn E Hd g j c e U → 1 ≤ e
  | 0, _, _, _, hU => by have := hU.1; omega
  | (j + 1), c, e, U, hU => by
      obtain ⟨e0, r, U0, G, -, he, -, -⟩ := hU
      omega

theorem VUn_mid {E Hd : ℕ → TrioSeq → Prop} {g : ℕ} (hH : HdOk E Hd) :
    ∀ (j c e : ℕ) (U : TrioSeq), VUn E Hd g j c e U → MidD (c + 2) U
  | 0, c, _, U, hU => hH.mid c U hU.2
  | (j + 1), c, e, U, hU => by
      obtain ⟨e0, r, U0, G, rfl, rfl, hU0, hG⟩ := hU
      have he0 := VUn_pos j c e0 U0 hU0
      refine MidD_append (VUn_mid hH j c e0 U0 hU0) ?_ (VU_mid r _ G hG).mono
      intro x hx
      have := MidD_col_ge (VU_mid r _ G hG) x hx
      omega

theorem VUn_head {E Hd : ℕ → TrioSeq → Prop} {g : ℕ} (hH : HdOk E Hd) :
    ∀ (j c e : ℕ) (U : TrioSeq), VUn E Hd g j c e U →
      ∃ M : TrioSeq, Hd c M ∧ entry U 1 0 = entry M 1 0
  | 0, c, _, U, hU => ⟨U, hU.2, rfl⟩
  | (j + 1), c, e, U, hU => by
      obtain ⟨e0, r, U0, G, rfl, rfl, hU0, -⟩ := hU
      obtain ⟨M, hM, hM1⟩ := VUn_head hH j c e0 U0 hU0
      refine ⟨M, hM, ?_⟩
      rw [entry_append_left (List.length_pos_iff.mpr (VUn_mid hH j c e0 U0 hU0).ne)]
      exact hM1

theorem VUn_shift {E Hd : ℕ → TrioSeq → Prop} {g : ℕ} (hH : HdOk E Hd) :
    ∀ (j c e : ℕ) (U : TrioSeq), VUn E Hd g j c e U → ∀ v : ℕ,
      VUn E Hd g j (c + v) e (shiftr01 v 0 U)
  | 0, c, e, U, hU, v => ⟨hU.1, hH.shift c U hU.2 v⟩
  | (j + 1), c, e, U, hU, v => by
      obtain ⟨e0, r, U0, G, rfl, rfl, hU0, hG⟩ := hU
      refine ⟨e0, r, shiftr01 v 0 U0, shiftr01 v 0 G, by rw [shiftr01_append0], rfl,
        VUn_shift hH j c e0 U0 hU0 v, ?_⟩
      have h1 := VU_shift r (c + e0) G hG v
      rwa [show c + e0 + v = c + v + e0 from by omega] at h1

/-- ユニットの記録: 頂上より低い記録（頭を除く）の行 1 は `g` 以上。 -/
theorem VUn_rec {E Hd : ℕ → TrioSeq → Prop} {g : ℕ} (hH : HdOk E Hd) :
    ∀ (j c e : ℕ) (U : TrioSeq), VUn E Hd g j c e U →
    ∀ t, 1 ≤ t → t < U.length → entry U 0 t < c + e + 1 →
      (∀ i, t < i → i < U.length → entry U 0 t < entry U 0 i) → g ≤ entry U 1 t
  | 0, c, e, U, hU, t, ht1, htl, hlt, _ => by
      obtain ⟨rfl, hM⟩ := hU
      have := (hH.mid c U hM).tail t ht1 htl
      omega
  | (j + 1), c, e, U, hU, t, ht1, htl, hlt, hrec => by
      obtain ⟨e0, r, U0, G, rfl, rfl, hU0, hG⟩ := hU
      have hU0mid := VUn_mid hH j c e0 U0 hU0
      have hGmid := VU_mid r _ G hG
      have hU0len : 0 < U0.length := List.length_pos_iff.mpr hU0mid.ne
      have hGlen : 0 < G.length := List.length_pos_iff.mpr hGmid.ne
      have hlen : (U0 ++ G).length = U0.length + G.length := by simp
      have hGh : entry (U0 ++ G) 0 U0.length = c + e0 + 1 := by
        rw [show U0.length = U0.length + 0 from rfl, entry_append_right]
        have := hGmid.head; omega
      rcases Nat.lt_trichotomy t U0.length with h | h | h
      · rw [entry_append_left h] at hlt ⊢
        have hlt' : entry U0 0 t < c + e0 + 1 := by
          have := hrec U0.length h (by omega)
          rw [entry_append_left h, hGh] at this
          omega
        refine VUn_rec hH j c e0 U0 hU0 t ht1 h hlt' ?_
        intro i hti hiU
        have := hrec i hti (by omega)
        rw [entry_append_left h, entry_append_left hiU] at this
        exact this
      · subst h
        rw [show U0.length = U0.length + 0 from rfl, entry_append_right]
        exact VU_head r _ G hG
      · obtain ⟨q, rfl⟩ : ∃ q, t = U0.length + q := ⟨t - U0.length, by omega⟩
        rw [entry_append_right] at hlt ⊢
        refine VU_rec r (c + e0) G hG q (by omega) (by omega) (by omega) ?_
        intro i hqi hiG
        have := hrec (U0.length + i) (by omega) (by omega)
        rw [entry_append_right, entry_append_right] at this
        exact this

/-! ## ★★★ ゆっくり戦法: 行294 の上に継ぐ

`R294 = (0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)` の上（高さ 4）に継ぐには、junk `(3,3,0)` の**上**に
吊るす補題が要る。`blkD_memS` を `M = (3,3,0) ++ junk`、不変量 = 「`RunA j` の頭 ++ `(2,2,0)` ++ junk」
で回す。junk はどの `RunA j` の頭にも（上向きにシフトして）継げるものに限る（`Jk2 s`）。
高さは絶対で持つ（吸収した junk の再継ぎは上向きシフトでしか取れない）。 -/

/-- 頭 `(2+s,2,0)` の後ろの junk: 高さ `3+s` 以上、`Mono`、どの `RunA j` の頭にも継げる。 -/
def Jk2 (s : ℕ) (J : TrioSeq) : Prop :=
  (∀ x ∈ J, 3 + s ≤ x.1) ∧ Mono J ∧
  ∀ (j t : ℕ) (X : TrioSeq), RunA j (1 + s + t) X →
    X ++ ([((2 + s + t, 2, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J) ∈ W 0

theorem Jk2_nil (s : ℕ) : Jk2 s [] := by
  refine ⟨by simp, by intro c hc; simp at hc, ?_⟩
  intro j t X hX
  have h := RunA_snoc2 j (1 + s + t) X hX
  simpa [shiftr01, show 1 + s + t + 1 = 2 + s + t from by omega] using h

theorem Jk2_shift {s : ℕ} {J : TrioSeq} (hJ : Jk2 s J) (u : ℕ) :
    Jk2 (s + u) (shiftr01 u 0 J) := by
  refine ⟨?_, shiftD_mono hJ.2.1, ?_⟩
  · intro x hx
    simp only [shiftr01, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have := hJ.1 p hp
    dsimp only
    omega
  · intro j t X hX
    rw [shiftr01_add0]
    have hX' : RunA j (1 + s + (u + t)) X := by
      rw [show 1 + s + (u + t) = 1 + (s + u) + t from by omega]; exact hX
    have h := hJ.2.2 j (u + t) X hX'
    rw [show 2 + (s + u) + t = 2 + s + (u + t) from by omega]
    exact h

theorem Jk2_mid {s : ℕ} {J : TrioSeq} (hJ : Jk2 s J) :
    MidD (3 + s) ([((2 + s, 2, 0) : ℕ × ℕ × ℕ)] ++ J) := by
  have h := MidD_append (MidD_col (2 + s) 2 (by omega) (by omega))
    (by intro x hx; have := hJ.1 x hx; omega) hJ.2.1
  rwa [show 2 + s + 1 = 3 + s from by omega] at h

theorem entry_cons_append_1 (c : ℕ × ℕ × ℕ) (J : TrioSeq) :
    entry ([c] ++ J) 1 0 = c.2.1 := by
  simp [entry]

/-- junk つきブロックはどの `RunA j` の頭にも継げる（`RunA (j+1)`）。 -/
theorem Jk2_blk {s : ℕ} {J : TrioSeq} (hJ : Jk2 s J) {j : ℕ} {X : TrioSeq}
    (hX : RunA j (1 + s) X) :
    RunA (j + 1) (2 + s) (X ++ ([((2 + s, 2, 0) : ℕ × ℕ × ℕ)] ++ J)) := by
  refine ⟨1 + s, X, _, by omega, rfl, hX, ?_, ?_, ?_⟩
  · have h := Jk2_mid hJ
    rwa [show 3 + s = 1 + s + 2 from by omega] at h
  · rw [entry_cons_append_1]
  · intro t X' hX'
    simpa [shiftr01_append0, shift_col] using hJ.2.2 j t X' hX'

theorem Jk2_tw {s : ℕ} {J : TrioSeq} (hJ : Jk2 s J) {j : ℕ} {X : TrioSeq}
    (hX : RunA j (1 + s) X) :
    ∀ n : ℕ, RunA (j + n) (1 + s + n) (Mtw X ([((2 + s, 2, 0) : ℕ × ℕ × ℕ)] ++ J) n)
  | 0 => by simpa [Mtw_zero] using hX
  | (n + 1) => by
      rw [Mtw_succ, shiftr01_append0, shift_col]
      have ih := Jk2_tw hJ hX n
      rw [show 1 + s + n = 1 + (s + n) from by omega] at ih
      have h := Jk2_blk (Jk2_shift hJ n) ih
      rw [show 2 + (s + n) = 2 + s + n from by omega] at h
      rw [show 1 + s + (n + 1) = 2 + s + n from by omega,
        show j + (n + 1) = j + n + 1 from by omega]
      exact h

/-- junk つきブロックの直後（頭の 1 つ上）に `(·,3,0)` を継げる。 -/
theorem Jk2_snoc3 {s : ℕ} {J : TrioSeq} (hJ : Jk2 s J) {j : ℕ} {X : TrioSeq}
    (hX : RunA j (1 + s) X) :
    (X ++ ([((2 + s, 2, 0) : ℕ × ℕ × ℕ)] ++ J)) ++ [((3 + s, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hXok : Aok X := (BaseOk_RunA j).aok _ _ hX
  have hM : MidD (2 + s + 1) ([((2 + s, 2, 0) : ℕ × ℕ × ℕ)] ++ J) := by
    have h := Jk2_mid hJ
    rwa [show 3 + s = 2 + s + 1 from by omega] at h
  have h := snocY_mem (L := 2 + s) (y := 3) hXok.ne hM
    (by rw [entry_cons_append_1]; show (2 : ℕ) < 3; omega)
    (by omega) (fun n => ((BaseOk_RunA (j + n)).aok _ _ (Jk2_tw hJ hX n)).mem)
  rwa [show 2 + s + 1 = 3 + s from by omega] at h

/-- `RunA j` の頭 ++ `(2+s,2,0)` ++ junk。レベル `2+s`。 -/
def Pk2 (s : ℕ) (Y : TrioSeq) : Prop :=
  ∃ (j : ℕ) (X J : TrioSeq), RunA j (1 + s) X ∧
    Y = X ++ ([((2 + s, 2, 0) : ℕ × ℕ × ℕ)] ++ J) ∧ Jk2 s J

theorem Pk2_Aok {s : ℕ} {Y : TrioSeq} (hY : Pk2 s Y) : Aok Y := by
  obtain ⟨j, X, J, hX, rfl, hJ⟩ := hY
  have hmem := hJ.2.2 j 0 X (by simpa using hX)
  simp only [shiftr01_zero, Nat.add_zero] at hmem
  exact Aok_append_Mid (by omega) ((BaseOk_RunA j).aok _ _ hX) (Jk2_mid hJ) hmem

theorem Pk2_Ancd {s : ℕ} {Y : TrioSeq} (hY : Pk2 s Y) : Ancd (3 + s) Y := by
  obtain ⟨j, X, J, hX, rfl, hJ⟩ := hY
  have h1 := (BaseOk_RunA j).ancd _ _ hX
  have hM := Jk2_mid hJ
  rw [show 3 + s = 2 + s + 1 from by omega] at hM ⊢
  rw [show 1 + s + 1 = 2 + s from by omega] at h1
  exact Ancd_append_Mid ((BaseOk_RunA j).aok _ _ hX).ne h1 hM

theorem BlkD_shift_eq (d s : ℕ) (M C : TrioSeq) :
    BlkD (d + s) (shiftr01 s 0 M) C = shiftr01 s 0 M ++ shiftr01 (d + s) 0 C := rfl

/-- `blkD_memS` の `hclose`: 吊るした junk を `(2,2,0)` の junk に吸収する。 -/
theorem Pk2_absorb {s : ℕ} {M : TrioSeq} (hM : MidD (4 + s) M) {C' : TrioSeq} (hmoC' : Mono C')
    (hIH : ∀ (t : ℕ) (A'' : TrioSeq), Aok A'' → Pk2 (s + t) A'' →
      A'' ++ BlkD (4 + s + t) (shiftr01 t 0 M) C' ∈ W 0)
    (t : ℕ) (A' : TrioSeq) (hA' : Pk2 (s + t) A') :
    Pk2 (s + t) (A' ++ BlkD (4 + s + t) (shiftr01 t 0 M) C') := by
  obtain ⟨j, X, J, hX, rfl, hJ⟩ := hA'
  refine ⟨j, X, J ++ BlkD (4 + s + t) (shiftr01 t 0 M) C', hX, by simp [List.append_assoc],
    ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hJ.1 x h
    · rcases List.mem_append.mp h with h' | h'
      · have := MidD_col_ge (MidD_shift hM t) x h'
        omega
      · have := shiftD_col x h'
        omega
  · have h1 : Mono (J ++ shiftr01 t 0 M) := by
      intro c hc
      rcases List.mem_append.mp hc with h | h
      · exact hJ.2.1 c h
      · exact shiftD_mono hM.mono c h
    have h2 := BlkD_mono (d := 4 + s + t) h1 hmoC'
    simpa [BlkD, List.append_assoc] using h2
  · intro j' t' X' hX'
    have hA'' : Pk2 (s + (t + t')) (X' ++ ([((2 + (s + t) + t', 2, 0) : ℕ × ℕ × ℕ)]
        ++ shiftr01 t' 0 J)) := by
      refine ⟨j', X', shiftr01 t' 0 J, ?_, ?_, ?_⟩
      · rw [show 1 + (s + (t + t')) = 1 + (s + t) + t' from by omega]; exact hX'
      · rw [show 2 + (s + (t + t')) = 2 + (s + t) + t' from by omega]
      · have h := Jk2_shift hJ t'
        rwa [show s + t + t' = s + (t + t') from by omega] at h
    have h := hIH (t + t') _ (Pk2_Aok hA'') hA''
    rw [BlkD_shift_eq] at h ⊢
    rw [shiftr01_append0, shiftr01_append0, shiftr01_add0, shiftr01_add0,
      show 4 + s + t + t' = 4 + s + (t + t') from by omega, ← List.append_assoc,
      show t + t' = t + t' from rfl]
    rw [show 4 + s + (t + t') = 4 + s + (t + t') from rfl] at h
    simpa only [List.append_assoc] using h

/-- `(3+s,3,0)` の後ろの junk: 高さ `4+s` 以上、`Mono`、`Pk2` の元の上に継げる。 -/
def Jk3 (s : ℕ) (J : TrioSeq) : Prop :=
  (∀ x ∈ J, 4 + s ≤ x.1) ∧ Mono J ∧
  ∀ (t : ℕ) (Y : TrioSeq), Pk2 (s + t) Y →
    Y ++ ([((3 + s + t, 3, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J) ∈ W 0

theorem Jk3_nil (s : ℕ) : Jk3 s [] := by
  refine ⟨by simp, by intro c hc; simp at hc, ?_⟩
  rintro t Y ⟨j, X, J, hX, rfl, hJ⟩
  have h := Jk2_snoc3 hJ hX
  simpa [shiftr01, show 3 + (s + t) = 3 + s + t from by omega] using h

theorem Jk3_shift {s : ℕ} {J : TrioSeq} (hJ : Jk3 s J) (u : ℕ) :
    Jk3 (s + u) (shiftr01 u 0 J) := by
  refine ⟨?_, shiftD_mono hJ.2.1, ?_⟩
  · intro x hx
    simp only [shiftr01, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have := hJ.1 p hp
    dsimp only
    omega
  · intro t Y hY
    rw [shiftr01_add0]
    have hY' : Pk2 (s + (u + t)) Y := by
      rw [show s + (u + t) = s + u + t from by omega]; exact hY
    have h := hJ.2.2 (u + t) Y hY'
    rw [show 3 + (s + u) + t = 3 + s + (u + t) from by omega]
    exact h

theorem Jk3_mid {s : ℕ} {J : TrioSeq} (hJ : Jk3 s J) :
    MidD (4 + s) ([((3 + s, 3, 0) : ℕ × ℕ × ℕ)] ++ J) := by
  have h := MidD_append (MidD_col (3 + s) 3 (by omega) (by omega))
    (by intro x hx; have := hJ.1 x hx; omega) hJ.2.1
  rwa [show 3 + s + 1 = 4 + s from by omega] at h

/-- `Pk2` の元 ++ `(3+s,3,0)` ++ junk。レベル `3+s`。 -/
def Pk23 (h : ℕ) (A : TrioSeq) : Prop :=
  ∃ (s : ℕ) (Y J : TrioSeq), h = 3 + s ∧ Pk2 s Y ∧
    A = Y ++ ([((3 + s, 3, 0) : ℕ × ℕ × ℕ)] ++ J) ∧ Jk3 s J

theorem Pk23_aok (h : ℕ) (A : TrioSeq) (hA : Pk23 h A) : Aok A := by
  obtain ⟨s, Y, J, rfl, hY, rfl, hJ⟩ := hA
  have hmem := hJ.2.2 0 Y (by simpa using hY)
  simp only [shiftr01_zero, Nat.add_zero] at hmem
  exact Aok_append_Mid (by omega) (Pk2_Aok hY) (Jk3_mid hJ) hmem

theorem Pk23_ancd (h : ℕ) (A : TrioSeq) (hA : Pk23 h A) : Ancd (h + 1) A := by
  obtain ⟨s, Y, J, rfl, hY, rfl, hJ⟩ := hA
  have hM := Jk3_mid hJ
  rw [show 4 + s = 3 + s + 1 from by omega] at hM
  exact Ancd_append_Mid (Pk2_Aok hY).ne (Pk2_Ancd hY) hM

/-- ★★ `Pk23` の頭の上（レベル `+1`）に `Bok` を吊るせる。 -/
theorem Pk23_hang (h : ℕ) (A : TrioSeq) (hA : Pk23 h A) (B : TrioSeq) (hB : Bok B) :
    A ++ shiftr01 (h + 1) 0 B ∈ W 0 := by
  obtain ⟨s, Y, J, rfl, hY, rfl, hJ⟩ := hA
  have hM := Jk3_mid hJ
  have hbase : ∀ (t : ℕ) (A : TrioSeq), Aok A → Pk2 (s + t) A →
      A ++ shiftr01 t 0 ([((3 + s, 3, 0) : ℕ × ℕ × ℕ)] ++ J) ∈ W 0 := by
    intro t A _ hA
    rw [shiftr01_append0, shift_col]
    exact hJ.2.2 t A hA
  have hclose : ∀ (t : ℕ) (A' C' : TrioSeq), Aok A' → Pk2 (s + t) A' → Mono C' →
      (∀ (t' : ℕ) (A'' : TrioSeq), Aok A'' → Pk2 (s + t') A'' →
        A'' ++ BlkD (4 + s + t') (shiftr01 t' 0 ([((3 + s, 3, 0) : ℕ × ℕ × ℕ)] ++ J)) C'
          ∈ W 0) →
      Pk2 (s + t) (A' ++ BlkD (4 + s + t)
        (shiftr01 t 0 ([((3 + s, 3, 0) : ℕ × ℕ × ℕ)] ++ J)) C') := by
    intro t A' C' _ hA' hmoC' hIH
    exact Pk2_absorb hM hmoC' hIH t A' hA'
  have hkey := blkD_memS (d := 4 + s) (by omega) _ hM hbase hclose B hB.mem
    hB.zroot hB.mono hB.root 0 Y (Pk2_Aok hY) (by simpa using hY)
  simp only [shiftr01_zero, Nat.add_zero] at hkey
  rw [BlkD_app] at hkey
  rwa [show 3 + s + 1 = 4 + s from by omega]

theorem Pk23_close (h : ℕ) (A Blk : TrioSeq) (hA : Pk23 h A)
    (hcol : ∀ x ∈ Blk, h + 1 ≤ x.1) (hmo : Mono Blk)
    (hre : ∀ (t : ℕ) (A' : TrioSeq), Pk23 (h + t) A' → A' ++ shiftr01 t 0 Blk ∈ W 0) :
    Pk23 h (A ++ Blk) := by
  obtain ⟨s, Y, J, rfl, hY, rfl, hJ⟩ := hA
  refine ⟨s, Y, J ++ Blk, rfl, hY, by simp [List.append_assoc], ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hJ.1 x h
    · have := hcol x h; omega
  · intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hJ.2.1 c h
    · exact hmo c h
  · intro t Y' hY'
    rw [shiftr01_append0, ← List.append_assoc, ← List.append_assoc]
    have hA' : Pk23 (3 + s + t) (Y' ++ ([((3 + s + t, 3, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J)) :=
      ⟨s + t, Y', shiftr01 t 0 J, by omega, hY', by rw [show 3 + (s + t) = 3 + s + t from by omega],
        Jk3_shift hJ t⟩
    have h := hre t _ hA'
    simpa only [List.append_assoc] using h

theorem BaseOk_Pk23 : BaseOk Pk23 where
  aok := Pk23_aok
  ancd := Pk23_ancd
  hang := Pk23_hang
  close := Pk23_close

theorem Pk2_R292 : Pk2 0 R292 := by
  refine ⟨0, Q ++ [((1, 1, 0) : ℕ × ℕ × ℕ)], [], ?_, ?_, Jk2_nil 0⟩
  · have h := RunA_Uu 0
    simpa [Uu] using h
  · simp [R292, Q]

theorem Pk23_R294 : Pk23 3 R294 :=
  ⟨0, R292, [], rfl, Pk2_R292, by simp [R292, R294], Jk3_nil 0⟩

/-- ★★ 行294 の上（高さ 4）に `Bok` を吊るせる。 -/
theorem hang_R294 (B : TrioSeq) (hB : Bok B) : R294 ++ shiftr01 4 0 B ∈ W 0 :=
  Pk23_hang 3 R294 Pk23_R294 B hB

theorem Aok_R294 : Aok R294 := Pk23_aok 3 R294 Pk23_R294

/-- ★★★ `(0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,1,0) ∈ W 0`。 -/
theorem R294_41 : R294 ++ [((4, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hok := Aok_R294
  have hsh : Ancd 4 R294 := Pk23_ancd 3 R294 Pk23_R294
  have htw : ∀ n, TwD 4 R294 n ∈ W 0 := by
    intro n
    induction n with
    | zero => simpa [TwD] using W_nil 0
    | succ n ih =>
        rw [TwD_succ]
        exact hang_R294 (TwD 4 R294 n)
          ⟨ih, TwD_zroot (by omega) hok.zroot n, TwD_mono hok.mono n,
            TwD_root hok.ne hok.deep.1 n⟩
  exact snocd_mem (by omega) hok.ne hok.deep hok.zroot hsh htw

#print axioms R294_41

/-! ### `(4,2,0)`: 塔 `Q (1 2 3)^n`（歩幅 3）を `Pk23` で回す -/

/-- `(1,1,0)(2,2,0)(3,3,0)`。 -/
def M123 : TrioSeq := [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 0) : ℕ × ℕ × ℕ)]

theorem St3_Pk23 : ∀ n : ℕ, Pk23 (3 * n + 3) (Mtwd 3 Q M123 (n + 1))
  | 0 => by
      rw [Mtwd_one]
      have h := Pk23_R294
      simpa [R294, Q, M123] using h
  | (n + 1) => by
      rw [Mtwd_succ]
      have ih := St3_Pk23 n
      have hL : LwA (3 * n + 3) (Mtwd 3 Q M123 (n + 1)) := ⟨Pk23, BaseOk_Pk23, 0, ih⟩
      have hR0 : RunA 0 (3 * n + 3 + 1)
          (Mtwd 3 Q M123 (n + 1) ++ [((3 * n + 3 + 1, 1, 0) : ℕ × ℕ × ℕ)]) :=
        ⟨3 * n + 3, _, _, rfl, rfl, hL, SegA_one (3 * n + 3)⟩
      have hP2 : Pk2 (3 * n + 3)
          ((Mtwd 3 Q M123 (n + 1) ++ [((3 * n + 3 + 1, 1, 0) : ℕ × ℕ × ℕ)])
            ++ ([((2 + (3 * n + 3), 2, 0) : ℕ × ℕ × ℕ)] ++ [])) := by
        refine ⟨0, _, [], ?_, rfl, Jk2_nil _⟩
        rwa [show 1 + (3 * n + 3) = 3 * n + 3 + 1 from by omega]
      have hP23 : Pk23 (3 + (3 * n + 3)) (_ ++ ([((3 + (3 * n + 3), 3, 0) : ℕ × ℕ × ℕ)] ++ [])) :=
        ⟨3 * n + 3, _, [], rfl, hP2, rfl, Jk3_nil _⟩
      have heq : Mtwd 3 Q M123 (n + 1) ++ shiftr01 (3 * (n + 1)) 0 M123
          = ((Mtwd 3 Q M123 (n + 1) ++ [((3 * n + 3 + 1, 1, 0) : ℕ × ℕ × ℕ)])
            ++ ([((2 + (3 * n + 3), 2, 0) : ℕ × ℕ × ℕ)] ++ []))
            ++ ([((3 + (3 * n + 3), 3, 0) : ℕ × ℕ × ℕ)] ++ []) := by
        simp only [M123, shiftr01, List.map_cons, List.map_nil, List.append_assoc,
          List.append_nil, List.cons_append, List.nil_append]
        congr 1
        simp only [List.cons.injEq, Prod.mk.injEq, Nat.add_zero, and_true]
        omega
      rw [heq, show 3 * (n + 1) + 3 = 3 + (3 * n + 3) from by omega]
      exact hP23

theorem St3_mem : ∀ n : ℕ, Mtwd 3 Q M123 n ∈ W 0
  | 0 => by rw [Mtwd_zero]; exact Aok_Q.mem
  | (n + 1) => (Pk23_aok _ _ (St3_Pk23 n)).mem

/-- ★★★ `(0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,2,0) ∈ W 0`。 -/
theorem R294_42 : R294 ++ [((4, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hM : MidD (1 + 1) M123 := by
    have h := MidD_append (MidD_col 1 1 (by omega) (by omega))
      (N := [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 0) : ℕ × ℕ × ℕ)])
      (by intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl <;> simp)
      (by intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl <;> simp)
    simpa [M123] using h
  have h := snocYd_mem (Y0 := Q) (M := M123) (L := 1) (y := 2) (dl := 3) (by simp [Q]) hM
    (by simp [M123, entry]) ?_ (by omega) (by omega) St3_mem
  · have heq : (Q ++ M123) ++ [((1 + 3, 2, 0) : ℕ × ℕ × ℕ)] = R294 ++ [((4, 2, 0) : ℕ × ℕ × ℕ)] := by
      simp [Q, M123, R294]
    rwa [heq] at h
  · intro t ht1 htl _ _
    simp only [M123, List.length_cons, List.length_nil] at htl
    rcases t with _ | _ | _ | t
    · omega
    · simp [M123, entry]
    · simp [M123, entry]
    · omega

#print axioms R294_42

/-! ## ★★★ 語クラス `Pw`（行295 への道）

`Pk2 = Pw [2]`, `Pk23 = Pw [3,2]` の一般化。語 `r` は逆順（先頭が最新の列）。各列の行 1 は 2 以上、
各列の後ろに junk（次の列より高い、`Mono`、一段下のクラスの元の上で再継ぎ可）が挟まる。
`BaseOk` は語について構造的に出る（帰納法不要）。 -/

/-- 語 `r` の上のクラス。`Pw r s A`: 最後の列の高さは `1 + s + r.length`。 -/
def Pw : List ℕ → ℕ → TrioSeq → Prop
  | [], s, A => ∃ j, RunA j (1 + s) A
  | (v :: r), s, A => ∃ (Y J : TrioSeq), Pw r s Y ∧
      A = Y ++ ([((2 + s + r.length, v, 0) : ℕ × ℕ × ℕ)] ++ J) ∧ 2 ≤ v ∧
      (∀ x ∈ J, 3 + s + r.length ≤ x.1) ∧ Mono J ∧
      (∀ (t : ℕ) (Y' : TrioSeq), Pw r (s + t) Y' →
        Y' ++ ([((2 + s + r.length + t, v, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J) ∈ W 0)

/-- 語 `r` の上、列 `v` の後ろの junk。 -/
def Jw (r : List ℕ) (v s : ℕ) (J : TrioSeq) : Prop :=
  (∀ x ∈ J, 3 + s + r.length ≤ x.1) ∧ Mono J ∧
  ∀ (t : ℕ) (Y' : TrioSeq), Pw r (s + t) Y' →
    Y' ++ ([((2 + s + r.length + t, v, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J) ∈ W 0

theorem Pw_cons {v : ℕ} {r : List ℕ} {s : ℕ} {A : TrioSeq} :
    Pw (v :: r) s A ↔ ∃ (Y J : TrioSeq), Pw r s Y ∧
      A = Y ++ ([((2 + s + r.length, v, 0) : ℕ × ℕ × ℕ)] ++ J) ∧ 2 ≤ v ∧ Jw r v s J := by
  constructor
  · rintro ⟨Y, J, hY, rfl, hv, h1, h2, h3⟩
    exact ⟨Y, J, hY, rfl, hv, h1, h2, h3⟩
  · rintro ⟨Y, J, hY, rfl, hv, h1, h2, h3⟩
    exact ⟨Y, J, hY, rfl, hv, h1, h2, h3⟩

theorem Jw_shift {r : List ℕ} {v s : ℕ} {J : TrioSeq} (hJ : Jw r v s J) (u : ℕ) :
    Jw r v (s + u) (shiftr01 u 0 J) := by
  refine ⟨?_, shiftD_mono hJ.2.1, ?_⟩
  · intro x hx
    simp only [shiftr01, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have := hJ.1 p hp
    dsimp only
    omega
  · intro t Y' hY'
    rw [shiftr01_add0]
    have hY'' : Pw r (s + (u + t)) Y' := by
      rw [show s + (u + t) = s + u + t from by omega]; exact hY'
    have h := hJ.2.2 (u + t) Y' hY''
    rw [show 2 + (s + u) + r.length + t = 2 + s + r.length + (u + t) from by omega]
    exact h

theorem Jw_mid {r : List ℕ} {v s : ℕ} {J : TrioSeq} (hJ : Jw r v s J) (hv : 2 ≤ v) :
    MidD (3 + s + r.length) ([((2 + s + r.length, v, 0) : ℕ × ℕ × ℕ)] ++ J) := by
  have h := MidD_append (MidD_col (2 + s + r.length) v (by omega) (by omega))
    (by intro x hx; have := hJ.1 x hx; omega) hJ.2.1
  rwa [show 2 + s + r.length + 1 = 3 + s + r.length from by omega] at h

theorem Pw_Aok : ∀ (r : List ℕ) (s : ℕ) (A : TrioSeq), Pw r s A → Aok A
  | [], s, A, hA => by
      obtain ⟨j, hj⟩ := hA
      exact (BaseOk_RunA j).aok _ _ hj
  | (v :: r), s, A, hA => by
      obtain ⟨Y, J, hY, rfl, hv, hJ⟩ := Pw_cons.mp hA
      have hmem := hJ.2.2 0 Y (by simpa using hY)
      simp only [shiftr01_zero, Nat.add_zero] at hmem
      exact Aok_append_Mid (by omega) (Pw_Aok r s Y hY) (Jw_mid hJ hv) hmem

theorem Pw_mem {r : List ℕ} {s : ℕ} {A : TrioSeq} (hA : Pw r s A) : A ∈ W 0 :=
  (Pw_Aok r s A hA).mem

theorem Pw_Ancd : ∀ (r : List ℕ) (s : ℕ) (A : TrioSeq), Pw r s A → Ancd (2 + s + r.length) A
  | [], s, A, hA => by
      obtain ⟨j, hj⟩ := hA
      have h := (BaseOk_RunA j).ancd _ _ hj
      simpa [show 1 + s + 1 = 2 + s from by omega] using h
  | (v :: r), s, A, hA => by
      obtain ⟨Y, J, hY, rfl, hv, hJ⟩ := Pw_cons.mp hA
      have hM := Jw_mid hJ hv
      have h := Ancd_append_Mid (Pw_Aok r s Y hY).ne (Pw_Ancd r s Y hY)
        (by rwa [show 3 + s + r.length = 2 + s + r.length + 1 from by omega] at hM)
      simp only [List.length_cons]
      rwa [show 2 + s + (r.length + 1) = 2 + s + r.length + 1 from by omega]

/-- `blkD_memS` の `hclose`: 吊るした junk を語の最後の junk（語が空なら `RunA` の頭）に吸収する。 -/
theorem Pw_absorb : ∀ (r : List ℕ) (s : ℕ) (M : TrioSeq), MidD (3 + s + r.length) M →
    ∀ (C' : TrioSeq), Mono C' →
    (∀ (t : ℕ) (A'' : TrioSeq), Aok A'' → Pw r (s + t) A'' →
      A'' ++ BlkD (3 + s + r.length + t) (shiftr01 t 0 M) C' ∈ W 0) →
    ∀ (t : ℕ) (A' : TrioSeq), Pw r (s + t) A' →
      Pw r (s + t) (A' ++ BlkD (3 + s + r.length + t) (shiftr01 t 0 M) C')
  | [], s, M, hM, C', hmoC', hIH, t, A', hA' => by
      obtain ⟨j, hj⟩ := hA'
      refine ⟨j, (BaseOk_RunA j).close _ _ _ hj ?_ ?_ ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · have := MidD_col_ge (MidD_shift hM t) x h
          simp only [List.length_nil] at this
          omega
        · have := shiftD_col x h
          simp only [List.length_nil] at this
          omega
      · exact BlkD_mono (MidD_shift hM t).mono hmoC'
      · intro t2 A3 hA3
        have hA3' : RunA j (1 + (s + (t + t2))) A3 := by
          rw [show 1 + (s + (t + t2)) = 1 + (s + t) + t2 from by omega]; exact hA3
        have h := hIH (t + t2) A3 ((BaseOk_RunA j).aok _ _ hA3') ⟨j, hA3'⟩
        rw [BlkD_shift_eq] at h ⊢
        rw [shiftr01_append0, shiftr01_add0, shiftr01_add0]
        simp only [List.length_nil, List.append_assoc] at h ⊢
        rwa [show 3 + s + 0 + t + t2 = 3 + s + 0 + (t + t2) from by omega]
  | (v :: r), s, M, hM, C', hmoC', hIH, t, A', hA' => by
      obtain ⟨Y, J, hY, rfl, hv, hJ⟩ := Pw_cons.mp hA'
      simp only [List.length_cons] at hM hIH ⊢
      refine Pw_cons.mpr ⟨Y, J ++ BlkD (3 + s + (r.length + 1) + t) (shiftr01 t 0 M) C', hY,
        by simp [List.append_assoc], hv, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hJ.1 x h
        · rcases List.mem_append.mp h with h2 | h2
          · have := MidD_col_ge (MidD_shift hM t) x h2
            omega
          · have := shiftD_col x h2
            omega
      · have h1 : Mono (J ++ shiftr01 t 0 M) := by
          intro c hc
          rcases List.mem_append.mp hc with h | h
          · exact hJ.2.1 c h
          · exact shiftD_mono hM.mono c h
        have h2 := BlkD_mono (d := 3 + s + (r.length + 1) + t) h1 hmoC'
        simpa [BlkD, List.append_assoc] using h2
      · intro t2 Y2 hY2
        have hA2 : Pw (v :: r) (s + (t + t2))
            (Y2 ++ ([((2 + (s + t) + r.length + t2, v, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t2 0 J)) := by
          refine Pw_cons.mpr ⟨Y2, shiftr01 t2 0 J, ?_, ?_, hv, ?_⟩
          · rw [show s + (t + t2) = s + t + t2 from by omega]; exact hY2
          · rw [show 2 + (s + (t + t2)) + r.length = 2 + (s + t) + r.length + t2 from by omega]
          · have h := Jw_shift hJ t2
            rwa [show s + t + t2 = s + (t + t2) from by omega] at h
        have h := hIH (t + t2) _ (Pw_Aok _ _ _ hA2) hA2
        rw [BlkD_shift_eq] at h ⊢
        rw [shiftr01_append0, shiftr01_append0, shiftr01_add0, shiftr01_add0,
          show 3 + s + (r.length + 1) + t + t2 = 3 + s + (r.length + 1) + (t + t2) from by omega]
        simpa only [List.append_assoc] using h

/-- ★★ `Pw (v :: r)` の頭の上（レベル `+1`）に `Bok` を吊るせる。 -/
theorem Pw_hang {v : ℕ} {r : List ℕ} {s : ℕ} {A : TrioSeq} (hA : Pw (v :: r) s A)
    (B : TrioSeq) (hB : Bok B) : A ++ shiftr01 (3 + s + r.length) 0 B ∈ W 0 := by
  obtain ⟨Y, J, hY, rfl, hv, hJ⟩ := Pw_cons.mp hA
  have hM := Jw_mid hJ hv
  have hbase : ∀ (t : ℕ) (A : TrioSeq), Aok A → Pw r (s + t) A →
      A ++ shiftr01 t 0 ([((2 + s + r.length, v, 0) : ℕ × ℕ × ℕ)] ++ J) ∈ W 0 := by
    intro t A _ hA
    rw [shiftr01_append0, shift_col]
    exact hJ.2.2 t A hA
  have hkey := blkD_memS (d := 3 + s + r.length) (by omega) _ hM hbase
    (fun t A' C' _ hA' hmoC' hIH => Pw_absorb r s _ hM C' hmoC' hIH t A' hA') B hB.mem
    hB.zroot hB.mono hB.root 0 Y (Pw_Aok r s Y hY) (by simpa using hY)
  simp only [shiftr01_zero, Nat.add_zero] at hkey
  rw [BlkD_app] at hkey
  exact hkey

theorem Pw_close : ∀ (r : List ℕ) (s : ℕ) (A Blk : TrioSeq), Pw r s A →
    (∀ x ∈ Blk, 2 + s + r.length ≤ x.1) → Mono Blk →
    (∀ (t : ℕ) (A' : TrioSeq), Pw r (s + t) A' → A' ++ shiftr01 t 0 Blk ∈ W 0) →
    Pw r s (A ++ Blk)
  | [], s, A, Blk, hA, hcol, hmo, hre => by
      obtain ⟨j, hj⟩ := hA
      refine ⟨j, (BaseOk_RunA j).close _ _ _ hj ?_ hmo ?_⟩
      · intro x hx; have := hcol x hx; simp only [List.length_nil] at this; omega
      · intro t A' hA'
        exact hre t A' ⟨j, by rwa [show 1 + (s + t) = 1 + s + t from by omega]⟩
  | (v :: r), s, A, Blk, hA, hcol, hmo, hre => by
      obtain ⟨Y, J, hY, rfl, hv, hJ⟩ := Pw_cons.mp hA
      simp only [List.length_cons] at hcol hre
      refine Pw_cons.mpr ⟨Y, J ++ Blk, hY, by simp [List.append_assoc], hv, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hJ.1 x h
        · have := hcol x h; omega
      · intro c hc
        rcases List.mem_append.mp hc with h | h
        · exact hJ.2.1 c h
        · exact hmo c h
      · intro t Y' hY'
        rw [shiftr01_append0, ← List.append_assoc, ← List.append_assoc]
        have hA' : Pw (v :: r) (s + t)
            (Y' ++ ([((2 + s + r.length + t, v, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J)) := by
          refine Pw_cons.mpr ⟨Y', shiftr01 t 0 J, hY', ?_, hv, Jw_shift hJ t⟩
          rw [show 2 + (s + t) + r.length = 2 + s + r.length + t from by omega]
        have h := hre t _ hA'
        simpa only [List.append_assoc] using h

/-- レベルつきの語クラス（`LwA` の台座に使う）。 -/
def PwL (r : List ℕ) (h : ℕ) (A : TrioSeq) : Prop := ∃ s, h = 1 + s + r.length ∧ Pw r s A

theorem BaseOk_PwL (r : List ℕ) : BaseOk (PwL r) where
  aok := by
    rintro h A ⟨s, rfl, hA⟩
    exact Pw_Aok r s A hA
  ancd := by
    rintro h A ⟨s, rfl, hA⟩
    have h := Pw_Ancd r s A hA
    rwa [show 1 + s + r.length + 1 = 2 + s + r.length from by omega]
  hang := by
    rintro h A ⟨s, rfl, hA⟩ B hB
    cases r with
    | nil =>
        obtain ⟨j, hj⟩ := hA
        have h := (BaseOk_RunA j).hang _ _ hj B hB
        simpa using h
    | cons v r =>
        have h := Pw_hang hA B hB
        simp only [List.length_cons]
        rwa [show 1 + s + (r.length + 1) + 1 = 3 + s + r.length from by omega]
  close := by
    rintro h A Blk ⟨s, rfl, hA⟩ hcol hmo hre
    refine ⟨s, rfl, Pw_close r s A Blk hA ?_ hmo ?_⟩
    · intro x hx; have := hcol x hx; omega
    · intro t A' hA'
      exact hre t A' ⟨s + t, by omega, hA'⟩

theorem Pw_LwA {r : List ℕ} {s : ℕ} {A : TrioSeq} (hA : Pw r s A) :
    LwA (1 + s + r.length) A :=
  ⟨PwL r, BaseOk_PwL r, 0, ⟨s, rfl, hA⟩⟩

/-! ## ★★★ ゆっくり戦法 (2): `(4,2,0)` の上に継ぐ

`A := R294 ++ (4,2,0)`。鍵は「任意の `LwA` の頭に `(1,1,0)(2,2,0)(3,3,0)(4,2,0)` を継げる」
（`R294_42` の台座 `Q` を一般の `X` に）。これで `M1232 := (1,1,0)(2,2,0)(3,3,0)(4,2,0)` が `SegA`
になり、`A ∈ RunA 0 1`。 -/

/-- `Pk23` の 1 段: `LwA` の頭に `(h+1,1,0)(h+2,2,0)(h+3,3,0)` を継いだものは `Pk23 (h+3)`。 -/
theorem Pk23_step (h : ℕ) (Y : TrioSeq) (hY : LwA h Y) :
    Pk23 (h + 3) (Y ++ [((h + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 0) : ℕ × ℕ × ℕ),
      ((h + 3, 3, 0) : ℕ × ℕ × ℕ)]) := by
  have hR0 : RunA 0 (h + 1) (Y ++ [((h + 1, 1, 0) : ℕ × ℕ × ℕ)]) :=
    ⟨h, _, _, rfl, rfl, hY, SegA_one h⟩
  have hP2 : Pk2 h ((Y ++ [((h + 1, 1, 0) : ℕ × ℕ × ℕ)])
      ++ ([((2 + h, 2, 0) : ℕ × ℕ × ℕ)] ++ [])) := by
    refine ⟨0, _, [], ?_, rfl, Jk2_nil _⟩
    rwa [show 1 + h = h + 1 from by omega]
  have hP23 : Pk23 (3 + h) (_ ++ ([((3 + h, 3, 0) : ℕ × ℕ × ℕ)] ++ [])) :=
    ⟨h, _, [], rfl, hP2, rfl, Jk3_nil _⟩
  have heq : Y ++ [((h + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 0) : ℕ × ℕ × ℕ),
      ((h + 3, 3, 0) : ℕ × ℕ × ℕ)]
      = ((Y ++ [((h + 1, 1, 0) : ℕ × ℕ × ℕ)]) ++ ([((2 + h, 2, 0) : ℕ × ℕ × ℕ)] ++ []))
        ++ ([((3 + h, 3, 0) : ℕ × ℕ × ℕ)] ++ []) := by
    rw [show 2 + h = h + 2 from by omega, show 3 + h = h + 3 from by omega]
    simp
  rw [heq, show h + 3 = 3 + h from by omega]
  exact hP23

theorem StG_Pk23 {c : ℕ} {X : TrioSeq} (hX : LwA c X) :
    ∀ n : ℕ, Pk23 (c + 3 * n + 3) (Mtwd 3 X (shiftr01 c 0 M123) (n + 1))
  | 0 => by
      rw [Mtwd_one]
      have h := Pk23_step c X hX
      rw [show c + 3 * 0 + 3 = c + 3 from by omega]
      convert h using 2
      simp only [M123, shiftr01, List.map_cons, List.map_nil, List.cons.injEq,
        Prod.mk.injEq, Nat.add_zero, and_true, true_and]
      omega
  | (n + 1) => by
      rw [Mtwd_succ, shiftr01_add0]
      have ih := StG_Pk23 hX n
      have hL : LwA (c + 3 * n + 3) (Mtwd 3 X (shiftr01 c 0 M123) (n + 1)) :=
        ⟨Pk23, BaseOk_Pk23, 0, ih⟩
      have h := Pk23_step _ _ hL
      rw [show c + 3 * (n + 1) + 3 = c + 3 * n + 3 + 3 from by omega]
      convert h using 2
      simp only [M123, shiftr01, List.map_cons, List.map_nil, List.cons.injEq,
        Prod.mk.injEq, Nat.add_zero, and_true, true_and]
      omega

theorem StG_mem {c : ℕ} {X : TrioSeq} (hX : LwA c X) :
    ∀ n : ℕ, Mtwd 3 X (shiftr01 c 0 M123) n ∈ W 0
  | 0 => by rw [Mtwd_zero]; exact (LwA_Aok hX).mem
  | (n + 1) => (Pk23_aok _ _ (StG_Pk23 hX n)).mem

/-- `(1,1,0)(2,2,0)(3,3,0)(4,2,0)`。 -/
def M1232 : TrioSeq :=
  [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 0) : ℕ × ℕ × ℕ),
    ((4, 2, 0) : ℕ × ℕ × ℕ)]

theorem MidD_M123 (c : ℕ) : MidD (c + 1 + 1) (shiftr01 c 0 M123) := by
  have h := MidD_append (MidD_col 1 1 (by omega) (by omega))
    (N := [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 0) : ℕ × ℕ × ℕ)])
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> simp)
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> simp)
  have h2 := MidD_shift h c
  rw [show 1 + 1 + c = c + 1 + 1 from by omega] at h2
  simpa [M123] using h2

/-- ★★ 任意の `LwA` の頭に `(1,1,0)(2,2,0)(3,3,0)(4,2,0)` を継げる。 -/
theorem LwA_snoc1232 {c : ℕ} {X : TrioSeq} (hX : LwA c X) :
    X ++ shiftr01 c 0 M1232 ∈ W 0 := by
  have h := snocYd_mem (Y0 := X) (M := shiftr01 c 0 M123) (L := c + 1) (y := 2) (dl := 3)
    (LwA_Aok hX).ne (MidD_M123 c) ?_ ?_ (by omega) (by omega) (StG_mem hX)
  · have heq : (X ++ shiftr01 c 0 M123) ++ [((c + 1 + 3, 2, 0) : ℕ × ℕ × ℕ)]
        = X ++ shiftr01 c 0 M1232 := by
      simp only [M123, M1232, shiftr01, List.map_cons, List.map_nil, List.append_assoc,
        List.cons_append, List.nil_append, List.singleton_append]
      congr 1
      simp only [List.cons.injEq, Prod.mk.injEq, Nat.add_zero, and_true, true_and]
      omega
    rwa [heq] at h
  · simp [M123, shiftr01, entry]
  · intro t ht1 htl _ _
    simp only [M123, shiftr01, List.length_map, List.length_cons, List.length_nil] at htl
    rcases t with _ | _ | _ | t
    · omega
    · simp [M123, shiftr01, entry]
    · simp [M123, shiftr01, entry]
    · omega

theorem MidD_M1232 : MidD 2 M1232 := by
  have h := MidD_append (MidD_col 1 1 (by omega) (by omega))
    (N := [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 0) : ℕ × ℕ × ℕ), ((4, 2, 0) : ℕ × ℕ × ℕ)])
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> simp)
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> simp)
  simpa [M1232] using h

/-- `M1232` は絶対セグメント。 -/
theorem SegA_M1232 : SegA 0 M1232 where
  mid := MidD_M1232
  head1 := by simp [M1232, entry]
  reapp := by
    intro P hP s A' hA'
    exact LwA_snoc1232 ⟨P, hP, by simpa using hA'⟩

/-- `A42 := (0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,2,0)`。 -/
def A42 : TrioSeq := R294 ++ [((4, 2, 0) : ℕ × ℕ × ℕ)]

theorem A42_eq : A42 = Q ++ M1232 := by simp [A42, R294, Q, M1232]

theorem RunA0_A42 : RunA 0 1 A42 := by
  rw [A42_eq]
  exact ⟨0, Q, M1232, rfl, rfl, LwA_Q, SegA_M1232⟩

theorem Aok_A42 : Aok A42 := (BaseOk_RunA 0).aok _ _ RunA0_A42

/-- ★★★ `A42 ++ (1,1,0) ∈ W 0`（根に吊るす、`bump`）。 -/
theorem A42_110 : A42 ++ [((1, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hok := Aok_A42
  have hsh : Ancd 1 A42 := by
    intro j hj0 hjl hlt _
    have := hok.deep.2 j hj0 hjl
    omega
  have htw : ∀ n, TwD 1 A42 n ∈ W 0 := by
    intro n
    induction n with
    | zero => simpa [TwD] using W_nil 0
    | succ n ih =>
        rw [TwD_succ]
        exact bump_zm ih (TwD_zroot (by omega) hok.zroot n) (TwD_mono hok.mono n)
          (TwD_root hok.ne hok.deep.1 n) hok.mem hok.ne hok.deep
  exact snocd_mem (by omega) hok.ne hok.deep hok.zroot hsh htw

/-- ★★★ `A42 ++ (2,1,0) ∈ W 0`（根に吊るす、歩幅 2）。 -/
theorem A42_210 : A42 ++ [((2, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hok := Aok_A42
  have hsh : Ancd 2 A42 := (BaseOk_RunA 0).ancd _ _ RunA0_A42
  have htw : ∀ n, TwD 2 A42 n ∈ W 0 := by
    intro n
    induction n with
    | zero => simpa [TwD] using W_nil 0
    | succ n ih =>
        rw [TwD_succ]
        exact (BaseOk_RunA 0).hang _ _ RunA0_A42 (TwD 2 A42 n)
          ⟨ih, TwD_zroot (by omega) hok.zroot n, TwD_mono hok.mono n,
            TwD_root hok.ne hok.deep.1 n⟩
  exact snocd_mem (by omega) hok.ne hok.deep hok.zroot hsh htw

/-- ★★★ `A42 ++ (2,2,0) ∈ W 0`（`(1,1,0)` が bad root、歩幅 1）。 -/
theorem A42_220 : A42 ++ [((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  rw [A42_eq]
  have h := snocY_mem (Y0 := Q) (M := M1232) (L := 1) (y := 2) (by simp [Q]) MidD_M1232
    (by simp [M1232, entry]) (by omega)
    (LwB_tower_mem BaseOk_zero (SegA_toSegB SegA_M1232 BaseOk_zero)
      (LwB_of_base ⟨(Aok_Q : Aok Q), rfl⟩))
  simpa using h

#print axioms A42_220

/-! ### `A42 ++ (2,0,0)`: srow 0、親は `(1,1,0)`（index 2）、平坦な複製 `Q (1 2 3 2)^n` -/

/-- `Q ++ M1232^n` は `Aok`。 -/
theorem Q_M1232_pow : ∀ n : ℕ, Aok (Q ++ (List.range n).flatMap (fun _ => M1232))
  | 0 => by simpa using Aok_Q
  | (n + 1) => by
      rw [List.range_succ, List.flatMap_append, ← List.append_assoc]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hok := Q_M1232_pow n
      have h := SegA_M1232.reapp _ BaseOk_zero 0 _ (LwB_of_base ⟨hok, rfl⟩)
      simp only [shiftr01_zero, Nat.add_zero] at h
      exact Aok_append_Mid (by omega) hok MidD_M1232 h

def A42_200 : TrioSeq := A42 ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]

theorem A42_200_len : A42_200.length = 7 := by simp [A42_200, A42, R294]

theorem nextrel0_A42_200 : nextrel0 A42_200 2 6 := by
  refine ⟨by simp [A42_200, A42, R294], by simp [A42_200, A42, R294], by omega,
    by simp [A42_200, A42, R294, entry], ?_⟩
  intro j hj
  obtain ⟨h1, h2⟩ := hj
  rcases j with _ | _ | _ | _ | _ | _ | j
  · omega
  · omega
  · omega
  · simp [A42_200, A42, R294, entry]
  · simp [A42_200, A42, R294, entry]
  · simp [A42_200, A42, R294, entry]
  · omega

theorem hasParent0_A42_200 : hasParent A42_200 0 6 := by
  refine ⟨2, ?_, ?_⟩
  · show nextR A42_200 0 2 6
    simp only [nextR, if_true]
    exact nextrel0_A42_200
  · intro j0 hj0
    change nextR A42_200 0 j0 6 at hj0
    simp only [nextR, if_true] at hj0
    obtain ⟨hj0l, -, hlt, hlt2, hall⟩ := hj0
    rcases j0 with _ | _ | _ | j0
    · exfalso
      have := hall 2 ⟨by omega, by omega⟩
      simp [A42_200, A42, R294, entry] at this
    · exfalso
      have := hall 2 ⟨by omega, by omega⟩
      simp [A42_200, A42, R294, entry] at this
    · rfl
    · exfalso
      rw [A42_200_len] at hj0l
      rcases j0 with _ | _ | _ | j0
      · simp [A42_200, A42, R294, entry] at hlt2
      · simp [A42_200, A42, R294, entry] at hlt2
      · simp [A42_200, A42, R294, entry] at hlt2
      · omega

theorem parent0_A42_200 : parent A42_200 0 6 = 2 :=
  hasParent0_A42_200.unique (parent_nextR hasParent0_A42_200)
    (by show nextR A42_200 0 2 6; simp only [nextR, if_true]; exact nextrel0_A42_200)

open Classical in
theorem oper_A42_200 (n : ℕ) :
    A42_200⟦n⟧ = Q ++ (List.range n).flatMap (fun _ => M1232) := by
  rw [L53.oper_flat (j1 := 6) (j0 := 2) (by rw [A42_200_len]) (by omega)
    (by simp [A42_200, A42, R294, entry]) (by simp [srow, A42_200, A42, R294, entry])
    hasParent0_A42_200 parent0_A42_200.symm n]
  simp [A42_200, A42, R294, Q, M1232, entry, List.range']

/-- ★★★ `A42 ++ (2,0,0) ∈ W 0`。 -/
theorem A42_200_mem : A42_200 ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_A42_200]
  exact (Q_M1232_pow n).mem

#print axioms A42_200_mem

/-! ### 語の部分 `Wp`（台座抜き）と、語の上への `(·,2,0)` の継ぎ足し `Pw_snoc2` -/

/-- 語 `r` の列たち（台座抜き）。 -/
def Wp : List ℕ → ℕ → TrioSeq → Prop
  | [], _, R => R = []
  | (v :: r), s, R => ∃ (R0 J : TrioSeq), Wp r s R0 ∧
      R = R0 ++ ([((2 + s + r.length, v, 0) : ℕ × ℕ × ℕ)] ++ J) ∧ 2 ≤ v ∧ Jw r v s J

theorem Pw_split : ∀ (r : List ℕ) (s : ℕ) (Y : TrioSeq), Pw r s Y →
    ∃ (j : ℕ) (X R : TrioSeq), RunA j (1 + s) X ∧ Y = X ++ R ∧ Wp r s R
  | [], s, Y, hY => by
      obtain ⟨j, hj⟩ := hY
      exact ⟨j, Y, [], hj, by simp, rfl⟩
  | (v :: r), s, Y, hY => by
      obtain ⟨Y0, J, hY0, rfl, hv, hJ⟩ := Pw_cons.mp hY
      obtain ⟨j, X, R0, hX, rfl, hR0⟩ := Pw_split r s Y0 hY0
      exact ⟨j, X, R0 ++ ([((2 + s + r.length, v, 0) : ℕ × ℕ × ℕ)] ++ J), hX,
        by simp [List.append_assoc], R0, J, hR0, rfl, hv, hJ⟩

theorem Pw_of_split : ∀ (r : List ℕ) (s j : ℕ) (X R : TrioSeq), RunA j (1 + s) X →
    Wp r s R → Pw r s (X ++ R)
  | [], s, j, X, R, hX, hR => by
      subst hR
      exact ⟨j, by simpa using hX⟩
  | (v :: r), s, j, X, R, hX, hR => by
      obtain ⟨R0, J, hR0, rfl, hv, hJ⟩ := hR
      exact Pw_cons.mpr ⟨X ++ R0, J, Pw_of_split r s j X R0 hX hR0,
        by simp [List.append_assoc], hv, hJ⟩

theorem Wp_shift : ∀ (r : List ℕ) (s : ℕ) (R : TrioSeq), Wp r s R → ∀ u : ℕ,
    Wp r (s + u) (shiftr01 u 0 R)
  | [], s, R, hR, u => by
      subst hR
      simp [Wp, shiftr01]
  | (v :: r), s, R, hR, u => by
      obtain ⟨R0, J, hR0, rfl, hv, hJ⟩ := hR
      refine ⟨shiftr01 u 0 R0, shiftr01 u 0 J, Wp_shift r s R0 hR0 u, ?_, hv, Jw_shift hJ u⟩
      rw [shiftr01_append0, shiftr01_append0, shift_col,
        show 2 + s + r.length + u = 2 + (s + u) + r.length from by omega]

theorem Wp_cols : ∀ (r : List ℕ) (s : ℕ) (R : TrioSeq), Wp r s R → ∀ x ∈ R, 2 + s ≤ x.1
  | [], s, R, hR, x, hx => by subst hR; simp at hx
  | (v :: r), s, R, hR, x, hx => by
      obtain ⟨R0, J, hR0, rfl, hv, hJ⟩ := hR
      rcases List.mem_append.mp hx with h | h
      · exact Wp_cols r s R0 hR0 x h
      · rcases List.mem_append.mp h with h' | h'
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
          subst h'
          show 2 + s ≤ 2 + s + r.length
          omega
        · have := hJ.1 x h'
          omega

theorem Wp_mono : ∀ (r : List ℕ) (s : ℕ) (R : TrioSeq), Wp r s R → Mono R
  | [], s, R, hR => by subst hR; intro c hc; simp at hc
  | (v :: r), s, R, hR => by
      obtain ⟨R0, J, hR0, rfl, hv, hJ⟩ := hR
      intro c hc
      rcases List.mem_append.mp hc with h | h
      · exact Wp_mono r s R0 hR0 c h
      · rcases List.mem_append.mp h with h' | h'
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
          subst h'
          show (0 : ℕ) ≤ v
          omega
        · exact hJ.2.1 c h'

/-- 語が空でなければ先頭の列の高さは `2 + s`。 -/
theorem Wp_head : ∀ (r : List ℕ) (s : ℕ) (R : TrioSeq), Wp r s R → r ≠ [] →
    0 < R.length ∧ entry R 0 0 = 2 + s
  | [], _, _, _, hne => absurd rfl hne
  | (v :: r), s, R, hR, _ => by
      obtain ⟨R0, J, hR0, rfl, hv, hJ⟩ := hR
      rcases r with _ | ⟨v', r'⟩
      · simp only [Wp] at hR0
        subst hR0
        refine ⟨by simp, ?_⟩
        simp [entry]
      · obtain ⟨hlen, hh⟩ := Wp_head (v' :: r') s R0 hR0 (by simp)
        refine ⟨by simp; omega, ?_⟩
        rw [entry_append_left hlen]
        exact hh

/-- 語の記録: 頂上より低い記録の行 1 は 2 以上。 -/
theorem Wp_rec : ∀ (r : List ℕ) (s : ℕ) (R : TrioSeq), Wp r s R →
    ∀ t, t < R.length → entry R 0 t < 2 + s + r.length →
      (∀ i, t < i → i < R.length → entry R 0 t < entry R 0 i) → 2 ≤ entry R 1 t
  | [], s, R, hR, t, htl, _, _ => by subst hR; simp at htl
  | (v :: r), s, R, hR, t, htl, hlt, hrec => by
      obtain ⟨R0, J, hR0, rfl, hv, hJ⟩ := hR
      have hlen : (R0 ++ ([((2 + s + r.length, v, 0) : ℕ × ℕ × ℕ)] ++ J)).length
          = R0.length + (1 + J.length) := by simp; omega
      have hch : entry (R0 ++ ([((2 + s + r.length, v, 0) : ℕ × ℕ × ℕ)] ++ J)) 0 R0.length
          = 2 + s + r.length := by
        rw [show R0.length = R0.length + 0 from rfl, entry_append_right]
        simp [entry]
      rcases Nat.lt_trichotomy t R0.length with h | h | h
      · rw [entry_append_left h] at hlt ⊢
        have hlt' : entry R0 0 t < 2 + s + r.length := by
          have := hrec R0.length h (by omega)
          rw [entry_append_left h, hch] at this
          exact this
        refine Wp_rec r s R0 hR0 t h hlt' ?_
        intro i hti hiR
        have := hrec i hti (by omega)
        rw [entry_append_left h, entry_append_left hiR] at this
        exact this
      · subst h
        rw [show R0.length = R0.length + 0 from rfl, entry_append_right]
        simpa [entry] using hv
      · exfalso
        obtain ⟨q, rfl⟩ : ∃ q, t = R0.length + q := ⟨t - R0.length, by omega⟩
        rw [entry_append_right] at hlt
        simp only [List.length_cons] at hlt
        rcases q with _ | q
        · omega
        · have hq : q < J.length := by simp at htl; omega
          have hmem : J.getD q ((0, 0, 0) : ℕ × ℕ × ℕ) ∈ J := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
            exact List.getElem_mem hq
          have := hJ.1 _ hmem
          have hq' : entry ([((2 + s + r.length, v, 0) : ℕ × ℕ × ℕ)] ++ J) 0 (q + 1)
              = (J.getD q ((0, 0, 0) : ℕ × ℕ × ℕ)).1 := by
            simp [entry]
          rw [hq'] at hlt
          omega

/-- ★★ 語の上（頂上の 1 つ上）に `(·,2,0)` を継げる。bad root は `RunA` の頭の頭。 -/
theorem Pw_snoc2 {r : List ℕ} {s : ℕ} {Y : TrioSeq} (hY : Pw r s Y) :
    Y ++ [((2 + s + r.length, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  obtain ⟨j, X, R, hX, rfl, hR⟩ := Pw_split r s Y hY
  obtain ⟨c, Y0, U, hc, rfl, hY0, hU⟩ := RunA_to j (1 + s) X hX
  have hs : s = c + j := by omega
  subst hs
  set d := 1 + j + r.length with hd
  have hUmid := RunU_mid j c U hU
  have hUlen : 0 < U.length := List.length_pos_iff.mpr hUmid.ne
  have hM : MidD (c + 1 + 1) (U ++ R) := by
    refine MidD_append (by rwa [show c + 1 + 1 = c + 2 from by omega]) ?_ (Wp_mono r _ R hR)
    intro x hx
    have := Wp_cols r _ R hR x hx
    omega
  have htw : ∀ n, Pw r (c + j + d * n) (Mtwd d Y0 (U ++ R) (n + 1)) := by
    intro n
    induction n with
    | zero =>
        rw [Mtwd_one, ← List.append_assoc]
        simpa using Pw_of_split r (c + j) j (Y0 ++ U) R hX hR
    | succ n ih =>
        rw [Mtwd_succ]
        have hL : LwA (1 + (c + j + d * n) + r.length) (Mtwd d Y0 (U ++ R) (n + 1)) := Pw_LwA ih
        have hdn : d * (n + 1) = d * n + d := Nat.mul_succ d n
        have hL' : LwA (c + d * (n + 1)) (Mtwd d Y0 (U ++ R) (n + 1)) := by
          have heq : c + d * (n + 1) = 1 + (c + j + d * n) + r.length := by
            rw [hdn, hd]; omega
          rw [heq]; exact hL
        have hUs := RunU_shift j c U hU (d * (n + 1))
        have hRA := RunA_of j _ _ _ hL' hUs
        rw [shiftr01_append0, ← List.append_assoc]
        have hRs := Wp_shift r (c + j) R hR (d * (n + 1))
        have hRA' : RunA j (1 + (c + j + d * (n + 1)))
            (Mtwd d Y0 (U ++ R) (n + 1) ++ shiftr01 (d * (n + 1)) 0 U) := by
          rwa [show c + d * (n + 1) + 1 + j = 1 + (c + j + d * (n + 1)) from by omega] at hRA
        exact Pw_of_split r _ j _ _ hRA' hRs
  have hmem : ∀ n, Mtwd d Y0 (U ++ R) n ∈ W 0 := by
    intro n
    cases n with
    | zero => rw [Mtwd_zero]; exact (LwA_Aok hY0).mem
    | succ n => exact Pw_mem (htw n)
  have hMy : ∀ t, 1 ≤ t → t < (U ++ R).length → entry (U ++ R) 0 t < c + 1 + d →
      (∀ i, t < i → i < (U ++ R).length → entry (U ++ R) 0 t < entry (U ++ R) 0 i) →
      2 ≤ entry (U ++ R) 1 t := by
    intro t ht1 htl hlt hrec
    have hlen : (U ++ R).length = U.length + R.length := by simp
    rcases Nat.lt_or_ge t U.length with h | h
    · rw [entry_append_left h] at hlt ⊢
      have hlt' : entry U 0 t < c + j + 2 := by
        rcases r with _ | ⟨v, r'⟩
        · simp only [Wp] at hR
          subst hR
          simp only [List.length_nil] at hd
          omega
        · obtain ⟨hRlen, hRh⟩ := Wp_head (v :: r') (c + j) R hR (by simp)
          have := hrec U.length h (by omega)
          rw [entry_append_left h, show U.length = U.length + 0 from rfl, entry_append_right,
            hRh] at this
          omega
      refine RunU_rec j c U hU t ht1 h hlt' ?_
      intro i hti hiU
      have := hrec i hti (by omega)
      rw [entry_append_left h, entry_append_left hiU] at this
      exact this
    · obtain ⟨q, rfl⟩ : ∃ q, t = U.length + q := ⟨t - U.length, by omega⟩
      rw [entry_append_right] at hlt ⊢
      refine Wp_rec r (c + j) R hR q (by omega) (by omega) ?_
      intro i hqi hiR
      have := hrec (U.length + i) (by omega) (by omega)
      rw [entry_append_right, entry_append_right] at this
      exact this
  have h := snocYd_mem (Y0 := Y0) (M := U ++ R) (L := c + 1) (y := 2) (dl := d)
    (LwA_Aok hY0).ne hM (by rw [entry_append_left hUlen]; exact RunU_head1 j c U hU) hMy
    (by omega) (by omega) hmem
  rw [← List.append_assoc] at h
  rwa [show c + 1 + d = 2 + (c + j) + r.length from by omega] at h

/-- 語の上に `(·,2,0)` を（junk なしで）足せる。 -/
theorem Pw_cons2 {r : List ℕ} {s : ℕ} {Y : TrioSeq} (hY : Pw r s Y) :
    Pw (2 :: r) s (Y ++ [((2 + s + r.length, 2, 0) : ℕ × ℕ × ℕ)]) := by
  refine Pw_cons.mpr ⟨Y, [], hY, by simp, le_refl 2, by simp, by intro c hc; simp at hc, ?_⟩
  intro t Y' hY'
  have h := Pw_snoc2 hY'
  simpa [show 2 + (s + t) + r.length = 2 + s + r.length + t from by omega] using h

theorem Jw_nil2_to_Jk2 {s : ℕ} {J : TrioSeq} (hJ : Jw [] 2 s J) : Jk2 s J := by
  refine ⟨by simpa using hJ.1, hJ.2.1, ?_⟩
  intro j t X hX
  have h := hJ.2.2 t X ⟨j, by rwa [show 1 + (s + t) = 1 + s + t from by omega]⟩
  simpa using h

/-- 最初の `2` の真横に `(·,3,0)` を足せる。 -/
theorem Jw_3first (s : ℕ) : Jw [2] 3 s [] := by
  refine ⟨by simp, by intro c hc; simp at hc, ?_⟩
  intro t Y' hY'
  obtain ⟨Y0, J, hY0, rfl, -, hJ⟩ := Pw_cons.mp hY'
  obtain ⟨j, hj⟩ := hY0
  have hJ' := Jw_nil2_to_Jk2 hJ
  simp only [List.length_nil, Nat.add_zero] at hJ' hj ⊢
  have h := Jk2_snoc3 hJ' hj
  have heq : 2 + s + [2].length + t = 3 + (s + t) := by
    simp only [List.length_cons, List.length_nil]; omega
  rw [heq]
  simpa using h

theorem Pw_nil_of_RunA {j h : ℕ} {Y : TrioSeq} (hY : RunA j (1 + h) Y) : Pw [] h Y := ⟨j, hY⟩

theorem Pw2_R292 : Pw [2] 0 R292 := by
  have h := Pw_cons2 (Pw_nil_of_RunA (h := 0) (by simpa [Uu] using RunA_Uu 0))
  simpa [R292, Q] using h

theorem Pw32_R294 : Pw [3, 2] 0 R294 := by
  refine Pw_cons.mpr ⟨R292, [], Pw2_R292, by simp [R292, R294], by omega, Jw_3first 0⟩

theorem Pw232_A42 : Pw [2, 3, 2] 0 A42 := by
  have h := Pw_cons2 Pw32_R294
  simpa [A42] using h

/-- `A42` を `Pw [3,2]`（`(4,2,0)` を `(3,3,0)` の junk に）として見る。 -/
theorem Pw32j_A42 : Pw [3, 2] 0 A42 := by
  refine Pw_cons.mpr ⟨R292, [((4, 2, 0) : ℕ × ℕ × ℕ)], Pw2_R292, by simp [R292, A42, R294],
    by omega, ?_⟩
  refine ⟨by simp, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp
  intro t Y' hY'
  have h1 : Pw [3, 2] t (Y' ++ [((2 + t + 1, 3, 0) : ℕ × ℕ × ℕ)]) :=
    Pw_cons.mpr ⟨Y', [], by simpa using hY', by simp, by omega, by simpa using Jw_3first t⟩
  have h2 := Pw_snoc2 h1
  simpa [shiftr01, List.append_assoc, show 2 + t + 2 = 4 + t from by omega,
    show 2 + t + 1 = 3 + t from by omega] using h2

/-- `A42` を `Pw [2]`（`(3,3,0)(4,2,0)` を `(2,2,0)` の junk に）として見る。 -/
theorem Pw2j_A42 : Pw [2] 0 A42 := by
  refine Pw_cons.mpr ⟨Q ++ [((1, 1, 0) : ℕ × ℕ × ℕ)],
    [((3, 3, 0) : ℕ × ℕ × ℕ), ((4, 2, 0) : ℕ × ℕ × ℕ)],
    Pw_nil_of_RunA (h := 0) (by simpa [Uu] using RunA_Uu 0), by simp [Q, A42, R294],
    by omega, ?_⟩
  refine ⟨by simp, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp
  intro t Y' hY'
  have h1 : Pw [2] t (Y' ++ [((2 + t + 0, 2, 0) : ℕ × ℕ × ℕ)]) := Pw_cons2 (by simpa using hY')
  have h2 : Pw [3, 2] t ((Y' ++ [((2 + t + 0, 2, 0) : ℕ × ℕ × ℕ)])
      ++ [((2 + t + 1, 3, 0) : ℕ × ℕ × ℕ)]) :=
    Pw_cons.mpr ⟨_, [], h1, by simp, by omega, by simpa using Jw_3first t⟩
  have h3 := Pw_snoc2 h2
  simpa [shiftr01, List.append_assoc, show 2 + t + 2 = 4 + t from by omega,
    show 2 + t + 1 = 3 + t from by omega] using h3

/-! ### `A42` の上の列たち（高さ 3, 4, 5） -/

theorem A42_snoc1 (r : List ℕ) (hA : Pw r 0 A42) :
    A42 ++ [((2 + r.length, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hok := Aok_A42
  have hsh : Ancd (2 + r.length) A42 := by simpa using Pw_Ancd r 0 A42 hA
  have hL : PwL r (1 + 0 + r.length) A42 := ⟨0, rfl, hA⟩
  have htw : ∀ n, TwD (2 + r.length) A42 n ∈ W 0 := by
    intro n
    induction n with
    | zero => simpa [TwD] using W_nil 0
    | succ n ih =>
        rw [TwD_succ]
        have h := (BaseOk_PwL r).hang _ _ hL (TwD (2 + r.length) A42 n)
          ⟨ih, TwD_zroot (by omega) hok.zroot n, TwD_mono hok.mono n,
            TwD_root hok.ne hok.deep.1 n⟩
        rwa [show 1 + 0 + r.length + 1 = 2 + r.length from by omega] at h
  exact snocd_mem (by omega) hok.ne hok.deep hok.zroot hsh htw

/-- ★★★ `A42(3,1,0)`。 -/
theorem A42_310 : A42 ++ [((3, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa using A42_snoc1 [2] Pw2j_A42

/-- ★★★ `A42(3,2,0)`。 -/
theorem A42_320 : A42 ++ [((3, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa using Pw_snoc2 Pw2j_A42

/-- ★★★ `A42(3,3,0)`（`(2,2,0)` の真横）。 -/
theorem A42_330 : A42 ++ [((3, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  obtain ⟨Y0, J, hY0, hA, -, hJ⟩ := Pw_cons.mp Pw2j_A42
  obtain ⟨j, hj⟩ := hY0
  have hJ' := Jw_nil2_to_Jk2 hJ
  simp only [List.length_nil, Nat.add_zero] at hJ' hj hA
  have h := Jk2_snoc3 hJ' hj
  rw [← hA] at h
  simpa using h

/-- ★★★ `A42(4,1,0)`。 -/
theorem A42_410 : A42 ++ [((4, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa using A42_snoc1 [3, 2] Pw32j_A42

/-- ★★★ `A42(4,2,0)`。 -/
theorem A42_420 : A42 ++ [((4, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa using Pw_snoc2 Pw32j_A42

/-- ★★★ `A42(5,1,0)`。 -/
theorem A42_510 : A42 ++ [((5, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa using A42_snoc1 [2, 3, 2] Pw232_A42

/-- ★★★ `A42(5,2,0)`。 -/
theorem A42_520 : A42 ++ [((5, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa using Pw_snoc2 Pw232_A42

/-- `R294 ++ (4,2,0)(5,2,0)...(n+3,2,0)` は語 `2^n 3 2`。 -/
theorem Pw_R294_tw2 : ∀ n : ℕ,
    Pw (List.replicate n 2 ++ [3, 2]) 0 (Mtw R294 [((4, 2, 0) : ℕ × ℕ × ℕ)] n)
  | 0 => by rw [Mtw_zero]; exact Pw32_R294
  | (n + 1) => by
      rw [Mtw_succ, shift_col]
      have h := Pw_cons2 (Pw_R294_tw2 n)
      rw [List.replicate_succ, List.cons_append]
      simp only [List.length_append, List.length_replicate, List.length_cons,
        List.length_nil, Nat.add_zero] at h ⊢
      rwa [show 2 + 0 + (n + (0 + 1 + 1)) = 4 + n from by omega] at h

/-- ★★★ `A42(5,3,0)`（`(4,2,0)` の真横。複製は `(4,2,0)` の 1 本ずつ）。 -/
theorem A42_530 : A42 ++ [((5, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := snocY_mem (Y0 := R294) (M := [((4, 2, 0) : ℕ × ℕ × ℕ)]) (L := 4) (y := 3)
    (by simp [R294]) (MidD_col 4 2 (by omega) (by omega)) (by simp [entry]) (by omega)
    (fun n => Pw_mem (Pw_R294_tw2 n))
  simpa [A42] using h

#print axioms A42_530

/-! ### `A42` の上の `(k,0,0)`（平坦な複製） -/

/-- `(2,2,0)(3,3,0)(4,2,0)`。 -/
def M232 : TrioSeq :=
  [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 0) : ℕ × ℕ × ℕ), ((4, 2, 0) : ℕ × ℕ × ℕ)]

/-- `(1,1,0) ++ M232^k`。 -/
def Sg (k : ℕ) : TrioSeq := [((1, 1, 0) : ℕ × ℕ × ℕ)] ++ (List.range k).flatMap (fun _ => M232)

theorem Sg_succ (k : ℕ) : Sg (k + 1) = Sg k ++ M232 := by
  simp [Sg, List.range_succ, List.flatMap_append, List.append_assoc]

theorem M232_cols : ∀ x ∈ M232, 2 ≤ x.1 := by
  intro x hx
  simp only [M232, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> simp

theorem M232_mono : Mono M232 := by
  intro x hx
  simp only [M232, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> simp

theorem MidD_Sg : ∀ k, MidD 2 (Sg k)
  | 0 => by
      have h := MidD_col 1 1 (by omega) (by omega)
      simpa [Sg] using h
  | (k + 1) => by
      rw [Sg_succ]
      exact MidD_append (MidD_Sg k) M232_cols M232_mono

/-- `Sg k` は絶対セグメント（`(2,2,0)` は `Pw_snoc2`、`(3,3,0)` は真横、`(4,2,0)` は `Pw_snoc2`）。 -/
theorem SegA_Sg : ∀ k, SegA 0 (Sg k)
  | 0 => by
      have h := SegA_one 0
      simpa [Sg] using h
  | (k + 1) => by
      refine ⟨MidD_Sg (k + 1), by simp [Sg, entry], ?_⟩
      intro P hP s A' hA'
      have hR0 : RunA 0 (s + 1) (A' ++ shiftr01 s 0 (Sg k)) :=
        ⟨s, A', _, rfl, rfl, ⟨P, hP, by simpa using hA'⟩,
          by simpa using SegA_shift (SegA_Sg k) s⟩
      have hP0 : Pw [] s (A' ++ shiftr01 s 0 (Sg k)) :=
        ⟨0, by rwa [show 1 + s = s + 1 from by omega]⟩
      have hP2 := Pw_cons2 hP0
      have hP32 : Pw [3, 2] s ((A' ++ shiftr01 s 0 (Sg k) ++ [((2 + s + ([] : List ℕ).length, 2, 0) : ℕ × ℕ × ℕ)])
          ++ [((2 + s + 1, 3, 0) : ℕ × ℕ × ℕ)]) :=
        Pw_cons.mpr ⟨_, [], hP2, by simp, by omega, by simpa using Jw_3first s⟩
      have h := Pw_snoc2 hP32
      have heq : shiftr01 s 0 M232 = [((2 + s + 0, 2, 0) : ℕ × ℕ × ℕ), ((2 + s + 1, 3, 0) : ℕ × ℕ × ℕ),
          ((2 + s + 2, 2, 0) : ℕ × ℕ × ℕ)] := by
        simp only [M232, shiftr01, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq,
          Nat.add_zero, and_true, true_and]
        omega
      rw [Sg_succ, shiftr01_append0, heq]
      simpa [List.append_assoc] using h

def A42_300 : TrioSeq := A42 ++ [((3, 0, 0) : ℕ × ℕ × ℕ)]
def A42_400 : TrioSeq := A42 ++ [((4, 0, 0) : ℕ × ℕ × ℕ)]
def A42_500 : TrioSeq := A42 ++ [((5, 0, 0) : ℕ × ℕ × ℕ)]

theorem A42_300_len : A42_300.length = 7 := by simp [A42_300, A42, R294]
theorem A42_400_len : A42_400.length = 7 := by simp [A42_400, A42, R294]
theorem A42_500_len : A42_500.length = 7 := by simp [A42_500, A42, R294]

theorem nextrel0_A42_300 : nextrel0 A42_300 3 6 := by
  refine ⟨by simp [A42_300, A42, R294], by simp [A42_300, A42, R294], by omega,
    by simp [A42_300, A42, R294, entry], ?_⟩
  intro j hj
  rcases j with _ | _ | _ | _ | _ | _ | j
  · omega
  · omega
  · omega
  · omega
  · simp [A42_300, A42, R294, entry]
  · simp [A42_300, A42, R294, entry]
  · omega

theorem nextrel0_A42_400 : nextrel0 A42_400 4 6 := by
  refine ⟨by simp [A42_400, A42, R294], by simp [A42_400, A42, R294], by omega,
    by simp [A42_400, A42, R294, entry], ?_⟩
  intro j hj
  rcases j with _ | _ | _ | _ | _ | _ | j
  · omega
  · omega
  · omega
  · omega
  · omega
  · simp [A42_400, A42, R294, entry]
  · omega

theorem nextrel0_A42_500 : nextrel0 A42_500 5 6 := by
  refine ⟨by simp [A42_500, A42, R294], by simp [A42_500, A42, R294], by omega,
    by simp [A42_500, A42, R294, entry], ?_⟩
  intro j hj
  omega

theorem hasParent0_A42_300 : hasParent A42_300 0 6 := by
  refine ⟨3, by show nextR A42_300 0 3 6; simp only [nextR, if_true]; exact nextrel0_A42_300, ?_⟩
  intro j0 hj0
  change nextR A42_300 0 j0 6 at hj0
  simp only [nextR, if_true] at hj0
  obtain ⟨hj0l, -, hlt, hlt2, hall⟩ := hj0
  rw [A42_300_len] at hj0l
  rcases j0 with _ | _ | _ | _ | _ | _ | j0
  · exfalso; have := hall 3 ⟨by omega, by omega⟩; simp [A42_300, A42, R294, entry] at this
  · exfalso; have := hall 3 ⟨by omega, by omega⟩; simp [A42_300, A42, R294, entry] at this
  · exfalso; have := hall 3 ⟨by omega, by omega⟩; simp [A42_300, A42, R294, entry] at this
  · rfl
  · exfalso; simp [A42_300, A42, R294, entry] at hlt2
  · exfalso; simp [A42_300, A42, R294, entry] at hlt2
  · omega

theorem hasParent0_A42_400 : hasParent A42_400 0 6 := by
  refine ⟨4, by show nextR A42_400 0 4 6; simp only [nextR, if_true]; exact nextrel0_A42_400, ?_⟩
  intro j0 hj0
  change nextR A42_400 0 j0 6 at hj0
  simp only [nextR, if_true] at hj0
  obtain ⟨hj0l, -, hlt, hlt2, hall⟩ := hj0
  rw [A42_400_len] at hj0l
  rcases j0 with _ | _ | _ | _ | _ | _ | j0
  · exfalso; have := hall 4 ⟨by omega, by omega⟩; simp [A42_400, A42, R294, entry] at this
  · exfalso; have := hall 4 ⟨by omega, by omega⟩; simp [A42_400, A42, R294, entry] at this
  · exfalso; have := hall 4 ⟨by omega, by omega⟩; simp [A42_400, A42, R294, entry] at this
  · exfalso; have := hall 4 ⟨by omega, by omega⟩; simp [A42_400, A42, R294, entry] at this
  · rfl
  · exfalso; simp [A42_400, A42, R294, entry] at hlt2
  · omega

theorem hasParent0_A42_500 : hasParent A42_500 0 6 := by
  refine ⟨5, by show nextR A42_500 0 5 6; simp only [nextR, if_true]; exact nextrel0_A42_500, ?_⟩
  intro j0 hj0
  change nextR A42_500 0 j0 6 at hj0
  simp only [nextR, if_true] at hj0
  obtain ⟨hj0l, -, hlt, hlt2, hall⟩ := hj0
  rw [A42_500_len] at hj0l
  rcases j0 with _ | _ | _ | _ | _ | _ | j0
  · exfalso; have := hall 5 ⟨by omega, by omega⟩; simp [A42_500, A42, R294, entry] at this
  · exfalso; have := hall 5 ⟨by omega, by omega⟩; simp [A42_500, A42, R294, entry] at this
  · exfalso; have := hall 5 ⟨by omega, by omega⟩; simp [A42_500, A42, R294, entry] at this
  · exfalso; have := hall 5 ⟨by omega, by omega⟩; simp [A42_500, A42, R294, entry] at this
  · exfalso; have := hall 5 ⟨by omega, by omega⟩; simp [A42_500, A42, R294, entry] at this
  · rfl
  · omega

theorem parent0_A42_300 : parent A42_300 0 6 = 3 :=
  hasParent0_A42_300.unique (parent_nextR hasParent0_A42_300)
    (by show nextR A42_300 0 3 6; simp only [nextR, if_true]; exact nextrel0_A42_300)

theorem parent0_A42_400 : parent A42_400 0 6 = 4 :=
  hasParent0_A42_400.unique (parent_nextR hasParent0_A42_400)
    (by show nextR A42_400 0 4 6; simp only [nextR, if_true]; exact nextrel0_A42_400)

theorem parent0_A42_500 : parent A42_500 0 6 = 5 :=
  hasParent0_A42_500.unique (parent_nextR hasParent0_A42_500)
    (by show nextR A42_500 0 5 6; simp only [nextR, if_true]; exact nextrel0_A42_500)

open Classical in
theorem oper_A42_300 (n : ℕ) : A42_300⟦n⟧ = Q ++ Sg n := by
  rw [L53.oper_flat (j1 := 6) (j0 := 3) (by rw [A42_300_len]) (by omega)
    (by simp [A42_300, A42, R294, entry]) (by simp [srow, A42_300, A42, R294, entry])
    hasParent0_A42_300 parent0_A42_300.symm n]
  simp [A42_300, A42, R294, Q, Sg, M232, entry, List.range']

/-- ★★★ `A42(3,0,0) ∈ W 0`。 -/
theorem A42_300_mem : A42_300 ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_A42_300]
  have h := (SegA_Sg n).reapp _ BaseOk_zero 0 Q (LwB_of_base ⟨(Aok_Q : Aok Q), rfl⟩)
  simpa using h

/-- `(3,3,0)(4,2,0)`。 -/
def M32 : TrioSeq := [((3, 3, 0) : ℕ × ℕ × ℕ), ((4, 2, 0) : ℕ × ℕ × ℕ)]

/-- 語の頂上の `(·,2,0)` には junk なしの条件が付く。 -/
theorem Jw_col2 (r : List ℕ) (s : ℕ) : Jw r 2 s [] := by
  refine ⟨by simp, by intro c hc; simp at hc, ?_⟩
  intro t Y' hY'
  have h := Pw_snoc2 hY'
  simpa [show 2 + (s + t) + r.length = 2 + s + r.length + t from by omega] using h

/-- `(2,2,0)` の後ろの junk `M32^n`。 -/
theorem Jw_M32pow : ∀ n : ℕ, Jw [] 2 0 ((List.range n).flatMap (fun _ => M32))
  | 0 => by simpa using Jw_col2 [] 0
  | (n + 1) => by
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have ih := Jw_M32pow n
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact ih.1 x h
        · simp only [M32, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl <;> simp
      · intro c hc
        rcases List.mem_append.mp hc with h | h
        · exact ih.2.1 c h
        · simp only [M32, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl <;> simp
      · intro t Y' hY'
        have hP2 : Pw [2] t (Y' ++ ([((2 + t + ([] : List ℕ).length, 2, 0) : ℕ × ℕ × ℕ)]
            ++ shiftr01 t 0 ((List.range n).flatMap (fun _ => M32)))) :=
          Pw_cons.mpr ⟨Y', _, by simpa using hY', rfl, by omega, by simpa using Jw_shift ih t⟩
        have hP32 : Pw [3, 2] t ((Y' ++ ([((2 + t + ([] : List ℕ).length, 2, 0) : ℕ × ℕ × ℕ)]
            ++ shiftr01 t 0 ((List.range n).flatMap (fun _ => M32))))
            ++ [((2 + t + 1, 3, 0) : ℕ × ℕ × ℕ)]) :=
          Pw_cons.mpr ⟨_, [], hP2, by simp, by omega, by simpa using Jw_3first t⟩
        have h := Pw_snoc2 hP32
        have heq : shiftr01 t 0 M32 = [((2 + t + 1, 3, 0) : ℕ × ℕ × ℕ),
            ((2 + t + 2, 2, 0) : ℕ × ℕ × ℕ)] := by
          simp only [M32, shiftr01, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq,
            Nat.add_zero, and_true, true_and]
          omega
        rw [shiftr01_append0, heq]
        simpa [List.append_assoc] using h

open Classical in
theorem oper_A42_400 (n : ℕ) :
    A42_400⟦n⟧ = (Q ++ [((1, 1, 0) : ℕ × ℕ × ℕ)]) ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)]
      ++ (List.range n).flatMap (fun _ => M32)) := by
  rw [L53.oper_flat (j1 := 6) (j0 := 4) (by rw [A42_400_len]) (by omega)
    (by simp [A42_400, A42, R294, entry]) (by simp [srow, A42_400, A42, R294, entry])
    hasParent0_A42_400 parent0_A42_400.symm n]
  simp [A42_400, A42, R294, Q, M32, entry, List.range']

/-- ★★★ `A42(4,0,0) ∈ W 0`。 -/
theorem A42_400_mem : A42_400 ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_A42_400]
  refine Pw_mem (r := [2]) (s := 0) (Pw_cons.mpr ⟨_, _, ?_, rfl, by omega, by simpa using Jw_M32pow n⟩)
  exact Pw_nil_of_RunA (h := 0) (by simpa [Uu] using RunA_Uu 0)

/-- `(3,3,0)` の後ろの junk `(4,2,0)^n`。 -/
theorem Jw_42pow : ∀ n : ℕ,
    Jw [2] 3 0 ((List.range n).flatMap (fun _ => [((4, 2, 0) : ℕ × ℕ × ℕ)]))
  | 0 => by simpa using Jw_3first 0
  | (n + 1) => by
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have ih := Jw_42pow n
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact ih.1 x h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          subst h; simp
      · intro c hc
        rcases List.mem_append.mp hc with h | h
        · exact ih.2.1 c h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          subst h; simp
      · intro t Y' hY'
        have hP32 : Pw [3, 2] t (Y' ++ ([((2 + t + [2].length, 3, 0) : ℕ × ℕ × ℕ)]
            ++ shiftr01 t 0 ((List.range n).flatMap (fun _ => [((4, 2, 0) : ℕ × ℕ × ℕ)])))) :=
          Pw_cons.mpr ⟨Y', _, by simpa using hY', rfl, by omega, by simpa using Jw_shift ih t⟩
        have h := Pw_snoc2 hP32
        rw [shiftr01_append0, shift_col]
        simp only [List.length_cons, List.length_nil, List.append_assoc, List.cons_append,
          List.nil_append] at h ⊢
        rw [show 4 + t = 2 + t + (0 + 1 + 1) from by omega,
          show 2 + 0 + (0 + 1) + t = 2 + t + (0 + 1) from by omega]
        exact h

open Classical in
theorem oper_A42_500 (n : ℕ) :
    A42_500⟦n⟧ = R292 ++ ([((3, 3, 0) : ℕ × ℕ × ℕ)]
      ++ (List.range n).flatMap (fun _ => [((4, 2, 0) : ℕ × ℕ × ℕ)])) := by
  rw [L53.oper_flat (j1 := 6) (j0 := 5) (by rw [A42_500_len]) (by omega)
    (by simp [A42_500, A42, R294, entry]) (by simp [srow, A42_500, A42, R294, entry])
    hasParent0_A42_500 parent0_A42_500.symm n]
  simp [A42_500, A42, R294, R292, Q, entry, List.range']

/-- ★★★ `A42(5,0,0) ∈ W 0`。 -/
theorem A42_500_mem : A42_500 ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_A42_500]
  exact Pw_mem (r := [3, 2]) (s := 0)
    (Pw_cons.mpr ⟨R292, _, Pw2_R292, rfl, by omega, by simpa using Jw_42pow n⟩)

#print axioms A42_500_mem

/-! ### 層の梯子（notes 続き25）: 台座クラス `E` の上の走り `RunG E` -/

/-- 「境界 `bd` より低い可視な記録（頭以外）の行 1 は 2 以上」（`snocYd_mem` の `hMy`）。 -/
def Vis2 (bd : ℕ) (M : TrioSeq) : Prop :=
  ∀ t, 1 ≤ t → t < M.length → entry M 0 t < bd →
    (∀ i, t < i → i < M.length → entry M 0 t < entry M 0 i) → 2 ≤ entry M 1 t

theorem Vis2_shift {bd : ℕ} {M : TrioSeq} (hM : Vis2 bd M) (v : ℕ) :
    Vis2 (bd + v) (shiftr01 v 0 M) := by
  intro t ht1 htl hlt hrec
  have hlen : (shiftr01 v 0 M).length = M.length := shiftr01_length v 0 M
  rw [hlen] at htl
  rw [entry_shift1 htl]
  rw [entry_shift0 htl] at hlt
  refine hM t ht1 htl (by omega) ?_
  intro i hti hiM
  have := hrec i hti (by rw [hlen]; exact hiM)
  rw [entry_shift0 htl, entry_shift0 hiM] at this
  omega

/-- 台座クラスの界面: `BaseOk` と再台座性（元は `LwA` の頭 ++ 単位 `M`、`M` はどの `LwA` 台座にも継げる）。 -/
structure Iface (E : ℕ → TrioSeq → Prop) : Prop where
  bok : BaseOk E
  rebase : ∀ (h : ℕ) (A : TrioSeq), E h A → ∃ (b : ℕ) (Y0 M : TrioSeq),
    A = Y0 ++ M ∧ LwA b Y0 ∧ MidD (b + 2) M ∧ entry M 1 0 < 2 ∧ b < h ∧ Vis2 (h + 1) M ∧
    (∀ (s : ℕ) (Y0' : TrioSeq), LwA (b + s) Y0' → E (h + s) (Y0' ++ shiftr01 s 0 M))

/-- `E` の元の上に `(·,2,0)` ブロックを `j` 本（`RunA` の台座を `E` にしたもの）。 -/
def RunG (E : ℕ → TrioSeq → Prop) : ℕ → ℕ → TrioSeq → Prop
  | 0, h, A => E h A
  | (j + 1), h, A => ∃ (b : ℕ) (A0 N : TrioSeq), h = b + 1 ∧ A = A0 ++ N ∧
      RunG E j b A0 ∧ MidD (b + 2) N ∧ 2 ≤ entry N 1 0 ∧
      (∀ (s : ℕ) (X : TrioSeq), RunG E j (b + s) X → X ++ shiftr01 s 0 N ∈ W 0)

theorem BaseOk_RunG {E : ℕ → TrioSeq → Prop} (hE : BaseOk E) : ∀ j : ℕ, BaseOk (RunG E j)
  | 0 => hE
  | (j + 1) => by
      have hIHj := BaseOk_RunG hE j
      refine ⟨?_, ?_, ?_, ?_⟩
      · rintro h A ⟨b, A0, N, rfl, rfl, hA0, hN, hN2, hre⟩
        have hmem : A0 ++ N ∈ W 0 := by
          have h1 := hre 0 A0 (by simpa using hA0)
          simpa using h1
        exact Aok_append_Mid (by omega) (hIHj.aok b A0 hA0) hN hmem
      · rintro h A ⟨b, A0, N, rfl, rfl, hA0, hN, hN2, hre⟩
        exact Ancd_append_Mid (hIHj.aok b A0 hA0).ne (hIHj.ancd b A0 hA0) hN
      · rintro h A ⟨b, A0, N, rfl, rfl, hA0, hN, hN2, hre⟩ B hB
        have hbase : ∀ (s : ℕ) (X : TrioSeq), Aok X → RunG E j (b + s) X →
            X ++ shiftr01 s 0 N ∈ W 0 := fun s X _ hX => hre s X hX
        have hclose : ∀ (s : ℕ) (X C' : TrioSeq), Aok X → RunG E j (b + s) X → Mono C' →
            (∀ (t : ℕ) (Y : TrioSeq), Aok Y → RunG E j (b + t) Y →
              Y ++ BlkD (b + 2 + t) (shiftr01 t 0 N) C' ∈ W 0) →
            RunG E j (b + s) (X ++ BlkD (b + 2 + s) (shiftr01 s 0 N) C') := by
          intro s X C' _ hX hmoC' hIH
          have hNs : MidD (b + 2 + s) (shiftr01 s 0 N) := MidD_shift hN s
          refine hIHj.close (b + s) X _ hX ?_ (BlkD_mono hNs.mono hmoC') ?_
          · intro x hx
            rcases List.mem_append.mp hx with hh | hh
            · have := MidD_col_ge hNs x hh; omega
            · have := shiftD_col x hh; omega
          · intro t Y hY
            have heq : shiftr01 t 0 (BlkD (b + 2 + s) (shiftr01 s 0 N) C')
                = BlkD (b + 2 + (s + t)) (shiftr01 (s + t) 0 N) C' := by
              simp only [BlkD, shiftr01_append0, shiftr01_add0]
              congr 2
              omega
            rw [heq]
            have hY' : RunG E j (b + (s + t)) Y := by
              rwa [show b + (s + t) = b + s + t from by omega]
            exact hIH (s + t) Y (hIHj.aok _ _ hY') hY'
        have hkey := blkD_memS (d := b + 2) (by omega) N hN hbase hclose B hB.mem
          hB.zroot hB.mono hB.root 0 A0 (hIHj.aok b A0 hA0) (by simpa using hA0)
        simp only [shiftr01_zero, Nat.add_zero] at hkey
        rw [BlkD_app] at hkey
        exact hkey
      · rintro h A Blk ⟨b, A0, N, rfl, rfl, hA0, hN, hN2, hre⟩ hcol hmo hcl
        refine ⟨b, A0, N ++ Blk, rfl, by rw [List.append_assoc], hA0,
          MidD_append hN (by intro x hx; have := hcol x hx; omega) hmo, ?_, ?_⟩
        · rw [entry_append_left (List.length_pos_iff.mpr hN.ne)]
          exact hN2
        · intro s X hX
          rw [shiftr01_append0, ← List.append_assoc]
          have h1 : X ++ shiftr01 s 0 N ∈ W 0 := hre s X hX
          have hstep : RunG E (j + 1) (b + 1 + s) (X ++ shiftr01 s 0 N) := by
            refine ⟨b + s, X, shiftr01 s 0 N, by omega, rfl, hX, ?_, ?_, ?_⟩
            · have h2 := MidD_shift hN s
              rwa [show b + 2 + s = b + s + 2 from by omega] at h2
            · rw [entry_shift1 (List.length_pos_iff.mpr hN.ne)]
              exact hN2
            · intro t Z hZ
              rw [shiftr01_add0]
              refine hre (s + t) Z ?_
              rwa [show b + (s + t) = b + s + t from by omega]
          exact hcl s _ hstep

theorem RunG_LwA {E : ℕ → TrioSeq → Prop} (hE : BaseOk E) (j h : ℕ) (Z : TrioSeq)
    (hZ : RunG E j h Z) : LwA h Z :=
  ⟨RunG E j, BaseOk_RunG hE j, 0, hZ⟩

/-- 走りの塊（台座 `E` 版）。`RunGU E j c h U`: `U` = `E` の単位（`LwA` レベル `c`、`E` レベル `h`）
++ `(·,2,0)` ブロック `j` 本。 -/
def RunGU (E : ℕ → TrioSeq → Prop) : ℕ → ℕ → ℕ → TrioSeq → Prop
  | 0, c, h, U => MidD (c + 2) U ∧ entry U 1 0 < 2 ∧ c < h ∧ Vis2 (h + 1) U ∧
      (∀ (s : ℕ) (Y0' : TrioSeq), LwA (c + s) Y0' → E (h + s) (Y0' ++ shiftr01 s 0 U))
  | (j + 1), c, h, U => ∃ U0 N : TrioSeq, U = U0 ++ N ∧ RunGU E j c h U0 ∧
      MidD (h + j + 2) N ∧ 2 ≤ entry N 1 0 ∧
      (∀ (s : ℕ) (X : TrioSeq), RunG E j (h + j + s) X → X ++ shiftr01 s 0 N ∈ W 0)

theorem RunGU_lt {E : ℕ → TrioSeq → Prop} : ∀ (j c h : ℕ) (U : TrioSeq),
    RunGU E j c h U → c < h
  | 0, _, _, _, hU => hU.2.2.1
  | (j + 1), c, h, U, hU => by
      obtain ⟨U0, N, rfl, hU0, -, -, -⟩ := hU
      exact RunGU_lt j c h U0 hU0

theorem RunGU_mid {E : ℕ → TrioSeq → Prop} : ∀ (j c h : ℕ) (U : TrioSeq),
    RunGU E j c h U → MidD (c + 2) U
  | 0, _, _, _, hU => hU.1
  | (j + 1), c, h, U, hU => by
      obtain ⟨U0, N, rfl, hU0, hN, hN2, hre⟩ := hU
      have hlt := RunGU_lt j c h U0 hU0
      refine MidD_append (RunGU_mid j c h U0 hU0) ?_ hN.mono
      intro x hx
      have := MidD_col_ge hN x hx
      omega

theorem RunGU_head1 {E : ℕ → TrioSeq → Prop} : ∀ (j c h : ℕ) (U : TrioSeq),
    RunGU E j c h U → entry U 1 0 < 2
  | 0, _, _, _, hU => hU.2.1
  | (j + 1), c, h, U, hU => by
      obtain ⟨U0, N, rfl, hU0, hN, hN2, hre⟩ := hU
      rw [entry_append_left (List.length_pos_iff.mpr (RunGU_mid j c h U0 hU0).ne)]
      exact RunGU_head1 j c h U0 hU0

theorem RunGU_shift {E : ℕ → TrioSeq → Prop} : ∀ (j c h : ℕ) (U : TrioSeq),
    RunGU E j c h U → ∀ v : ℕ, RunGU E j (c + v) (h + v) (shiftr01 v 0 U)
  | 0, c, h, U, hU, v => by
      obtain ⟨hM, h1, hlt, hvis, hre⟩ := hU
      refine ⟨?_, ?_, by omega, ?_, ?_⟩
      · have h2 := MidD_shift hM v
        rwa [show c + 2 + v = c + v + 2 from by omega] at h2
      · rw [entry_shift1 (List.length_pos_iff.mpr hM.ne)]; exact h1
      · have h2 := Vis2_shift hvis v
        rwa [show h + 1 + v = h + v + 1 from by omega] at h2
      · intro s Y0' hY0'
        rw [shiftr01_add0]
        have h2 := hre (v + s) Y0' (by rwa [show c + (v + s) = c + v + s from by omega])
        rwa [show h + (v + s) = h + v + s from by omega] at h2
  | (j + 1), c, h, U, hU, v => by
      obtain ⟨U0, N, rfl, hU0, hN, hN2, hre⟩ := hU
      refine ⟨shiftr01 v 0 U0, shiftr01 v 0 N, by rw [shiftr01_append0],
        RunGU_shift j c h U0 hU0 v, ?_, ?_, ?_⟩
      · have h1 := MidD_shift hN v
        rwa [show h + j + 2 + v = h + v + j + 2 from by omega] at h1
      · rw [entry_shift1 (List.length_pos_iff.mpr hN.ne)]
        exact hN2
      · intro s X hX
        rw [shiftr01_add0]
        refine hre (v + s) X ?_
        rwa [show h + j + (v + s) = h + v + j + s from by omega]

/-- `snocYd_mem` の `hMy`（`RunU_rec` の台座 `E` 版）。 -/
theorem RunGU_rec {E : ℕ → TrioSeq → Prop} : ∀ (j c h : ℕ) (U : TrioSeq),
    RunGU E j c h U → Vis2 (h + j + 1) U
  | 0, c, h, U, hU => by
      have h1 := hU.2.2.2.1
      rwa [show h + 0 + 1 = h + 1 from by omega]
  | (j + 1), c, h, U, hU => by
      obtain ⟨U0, N, rfl, hU0, hN, hN2, hre⟩ := hU
      intro t ht1 htl hlt hrec
      have hU0mid := RunGU_mid j c h U0 hU0
      have hU0len : 0 < U0.length := List.length_pos_iff.mpr hU0mid.ne
      have hNlen : 0 < N.length := List.length_pos_iff.mpr hN.ne
      have hlen : (U0 ++ N).length = U0.length + N.length := by simp
      have hNh : entry (U0 ++ N) 0 U0.length = h + j + 1 := by
        rw [show U0.length = U0.length + 0 from rfl, entry_append_right]
        have := hN.head; omega
      rcases Nat.lt_trichotomy t U0.length with hh | hh | hh
      · rw [entry_append_left hh] at hlt ⊢
        have hlt' : entry U0 0 t < h + j + 1 := by
          have := hrec U0.length hh (by omega)
          rw [entry_append_left hh, hNh] at this
          omega
        refine RunGU_rec j c h U0 hU0 t ht1 hh hlt' ?_
        intro i hti hiU
        have := hrec i hti (by omega)
        rw [entry_append_left hh, entry_append_left hiU] at this
        exact this
      · subst hh
        rw [show U0.length = U0.length + 0 from rfl, entry_append_right]
        exact hN2
      · exfalso
        obtain ⟨q, rfl⟩ : ∃ q, t = U0.length + q := ⟨t - U0.length, by omega⟩
        rw [entry_append_right] at hlt
        have := hN.tail q (by omega) (by omega)
        omega

theorem RunG_of {E : ℕ → TrioSeq → Prop} : ∀ (j c h : ℕ) (Y0 U : TrioSeq),
    LwA c Y0 → RunGU E j c h U → RunG E j (h + j) (Y0 ++ U)
  | 0, c, h, Y0, U, hY0, hU => by
      have h1 := hU.2.2.2.2 0 Y0 (by simpa using hY0)
      simpa using h1
  | (j + 1), c, h, Y0, U, hY0, hU => by
      obtain ⟨U0, N, rfl, hU0, hN, hN2, hre⟩ := hU
      refine ⟨h + j, Y0 ++ U0, N, by omega, by rw [List.append_assoc],
        RunG_of j c h Y0 U0 hY0 hU0, hN, hN2, ?_⟩
      exact hre

theorem RunG_to {E : ℕ → TrioSeq → Prop} (hI : Iface E) : ∀ (j h' : ℕ) (X : TrioSeq),
    RunG E j h' X →
    ∃ (c h : ℕ) (Y0 U : TrioSeq), h' = h + j ∧ X = Y0 ++ U ∧ LwA c Y0 ∧ RunGU E j c h U
  | 0, h', X, hX => by
      obtain ⟨b, Y0, M, rfl, hY0, hM, hM1, hlt, hvis, hre⟩ := hI.rebase h' X hX
      exact ⟨b, h', Y0, M, rfl, rfl, hY0, hM, hM1, hlt, hvis, hre⟩
  | (j + 1), h', X, hX => by
      obtain ⟨b, A0, N, rfl, rfl, hA0, hN, hN2, hre⟩ := hX
      obtain ⟨c, h, Y0, U0, rfl, rfl, hY0, hU0⟩ := RunG_to hI j b A0 hA0
      refine ⟨c, h, Y0, U0 ++ N, by omega, by rw [List.append_assoc], hY0,
        ⟨U0, N, rfl, hU0, ?_, hN2, ?_⟩⟩
      · rwa [show h + j + 2 = h + j + 2 from rfl] at hN
      · exact hre

/-- ★★ 走りの塊の塔（歩幅 `h + j - c`）。段が上がっても `RunG E j` のまま。 -/
theorem RunGU_tower {E : ℕ → TrioSeq → Prop} (hE : BaseOk E) {j c h : ℕ} {Y0 U : TrioSeq}
    (hY0 : LwA c Y0) (hU : RunGU E j c h U) :
    ∀ n : ℕ, RunG E j (h + j + n * (h + j - c)) (Mtwd (h + j - c) Y0 U (n + 1))
  | 0 => by
      rw [Mtwd_one]
      simpa using RunG_of j c h Y0 U hY0 hU
  | (n + 1) => by
      have hlt := RunGU_lt j c h U hU
      have hprev := RunGU_tower hE hY0 hU n
      rw [Mtwd_succ]
      have hL : LwA (h + j + n * (h + j - c)) (Mtwd (h + j - c) Y0 U (n + 1)) :=
        RunG_LwA hE j _ _ hprev
      have hv : c + (h + j - c) * (n + 1) = h + j + n * (h + j - c) := by
        rw [Nat.mul_succ, Nat.mul_comm (h + j - c) n]
        omega
      have hUs : RunGU E j (h + j + n * (h + j - c)) (h + (h + j - c) * (n + 1))
          (shiftr01 ((h + j - c) * (n + 1)) 0 U) := by
        have h1 := RunGU_shift j c h U hU ((h + j - c) * (n + 1))
        rwa [hv] at h1
      have h2 := RunG_of j _ _ _ _ hL hUs
      rw [show h + (h + j - c) * (n + 1) + j = h + j + (n + 1) * (h + j - c) from by
        rw [Nat.succ_mul, Nat.mul_succ, Nat.mul_comm (h + j - c) n]; omega] at h2
      exact h2

theorem RunGU_tower_mem {E : ℕ → TrioSeq → Prop} (hE : BaseOk E) {j c h : ℕ} {Y0 U : TrioSeq}
    (hY0 : LwA c Y0) (hU : RunGU E j c h U) :
    ∀ n : ℕ, Mtwd (h + j - c) Y0 U n ∈ W 0
  | 0 => by rw [Mtwd_zero]; exact (LwA_Aok hY0).mem
  | (n + 1) => ((BaseOk_RunG hE j).aok _ _ (RunGU_tower hE hY0 hU n)).mem

/-- ★★★ 走りの上に `(·,2,0)` を継げる（台座 `E` 版）。 -/
theorem RunG_snoc2 {E : ℕ → TrioSeq → Prop} (hI : Iface E) (j h : ℕ) (X : TrioSeq)
    (hX : RunG E j h X) : X ++ [((h + 1, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  obtain ⟨c, h0, Y0, U, rfl, rfl, hY0, hU⟩ := RunG_to hI j _ X hX
  have hlt := RunGU_lt j c h0 U hU
  have hmid : MidD (c + 2) U := RunGU_mid j c h0 U hU
  have hne : Y0 ≠ [] := (LwA_Aok hY0).ne
  have h1 := snocYd_mem (Y0 := Y0) (M := U) (L := c + 1) (y := 2) (dl := h0 + j - c)
    hne (by rwa [show c + 1 + 1 = c + 2 from by omega]) (RunGU_head1 j c h0 U hU)
    ?_ (by omega) (by omega) (RunGU_tower_mem hI.bok hY0 hU)
  · rwa [show c + 1 + (h0 + j - c) = h0 + j + 1 from by omega] at h1
  · intro t ht1 htl hlt' hrec
    refine RunGU_rec j c h0 U hU t ht1 htl ?_ hrec
    omega

#print axioms RunG_snoc2

/-! ### `E` の上の 2-ブロック（全 rank で継げる junk つき）と 3-記録: `PkG E`, `Pk3 E` -/

/-- `(c+1,2,0)` の後ろの junk: 高さ `c+2` 以上、`Mono`、どの `RunG E j` の頭にも継げる（全 rank）。 -/
def JkG (E : ℕ → TrioSeq → Prop) (c : ℕ) (J : TrioSeq) : Prop :=
  (∀ x ∈ J, c + 2 ≤ x.1) ∧ Mono J ∧
  ∀ (j t : ℕ) (X : TrioSeq), RunG E j (c + t) X →
    X ++ ([((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J) ∈ W 0

theorem JkG_nil {E : ℕ → TrioSeq → Prop} (hI : Iface E) (c : ℕ) : JkG E c [] := by
  refine ⟨by simp, by intro x hx; simp at hx, ?_⟩
  intro j t X hX
  have h := RunG_snoc2 hI j (c + t) X hX
  simpa [shiftr01, show c + t + 1 = c + 1 + t from by omega] using h

theorem JkG_shift {E : ℕ → TrioSeq → Prop} {c : ℕ} {J : TrioSeq} (hJ : JkG E c J) (u : ℕ) :
    JkG E (c + u) (shiftr01 u 0 J) := by
  refine ⟨?_, shiftD_mono hJ.2.1, ?_⟩
  · intro x hx
    simp only [shiftr01, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have := hJ.1 p hp
    dsimp only
    omega
  · intro j t X hX
    rw [shiftr01_add0]
    have hX' : RunG E j (c + (u + t)) X := by
      rw [show c + (u + t) = c + u + t from by omega]; exact hX
    have h := hJ.2.2 j (u + t) X hX'
    rw [show c + u + 1 + t = c + 1 + (u + t) from by omega]
    exact h

theorem JkG_mid {E : ℕ → TrioSeq → Prop} {c : ℕ} {J : TrioSeq} (hJ : JkG E c J) :
    MidD (c + 2) ([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J) := by
  have h := MidD_append (MidD_col (c + 1) 2 (by omega) (by omega))
    (by intro x hx; have := hJ.1 x hx; omega) hJ.2.1
  rwa [show c + 1 + 1 = c + 2 from by omega] at h

/-- junk つきブロックはどの `RunG E j` の頭にも継げる（`RunG E (j+1)`）。 -/
theorem JkG_blk {E : ℕ → TrioSeq → Prop} {c : ℕ} {J : TrioSeq} (hJ : JkG E c J) {j : ℕ}
    {X : TrioSeq} (hX : RunG E j c X) :
    RunG E (j + 1) (c + 1) (X ++ ([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J)) := by
  refine ⟨c, X, _, rfl, rfl, hX, JkG_mid hJ, ?_, ?_⟩
  · rw [entry_cons_append_1]
  · intro t X' hX'
    simpa [shiftr01_append0, shift_col] using hJ.2.2 j t X' hX'

theorem JkG_tw {E : ℕ → TrioSeq → Prop} {c : ℕ} {J : TrioSeq} (hJ : JkG E c J) {j : ℕ}
    {X : TrioSeq} (hX : RunG E j c X) :
    ∀ n : ℕ, RunG E (j + n) (c + n) (Mtw X ([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J) n)
  | 0 => by simpa [Mtw_zero] using hX
  | (n + 1) => by
      rw [Mtw_succ, shiftr01_append0, shift_col]
      have ih := JkG_tw hJ hX n
      have h := JkG_blk (JkG_shift hJ n) ih
      rw [show c + (n + 1) = c + n + 1 from by omega, show j + (n + 1) = j + n + 1 from by omega,
        show c + 1 + n = c + n + 1 from by omega]
      exact h

/-- junk つきブロックの直後（頭の 1 つ上）に `(·,3,0)` を継げる。 -/
theorem JkG_snoc3 {E : ℕ → TrioSeq → Prop} (hE : BaseOk E) {c : ℕ} {J : TrioSeq}
    (hJ : JkG E c J) {j : ℕ} {X : TrioSeq} (hX : RunG E j c X) :
    (X ++ ([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J)) ++ [((c + 2, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hXok : Aok X := (BaseOk_RunG hE j).aok _ _ hX
  have hM : MidD (c + 1 + 1) ([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J) := by
    have h := JkG_mid hJ
    rwa [show c + 2 = c + 1 + 1 from by omega] at h
  have h := snocY_mem (L := c + 1) (y := 3) hXok.ne hM
    (by rw [entry_cons_append_1]; show (2 : ℕ) < 3; omega)
    (by omega) (fun n => ((BaseOk_RunG hE (j + n)).aok _ _ (JkG_tw hJ hX n)).mem)
  rwa [show c + 1 + 1 = c + 2 from by omega] at h

/-- `RunG E j` の頭 ++ `(c+1,2,0)` ++ junk。レベル `c+1`。 -/
def PkG (E : ℕ → TrioSeq → Prop) (h : ℕ) (Y : TrioSeq) : Prop :=
  ∃ (j c : ℕ) (X J : TrioSeq), h = c + 1 ∧ RunG E j c X ∧
    Y = X ++ ([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J) ∧ JkG E c J

theorem PkG_Aok {E : ℕ → TrioSeq → Prop} (hE : BaseOk E) {h : ℕ} {Y : TrioSeq}
    (hY : PkG E h Y) : Aok Y := by
  obtain ⟨j, c, X, J, rfl, hX, rfl, hJ⟩ := hY
  have hmem := hJ.2.2 j 0 X (by simpa using hX)
  simp only [shiftr01_zero, Nat.add_zero] at hmem
  exact Aok_append_Mid (by omega) ((BaseOk_RunG hE j).aok _ _ hX) (JkG_mid hJ) hmem

theorem PkG_Ancd {E : ℕ → TrioSeq → Prop} (hE : BaseOk E) {h : ℕ} {Y : TrioSeq}
    (hY : PkG E h Y) : Ancd (h + 1) Y := by
  obtain ⟨j, c, X, J, rfl, hX, rfl, hJ⟩ := hY
  have h1 := (BaseOk_RunG hE j).ancd _ _ hX
  have hM := JkG_mid hJ
  rw [show c + 1 + 1 = c + 2 from by omega]
  exact Ancd_append_Mid ((BaseOk_RunG hE j).aok _ _ hX).ne h1 hM

/-- `blkD_memS` の `hclose`: 吊るした junk を `(c+1,2,0)` の junk に吸収する。 -/
theorem PkG_absorb {E : ℕ → TrioSeq → Prop} (hE : BaseOk E) {c : ℕ} {M : TrioSeq}
    (hM : MidD (c + 3) M) {C' : TrioSeq} (hmoC' : Mono C')
    (hIH : ∀ (t : ℕ) (A'' : TrioSeq), Aok A'' → PkG E (c + 1 + t) A'' →
      A'' ++ BlkD (c + 3 + t) (shiftr01 t 0 M) C' ∈ W 0)
    (t : ℕ) (A' : TrioSeq) (hA' : PkG E (c + 1 + t) A') :
    PkG E (c + 1 + t) (A' ++ BlkD (c + 3 + t) (shiftr01 t 0 M) C') := by
  obtain ⟨j, c', X, J, hc, hX, rfl, hJ⟩ := hA'
  have hc' : c' = c + t := by omega
  subst hc'
  refine ⟨j, c + t, X, J ++ BlkD (c + 3 + t) (shiftr01 t 0 M) C', by omega, hX,
    by simp [List.append_assoc], ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hJ.1 x h
    · rcases List.mem_append.mp h with h' | h'
      · have := MidD_col_ge (MidD_shift hM t) x h'
        omega
      · have := shiftD_col x h'
        omega
  · have h1 : Mono (J ++ shiftr01 t 0 M) := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hJ.2.1 x h
      · exact shiftD_mono hM.mono x h
    have h2 := BlkD_mono (d := c + 3 + t) h1 hmoC'
    simpa [BlkD, List.append_assoc] using h2
  · intro j' t' X' hX'
    have hA'' : PkG E (c + 1 + (t + t')) (X' ++ ([((c + t + 1 + t', 2, 0) : ℕ × ℕ × ℕ)]
        ++ shiftr01 t' 0 J)) := by
      refine ⟨j', c + t + t', X', shiftr01 t' 0 J, by omega, hX',
        by rw [show c + t + t' + 1 = c + t + 1 + t' from by omega], JkG_shift hJ t'⟩
    have h := hIH (t + t') _ (PkG_Aok hE hA'') hA''
    rw [BlkD_shift_eq] at h ⊢
    rw [shiftr01_append0, shiftr01_append0, shiftr01_add0, shiftr01_add0,
      show c + 3 + t + t' = c + 3 + (t + t') from by omega, ← List.append_assoc]
    simpa only [List.append_assoc] using h

/-- `(c+2,3,0)` の後ろの junk: 高さ `c+3` 以上、`Mono`、`PkG E` の元の上に継げる。 -/
def Jk3G (E : ℕ → TrioSeq → Prop) (c : ℕ) (J : TrioSeq) : Prop :=
  (∀ x ∈ J, c + 3 ≤ x.1) ∧ Mono J ∧
  ∀ (t : ℕ) (Y : TrioSeq), PkG E (c + 1 + t) Y →
    Y ++ ([((c + 2 + t, 3, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J) ∈ W 0

theorem Jk3G_nil {E : ℕ → TrioSeq → Prop} (hE : BaseOk E) (c : ℕ) : Jk3G E c [] := by
  refine ⟨by simp, by intro x hx; simp at hx, ?_⟩
  intro t Y hY
  obtain ⟨j, c', X, J, hc, hX, rfl, hJ⟩ := hY
  have hc' : c' = c + t := by omega
  subst hc'
  have h := JkG_snoc3 hE hJ hX
  simpa [shiftr01, show c + t + 2 = c + 2 + t from by omega] using h

theorem Jk3G_shift {E : ℕ → TrioSeq → Prop} {c : ℕ} {J : TrioSeq} (hJ : Jk3G E c J) (u : ℕ) :
    Jk3G E (c + u) (shiftr01 u 0 J) := by
  refine ⟨?_, shiftD_mono hJ.2.1, ?_⟩
  · intro x hx
    simp only [shiftr01, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have := hJ.1 p hp
    dsimp only
    omega
  · intro t Y hY
    rw [shiftr01_add0]
    have hY' : PkG E (c + 1 + (u + t)) Y := by
      rw [show c + 1 + (u + t) = c + u + 1 + t from by omega]; exact hY
    have h := hJ.2.2 (u + t) Y hY'
    rw [show c + u + 2 + t = c + 2 + (u + t) from by omega]
    exact h

theorem Jk3G_mid {E : ℕ → TrioSeq → Prop} {c : ℕ} {J : TrioSeq} (hJ : Jk3G E c J) :
    MidD (c + 3) ([((c + 2, 3, 0) : ℕ × ℕ × ℕ)] ++ J) := by
  have h := MidD_append (MidD_col (c + 2) 3 (by omega) (by omega))
    (by intro x hx; have := hJ.1 x hx; omega) hJ.2.1
  rwa [show c + 2 + 1 = c + 3 from by omega] at h

/-- `PkG E` の頭 ++ `(c+2,3,0)` ++ junk。レベル `c+2`。 -/
def Pk3 (E : ℕ → TrioSeq → Prop) (h : ℕ) (A : TrioSeq) : Prop :=
  ∃ (c : ℕ) (Y J : TrioSeq), h = c + 2 ∧ PkG E (c + 1) Y ∧
    A = Y ++ ([((c + 2, 3, 0) : ℕ × ℕ × ℕ)] ++ J) ∧ Jk3G E c J

theorem Pk3_aok {E : ℕ → TrioSeq → Prop} (hE : BaseOk E) (h : ℕ) (A : TrioSeq)
    (hA : Pk3 E h A) : Aok A := by
  obtain ⟨c, Y, J, rfl, hY, rfl, hJ⟩ := hA
  have hmem := hJ.2.2 0 Y (by simpa using hY)
  simp only [shiftr01_zero, Nat.add_zero] at hmem
  exact Aok_append_Mid (by omega) (PkG_Aok hE hY) (Jk3G_mid hJ) hmem

theorem Pk3_ancd {E : ℕ → TrioSeq → Prop} (hE : BaseOk E) (h : ℕ) (A : TrioSeq)
    (hA : Pk3 E h A) : Ancd (h + 1) A := by
  obtain ⟨c, Y, J, rfl, hY, rfl, hJ⟩ := hA
  have hM := Jk3G_mid hJ
  rw [show c + 3 = c + 2 + 1 from by omega] at hM
  have h1 := PkG_Ancd hE hY
  rw [show c + 1 + 1 = c + 2 from by omega] at h1
  exact Ancd_append_Mid (PkG_Aok hE hY).ne h1 hM

/-- ★★ `Pk3 E` の頭の上（レベル `+1`）に `Bok` を吊るせる。 -/
theorem Pk3_hang {E : ℕ → TrioSeq → Prop} (hE : BaseOk E) (h : ℕ) (A : TrioSeq)
    (hA : Pk3 E h A) (B : TrioSeq) (hB : Bok B) : A ++ shiftr01 (h + 1) 0 B ∈ W 0 := by
  obtain ⟨c, Y, J, rfl, hY, rfl, hJ⟩ := hA
  have hM := Jk3G_mid hJ
  have hbase : ∀ (t : ℕ) (A : TrioSeq), Aok A → PkG E (c + 1 + t) A →
      A ++ shiftr01 t 0 ([((c + 2, 3, 0) : ℕ × ℕ × ℕ)] ++ J) ∈ W 0 := by
    intro t A _ hA
    rw [shiftr01_append0, shift_col]
    exact hJ.2.2 t A hA
  have hclose : ∀ (t : ℕ) (A' C' : TrioSeq), Aok A' → PkG E (c + 1 + t) A' → Mono C' →
      (∀ (t' : ℕ) (A'' : TrioSeq), Aok A'' → PkG E (c + 1 + t') A'' →
        A'' ++ BlkD (c + 3 + t') (shiftr01 t' 0 ([((c + 2, 3, 0) : ℕ × ℕ × ℕ)] ++ J)) C'
          ∈ W 0) →
      PkG E (c + 1 + t) (A' ++ BlkD (c + 3 + t)
        (shiftr01 t 0 ([((c + 2, 3, 0) : ℕ × ℕ × ℕ)] ++ J)) C') := by
    intro t A' C' _ hA' hmoC' hIH
    exact PkG_absorb hE hM hmoC' hIH t A' hA'
  have hkey := blkD_memS (d := c + 3) (by omega) _ hM hbase hclose B hB.mem
    hB.zroot hB.mono hB.root 0 Y (PkG_Aok hE hY) (by simpa using hY)
  simp only [shiftr01_zero, Nat.add_zero] at hkey
  rw [BlkD_app] at hkey
  rwa [show c + 2 + 1 = c + 3 from by omega]

theorem Pk3_close {E : ℕ → TrioSeq → Prop} (h : ℕ) (A Blk : TrioSeq) (hA : Pk3 E h A)
    (hcol : ∀ x ∈ Blk, h + 1 ≤ x.1) (hmo : Mono Blk)
    (hre : ∀ (t : ℕ) (A' : TrioSeq), Pk3 E (h + t) A' → A' ++ shiftr01 t 0 Blk ∈ W 0) :
    Pk3 E h (A ++ Blk) := by
  obtain ⟨c, Y, J, rfl, hY, rfl, hJ⟩ := hA
  refine ⟨c, Y, J ++ Blk, rfl, hY, by simp [List.append_assoc], ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hJ.1 x h
    · have := hcol x h; omega
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hJ.2.1 x h
    · exact hmo x h
  · intro t Y' hY'
    rw [shiftr01_append0, ← List.append_assoc, ← List.append_assoc]
    have hA' : Pk3 E (c + 2 + t) (Y' ++ ([((c + 2 + t, 3, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J)) :=
      ⟨c + t, Y', shiftr01 t 0 J, by omega,
        by rwa [show c + t + 1 = c + 1 + t from by omega],
        by rw [show c + t + 2 = c + 2 + t from by omega], Jk3G_shift hJ t⟩
    have h := hre t _ hA'
    simpa only [List.append_assoc] using h

theorem BaseOk_Pk3 {E : ℕ → TrioSeq → Prop} (hE : BaseOk E) : BaseOk (Pk3 E) where
  aok := Pk3_aok hE
  ancd := Pk3_ancd hE
  hang := Pk3_hang hE
  close := Pk3_close

#print axioms BaseOk_Pk3

/-! ### 界面の継承 `Iface E → Iface (Pk3 E)`、層 `Lay n`、そして `R294(4,3,0)` -/

theorem Vis2_high {bd : ℕ} {N : TrioSeq}
    (h : ∀ t, 1 ≤ t → t < N.length → bd ≤ entry N 0 t) : Vis2 bd N := by
  intro t ht1 htl hlt _
  have := h t ht1 htl
  omega

theorem Vis2_append {bd : ℕ} {M N : TrioSeq} (hNlen : 0 < N.length)
    (hM : Vis2 (entry N 0 0) M) (hN0 : 2 ≤ entry N 1 0) (hN : Vis2 bd N) :
    Vis2 bd (M ++ N) := by
  intro t ht1 htl hlt hrec
  have hlen : (M ++ N).length = M.length + N.length := by simp
  have hNh : entry (M ++ N) 0 M.length = entry N 0 0 := by
    rw [show M.length = M.length + 0 from rfl, entry_append_right]
  rcases Nat.lt_trichotomy t M.length with hh | hh | hh
  · rw [entry_append_left hh] at hlt ⊢
    have hlt' : entry M 0 t < entry N 0 0 := by
      have := hrec M.length hh (by omega)
      rw [entry_append_left hh, hNh] at this
      exact this
    refine hM t ht1 hh hlt' ?_
    intro i hti hiM
    have := hrec i hti (by omega)
    rw [entry_append_left hh, entry_append_left hiM] at this
    exact this
  · subst hh
    rw [show M.length = M.length + 0 from rfl, entry_append_right]
    exact hN0
  · obtain ⟨q, rfl⟩ : ∃ q, t = M.length + q := ⟨t - M.length, by omega⟩
    rw [entry_append_right] at hlt ⊢
    refine hN q (by omega) (by omega) hlt ?_
    intro i hqi hiN
    have := hrec (M.length + i) (by omega) (by omega)
    rw [entry_append_right, entry_append_right] at this
    exact this

/-- ★★ 界面は `Pk3` で継承される。 -/
theorem Iface_Pk3 {E : ℕ → TrioSeq → Prop} (hI : Iface E) : Iface (Pk3 E) where
  bok := BaseOk_Pk3 hI.bok
  rebase := by
    intro h A hA
    obtain ⟨c, Y, J, rfl, hY, rfl, hJ⟩ := hA
    obtain ⟨j, c', X, J', hc, hX, rfl, hJ'⟩ := hY
    have hc' : c = c' := by omega
    subst hc'
    obtain ⟨c0, h0, Y0, U, hh, rfl, hY0, hU⟩ := RunG_to hI j c X hX
    have hlt := RunGU_lt j c0 h0 U hU
    have hUmid := RunGU_mid j c0 h0 U hU
    have hM2 := JkG_mid hJ'
    have hM3 := Jk3G_mid hJ
    refine ⟨c0, Y0, (U ++ ([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J')) ++ ([((c + 2, 3, 0) : ℕ × ℕ × ℕ)] ++ J),
      by simp [List.append_assoc], hY0, ?_, ?_, by omega, ?_, ?_⟩
    · refine MidD_append (MidD_append hUmid ?_ hM2.mono) ?_ hM3.mono
      · intro x hx; have := MidD_col_ge hM2 x hx; omega
      · intro x hx; have := MidD_col_ge hM3 x hx; omega
    · rw [entry_append_left (List.length_pos_iff.mpr (MidD_append hUmid
        (by intro x hx; have := MidD_col_ge hM2 x hx; omega) hM2.mono).ne)]
      rw [entry_append_left (List.length_pos_iff.mpr hUmid.ne)]
      exact RunGU_head1 j c0 h0 U hU
    · refine Vis2_append (by simp) ?_ (by simp [entry]) ?_
      · refine Vis2_append (by simp) ?_ (by simp [entry]) ?_
        · have h1 := RunGU_rec j c0 h0 U hU
          rw [hh]
          simpa [entry, show h0 + j + 1 = h0 + j + 1 from rfl] using h1
        · have hN3 : entry ([((c + 2, 3, 0) : ℕ × ℕ × ℕ)] ++ J) 0 0 = c + 2 := by simp [entry]
          rw [hN3]
          refine Vis2_high ?_
          intro t ht1 htl
          exact hM2.tail t ht1 htl
      · refine Vis2_high ?_
        intro t ht1 htl
        have := hM3.tail t ht1 htl
        omega
    · intro s Y0' hY0'
      rw [shiftr01_append0, shiftr01_append0, shiftr01_append0, shiftr01_append0,
        shift_col, shift_col]
      have hR : RunG E j (h0 + s + j) (Y0' ++ shiftr01 s 0 U) :=
        RunG_of j (c0 + s) (h0 + s) Y0' _ hY0' (RunGU_shift j c0 h0 U hU s)
      have hP : PkG E (c + s + 1) ((Y0' ++ shiftr01 s 0 U) ++
          ([((c + 1 + s, 2, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 s 0 J')) := by
        refine ⟨j, c + s, _, _, rfl, ?_, by rw [show c + s + 1 = c + 1 + s from by omega],
          JkG_shift hJ' s⟩
        rwa [show c + s = h0 + s + j from by omega]
      refine ⟨c + s, (Y0' ++ shiftr01 s 0 U) ++ ([((c + 1 + s, 2, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 s 0 J'),
        shiftr01 s 0 J, by omega, hP, ?_, Jk3G_shift hJ s⟩
      simp only [List.append_assoc]
      rw [show c + s + 2 = c + 2 + s from by omega]

theorem Iface_RunA0 : Iface (RunA 0) where
  bok := BaseOk_RunA 0
  rebase := by
    rintro h A ⟨b, Y0, M, rfl, rfl, hY0, hM⟩
    refine ⟨b, Y0, M, rfl, hY0, hM.mid, hM.head1, by omega, ?_, ?_⟩
    · refine Vis2_high ?_
      intro t ht1 htl
      have := hM.mid.tail t ht1 htl
      omega
    · intro s Y0' hY0'
      exact ⟨b + s, Y0', _, by omega, rfl, hY0', SegA_shift hM s⟩

/-- 層。`Lay 0 = RunA 0`、`Lay (n+1) = Pk3 (Lay n)`。 -/
def Lay : ℕ → ℕ → TrioSeq → Prop
  | 0 => RunA 0
  | (n + 1) => Pk3 (Lay n)

theorem Iface_Lay : ∀ n : ℕ, Iface (Lay n)
  | 0 => Iface_RunA0
  | (n + 1) => Iface_Pk3 (Iface_Lay n)

/-- `(2,2,0)(3,3,0)`。 -/
def N23 : TrioSeq := [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 0) : ℕ × ℕ × ℕ)]

/-- `D1 = (0,0,0)(1,1,1)(1,1,0)`。 -/
def D1 : TrioSeq := Q ++ [((1, 1, 0) : ℕ × ℕ × ℕ)]

theorem D1_RunA0 : RunA 0 1 D1 :=
  ⟨0, Q, _, rfl, rfl, ⟨_, BaseOk_zero, LwB_of_base ⟨(Aok_Q : Aok Q), rfl⟩⟩, SegA_one 0⟩

/-- ★★★ `D1 ++ (2 3)^n` は第 `n` 層の元（レベル `2n+1`）。 -/
theorem Lay_stage : ∀ n : ℕ, Lay n (2 * n + 1) (Mtwd 2 D1 N23 n)
  | 0 => by
      rw [Mtwd_zero]
      exact D1_RunA0
  | (n + 1) => by
      rw [Mtwd_succ]
      have ih := Lay_stage n
      have hI := Iface_Lay n
      have heq : shiftr01 (2 * n) 0 N23
          = [((2 * n + 1 + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ [((2 * n + 1 + 2, 3, 0) : ℕ × ℕ × ℕ)] := by
        simp only [N23, shiftr01, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
          List.cons.injEq, Prod.mk.injEq, Nat.add_zero, and_true, true_and]
        omega
      rw [heq]
      have hP : PkG (Lay n) (2 * n + 1 + 1)
          (Mtwd 2 D1 N23 n ++ ([((2 * n + 1 + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ [])) :=
        ⟨0, 2 * n + 1, _, [], rfl, ih, rfl, JkG_nil hI _⟩
      have h3 : Pk3 (Lay n) (2 * n + 1 + 2)
          ((Mtwd 2 D1 N23 n ++ ([((2 * n + 1 + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ []))
            ++ ([((2 * n + 1 + 2, 3, 0) : ℕ × ℕ × ℕ)] ++ [])) :=
        ⟨2 * n + 1, _, [], rfl, hP, rfl, Jk3G_nil hI.bok _⟩
      show Pk3 (Lay n) (2 * (n + 1) + 1) _
      rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 from by omega]
      simpa only [List.append_assoc, List.append_nil, List.nil_append] using h3

theorem Lay_stage_mem (n : ℕ) : Mtwd 2 D1 N23 n ∈ W 0 :=
  ((Iface_Lay n).bok.aok _ _ (Lay_stage n)).mem

/-- ★★★★ `R294(4,3,0) = (0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,3,0) ∈ W 0`（壁だった行列）。 -/
theorem R294_43 : R294 ++ [((4, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hM : MidD (2 + 1) N23 := by
    refine MidD_append (MidD_col 2 2 (by omega) (by omega)) ?_ ?_
    · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; simp
    · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; simp
  have h := snocYd_mem (Y0 := D1) (M := N23) (L := 2) (y := 3) (dl := 2)
    (by simp [D1, Q]) hM (by simp [N23, entry]) ?_ (by omega) (by omega) Lay_stage_mem
  · simpa [D1, N23, R294, Q] using h
  · intro t ht1 htl _ _
    have : t = 1 := by simp [N23] at htl; omega
    subst this
    simp [N23, entry]

#print axioms R294_43

theorem Mtwd2_D1_eq : ∀ n : ℕ, Mtwd 2 D1 N23 n = D1 ++ (List.range n).flatMap (fun i =>
    [((2 * i + 2, 2, 0) : ℕ × ℕ × ℕ), ((2 * i + 3, 3, 0) : ℕ × ℕ × ℕ)])
  | 0 => by simp [Mtwd_zero]
  | (n + 1) => by
      have heq : shiftr01 (2 * n) 0 N23
          = [((2 * n + 2, 2, 0) : ℕ × ℕ × ℕ), ((2 * n + 3, 3, 0) : ℕ × ℕ × ℕ)] := by
        simp only [N23, shiftr01, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq,
          Nat.add_zero, and_true]
        omega
      rw [Mtwd_succ, Mtwd2_D1_eq n, heq, List.range_succ, List.flatMap_append, List.append_assoc]
      simp

/-- ユーザーの列: `D1 ++ (2 3)^n` は全部 `W 0`。 -/
theorem D1_23pow (n : ℕ) : D1 ++ (List.range n).flatMap (fun i =>
    [((2 * i + 2, 2, 0) : ℕ × ℕ × ℕ), ((2 * i + 3, 3, 0) : ℕ × ℕ × ℕ)]) ∈ W 0 := by
  rw [← Mtwd2_D1_eq]
  exact Lay_stage_mem n

/-! ### 任意の界面台座の上の `(2 3)` の登り、`(2,2,0)(3,3,0)(4,3,0)` の継ぎ足し、`R294(4,3,0)(3,0,0)` -/

/-- 層（台座 `E` 版）。 -/
def LayE (E : ℕ → TrioSeq → Prop) : ℕ → ℕ → TrioSeq → Prop
  | 0 => E
  | (i + 1) => Pk3 (LayE E i)

theorem Iface_LayE {E : ℕ → TrioSeq → Prop} (hI : Iface E) : ∀ i : ℕ, Iface (LayE E i)
  | 0 => hI
  | (i + 1) => Iface_Pk3 (Iface_LayE hI i)

/-- `(c+1,2,0)(c+2,3,0)`。 -/
def N23c (c : ℕ) : TrioSeq := [((c + 1, 2, 0) : ℕ × ℕ × ℕ), ((c + 2, 3, 0) : ℕ × ℕ × ℕ)]

theorem N23c_shift (c v : ℕ) : shiftr01 v 0 (N23c c) = N23c (c + v) := by
  simp only [N23c, shiftr01, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq,
    Nat.add_zero, and_true]
  omega

/-- ★★★ 界面台座の元 `X`（レベル `c`）の上の `(2 3)^k` は第 `k` 層の元（レベル `c+2k`）。 -/
theorem LayE_stage {E : ℕ → TrioSeq → Prop} (hI : Iface E) {c : ℕ} {X : TrioSeq} (hX : E c X) :
    ∀ k : ℕ, LayE E k (c + 2 * k) (Mtwd 2 X (N23c c) k)
  | 0 => by
      rw [Mtwd_zero]
      simpa using hX
  | (k + 1) => by
      rw [Mtwd_succ, N23c_shift]
      have ih := LayE_stage hI hX k
      have hIk := Iface_LayE hI k
      have hP : PkG (LayE E k) (c + 2 * k + 1)
          (Mtwd 2 X (N23c c) k ++ ([((c + 2 * k + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ [])) :=
        ⟨0, c + 2 * k, _, [], rfl, ih, rfl, JkG_nil hIk _⟩
      have h3 : Pk3 (LayE E k) (c + 2 * k + 2)
          ((Mtwd 2 X (N23c c) k ++ ([((c + 2 * k + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ []))
            ++ ([((c + 2 * k + 2, 3, 0) : ℕ × ℕ × ℕ)] ++ [])) :=
        ⟨c + 2 * k, _, [], rfl, hP, rfl, Jk3G_nil hIk.bok _⟩
      show Pk3 (LayE E k) (c + 2 * (k + 1)) _
      rw [show c + 2 * (k + 1) = c + 2 * k + 2 from by omega]
      simpa only [N23c, List.append_assoc, List.append_nil, List.nil_append,
        List.cons_append] using h3

theorem LayE_stage_mem {E : ℕ → TrioSeq → Prop} (hI : Iface E) {c : ℕ} {X : TrioSeq}
    (hX : E c X) (k : ℕ) : Mtwd 2 X (N23c c) k ∈ W 0 :=
  ((Iface_LayE hI k).bok.aok _ _ (LayE_stage hI hX k)).mem

/-- ★★★ 界面台座の元の上に `(2,2,0)(3,3,0)(4,3,0)`（3 の上の 3）を継げる。 -/
theorem Iface_snoc233 {E : ℕ → TrioSeq → Prop} (hI : Iface E) {c : ℕ} {X : TrioSeq}
    (hX : E c X) :
    X ++ [((c + 1, 2, 0) : ℕ × ℕ × ℕ), ((c + 2, 3, 0) : ℕ × ℕ × ℕ), ((c + 3, 3, 0) : ℕ × ℕ × ℕ)]
      ∈ W 0 := by
  have hM : MidD (c + 1 + 1) (N23c c) := by
    refine MidD_append (MidD_col (c + 1) 2 (by omega) (by omega)) ?_ ?_
    · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; simp
    · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; simp
  have h := snocYd_mem (Y0 := X) (M := N23c c) (L := c + 1) (y := 3) (dl := 2)
    (hI.bok.aok _ _ hX).ne hM (by simp [N23c, entry]) ?_ (by omega) (by omega)
    (LayE_stage_mem hI hX)
  · have heq : (X ++ N23c c) ++ [((c + 1 + 2, 3, 0) : ℕ × ℕ × ℕ)]
        = X ++ [((c + 1, 2, 0) : ℕ × ℕ × ℕ), ((c + 2, 3, 0) : ℕ × ℕ × ℕ),
            ((c + 3, 3, 0) : ℕ × ℕ × ℕ)] := by
      simp only [N23c, List.append_assoc, List.cons_append, List.nil_append]
    rwa [heq] at h
  · intro t ht1 htl _ _
    have : t = 1 := by simp [N23c] at htl; omega
    subst this
    simp [N23c, entry]

/-- `(2,2,0)(3,3,0)(4,3,0)`。 -/
def M233 : TrioSeq :=
  [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 0) : ℕ × ℕ × ℕ), ((4, 3, 0) : ℕ × ℕ × ℕ)]

/-- `(1,1,0) ++ M233^m`（平坦に並べた単位）。 -/
def U3 (m : ℕ) : TrioSeq := [((1, 1, 0) : ℕ × ℕ × ℕ)] ++ (List.range m).flatMap (fun _ => M233)

theorem U3_succ (m : ℕ) : U3 (m + 1) = U3 m ++ M233 := by
  simp [U3, List.range_succ, List.flatMap_append, List.append_assoc]

theorem M233_cols : ∀ x ∈ M233, 2 ≤ x.1 := by
  intro x hx
  simp only [M233, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> simp

theorem M233_mono : Mono M233 := by
  intro x hx
  simp only [M233, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> simp

theorem MidD_U3 : ∀ m, MidD 2 (U3 m)
  | 0 => by
      have h := MidD_col 1 1 (by omega) (by omega)
      simpa [U3] using h
  | (m + 1) => by
      rw [U3_succ]
      exact MidD_append (MidD_U3 m) M233_cols M233_mono

/-- ★★★ `(1,1,0)` に `(2,2,0)(3,3,0)(4,3,0)` を `m` 個横に並べたものは絶対セグメント。 -/
theorem SegA_U3 : ∀ m, SegA 0 (U3 m)
  | 0 => by
      have h := SegA_one 0
      simpa [U3] using h
  | (m + 1) => by
      refine ⟨MidD_U3 (m + 1), by simp [U3, entry], ?_⟩
      intro P hP s A' hA'
      have hR0 : RunA 0 (s + 1) (A' ++ shiftr01 s 0 (U3 m)) :=
        ⟨s, A', _, rfl, rfl, ⟨P, hP, by simpa using hA'⟩,
          by simpa using SegA_shift (SegA_U3 m) s⟩
      have h := Iface_snoc233 Iface_RunA0 hR0
      rw [U3_succ, shiftr01_append0, ← List.append_assoc]
      have heq : shiftr01 s 0 M233 = [((s + 1 + 1, 2, 0) : ℕ × ℕ × ℕ),
          ((s + 1 + 2, 3, 0) : ℕ × ℕ × ℕ), ((s + 1 + 3, 3, 0) : ℕ × ℕ × ℕ)] := by
        simp only [M233, shiftr01, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq,
          Nat.add_zero, and_true]
        omega
      rw [heq]
      exact h

theorem Q_U3_mem (m : ℕ) : Q ++ U3 m ∈ W 0 := by
  have h := (SegA_U3 m).reapp _ BaseOk_zero 0 Q (LwB_of_base ⟨(Aok_Q : Aok Q), rfl⟩)
  simpa using h

/-- `R43 = (0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,3,0)`。 -/
def R43 : TrioSeq := R294 ++ [((4, 3, 0) : ℕ × ℕ × ℕ)]
def R43_300 : TrioSeq := R43 ++ [((3, 0, 0) : ℕ × ℕ × ℕ)]

theorem R43_300_len : R43_300.length = 7 := by simp [R43_300, R43, R294]

theorem nextrel0_R43_300 : nextrel0 R43_300 3 6 := by
  refine ⟨by simp [R43_300, R43, R294], by simp [R43_300, R43, R294], by omega,
    by simp [R43_300, R43, R294, entry], ?_⟩
  intro j hj
  rcases j with _ | _ | _ | _ | _ | _ | j
  · omega
  · omega
  · omega
  · omega
  · simp [R43_300, R43, R294, entry]
  · simp [R43_300, R43, R294, entry]
  · omega

theorem hasParent0_R43_300 : hasParent R43_300 0 6 := by
  refine ⟨3, by show nextR R43_300 0 3 6; simp only [nextR, if_true]; exact nextrel0_R43_300, ?_⟩
  intro j0 hj0
  change nextR R43_300 0 j0 6 at hj0
  simp only [nextR, if_true] at hj0
  obtain ⟨hj0l, -, hlt, hlt2, hall⟩ := hj0
  rw [R43_300_len] at hj0l
  rcases j0 with _ | _ | _ | _ | _ | _ | j0
  · exfalso; have := hall 3 ⟨by omega, by omega⟩; simp [R43_300, R43, R294, entry] at this
  · exfalso; have := hall 3 ⟨by omega, by omega⟩; simp [R43_300, R43, R294, entry] at this
  · exfalso; have := hall 3 ⟨by omega, by omega⟩; simp [R43_300, R43, R294, entry] at this
  · rfl
  · exfalso; simp [R43_300, R43, R294, entry] at hlt2
  · exfalso; simp [R43_300, R43, R294, entry] at hlt2
  · omega

theorem parent0_R43_300 : parent R43_300 0 6 = 3 :=
  hasParent0_R43_300.unique (parent_nextR hasParent0_R43_300)
    (by show nextR R43_300 0 3 6; simp only [nextR, if_true]; exact nextrel0_R43_300)

open Classical in
theorem oper_R43_300 (n : ℕ) : R43_300⟦n⟧ = Q ++ U3 n := by
  rw [L53.oper_flat (j1 := 6) (j0 := 3) (by rw [R43_300_len]) (by omega)
    (by simp [R43_300, R43, R294, entry]) (by simp [srow, R43_300, R43, R294, entry])
    hasParent0_R43_300 parent0_R43_300.symm n]
  simp [R43_300, R43, R294, Q, U3, M233, entry, List.range']

/-- ★★★★ `(0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,3,0)(3,0,0) ∈ W 0`。 -/
theorem R43_300_mem : R43_300 ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_R43_300]
  exact Q_U3_mem n

#print axioms R43_300_mem

/-! ### `R43 = R294(4,3,0)` を「`(2,2,0)` + junk `(3,3,0)(4,3,0)`」のブロックと見る: 高さ 3 の列 -/

theorem MidD_M233 : MidD 3 M233 := by
  refine MidD_append (MidD_col 2 2 (by omega) (by omega)) ?_ ?_
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp

/-- `R43 ∈ RunG (RunA 0) 1`（レベル 2）: `D1` の上のブロック `(2,2,0)(3,3,0)(4,3,0)`。 -/
theorem R43_RunG1 : RunG (RunA 0) 1 2 R43 := by
  refine ⟨1, D1, M233, rfl, by simp [R43, R294, D1, Q, M233], D1_RunA0, MidD_M233,
    by simp [M233, entry], ?_⟩
  intro s X hX
  have h := Iface_snoc233 Iface_RunA0 hX
  have heq : shiftr01 s 0 M233 = [((1 + s + 1, 2, 0) : ℕ × ℕ × ℕ),
      ((1 + s + 2, 3, 0) : ℕ × ℕ × ℕ), ((1 + s + 3, 3, 0) : ℕ × ℕ × ℕ)] := by
    simp only [M233, shiftr01, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq,
      Nat.add_zero, and_true]
    omega
  rw [heq]
  exact h

/-- ★★★ `(0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,3,0)(3,1,0) ∈ W 0`。 -/
theorem R43_310 : R43 ++ [((3, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  LvB_snoc (BaseOk_RunG (BaseOk_RunA 0) 1) 0 2 R43 R43_RunG1

/-- ★★★ `(0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,3,0)(3,2,0) ∈ W 0`。 -/
theorem R43_320 : R43 ++ [((3, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  RunG_snoc2 Iface_RunA0 1 2 R43 R43_RunG1

#print axioms R43_310
#print axioms R43_320

/-! ### 界面は `RunG` でも継承される。`R43(3,3,0)` -/

theorem Iface_RunG {E : ℕ → TrioSeq → Prop} (hI : Iface E) (j : ℕ) : Iface (RunG E j) where
  bok := BaseOk_RunG hI.bok j
  rebase := by
    intro h A hA
    obtain ⟨c0, h0, Y0, U, rfl, rfl, hY0, hU⟩ := RunG_to hI j h A hA
    refine ⟨c0, Y0, U, rfl, hY0, RunGU_mid j c0 h0 U hU, RunGU_head1 j c0 h0 U hU,
      by have := RunGU_lt j c0 h0 U hU; omega, RunGU_rec j c0 h0 U hU, ?_⟩
    intro s Y0' hY0'
    have h := RunG_of j (c0 + s) (h0 + s) Y0' _ hY0' (RunGU_shift j c0 h0 U hU s)
    rwa [show h0 + s + j = h0 + j + s from by omega] at h

/-- `(3,3,0)(4,3,0)` は `(2,2,0)` の junk としてどの `RunG (RunA 0) j` の頭にも継げる。 -/
theorem JkG_R43 : JkG (RunA 0) 1 [((3, 3, 0) : ℕ × ℕ × ℕ), ((4, 3, 0) : ℕ × ℕ × ℕ)] := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp
  · intro j t X hX
    have h := Iface_snoc233 (Iface_RunG Iface_RunA0 j) hX
    simpa [shiftr01, show 1 + t + 1 = 1 + 1 + t from by omega,
      show 1 + t + 2 = 3 + t from by omega, show 1 + t + 3 = 4 + t from by omega] using h

/-- ★★★ `(0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,3,0)(3,3,0) ∈ W 0`。 -/
theorem R43_330 : R43 ++ [((3, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := JkG_snoc3 (BaseOk_RunA 0) JkG_R43 (j := 0) D1_RunA0
  simpa [R43, R294, D1, Q] using h

#print axioms R43_330

end Small
end TRIO
