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

/-! ### `(2,2,0)` の junk `(3,3,0)(4,3,0)`（任意の界面台座・レベル）と、`R43(3,3,0)` の塔の第 1 段 -/

theorem JkG_233 {E : ℕ → TrioSeq → Prop} (hI : Iface E) (c : ℕ) :
    JkG E c [((c + 2, 3, 0) : ℕ × ℕ × ℕ), ((c + 3, 3, 0) : ℕ × ℕ × ℕ)] := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp
  · intro j t X hX
    have h := Iface_snoc233 (Iface_RunG hI j) hX
    simpa [shiftr01, show c + t + 1 = c + 1 + t from by omega,
      show c + t + 2 = c + 2 + t from by omega, show c + t + 3 = c + 3 + t from by omega] using h

/-- `D1 (2,2,0)(3,3,0)(4,3,0)(3,3,0)` は `Pk3 (RunA 0)` の元（レベル 3）: `(4,3,0)` は 2 の junk、
最後の `(3,3,0)` が 3 の記録。 -/
theorem R43_330_Pk3 : Pk3 (RunA 0) 3 (R43 ++ [((3, 3, 0) : ℕ × ℕ × ℕ)]) := by
  refine ⟨1, D1 ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++ [((3, 3, 0) : ℕ × ℕ × ℕ), ((4, 3, 0) : ℕ × ℕ × ℕ)]),
    [], rfl, ⟨0, 1, D1, _, rfl, D1_RunA0, rfl, JkG_233 Iface_RunA0 1⟩, ?_,
    Jk3G_nil (BaseOk_RunA 0) 1⟩
  simp [R43, R294, D1, Q]

/-- ★★★ `(0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,3,0)(3,3,0)(4,2,0)(5,3,0)(6,3,0)(5,3,0) ∈ W 0`。 -/
theorem R43_330_stage1 : R43 ++ [((3, 3, 0) : ℕ × ℕ × ℕ), ((4, 2, 0) : ℕ × ℕ × ℕ),
    ((5, 3, 0) : ℕ × ℕ × ℕ), ((6, 3, 0) : ℕ × ℕ × ℕ), ((5, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hX : RunG (Lay 1) 0 3 (R43 ++ [((3, 3, 0) : ℕ × ℕ × ℕ)]) := R43_330_Pk3
  have h := JkG_snoc3 (Iface_Lay 1).bok (JkG_233 (Iface_Lay 1) 3) hX
  simpa using h

#print axioms R43_330_stage1

/-! ### 単位 `(c+1,2,0)(c+2,3,0)(c+3,3,0)(c+2,3,0)` の登り: `R43(3,3,0)(4,3,0)` -/

/-- `(c+1,2,0)(c+2,3,0)(c+3,3,0)(c+2,3,0)`: 2 のブロック（junk `(3)(3)`）+ 平坦な 3 の記録。 -/
def U4 (c : ℕ) : TrioSeq :=
  [((c + 1, 2, 0) : ℕ × ℕ × ℕ), ((c + 2, 3, 0) : ℕ × ℕ × ℕ), ((c + 3, 3, 0) : ℕ × ℕ × ℕ),
    ((c + 2, 3, 0) : ℕ × ℕ × ℕ)]

theorem U4_shift (c v : ℕ) : shiftr01 v 0 (U4 c) = U4 (c + v) := by
  simp only [U4, shiftr01, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq,
    Nat.add_zero, and_true]
  omega

/-- 界面台座の元 `X`（レベル `c`）の上の `U4` 1 個は第 1 層の元（レベル `c+2`）。 -/
theorem Pk3_U4 {E : ℕ → TrioSeq → Prop} (hI : Iface E) {c : ℕ} {X : TrioSeq} (hX : E c X) :
    Pk3 E (c + 2) (X ++ U4 c) := by
  refine ⟨c, X ++ ([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ [((c + 2, 3, 0) : ℕ × ℕ × ℕ),
      ((c + 3, 3, 0) : ℕ × ℕ × ℕ)]), [], rfl,
    ⟨0, c, X, _, rfl, hX, rfl, JkG_233 hI c⟩, ?_, Jk3G_nil hI.bok c⟩
  simp [U4]

/-- ★★★ `X ++ U4^k` は第 `k` 層の元（レベル `c + 2k`）。単位は層を登るが、junk の条件が普遍なので通る。 -/
theorem LayE_stage4 {E : ℕ → TrioSeq → Prop} (hI : Iface E) {c : ℕ} {X : TrioSeq} (hX : E c X) :
    ∀ k : ℕ, LayE E k (c + 2 * k) (Mtwd 2 X (U4 c) k)
  | 0 => by
      rw [Mtwd_zero]
      simpa using hX
  | (k + 1) => by
      rw [Mtwd_succ, U4_shift]
      have ih := LayE_stage4 hI hX k
      have h := Pk3_U4 (Iface_LayE hI k) ih
      show Pk3 (LayE E k) (c + 2 * (k + 1)) _
      rwa [show c + 2 * (k + 1) = c + 2 * k + 2 from by omega]

theorem LayE_stage4_mem {E : ℕ → TrioSeq → Prop} (hI : Iface E) {c : ℕ} {X : TrioSeq}
    (hX : E c X) (k : ℕ) : Mtwd 2 X (U4 c) k ∈ W 0 :=
  ((Iface_LayE hI k).bok.aok _ _ (LayE_stage4 hI hX k)).mem

/-- ★★★★ `(0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,3,0)(3,3,0)(4,3,0) ∈ W 0`。 -/
theorem R43_330_430 : R43 ++ [((3, 3, 0) : ℕ × ℕ × ℕ), ((4, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hM : MidD (2 + 1) (U4 1) := by
    refine MidD_append (MidD_col 2 2 (by omega) (by omega)) ?_ ?_
    · intro x hx; simp only [U4, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp
    · intro x hx; simp only [U4, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp
  have h := snocYd_mem (Y0 := D1) (M := U4 1) (L := 2) (y := 3) (dl := 2)
    (by simp [D1, Q]) hM (by simp [U4, entry]) ?_ (by omega) (by omega)
    (LayE_stage4_mem Iface_RunA0 D1_RunA0)
  · simpa [D1, U4, R43, R294, Q] using h
  · intro t ht1 htl hlt hrec
    simp only [U4, List.length_cons, List.length_nil] at htl
    rcases (by omega : t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl
    · exfalso
      have := hrec 3 (by omega) (by simp [U4])
      simp [U4, entry] at this
    · exfalso
      simp [U4, entry] at hlt
    · simp [U4, entry]

#print axioms R43_330_430

/-- ユーザーの行列（塔の第 3 段）。 -/
theorem R43_330_stage3 : R43 ++ [((3, 3, 0) : ℕ × ℕ × ℕ), ((4, 2, 0) : ℕ × ℕ × ℕ),
    ((5, 3, 0) : ℕ × ℕ × ℕ), ((6, 3, 0) : ℕ × ℕ × ℕ), ((5, 3, 0) : ℕ × ℕ × ℕ),
    ((6, 2, 0) : ℕ × ℕ × ℕ), ((7, 3, 0) : ℕ × ℕ × ℕ), ((8, 3, 0) : ℕ × ℕ × ℕ),
    ((7, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := LayE_stage4_mem Iface_RunA0 D1_RunA0 3
  simpa [Mtwd, U4, D1, R43, R294, Q, shiftr01] using h

/-! ### 普遍な junk つきの 2 のブロックの上の「3 の上に 3」、`R294(4,3,0)(4,0,0)` -/

/-- 2 のブロック（junk `J`、普遍）+ 3 の記録 `(c+2,3,0)` は `Pk3` の 1 段。 -/
theorem Pk3_UJ {E : ℕ → TrioSeq → Prop} (hI : Iface E) {c : ℕ} {X J : TrioSeq} (hX : E c X)
    (hJ : JkG E c J) :
    Pk3 E (c + 2) ((X ++ ([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J)) ++ [((c + 2, 3, 0) : ℕ × ℕ × ℕ)]) :=
  ⟨c, X ++ ([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J), [], rfl, ⟨0, c, X, J, rfl, hX, rfl, hJ⟩,
    by simp, Jk3G_nil hI.bok c⟩

/-- 単位 `U = (c+1,2,0) ++ J ++ (c+2,3,0)` を歩幅 2 で積んだ塔。junk `J` はどの界面台座でも通るとする。 -/
theorem LayE_stageUJ {E : ℕ → TrioSeq → Prop} (hI : Iface E) {c : ℕ} {X J : TrioSeq} (hX : E c X)
    (hJ : ∀ (E' : ℕ → TrioSeq → Prop), Iface E' → JkG E' c J) :
    ∀ k : ℕ, LayE E k (c + 2 * k)
      (Mtwd 2 X (([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J) ++ [((c + 2, 3, 0) : ℕ × ℕ × ℕ)]) k)
  | 0 => by
      rw [Mtwd_zero]
      simpa using hX
  | (k + 1) => by
      rw [Mtwd_succ, shiftr01_append0, shiftr01_append0, shift_col, shift_col]
      have ih := LayE_stageUJ hI hX hJ k
      have hIk := Iface_LayE hI k
      have hJk : JkG (LayE E k) (c + 2 * k) (shiftr01 (2 * k) 0 J) := JkG_shift (hJ _ hIk) (2 * k)
      have h := Pk3_UJ hIk ih hJk
      show Pk3 (LayE E k) (c + 2 * (k + 1)) _
      rw [show c + 2 * (k + 1) = c + 2 * k + 2 from by omega, show c + 1 + 2 * k = c + 2 * k + 1 from by omega,
        show c + 2 + 2 * k = c + 2 * k + 2 from by omega]
      simpa only [List.append_assoc] using h

theorem LayE_stageUJ_mem {E : ℕ → TrioSeq → Prop} (hI : Iface E) {c : ℕ} {X J : TrioSeq}
    (hX : E c X) (hJ : ∀ (E' : ℕ → TrioSeq → Prop), Iface E' → JkG E' c J) (k : ℕ) :
    Mtwd 2 X (([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J) ++ [((c + 2, 3, 0) : ℕ × ℕ × ℕ)]) k ∈ W 0 :=
  ((Iface_LayE hI k).bok.aok _ _ (LayE_stageUJ hI hX hJ k)).mem

/-- ★★★ 普遍な junk つきの 2 のブロックの上に `(c+2,3,0)(c+3,3,0)`（3 の上に 3）を継げる。 -/
theorem Iface_snocJ33 {E : ℕ → TrioSeq → Prop} (hI : Iface E) {c : ℕ} {X J : TrioSeq} (hX : E c X)
    (hJ : ∀ (E' : ℕ → TrioSeq → Prop), Iface E' → JkG E' c J) :
    ((X ++ ([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J)) ++ [((c + 2, 3, 0) : ℕ × ℕ × ℕ)])
      ++ [((c + 3, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hJE := hJ E hI
  have hM2 : MidD (c + 2) ([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J) := JkG_mid hJE
  have hM : MidD (c + 1 + 1) (([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J) ++ [((c + 2, 3, 0) : ℕ × ℕ × ℕ)]) := by
    rw [show c + 1 + 1 = c + 2 from by omega]
    refine MidD_append hM2 ?_ ?_
    · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; simp
    · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; simp
  have hlen2 : 0 < ([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J).length := by simp
  have h := snocYd_mem (Y0 := X) (M := ([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J) ++ [((c + 2, 3, 0) : ℕ × ℕ × ℕ)])
    (L := c + 1) (y := 3) (dl := 2) (hI.bok.aok _ _ hX).ne hM
    (by rw [entry_append_left hlen2, entry_cons_append_1]; show (2 : ℕ) < 3; omega) ?_
    (by omega) (by omega) (LayE_stageUJ_mem hI hX hJ)
  · rw [show c + 1 + 2 = c + 3 from by omega] at h
    simpa only [List.append_assoc] using h
  · intro t ht1 htl hlt hrec
    set M2 := ([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J) with hM2def
    have hlen : (M2 ++ [((c + 2, 3, 0) : ℕ × ℕ × ℕ)]).length = M2.length + 1 := by simp
    rw [hlen] at htl
    rcases Nat.lt_or_ge t M2.length with hh | hh
    · exfalso
      rw [entry_append_left hh] at hlt
      have h1 := hrec M2.length hh (by omega)
      rw [entry_append_left hh, show M2.length = M2.length + 0 from rfl, entry_append_right] at h1
      have h2 := hM2.tail t ht1 hh
      rw [show entry [((c + 2, 3, 0) : ℕ × ℕ × ℕ)] 0 0 = c + 2 from by simp [entry]] at h1
      omega
    · have : t = M2.length := by omega
      subst this
      rw [show M2.length = M2.length + 0 from rfl, entry_append_right]
      simp [entry]

/-- `(c+2,3,0)(c+3,3,0)` を `n` 組（平坦に並べた junk）。 -/
def J34 (c n : ℕ) : TrioSeq :=
  (List.range n).flatMap (fun _ => [((c + 2, 3, 0) : ℕ × ℕ × ℕ), ((c + 3, 3, 0) : ℕ × ℕ × ℕ)])

theorem J34_succ (c n : ℕ) : J34 c (n + 1) = J34 c n ++ [((c + 2, 3, 0) : ℕ × ℕ × ℕ), ((c + 3, 3, 0) : ℕ × ℕ × ℕ)] := by
  simp [J34, List.range_succ, List.flatMap_append]

theorem J34_shift (c n t : ℕ) : shiftr01 t 0 (J34 c n) = J34 (c + t) n := by
  induction n with
  | zero => simp [J34]
  | succ n ih =>
      rw [J34_succ, J34_succ, shiftr01_append0, ih]
      congr 1
      simp only [shiftr01, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq,
        Nat.add_zero, and_true]
      omega

/-- ★★★ `J34 c n` はどの界面台座でも `(c+1,2,0)` の junk として通る。 -/
theorem JkG_J34 : ∀ (n : ℕ) (E : ℕ → TrioSeq → Prop), Iface E → ∀ c : ℕ, JkG E c (J34 c n)
  | 0, E, hI, c => by simpa [J34] using JkG_nil hI c
  | (n + 1), E, hI, c => by
      rw [J34_succ]
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact (JkG_J34 n E hI c).1 x h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl <;> simp
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact (JkG_J34 n E hI c).2.1 x h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl <;> simp
      · intro j t X hX
        have h := Iface_snocJ33 (Iface_RunG hI j) (c := c + t) (J := J34 (c + t) n) hX
          (fun E' hI' => JkG_J34 n E' hI' (c + t))
        rw [shiftr01_append0, J34_shift]
        have heq : shiftr01 t 0 [((c + 2, 3, 0) : ℕ × ℕ × ℕ), ((c + 3, 3, 0) : ℕ × ℕ × ℕ)]
            = [((c + t + 2, 3, 0) : ℕ × ℕ × ℕ), ((c + t + 3, 3, 0) : ℕ × ℕ × ℕ)] := by
          simp only [shiftr01, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq,
            Nat.add_zero, and_true]
          omega
        rw [heq, show c + 1 + t = c + t + 1 from by omega]
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using h

/-- `R294(4,3,0)(4,0,0)` の各段 `R292 ++ ((3,3,0)(4,3,0))^n ∈ W 0`。 -/
theorem R292_J34_mem (n : ℕ) : D1 ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++ J34 1 n) ∈ W 0 :=
  (PkG_Aok (BaseOk_RunA 0) ⟨0, 1, D1, J34 1 n, rfl, D1_RunA0, rfl,
    JkG_J34 n (RunA 0) Iface_RunA0 1⟩).mem

def R43_400 : TrioSeq := R43 ++ [((4, 0, 0) : ℕ × ℕ × ℕ)]

theorem R43_400_len : R43_400.length = 7 := by simp [R43_400, R43, R294]

theorem nextrel0_R43_400 : nextrel0 R43_400 4 6 := by
  refine ⟨by simp [R43_400, R43, R294], by simp [R43_400, R43, R294], by omega,
    by simp [R43_400, R43, R294, entry], ?_⟩
  intro j hj
  rcases j with _ | _ | _ | _ | _ | _ | j
  · omega
  · omega
  · omega
  · omega
  · omega
  · simp [R43_400, R43, R294, entry]
  · omega

theorem hasParent0_R43_400 : hasParent R43_400 0 6 := by
  refine ⟨4, by show nextR R43_400 0 4 6; simp only [nextR, if_true]; exact nextrel0_R43_400, ?_⟩
  intro j0 hj0
  change nextR R43_400 0 j0 6 at hj0
  simp only [nextR, if_true] at hj0
  obtain ⟨hj0l, -, hlt, hlt2, hall⟩ := hj0
  rw [R43_400_len] at hj0l
  rcases j0 with _ | _ | _ | _ | _ | _ | j0
  · exfalso; have := hall 4 ⟨by omega, by omega⟩; simp [R43_400, R43, R294, entry] at this
  · exfalso; have := hall 4 ⟨by omega, by omega⟩; simp [R43_400, R43, R294, entry] at this
  · exfalso; have := hall 4 ⟨by omega, by omega⟩; simp [R43_400, R43, R294, entry] at this
  · exfalso; have := hall 4 ⟨by omega, by omega⟩; simp [R43_400, R43, R294, entry] at this
  · rfl
  · exfalso; simp [R43_400, R43, R294, entry] at hlt2
  · omega

theorem parent0_R43_400 : parent R43_400 0 6 = 4 :=
  hasParent0_R43_400.unique (parent_nextR hasParent0_R43_400)
    (by show nextR R43_400 0 4 6; simp only [nextR, if_true]; exact nextrel0_R43_400)

open Classical in
theorem oper_R43_400 (n : ℕ) : R43_400⟦n⟧ = D1 ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++ J34 1 n) := by
  rw [L53.oper_flat (j1 := 6) (j0 := 4) (by rw [R43_400_len]) (by omega)
    (by simp [R43_400, R43, R294, entry]) (by simp [srow, R43_400, R43, R294, entry])
    hasParent0_R43_400 parent0_R43_400.symm n]
  simp [R43_400, R43, R294, Q, D1, J34, entry, List.range']

/-- ★★★★ `(0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,3,0)(4,0,0) ∈ W 0`。 -/
theorem R43_400_mem : R43_400 ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_R43_400]
  exact R292_J34_mem n

#print axioms R43_400_mem

/-! ### 普遍な junk つきの `Pk3`（`Pk3U`）: 吊るしの不変量を「どの界面台座でも」に取る。`R294(4,3,0)(4,1,0)` -/

/-- 普遍な junk: どの界面台座の走りの頭にも継げる。 -/
def JkGU (c : ℕ) (J : TrioSeq) : Prop := ∀ (E : ℕ → TrioSeq → Prop), Iface E → JkG E c J

theorem JkGU_nil (c : ℕ) : JkGU c [] := fun _ hI => JkG_nil hI c

theorem JkGU_shift {c : ℕ} {J : TrioSeq} (hJ : JkGU c J) (u : ℕ) : JkGU (c + u) (shiftr01 u 0 J) :=
  fun E hI => JkG_shift (hJ E hI) u

/-- `RunG E j` の頭 ++ `(c+1,2,0)` ++ 普遍な junk。 -/
def PkGU (E : ℕ → TrioSeq → Prop) (h : ℕ) (Y : TrioSeq) : Prop :=
  ∃ (j c : ℕ) (X J : TrioSeq), h = c + 1 ∧ RunG E j c X ∧
    Y = X ++ ([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J) ∧ JkGU c J

/-- 台座を ∃ で潰したもの（吊るしの不変量）。 -/
def PkGA (h : ℕ) (Y : TrioSeq) : Prop := ∃ E : ℕ → TrioSeq → Prop, Iface E ∧ PkGU E h Y

theorem PkGU_toPkG {E : ℕ → TrioSeq → Prop} (hI : Iface E) {h : ℕ} {Y : TrioSeq}
    (hY : PkGU E h Y) : PkG E h Y := by
  obtain ⟨j, c, X, J, hc, hX, rfl, hJ⟩ := hY
  exact ⟨j, c, X, J, hc, hX, rfl, hJ E hI⟩

theorem PkGA_Aok {h : ℕ} {Y : TrioSeq} (hY : PkGA h Y) : Aok Y := by
  obtain ⟨E, hI, hY⟩ := hY
  exact PkG_Aok hI.bok (PkGU_toPkG hI hY)

/-- `blkD_memS` の `hclose`（普遍版）: 吊るした junk を `(c+1,2,0)` の junk に吸収する。 -/
theorem PkGU_absorb {c : ℕ} {M : TrioSeq} (hM : MidD (c + 3) M) {C' : TrioSeq} (hmoC' : Mono C')
    (hIH : ∀ (t : ℕ) (A'' : TrioSeq), Aok A'' → PkGA (c + 1 + t) A'' →
      A'' ++ BlkD (c + 3 + t) (shiftr01 t 0 M) C' ∈ W 0)
    (t : ℕ) (A' : TrioSeq) (hA' : PkGA (c + 1 + t) A') :
    PkGA (c + 1 + t) (A' ++ BlkD (c + 3 + t) (shiftr01 t 0 M) C') := by
  obtain ⟨E, hI, j, c', X, J, hc, hX, rfl, hJ⟩ := hA'
  have hc' : c' = c + t := by omega
  subst hc'
  refine ⟨E, hI, j, c + t, X, J ++ BlkD (c + 3 + t) (shiftr01 t 0 M) C', by omega, hX,
    by simp [List.append_assoc], ?_⟩
  intro E'' hI''
  have hJE := hJ E'' hI''
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hJE.1 x h
    · rcases List.mem_append.mp h with h' | h'
      · have := MidD_col_ge (MidD_shift hM t) x h'
        omega
      · have := shiftD_col x h'
        omega
  · have h1 : Mono (J ++ shiftr01 t 0 M) := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hJE.2.1 x h
      · exact shiftD_mono hM.mono x h
    have h2 := BlkD_mono (d := c + 3 + t) h1 hmoC'
    simpa [BlkD, List.append_assoc] using h2
  · intro j' t' X' hX'
    have hA'' : PkGA (c + 1 + (t + t')) (X' ++ ([((c + t + 1 + t', 2, 0) : ℕ × ℕ × ℕ)]
        ++ shiftr01 t' 0 J)) := by
      refine ⟨E'', hI'', j', c + t + t', X', shiftr01 t' 0 J, by omega, hX',
        by rw [show c + t + t' + 1 = c + t + 1 + t' from by omega], JkGU_shift hJ t'⟩
    have h := hIH (t + t') _ (PkGA_Aok hA'') hA''
    rw [BlkD_shift_eq] at h ⊢
    rw [shiftr01_append0, shiftr01_append0, shiftr01_add0, shiftr01_add0,
      show c + 3 + t + t' = c + 3 + (t + t') from by omega, ← List.append_assoc]
    simpa only [List.append_assoc] using h

/-- `(c+2,3,0)` の後ろの junk（普遍版）: `PkGA` の元の上に継げる。 -/
def Jk3GU (c : ℕ) (J : TrioSeq) : Prop :=
  (∀ x ∈ J, c + 3 ≤ x.1) ∧ Mono J ∧
  ∀ (t : ℕ) (Y : TrioSeq), PkGA (c + 1 + t) Y →
    Y ++ ([((c + 2 + t, 3, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J) ∈ W 0

theorem Jk3GU_nil (c : ℕ) : Jk3GU c [] := by
  refine ⟨by simp, by intro x hx; simp at hx, ?_⟩
  intro t Y hY
  obtain ⟨E, hI, j, c', X, J, hc, hX, rfl, hJ⟩ := hY
  have hc' : c' = c + t := by omega
  subst hc'
  have h := JkG_snoc3 hI.bok (hJ E hI) hX
  simpa [shiftr01, show c + t + 2 = c + 2 + t from by omega] using h

theorem Jk3GU_mid {c : ℕ} {J : TrioSeq} (hJ : Jk3GU c J) :
    MidD (c + 3) ([((c + 2, 3, 0) : ℕ × ℕ × ℕ)] ++ J) := by
  have h := MidD_append (MidD_col (c + 2) 3 (by omega) (by omega))
    (by intro x hx; have := hJ.1 x hx; omega) hJ.2.1
  rwa [show c + 2 + 1 = c + 3 from by omega] at h

/-- `PkGU E` の頭 ++ `(c+2,3,0)` ++ junk。レベル `c+2`。 -/
def Pk3U (E : ℕ → TrioSeq → Prop) (h : ℕ) (A : TrioSeq) : Prop :=
  ∃ (c : ℕ) (Y J : TrioSeq), h = c + 2 ∧ PkGU E (c + 1) Y ∧
    A = Y ++ ([((c + 2, 3, 0) : ℕ × ℕ × ℕ)] ++ J) ∧ Jk3GU c J

theorem Pk3U_aok {E : ℕ → TrioSeq → Prop} (hI : Iface E) (h : ℕ) (A : TrioSeq)
    (hA : Pk3U E h A) : Aok A := by
  obtain ⟨c, Y, J, rfl, hY, rfl, hJ⟩ := hA
  have hmem := hJ.2.2 0 Y (by simpa using (⟨E, hI, hY⟩ : PkGA (c + 1) Y))
  simp only [shiftr01_zero, Nat.add_zero] at hmem
  exact Aok_append_Mid (by omega) (PkG_Aok hI.bok (PkGU_toPkG hI hY)) (Jk3GU_mid hJ) hmem

theorem Pk3U_ancd {E : ℕ → TrioSeq → Prop} (hI : Iface E) (h : ℕ) (A : TrioSeq)
    (hA : Pk3U E h A) : Ancd (h + 1) A := by
  obtain ⟨c, Y, J, rfl, hY, rfl, hJ⟩ := hA
  have hM := Jk3GU_mid hJ
  rw [show c + 3 = c + 2 + 1 from by omega] at hM
  have h1 := PkG_Ancd hI.bok (PkGU_toPkG hI hY)
  rw [show c + 1 + 1 = c + 2 from by omega] at h1
  exact Ancd_append_Mid (PkG_Aok hI.bok (PkGU_toPkG hI hY)).ne h1 hM

/-- ★★★ `Pk3U E` の頭の上（レベル `+1`）に `Bok` を吊るせる。不変量は `PkGA`（どの台座でも）。 -/
theorem Pk3U_hang {E : ℕ → TrioSeq → Prop} (hI : Iface E) (h : ℕ) (A : TrioSeq)
    (hA : Pk3U E h A) (B : TrioSeq) (hB : Bok B) : A ++ shiftr01 (h + 1) 0 B ∈ W 0 := by
  obtain ⟨c, Y, J, rfl, hY, rfl, hJ⟩ := hA
  have hM := Jk3GU_mid hJ
  have hbase : ∀ (t : ℕ) (A : TrioSeq), Aok A → PkGA (c + 1 + t) A →
      A ++ shiftr01 t 0 ([((c + 2, 3, 0) : ℕ × ℕ × ℕ)] ++ J) ∈ W 0 := by
    intro t A _ hA
    rw [shiftr01_append0, shift_col]
    exact hJ.2.2 t A hA
  have hclose : ∀ (t : ℕ) (A' C' : TrioSeq), Aok A' → PkGA (c + 1 + t) A' → Mono C' →
      (∀ (t' : ℕ) (A'' : TrioSeq), Aok A'' → PkGA (c + 1 + t') A'' →
        A'' ++ BlkD (c + 3 + t') (shiftr01 t' 0 ([((c + 2, 3, 0) : ℕ × ℕ × ℕ)] ++ J)) C'
          ∈ W 0) →
      PkGA (c + 1 + t) (A' ++ BlkD (c + 3 + t)
        (shiftr01 t 0 ([((c + 2, 3, 0) : ℕ × ℕ × ℕ)] ++ J)) C') := by
    intro t A' C' _ hA' hmoC' hIH
    exact PkGU_absorb hM hmoC' hIH t A' hA'
  have hkey := blkD_memS (d := c + 3) (by omega) _ hM hbase hclose B hB.mem
    hB.zroot hB.mono hB.root 0 Y (PkGA_Aok ⟨E, hI, hY⟩)
    (by simpa using (⟨E, hI, hY⟩ : PkGA (c + 1) Y))
  simp only [shiftr01_zero, Nat.add_zero] at hkey
  rw [BlkD_app] at hkey
  rwa [show c + 2 + 1 = c + 3 from by omega]

/-- `R43 = D1 (2,2,0)(3,3,0)(4,3,0) ∈ Pk3U (RunA 0)`（レベル 3。`(4,3,0)` は 3 の junk）。 -/
theorem R43_Pk3U : Pk3U (RunA 0) 3 R43 := by
  refine ⟨1, D1 ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++ []), [((4, 3, 0) : ℕ × ℕ × ℕ)], rfl,
    ⟨0, 1, D1, [], rfl, D1_RunA0, rfl, JkGU_nil 1⟩, by simp [R43, R294, D1, Q], ?_, ?_, ?_⟩
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; simp
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; simp
  · intro t Y hY
    obtain ⟨E, hI, j, c', X, J, hc, hX, rfl, hJ⟩ := hY
    have hc' : c' = 1 + t := by omega
    subst hc'
    have h := Iface_snocJ33 (Iface_RunG hI j) hX (fun E' hI' => hJ E' hI')
    simpa [shiftr01, List.append_assoc, show 1 + t + 2 = 3 + t from by omega,
      show 1 + t + 3 = 4 + t from by omega] using h

theorem R43_Aok : Aok R43 := Pk3U_aok Iface_RunA0 3 R43 R43_Pk3U

/-- ★★★ `R43` の上（高さ 4）に `Bok` を吊るせる。 -/
theorem R43_hang (B : TrioSeq) (hB : Bok B) : R43 ++ shiftr01 4 0 B ∈ W 0 :=
  Pk3U_hang Iface_RunA0 3 R43 R43_Pk3U B hB

/-- ユーザーの行列 `R43 ++ R43↑4`。 -/
theorem R43_R43 : R43 ++ shiftr01 4 0 R43 ∈ W 0 :=
  R43_hang R43 ⟨R43_Aok.mem, R43_Aok.zroot, R43_Aok.mono, by simp [R43, R294, entry]⟩

theorem R43_tw : ∀ n, TwD 4 R43 n ∈ W 0
  | 0 => by simpa [TwD] using W_nil 0
  | (n + 1) => by
      rw [TwD_succ]
      exact R43_hang (TwD 4 R43 n)
        ⟨R43_tw n, TwD_zroot (by omega) R43_Aok.zroot n, TwD_mono R43_Aok.mono n,
          TwD_root R43_Aok.ne R43_Aok.deep.1 n⟩

/-- ★★★★ `(0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,3,0)(4,1,0) ∈ W 0`。 -/
theorem R43_410 : R43 ++ [((4, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  snocd_mem (by omega) R43_Aok.ne R43_Aok.deep R43_Aok.zroot
    (Pk3U_ancd Iface_RunA0 3 R43 R43_Pk3U) R43_tw

#print axioms R43_410
#print axioms R43_R43

/-! ### `Pk3A`（台座を ∃ で潰した `Pk3U`）は `BaseOk`。`R294(4,3,0)(4,2,0)` -/

def Pk3A (h : ℕ) (A : TrioSeq) : Prop := ∃ E : ℕ → TrioSeq → Prop, Iface E ∧ Pk3U E h A

theorem Pk3A_close (h : ℕ) (A Blk : TrioSeq) (hA : Pk3A h A)
    (hcol : ∀ x ∈ Blk, h + 1 ≤ x.1) (hmo : Mono Blk)
    (hre : ∀ (t : ℕ) (A' : TrioSeq), Pk3A (h + t) A' → A' ++ shiftr01 t 0 Blk ∈ W 0) :
    Pk3A h (A ++ Blk) := by
  obtain ⟨E, hI, c, Y, J, rfl, hY, rfl, hJ⟩ := hA
  refine ⟨E, hI, c, Y, J ++ Blk, rfl, hY, by simp [List.append_assoc], ?_, ?_, ?_⟩
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
    obtain ⟨E', hI', hY'⟩ := hY'
    have hA' : Pk3A (c + 2 + t) (Y' ++ ([((c + 2 + t, 3, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J)) :=
      ⟨E', hI', c + t, Y', shiftr01 t 0 J, by omega,
        by rwa [show c + t + 1 = c + 1 + t from by omega],
        by rw [show c + t + 2 = c + 2 + t from by omega], ?_⟩
    · have h := hre t _ hA'
      simpa only [List.append_assoc] using h
    · refine ⟨?_, shiftD_mono hJ.2.1, ?_⟩
      · intro x hx
        simp only [shiftr01, List.mem_map] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        have := hJ.1 p hp
        dsimp only
        omega
      · intro t' Y'' hY''
        rw [shiftr01_add0]
        have h := hJ.2.2 (t + t') Y'' (by rwa [show c + 1 + (t + t') = c + t + 1 + t' from by omega])
        rwa [show c + t + 2 + t' = c + 2 + (t + t') from by omega]

theorem BaseOk_Pk3A : BaseOk Pk3A where
  aok := fun h A ⟨E, hI, hA⟩ => Pk3U_aok hI h A hA
  ancd := fun h A ⟨E, hI, hA⟩ => Pk3U_ancd hI h A hA
  hang := fun h A ⟨E, hI, hA⟩ => Pk3U_hang hI h A hA
  close := Pk3A_close

/-- `(c+3,3,0)` は `(c+2,3,0)` の普遍な junk（3 の上に 3）。 -/
theorem Jk3GU_one (c : ℕ) : Jk3GU c [((c + 3, 3, 0) : ℕ × ℕ × ℕ)] := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; simp
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; simp
  · intro t Y hY
    obtain ⟨E, hI, j, c', X, J, hc, hX, rfl, hJ⟩ := hY
    have hc' : c' = c + t := by omega
    subst hc'
    have h := Iface_snocJ33 (Iface_RunG hI j) hX (fun E' hI' => hJ E' hI')
    simpa [shiftr01, List.append_assoc, show c + t + 2 = c + 2 + t from by omega,
      show c + t + 3 = c + 3 + t from by omega] using h

/-- 梯子の頭 `Y`（レベル `h`）の上に `(1)(2)(3)(3)` を継ぐと `Pk3U (RunA 0)` の元（レベル `h+3`）。 -/
theorem Pk3U_step {h : ℕ} {Y : TrioSeq} (hL : LwA h Y) :
    Pk3U (RunA 0) (h + 3) (Y ++ [((h + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 0) : ℕ × ℕ × ℕ),
      ((h + 3, 3, 0) : ℕ × ℕ × ℕ), ((h + 4, 3, 0) : ℕ × ℕ × ℕ)]) := by
  have hR0 : RunA 0 (h + 1) (Y ++ [((h + 1, 1, 0) : ℕ × ℕ × ℕ)]) :=
    ⟨h, _, _, rfl, rfl, hL, SegA_one h⟩
  have hP : PkGU (RunA 0) (h + 1 + 1) ((Y ++ [((h + 1, 1, 0) : ℕ × ℕ × ℕ)])
      ++ ([((h + 1 + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ [])) :=
    ⟨0, h + 1, _, [], rfl, hR0, rfl, JkGU_nil _⟩
  have h3 : Pk3U (RunA 0) (h + 1 + 2) (((Y ++ [((h + 1, 1, 0) : ℕ × ℕ × ℕ)])
      ++ ([((h + 1 + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ []))
      ++ ([((h + 1 + 2, 3, 0) : ℕ × ℕ × ℕ)] ++ [((h + 1 + 3, 3, 0) : ℕ × ℕ × ℕ)])) :=
    ⟨h + 1, _, _, rfl, hP, rfl, Jk3GU_one (h + 1)⟩
  rw [show h + 3 = h + 1 + 2 from by omega]
  simpa [List.append_assoc, show h + 1 + 1 = h + 2 from by omega,
    show h + 1 + 2 = h + 3 from by omega, show h + 1 + 3 = h + 4 from by omega] using h3

/-- `(1,1,0)(2,2,0)(3,3,0)(4,3,0)`。 -/
def M1233 : TrioSeq :=
  [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 0) : ℕ × ℕ × ℕ), ((4, 3, 0) : ℕ × ℕ × ℕ)]

theorem M1233_shift (v : ℕ) : shiftr01 v 0 M1233 = [((v + 1, 1, 0) : ℕ × ℕ × ℕ),
    ((v + 2, 2, 0) : ℕ × ℕ × ℕ), ((v + 3, 3, 0) : ℕ × ℕ × ℕ), ((v + 4, 3, 0) : ℕ × ℕ × ℕ)] := by
  simp only [M1233, shiftr01, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq,
    Nat.add_zero, and_true]
  omega

/-- `R43(4,2,0)` の塔の段（歩幅 3）は全部 `Pk3U (RunA 0)` の元。 -/
theorem R43_420_stage : ∀ n : ℕ, Pk3U (RunA 0) (3 * n + 3) (Mtwd 3 Q M1233 (n + 1))
  | 0 => by
      rw [Mtwd_one]
      have h := Pk3U_step (h := 0) ⟨_, BaseOk_zero, LwB_of_base ⟨(Aok_Q : Aok Q), rfl⟩⟩
      simpa [M1233] using h
  | (n + 1) => by
      rw [Mtwd_succ, M1233_shift]
      have ih := R43_420_stage n
      have hL : LwA (3 * n + 3) (Mtwd 3 Q M1233 (n + 1)) :=
        ⟨Pk3A, BaseOk_Pk3A, LwB_of_base ⟨RunA 0, Iface_RunA0, ih⟩⟩
      have h := Pk3U_step hL
      rw [show 3 * (n + 1) + 3 = 3 * n + 3 + 3 from by omega,
        show 3 * (n + 1) = 3 * n + 3 from by omega]
      exact h

theorem R43_420_tw (n : ℕ) : Mtwd 3 Q M1233 n ∈ W 0 := by
  cases n with
  | zero => rw [Mtwd_zero]; exact Aok_Q.mem
  | succ n => exact (Pk3U_aok Iface_RunA0 _ _ (R43_420_stage n)).mem

/-- ★★★★ `(0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,3,0)(4,2,0) ∈ W 0`。 -/
theorem R43_420 : R43 ++ [((4, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hM : MidD (1 + 1) M1233 := by
    refine MidD_append (MidD_col 1 1 (by omega) (by omega)) ?_ ?_
    · intro x hx; simp only [M1233, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp
    · intro x hx; simp only [M1233, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp
  have h := snocYd_mem (Y0 := Q) (M := M1233) (L := 1) (y := 2) (dl := 3)
    (by simp [Q]) hM (by simp [M1233, entry]) ?_ (by omega) (by omega) R43_420_tw
  · simpa [Q, M1233, R43, R294] using h
  · intro t ht1 htl hlt _
    simp only [M1233, List.length_cons, List.length_nil] at htl
    rcases (by omega : t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl
    · simp [M1233, entry]
    · simp [M1233, entry]
    · exfalso; simp [M1233, entry] at hlt

#print axioms R43_420

/-! ### 3 の記録の階層 `Lk k`（`(c+1,2,0)` の上に 3 を `k` 本積む）: 行295 へ -/

theorem PkGA_Ancd {h : ℕ} {Y : TrioSeq} (hY : PkGA h Y) : Ancd (h + 1) Y := by
  obtain ⟨E, hI, hY⟩ := hY
  exact PkG_Ancd hI.bok (PkGU_toPkG hI hY)

theorem PkGA_hang (h : ℕ) (A : TrioSeq) (hA : PkGA h A) (B : TrioSeq) (hB : Bok B) :
    A ++ shiftr01 (h + 1) 0 B ∈ W 0 := by
  obtain ⟨E, hI, j, c, X, J, rfl, hX, rfl, hJ⟩ := hA
  have h1 : RunG E (j + 1) (c + 1) (X ++ ([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J)) :=
    JkG_blk (hJ E hI) hX
  exact (BaseOk_RunG hI.bok (j + 1)).hang _ _ h1 B hB

theorem PkGA_close (h : ℕ) (A Blk : TrioSeq) (hA : PkGA h A)
    (hcol : ∀ x ∈ Blk, h + 1 ≤ x.1) (hmo : Mono Blk)
    (hre : ∀ (t : ℕ) (A' : TrioSeq), PkGA (h + t) A' → A' ++ shiftr01 t 0 Blk ∈ W 0) :
    PkGA h (A ++ Blk) := by
  obtain ⟨E, hI, j, c, X, J, rfl, hX, rfl, hJ⟩ := hA
  refine ⟨E, hI, j, c, X, J ++ Blk, rfl, hX, by simp [List.append_assoc], ?_⟩
  intro E'' hI''
  have hJE := hJ E'' hI''
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hJE.1 x h
    · have := hcol x h; omega
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hJE.2.1 x h
    · exact hmo x h
  · intro j' t X' hX'
    rw [shiftr01_append0, ← List.append_assoc, ← List.append_assoc]
    have hA' : PkGA (c + 1 + t) (X' ++ ([((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J)) :=
      ⟨E'', hI'', j', c + t, X', shiftr01 t 0 J, by omega, hX',
        by rw [show c + t + 1 = c + 1 + t from by omega], JkGU_shift hJ t⟩
    have h := hre t _ hA'
    simpa only [List.append_assoc] using h

theorem BaseOk_PkGA : BaseOk PkGA where
  aok := fun _ _ hA => PkGA_Aok hA
  ancd := fun _ _ hA => PkGA_Ancd hA
  hang := PkGA_hang
  close := PkGA_close

theorem Iface_PkGA : Iface PkGA where
  bok := BaseOk_PkGA
  rebase := by
    intro h A hA
    obtain ⟨E, hI, j, c, X, J, rfl, hX, rfl, hJ⟩ := hA
    obtain ⟨c0, h0, Y0, U, hh, rfl, hY0, hU⟩ := RunG_to hI j c X hX
    have hlt := RunGU_lt j c0 h0 U hU
    have hUmid := RunGU_mid j c0 h0 U hU
    have hM2 := JkG_mid (hJ E hI)
    refine ⟨c0, Y0, U ++ ([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J), by simp [List.append_assoc], hY0,
      ?_, ?_, by omega, ?_, ?_⟩
    · refine MidD_append hUmid ?_ hM2.mono
      intro x hx; have := MidD_col_ge hM2 x hx; omega
    · rw [entry_append_left (List.length_pos_iff.mpr hUmid.ne)]
      exact RunGU_head1 j c0 h0 U hU
    · have e : entry ([((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J) 0 0 = c + 1 := by simp [entry]
      refine Vis2_append (by simp) ?_ (by simp [entry]) ?_
      · rw [e, hh]
        exact RunGU_rec j c0 h0 U hU
      · refine Vis2_high ?_
        intro t ht1 htl
        have := hM2.tail t ht1 htl
        omega
    · intro s Y0' hY0'
      rw [shiftr01_append0, shiftr01_append0, shift_col, ← List.append_assoc]
      have hR : RunG E j (h0 + s + j) (Y0' ++ shiftr01 s 0 U) :=
        RunG_of j (c0 + s) (h0 + s) Y0' _ hY0' (RunGU_shift j c0 h0 U hU s)
      refine ⟨E, hI, j, c + s, Y0' ++ shiftr01 s 0 U, shiftr01 s 0 J, by omega, ?_,
        by rw [show c + s + 1 = c + 1 + s from by omega], JkGU_shift hJ s⟩
      rwa [show c + s = h0 + s + j from by omega]

/-- `Lk 0 = PkGA`、`Lk (k+1) = Lk k の元 ++ (3 + junk)`。レベルは頂上の記録の高さ。 -/
def Lk : ℕ → ℕ → TrioSeq → Prop
  | 0 => PkGA
  | (k + 1) => fun h A => ∃ (c : ℕ) (Y J : TrioSeq), h = c + 1 ∧ Lk k c Y ∧
      A = Y ++ ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J) ∧ (∀ x ∈ J, c + 2 ≤ x.1) ∧ Mono J ∧
      (∀ (t : ℕ) (Y' : TrioSeq), Lk k (c + t) Y' →
        Y' ++ ([((c + 1 + t, 3, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J) ∈ W 0)

/-- `Lk (k+1)` の記録 `(c+1,3,0)` の junk の条件。 -/
def JkL (k c : ℕ) (J : TrioSeq) : Prop :=
  (∀ x ∈ J, c + 2 ≤ x.1) ∧ Mono J ∧
  ∀ (t : ℕ) (Y' : TrioSeq), Lk k (c + t) Y' →
    Y' ++ ([((c + 1 + t, 3, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J) ∈ W 0

theorem Lk_succ_iff (k h : ℕ) (A : TrioSeq) : Lk (k + 1) h A ↔
    ∃ (c : ℕ) (Y J : TrioSeq), h = c + 1 ∧ Lk k c Y ∧
      A = Y ++ ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J) ∧ JkL k c J := Iff.rfl

theorem JkL_shift {k c : ℕ} {J : TrioSeq} (hJ : JkL k c J) (u : ℕ) :
    JkL k (c + u) (shiftr01 u 0 J) := by
  refine ⟨?_, shiftD_mono hJ.2.1, ?_⟩
  · intro x hx
    simp only [shiftr01, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have := hJ.1 p hp
    dsimp only
    omega
  · intro t Y hY
    rw [shiftr01_add0]
    have hY' : Lk k (c + (u + t)) Y := by
      rw [show c + (u + t) = c + u + t from by omega]; exact hY
    have h := hJ.2.2 (u + t) Y hY'
    rw [show c + u + 1 + t = c + 1 + (u + t) from by omega]
    exact h

theorem JkL_mid {k c : ℕ} {J : TrioSeq} (hJ : JkL k c J) :
    MidD (c + 2) ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J) := by
  have h := MidD_append (MidD_col (c + 1) 3 (by omega) (by omega))
    (by intro x hx; have := hJ.1 x hx; omega) hJ.2.1
  rwa [show c + 1 + 1 = c + 2 from by omega] at h

theorem BaseOk_Lk : ∀ k : ℕ, BaseOk (Lk k)
  | 0 => BaseOk_PkGA
  | (k + 1) => by
      have hIHk := BaseOk_Lk k
      refine ⟨?_, ?_, ?_, ?_⟩
      · rintro h A ⟨c, Y, J, rfl, hY, rfl, hJ⟩
        have hJ' : JkL k c J := hJ
        have hmem := hJ'.2.2 0 Y (by simpa using hY)
        simp only [shiftr01_zero, Nat.add_zero] at hmem
        exact Aok_append_Mid (by omega) (hIHk.aok c Y hY) (JkL_mid hJ') hmem
      · rintro h A ⟨c, Y, J, rfl, hY, rfl, hJ⟩
        have hJ' : JkL k c J := hJ
        exact Ancd_append_Mid (hIHk.aok c Y hY).ne (hIHk.ancd c Y hY) (JkL_mid hJ')
      · rintro h A ⟨c, Y, J, rfl, hY, rfl, hJ⟩ B hB
        have hJ' : JkL k c J := hJ
        have hM := JkL_mid hJ'
        have hbase : ∀ (t : ℕ) (A : TrioSeq), Aok A → Lk k (c + t) A →
            A ++ shiftr01 t 0 ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J) ∈ W 0 := by
          intro t A _ hA
          rw [shiftr01_append0, shift_col]
          exact hJ'.2.2 t A hA
        have hclose : ∀ (t : ℕ) (A' C' : TrioSeq), Aok A' → Lk k (c + t) A' → Mono C' →
            (∀ (t' : ℕ) (A'' : TrioSeq), Aok A'' → Lk k (c + t') A'' →
              A'' ++ BlkD (c + 2 + t') (shiftr01 t' 0 ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J)) C'
                ∈ W 0) →
            Lk k (c + t) (A' ++ BlkD (c + 2 + t)
              (shiftr01 t 0 ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J)) C') := by
          intro t A' C' _ hA' hmoC' hIH
          have hNs : MidD (c + 2 + t) (shiftr01 t 0 ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J)) :=
            MidD_shift hM t
          refine hIHk.close (c + t) A' _ hA' ?_ (BlkD_mono hNs.mono hmoC') ?_
          · intro x hx
            rcases List.mem_append.mp hx with hh | hh
            · have := MidD_col_ge hNs x hh; omega
            · have := shiftD_col x hh; omega
          · intro t' Z hZ
            have heq : shiftr01 t' 0 (BlkD (c + 2 + t)
                (shiftr01 t 0 ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J)) C')
                = BlkD (c + 2 + (t + t')) (shiftr01 (t + t') 0
                    ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J)) C' := by
              simp only [BlkD, shiftr01_append0, shiftr01_add0]
              congr 2
              omega
            rw [heq]
            have hZ' : Lk k (c + (t + t')) Z := by
              rwa [show c + (t + t') = c + t + t' from by omega]
            exact hIH (t + t') Z (hIHk.aok _ _ hZ') hZ'
        have hkey := blkD_memS (d := c + 2) (by omega) _ hM hbase hclose B hB.mem
          hB.zroot hB.mono hB.root 0 Y (hIHk.aok c Y hY) (by simpa using hY)
        simp only [shiftr01_zero, Nat.add_zero] at hkey
        rw [BlkD_app] at hkey
        rwa [show c + 1 + 1 = c + 2 from by omega]
      · rintro h A Blk ⟨c, Y, J, rfl, hY, rfl, hJ⟩ hcol hmo hcl
        have hJ' : JkL k c J := hJ
        refine ⟨c, Y, J ++ Blk, rfl, hY, by simp [List.append_assoc], ?_, ?_, ?_⟩
        · intro x hx
          rcases List.mem_append.mp hx with hh | hh
          · exact hJ'.1 x hh
          · have := hcol x hh; omega
        · intro x hx
          rcases List.mem_append.mp hx with hh | hh
          · exact hJ'.2.1 x hh
          · exact hmo x hh
        · intro t Y' hY'
          rw [shiftr01_append0, ← List.append_assoc, ← List.append_assoc]
          have hstep : Lk (k + 1) (c + 1 + t)
              (Y' ++ ([((c + 1 + t, 3, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J)) :=
            ⟨c + t, Y', shiftr01 t 0 J, by omega, hY',
              by rw [show c + t + 1 = c + 1 + t from by omega], JkL_shift hJ' t⟩
          have h := hcl t _ hstep
          simpa only [List.append_assoc] using h

theorem Iface_Lk : ∀ k : ℕ, Iface (Lk k)
  | 0 => Iface_PkGA
  | (k + 1) => by
      have hIk := Iface_Lk k
      refine ⟨BaseOk_Lk (k + 1), ?_⟩
      rintro h A ⟨c, Y, J, rfl, hY, rfl, hJ⟩
      have hJ' : JkL k c J := hJ
      obtain ⟨b, Y0, M, rfl, hY0, hM, hM1, hlt, hvis, hre⟩ := hIk.rebase c Y hY
      have hM3 := JkL_mid hJ'
      refine ⟨b, Y0, M ++ ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J), by simp [List.append_assoc],
        hY0, ?_, ?_, by omega, ?_, ?_⟩
      · refine MidD_append hM ?_ hM3.mono
        intro x hx; have := MidD_col_ge hM3 x hx; omega
      · rw [entry_append_left (List.length_pos_iff.mpr hM.ne)]
        exact hM1
      · have e : entry ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J) 0 0 = c + 1 := by simp [entry]
        refine Vis2_append (by simp) ?_ (by simp [entry]) ?_
        · rw [e]; exact hvis
        · refine Vis2_high ?_
          intro t ht1 htl
          have := hM3.tail t ht1 htl
          omega
      · intro s Y0' hY0'
        rw [shiftr01_append0, shiftr01_append0, shift_col, ← List.append_assoc]
        exact ⟨c + s, Y0' ++ shiftr01 s 0 M, shiftr01 s 0 J, by omega, hre s Y0' hY0',
          by rw [show c + s + 1 = c + 1 + s from by omega], JkL_shift hJ' s⟩

#print axioms Iface_Lk

/-! ### `Lk k` の単位と塔、`Lk_snoc3`（3 の記録の上にさらに 3）、行295 -/

/-- `Vis2` の 3 版。 -/
def Vis3 (bd : ℕ) (M : TrioSeq) : Prop :=
  ∀ t, 1 ≤ t → t < M.length → entry M 0 t < bd →
    (∀ i, t < i → i < M.length → entry M 0 t < entry M 0 i) → 3 ≤ entry M 1 t

theorem Vis3_high {bd : ℕ} {N : TrioSeq}
    (h : ∀ t, 1 ≤ t → t < N.length → bd ≤ entry N 0 t) : Vis3 bd N := by
  intro t ht1 htl hlt _
  have := h t ht1 htl
  omega

theorem Vis3_append {bd : ℕ} {M N : TrioSeq} (hNlen : 0 < N.length)
    (hM : Vis3 (entry N 0 0) M) (hN0 : 3 ≤ entry N 1 0) (hN : Vis3 bd N) :
    Vis3 bd (M ++ N) := by
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

/-- 単位: `(c+1,2,0)` + 普遍 junk、その上に 3 の記録 `k` 本（junk つき）。 -/
def UnitL : ℕ → ℕ → TrioSeq → Prop
  | 0, c, U => ∃ J : TrioSeq, U = [((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J ∧ JkGU c J
  | (k + 1), c, U => ∃ U0 J : TrioSeq, U = U0 ++ ([((c + k + 2, 3, 0) : ℕ × ℕ × ℕ)] ++ J) ∧
      UnitL k c U0 ∧ JkL k (c + k + 1) J

theorem UnitL_mid : ∀ (k c : ℕ) (U : TrioSeq), UnitL k c U → MidD (c + 2) U
  | 0, c, U, hU => by
      obtain ⟨J, rfl, hJ⟩ := hU
      exact JkG_mid (hJ (RunA 0) Iface_RunA0)
  | (k + 1), c, U, hU => by
      obtain ⟨U0, J, rfl, hU0, hJ⟩ := hU
      have hM := JkL_mid hJ
      refine MidD_append (UnitL_mid k c U0 hU0) ?_ hM.mono
      intro x hx; have := MidD_col_ge hM x hx; omega

theorem UnitL_head : ∀ (k c : ℕ) (U : TrioSeq), UnitL k c U → entry U 1 0 = 2
  | 0, c, U, hU => by
      obtain ⟨J, rfl, _⟩ := hU
      rw [entry_cons_append_1]
  | (k + 1), c, U, hU => by
      obtain ⟨U0, J, rfl, hU0, _⟩ := hU
      rw [entry_append_left (List.length_pos_iff.mpr (UnitL_mid k c U0 hU0).ne)]
      exact UnitL_head k c U0 hU0

theorem UnitL_vis : ∀ (k c : ℕ) (U : TrioSeq), UnitL k c U → Vis3 (c + k + 2) U
  | 0, c, U, hU => by
      obtain ⟨J, rfl, hJ⟩ := hU
      have hM := JkG_mid (hJ (RunA 0) Iface_RunA0)
      refine Vis3_high ?_
      intro t ht1 htl
      have := hM.tail t ht1 htl
      omega
  | (k + 1), c, U, hU => by
      obtain ⟨U0, J, rfl, hU0, hJ⟩ := hU
      have hM := JkL_mid hJ
      have e : entry ([((c + k + 2, 3, 0) : ℕ × ℕ × ℕ)] ++ J) 0 0 = c + k + 2 := by simp [entry]
      refine Vis3_append (by simp) ?_ (by simp [entry]) ?_
      · rw [e]; exact UnitL_vis k c U0 hU0
      · refine Vis3_high ?_
        intro t ht1 htl
        have := hM.tail t ht1 htl
        omega

theorem UnitL_shift : ∀ (k c : ℕ) (U : TrioSeq), UnitL k c U → ∀ v : ℕ,
    UnitL k (c + v) (shiftr01 v 0 U)
  | 0, c, U, hU, v => by
      obtain ⟨J, rfl, hJ⟩ := hU
      refine ⟨shiftr01 v 0 J, ?_, JkGU_shift hJ v⟩
      rw [shiftr01_append0, shift_col, show c + 1 + v = c + v + 1 from by omega]
  | (k + 1), c, U, hU, v => by
      obtain ⟨U0, J, rfl, hU0, hJ⟩ := hU
      refine ⟨shiftr01 v 0 U0, shiftr01 v 0 J, ?_, UnitL_shift k c U0 hU0 v, ?_⟩
      · rw [shiftr01_append0, shiftr01_append0, shift_col,
          show c + k + 2 + v = c + v + k + 2 from by omega]
      · have h := JkL_shift hJ v
        rwa [show c + k + 1 + v = c + v + k + 1 from by omega] at h

theorem Lk_of {E : ℕ → TrioSeq → Prop} (hI : Iface E) : ∀ (k j c : ℕ) (X U : TrioSeq),
    RunG E j c X → UnitL k c U → Lk k (c + k + 1) (X ++ U)
  | 0, j, c, X, U, hX, hU => by
      obtain ⟨J, rfl, hJ⟩ := hU
      show PkGA (c + 0 + 1) _
      exact ⟨E, hI, j, c, X, J, by omega, hX, rfl, hJ⟩
  | (k + 1), j, c, X, U, hX, hU => by
      obtain ⟨U0, J, rfl, hU0, hJ⟩ := hU
      refine ⟨c + k + 1, X ++ U0, J, by omega, Lk_of hI k j c X U0 hX hU0,
        by simp [List.append_assoc], ?_⟩
      exact hJ

theorem Lk_to : ∀ (k h : ℕ) (A : TrioSeq), Lk k h A →
    ∃ E : ℕ → TrioSeq → Prop, Iface E ∧ ∃ (j c : ℕ) (X U : TrioSeq),
      h = c + k + 1 ∧ A = X ++ U ∧ RunG E j c X ∧ UnitL k c U
  | 0, h, A, hA => by
      obtain ⟨E, hI, j, c, X, J, rfl, hX, rfl, hJ⟩ := hA
      exact ⟨E, hI, j, c, X, _, by omega, rfl, hX, ⟨J, rfl, hJ⟩⟩
  | (k + 1), h, A, hA => by
      obtain ⟨c', Y, J, rfl, hY, rfl, hJ⟩ := hA
      have hJ' : JkL k c' J := hJ
      obtain ⟨E, hI, j, c, X, U0, hc', rfl, hX, hU0⟩ := Lk_to k c' Y hY
      subst hc'
      refine ⟨E, hI, j, c, X, U0 ++ ([((c + k + 1 + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J), by omega,
        by simp [List.append_assoc], hX, ⟨U0, J, ?_, hU0, hJ'⟩⟩
      rw [show c + k + 2 = c + k + 1 + 1 from by omega]

/-- ★★★ 単位の塔（歩幅 `k+1`）。段が上がっても `Lk k` のまま。 -/
theorem Lk_tower {E : ℕ → TrioSeq → Prop} (hI : Iface E) {k j c : ℕ} {X U : TrioSeq}
    (hX : RunG E j c X) (hU : UnitL k c U) :
    ∀ n : ℕ, Lk k (c + k + 1 + n * (k + 1)) (Mtwd (k + 1) X U (n + 1))
  | 0 => by
      rw [Mtwd_one]
      simpa using Lk_of hI k j c X U hX hU
  | (n + 1) => by
      rw [Mtwd_succ]
      have ih := Lk_tower hI hX hU n
      have hIk := Iface_Lk k
      have hUs : UnitL k (c + k + 1 + n * (k + 1)) (shiftr01 ((k + 1) * (n + 1)) 0 U) := by
        have h := UnitL_shift k c U hU ((k + 1) * (n + 1))
        rwa [show c + (k + 1) * (n + 1) = c + k + 1 + n * (k + 1) from by
          rw [Nat.mul_succ, Nat.mul_comm (k + 1) n]; omega] at h
      have h := Lk_of hIk k 0 _ _ _ ih hUs
      rwa [show c + k + 1 + n * (k + 1) + k + 1 = c + k + 1 + (n + 1) * (k + 1) from by
        rw [Nat.succ_mul]; omega] at h

theorem Lk_tower_mem {E : ℕ → TrioSeq → Prop} (hI : Iface E) {k j c : ℕ} {X U : TrioSeq}
    (hX : RunG E j c X) (hU : UnitL k c U) : ∀ n : ℕ, Mtwd (k + 1) X U n ∈ W 0
  | 0 => by rw [Mtwd_zero]; exact ((BaseOk_RunG hI.bok j).aok _ _ hX).mem
  | (n + 1) => ((BaseOk_Lk k).aok _ _ (Lk_tower hI hX hU n)).mem

/-- ★★★★ `Lk k` の元の頂上に `(·,3,0)` をもう 1 本継げる（3 の上に 3、`k` 本目）。 -/
theorem Lk_snoc3 {k h : ℕ} {A : TrioSeq} (hA : Lk k h A) : A ++ [((h + 1, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  obtain ⟨E, hI, j, c, X, U, rfl, rfl, hX, hU⟩ := Lk_to k h A hA
  have hne : X ≠ [] := ((BaseOk_RunG hI.bok j).aok _ _ hX).ne
  have hMe : entry U 1 0 < 3 := by rw [UnitL_head k c U hU]; omega
  have h := snocYd_mem (Y0 := X) (M := U) (L := c + 1) (y := 3) (dl := k + 1) hne
    (by rw [show c + 1 + 1 = c + 2 from by omega]; exact UnitL_mid k c U hU) hMe
    (by rw [show c + 1 + (k + 1) = c + k + 2 from by omega]; exact UnitL_vis k c U hU)
    (by omega) (by omega) (Lk_tower_mem hI hX hU)
  rwa [show c + 1 + (k + 1) = c + k + 1 + 1 from by omega] at h

theorem JkL_nil (k c : ℕ) : JkL k c [] := by
  refine ⟨by simp, by intro x hx; simp at hx, ?_⟩
  intro t Y hY
  have h := Lk_snoc3 hY
  simpa [shiftr01, show c + t + 1 = c + 1 + t from by omega] using h

/-- `Tn n = (0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,3,0)…(n+2,3,0)`（3 が `n` 本）。 -/
def Tn : ℕ → TrioSeq
  | 0 => D1 ++ [((2, 2, 0) : ℕ × ℕ × ℕ)]
  | (n + 1) => Tn n ++ [((n + 3, 3, 0) : ℕ × ℕ × ℕ)]

theorem Lk_Tn : ∀ n : ℕ, Lk n (n + 2) (Tn n)
  | 0 => by
      show PkGA (0 + 2) (D1 ++ [((2, 2, 0) : ℕ × ℕ × ℕ)])
      exact ⟨RunA 0, Iface_RunA0, 0, 1, D1, [], by omega, D1_RunA0, by simp, JkGU_nil 1⟩
  | (n + 1) => by
      refine ⟨n + 2, Tn n, [], by omega, Lk_Tn n, ?_, JkL_nil n (n + 2)⟩
      simp [Tn]

theorem Tn_mem (n : ℕ) : Tn n ∈ W 0 := ((BaseOk_Lk n).aok _ _ (Lk_Tn n)).mem

theorem Mtw_Tn : ∀ n : ℕ, Mtw (Tn 0) [((3, 3, 0) : ℕ × ℕ × ℕ)] n = Tn n
  | 0 => by rw [Mtw_zero]
  | (n + 1) => by
      rw [Mtw_succ, Mtw_Tn n, shift_col]
      simp [Tn, show 3 + n = n + 3 from by omega]

/-- `R295 = (0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,4,0)`（シート行295、`psi(W_w + psi_1(W_4))`）。 -/
def R295 : TrioSeq := R294 ++ [((4, 4, 0) : ℕ × ℕ × ℕ)]

/-- ★★★★★ シート行295 `(0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,4,0) ∈ W 0`。 -/
theorem R295_mem : R295 ∈ W 0 := by
  have h := snocY_mem (Y0 := Tn 0) (M := [((3, 3, 0) : ℕ × ℕ × ℕ)]) (L := 3) (y := 4)
    (by simp [Tn, D1, Q]) (MidD_col 3 3 (by omega) (by omega)) (by simp [entry]) (by omega)
    (fun n => by rw [Mtw_Tn]; exact Tn_mem n)
  simpa [Tn, D1, Q, R295, R294] using h

#print axioms R295_mem

/-! ### 記録の階層を値で一般化: `StkF B y k`（台座 `B` の上に値 `y+1` の記録を `k` 本） -/

def StkF (B : ℕ → TrioSeq → Prop) (y : ℕ) : ℕ → ℕ → TrioSeq → Prop
  | 0 => B
  | (k + 1) => fun h A => ∃ (c : ℕ) (Y J : TrioSeq), h = c + 1 ∧ StkF B y k c Y ∧
      A = Y ++ ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J) ∧ (∀ x ∈ J, c + 2 ≤ x.1) ∧ Mono J ∧
      (∀ (t : ℕ) (Y' : TrioSeq), StkF B y k (c + t) Y' →
        Y' ++ ([((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J) ∈ W 0)

/-- `StkF B y (k+1)` の記録の junk の条件。 -/
def JkS (B : ℕ → TrioSeq → Prop) (y k c : ℕ) (J : TrioSeq) : Prop :=
  (∀ x ∈ J, c + 2 ≤ x.1) ∧ Mono J ∧
  ∀ (t : ℕ) (Y' : TrioSeq), StkF B y k (c + t) Y' →
    Y' ++ ([((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J) ∈ W 0

theorem Lk_eq_StkF : ∀ k, Lk k = StkF PkGA 2 k
  | 0 => rfl
  | (k + 1) => by
      show (fun h A => ∃ (c : ℕ) (Y J : TrioSeq), h = c + 1 ∧ Lk k c Y ∧ _) = _
      rw [Lk_eq_StkF k]
      rfl

theorem JkS_shift {B : ℕ → TrioSeq → Prop} {y k c : ℕ} {J : TrioSeq} (hJ : JkS B y k c J) (u : ℕ) :
    JkS B y k (c + u) (shiftr01 u 0 J) := by
  refine ⟨?_, shiftD_mono hJ.2.1, ?_⟩
  · intro x hx
    simp only [shiftr01, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have := hJ.1 p hp
    dsimp only
    omega
  · intro t Y hY
    rw [shiftr01_add0]
    have hY' : StkF B y k (c + (u + t)) Y := by
      rw [show c + (u + t) = c + u + t from by omega]; exact hY
    have h := hJ.2.2 (u + t) Y hY'
    rw [show c + u + 1 + t = c + 1 + (u + t) from by omega]
    exact h

theorem JkS_mid {B : ℕ → TrioSeq → Prop} {y k c : ℕ} {J : TrioSeq} (hy : 1 ≤ y)
    (hJ : JkS B y k c J) : MidD (c + 2) ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J) := by
  have h := MidD_append (MidD_col (c + 1) (y + 1) (by omega) (by omega))
    (by intro x hx; have := hJ.1 x hx; omega) hJ.2.1
  rwa [show c + 1 + 1 = c + 2 from by omega] at h

theorem BaseOk_StkF {B : ℕ → TrioSeq → Prop} (hB : BaseOk B) {y : ℕ} (hy : 1 ≤ y) :
    ∀ k : ℕ, BaseOk (StkF B y k)
  | 0 => hB
  | (k + 1) => by
      have hIHk := BaseOk_StkF hB hy k
      refine ⟨?_, ?_, ?_, ?_⟩
      · rintro h A ⟨c, Y, J, rfl, hY, rfl, hJ⟩
        have hJ' : JkS B y k c J := hJ
        have hmem := hJ'.2.2 0 Y (by simpa using hY)
        simp only [shiftr01_zero, Nat.add_zero] at hmem
        exact Aok_append_Mid (by omega) (hIHk.aok c Y hY) (JkS_mid hy hJ') hmem
      · rintro h A ⟨c, Y, J, rfl, hY, rfl, hJ⟩
        have hJ' : JkS B y k c J := hJ
        exact Ancd_append_Mid (hIHk.aok c Y hY).ne (hIHk.ancd c Y hY) (JkS_mid hy hJ')
      · rintro h A ⟨c, Y, J, rfl, hY, rfl, hJ⟩ Bk hBk
        have hJ' : JkS B y k c J := hJ
        have hM := JkS_mid hy hJ'
        have hbase : ∀ (t : ℕ) (A : TrioSeq), Aok A → StkF B y k (c + t) A →
            A ++ shiftr01 t 0 ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J) ∈ W 0 := by
          intro t A _ hA
          rw [shiftr01_append0, shift_col]
          exact hJ'.2.2 t A hA
        have hclose : ∀ (t : ℕ) (A' C' : TrioSeq), Aok A' → StkF B y k (c + t) A' → Mono C' →
            (∀ (t' : ℕ) (A'' : TrioSeq), Aok A'' → StkF B y k (c + t') A'' →
              A'' ++ BlkD (c + 2 + t') (shiftr01 t' 0 ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J)) C'
                ∈ W 0) →
            StkF B y k (c + t) (A' ++ BlkD (c + 2 + t)
              (shiftr01 t 0 ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J)) C') := by
          intro t A' C' _ hA' hmoC' hIH
          have hNs : MidD (c + 2 + t) (shiftr01 t 0 ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J)) :=
            MidD_shift hM t
          refine hIHk.close (c + t) A' _ hA' ?_ (BlkD_mono hNs.mono hmoC') ?_
          · intro x hx
            rcases List.mem_append.mp hx with hh | hh
            · have := MidD_col_ge hNs x hh; omega
            · have := shiftD_col x hh; omega
          · intro t' Z hZ
            have heq : shiftr01 t' 0 (BlkD (c + 2 + t)
                (shiftr01 t 0 ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J)) C')
                = BlkD (c + 2 + (t + t')) (shiftr01 (t + t') 0
                    ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J)) C' := by
              simp only [BlkD, shiftr01_append0, shiftr01_add0]
              congr 2
              omega
            rw [heq]
            have hZ' : StkF B y k (c + (t + t')) Z := by
              rwa [show c + (t + t') = c + t + t' from by omega]
            exact hIH (t + t') Z (hIHk.aok _ _ hZ') hZ'
        have hkey := blkD_memS (d := c + 2) (by omega) _ hM hbase hclose Bk hBk.mem
          hBk.zroot hBk.mono hBk.root 0 Y (hIHk.aok c Y hY) (by simpa using hY)
        simp only [shiftr01_zero, Nat.add_zero] at hkey
        rw [BlkD_app] at hkey
        rwa [show c + 1 + 1 = c + 2 from by omega]
      · rintro h A Blk ⟨c, Y, J, rfl, hY, rfl, hJ⟩ hcol hmo hcl
        have hJ' : JkS B y k c J := hJ
        refine ⟨c, Y, J ++ Blk, rfl, hY, by simp [List.append_assoc], ?_, ?_, ?_⟩
        · intro x hx
          rcases List.mem_append.mp hx with hh | hh
          · exact hJ'.1 x hh
          · have := hcol x hh; omega
        · intro x hx
          rcases List.mem_append.mp hx with hh | hh
          · exact hJ'.2.1 x hh
          · exact hmo x hh
        · intro t Y' hY'
          rw [shiftr01_append0, ← List.append_assoc, ← List.append_assoc]
          have hstep : StkF B y (k + 1) (c + 1 + t)
              (Y' ++ ([((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J)) :=
            ⟨c + t, Y', shiftr01 t 0 J, by omega, hY',
              by rw [show c + t + 1 = c + 1 + t from by omega], JkS_shift hJ' t⟩
          have h := hcl t _ hstep
          simpa only [List.append_assoc] using h

theorem Iface_StkF {B : ℕ → TrioSeq → Prop} (hB : Iface B) {y : ℕ} (hy : 1 ≤ y) :
    ∀ k : ℕ, Iface (StkF B y k)
  | 0 => hB
  | (k + 1) => by
      have hIk := Iface_StkF hB hy k
      refine ⟨BaseOk_StkF hB.bok hy (k + 1), ?_⟩
      rintro h A ⟨c, Y, J, rfl, hY, rfl, hJ⟩
      have hJ' : JkS B y k c J := hJ
      obtain ⟨b, Y0, M, rfl, hY0, hM, hM1, hlt, hvis, hre⟩ := hIk.rebase c Y hY
      have hM3 := JkS_mid hy hJ'
      refine ⟨b, Y0, M ++ ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J), by simp [List.append_assoc],
        hY0, ?_, ?_, by omega, ?_, ?_⟩
      · refine MidD_append hM ?_ hM3.mono
        intro x hx; have := MidD_col_ge hM3 x hx; omega
      · rw [entry_append_left (List.length_pos_iff.mpr hM.ne)]
        exact hM1
      · have e : entry ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J) 0 0 = c + 1 := by simp [entry]
        refine Vis2_append (by simp) ?_ (by simp [entry]; omega) ?_
        · rw [e]; exact hvis
        · refine Vis2_high ?_
          intro t ht1 htl
          have := hM3.tail t ht1 htl
          omega
      · intro s Y0' hY0'
        rw [shiftr01_append0, shiftr01_append0, shift_col, ← List.append_assoc]
        exact ⟨c + s, Y0' ++ shiftr01 s 0 M, shiftr01 s 0 J, by omega, hre s Y0' hY0',
          by rw [show c + s + 1 = c + 1 + s from by omega], JkS_shift hJ' s⟩

#print axioms Iface_StkF


/-! ### 記録の積の和 `Stk B y := ∃ i, StkF B y i` と、3 の snoc のための界面 `Ifc3` -/

def Stk (B : ℕ → TrioSeq → Prop) (y : ℕ) (h : ℕ) (A : TrioSeq) : Prop := ∃ i, StkF B y i h A

theorem BaseOk_Stk {B : ℕ → TrioSeq → Prop} (hB : BaseOk B) {y : ℕ} (hy : 1 ≤ y) :
    BaseOk (Stk B y) where
  aok := fun h A ⟨i, hA⟩ => (BaseOk_StkF hB hy i).aok h A hA
  ancd := fun h A ⟨i, hA⟩ => (BaseOk_StkF hB hy i).ancd h A hA
  hang := fun h A ⟨i, hA⟩ => (BaseOk_StkF hB hy i).hang h A hA
  close := fun h A Blk ⟨i, hA⟩ hcol hmo hcl =>
    ⟨i, (BaseOk_StkF hB hy i).close h A Blk hA hcol hmo (fun t A' hA' => hcl t A' ⟨i, hA'⟩)⟩

theorem Iface_Stk {B : ℕ → TrioSeq → Prop} (hB : Iface B) {y : ℕ} (hy : 1 ≤ y) :
    Iface (Stk B y) where
  bok := BaseOk_Stk hB.bok hy
  rebase := by
    rintro h A ⟨i, hA⟩
    obtain ⟨b, Y0, M, rfl, hY0, hM, hM1, hlt, hvis, hre⟩ := (Iface_StkF hB hy i).rebase h A hA
    exact ⟨b, Y0, M, rfl, hY0, hM, hM1, hlt, hvis, fun s Y0' hY0' => ⟨i, hre s Y0' hY0'⟩⟩

/-- 3 の snoc のための界面: `E` の元は「任意の Iface 台座の上の走り `X`」++「単位 `U`」で、
`U` の頭は `(c+1,2,0)`、見える列は row1 ≥ 3、そして任意の走り `X'` の上に `U` を置き直しても `E`。 -/
structure Ifc3 (E : ℕ → TrioSeq → Prop) : Prop where
  ifc : Iface E
  reb : ∀ (h : ℕ) (A : TrioSeq), E h A → ∃ (c : ℕ) (X U : TrioSeq),
    A = X ++ U ∧ (∃ (E' : ℕ → TrioSeq → Prop) (j : ℕ), Iface E' ∧ RunG E' j c X) ∧
    MidD (c + 2) U ∧ entry U 1 0 = 2 ∧ c < h ∧ Vis3 (h + 1) U ∧
    (∀ (s : ℕ) (E'' : ℕ → TrioSeq → Prop) (j'' : ℕ) (X' : TrioSeq), Iface E'' →
      RunG E'' j'' (c + s) X' → E (h + s) (X' ++ shiftr01 s 0 U))

theorem Ifc3_tower {E : ℕ → TrioSeq → Prop} (hE : Ifc3 E) {h c : ℕ} {X U : TrioSeq}
    (hX : ∃ (E' : ℕ → TrioSeq → Prop) (j : ℕ), Iface E' ∧ RunG E' j c X)
    (hre : ∀ (s : ℕ) (E'' : ℕ → TrioSeq → Prop) (j'' : ℕ) (X' : TrioSeq), Iface E'' →
      RunG E'' j'' (c + s) X' → E (h + s) (X' ++ shiftr01 s 0 U)) (hlt : c < h) :
    ∀ n : ℕ, E (h + n * (h - c)) (Mtwd (h - c) X U (n + 1))
  | 0 => by
      rw [Mtwd_one]
      obtain ⟨E', j, hI', hX'⟩ := hX
      have := hre 0 E' j X hI' (by simpa using hX')
      simpa using this
  | (n + 1) => by
      rw [Mtwd_succ]
      have ih := Ifc3_tower hE hX hre hlt n
      have h1 := hre ((h - c) * (n + 1)) E 0 _ hE.ifc
        (by
          show E (c + (h - c) * (n + 1)) (Mtwd (h - c) X U (n + 1))
          rwa [show c + (h - c) * (n + 1) = h + n * (h - c) from by
            rw [Nat.mul_succ, Nat.mul_comm (h - c) n]; omega])
      rwa [show h + (h - c) * (n + 1) = h + (n + 1) * (h - c) from by
        rw [Nat.mul_comm (h - c) (n + 1)]] at h1

theorem Ifc3_tower_mem {E : ℕ → TrioSeq → Prop} (hE : Ifc3 E) {h c : ℕ} {X U : TrioSeq}
    (hX : ∃ (E' : ℕ → TrioSeq → Prop) (j : ℕ), Iface E' ∧ RunG E' j c X)
    (hre : ∀ (s : ℕ) (E'' : ℕ → TrioSeq → Prop) (j'' : ℕ) (X' : TrioSeq), Iface E'' →
      RunG E'' j'' (c + s) X' → E (h + s) (X' ++ shiftr01 s 0 U)) (hlt : c < h) :
    ∀ n : ℕ, Mtwd (h - c) X U n ∈ W 0
  | 0 => by
      rw [Mtwd_zero]
      obtain ⟨E', j, hI', hX'⟩ := hX
      exact ((BaseOk_RunG hI'.bok j).aok _ _ hX').mem
  | (n + 1) => (hE.ifc.bok.aok _ _ (Ifc3_tower hE hX hre hlt n)).mem

/-- ★★★ `Ifc3` の元の頂上に `(h+1,3,0)`。 -/
theorem Ifc3_snoc3 {E : ℕ → TrioSeq → Prop} (hE : Ifc3 E) {h : ℕ} {A : TrioSeq} (hA : E h A) :
    A ++ [((h + 1, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  obtain ⟨c, X, U, rfl, hX, hU, hU1, hlt, hvis, hre⟩ := hE.reb h A hA
  have hne : X ≠ [] := by
    obtain ⟨E', j, hI', hX'⟩ := hX
    exact ((BaseOk_RunG hI'.bok j).aok _ _ hX').ne
  have h1 := snocYd_mem (Y0 := X) (M := U) (L := c + 1) (y := 3) (dl := h - c) hne
    (by rw [show c + 1 + 1 = c + 2 from by omega]; exact hU) (by rw [hU1]; omega)
    (by rw [show c + 1 + (h - c) = h + 1 from by omega]; exact hvis)
    (by omega) (by omega) (Ifc3_tower_mem hE hX hre hlt)
  rwa [show c + 1 + (h - c) = h + 1 from by omega] at h1

theorem Ifc3_PkGA : Ifc3 PkGA where
  ifc := Iface_PkGA
  reb := by
    intro h A hA
    obtain ⟨E, hI, j, c, X, J, rfl, hX, rfl, hJ⟩ := hA
    have hM2 := JkG_mid (hJ E hI)
    refine ⟨c, X, [((c + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ J, rfl, ⟨E, j, hI, hX⟩, hM2,
      entry_cons_append_1 _ _, by omega, ?_, ?_⟩
    · refine Vis3_high ?_
      intro t ht1 htl
      have := hM2.tail t ht1 htl
      omega
    · intro s E'' j'' X' hI'' hX'
      rw [shiftr01_append0, shift_col]
      exact ⟨E'', hI'', j'', c + s, X', shiftr01 s 0 J, by omega, hX',
        by rw [show c + s + 1 = c + 1 + s from by omega], JkGU_shift hJ s⟩

theorem Ifc3_StkF {B : ℕ → TrioSeq → Prop} (hB : Ifc3 B) {y : ℕ} (hy : 2 ≤ y) :
    ∀ k : ℕ, Ifc3 (StkF B y k)
  | 0 => hB
  | (k + 1) => by
      have hIk := Ifc3_StkF hB hy k
      refine ⟨Iface_StkF hB.ifc (by omega) (k + 1), ?_⟩
      rintro h A ⟨c, Y, J, rfl, hY, rfl, hJ⟩
      have hJ' : JkS B y k c J := hJ
      obtain ⟨c0, X, U, rfl, hX, hU, hU1, hlt, hvis, hre⟩ := hIk.reb c Y hY
      have hM3 := JkS_mid (by omega) hJ'
      refine ⟨c0, X, U ++ ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J), by simp [List.append_assoc],
        hX, ?_, ?_, by omega, ?_, ?_⟩
      · refine MidD_append hU ?_ hM3.mono
        intro x hx; have := MidD_col_ge hM3 x hx; omega
      · rw [entry_append_left (List.length_pos_iff.mpr hU.ne)]
        exact hU1
      · have e : entry ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J) 0 0 = c + 1 := by simp [entry]
        refine Vis3_append (by simp) ?_ (by simp [entry]; omega) ?_
        · rw [e]; exact hvis
        · refine Vis3_high ?_
          intro t ht1 htl
          have := hM3.tail t ht1 htl
          omega
      · intro s E'' j'' X' hI'' hX'
        rw [shiftr01_append0, shiftr01_append0, shift_col, ← List.append_assoc]
        exact ⟨c + s, X' ++ shiftr01 s 0 U, shiftr01 s 0 J, by omega, hre s E'' j'' X' hI'' hX',
          by rw [show c + s + 1 = c + 1 + s from by omega], JkS_shift hJ' s⟩

theorem Ifc3_Stk {B : ℕ → TrioSeq → Prop} (hB : Ifc3 B) {y : ℕ} (hy : 2 ≤ y) :
    Ifc3 (Stk B y) where
  ifc := Iface_Stk hB.ifc (by omega)
  reb := by
    rintro h A ⟨i, hA⟩
    obtain ⟨c0, X, U, rfl, hX, hU, hU1, hlt, hvis, hre⟩ := (Ifc3_StkF hB hy i).reb h A hA
    exact ⟨c0, X, U, rfl, hX, hU, hU1, hlt, hvis,
      fun s E'' j'' X' hI'' hX' => ⟨i, hre s E'' j'' X' hI'' hX'⟩⟩

/-! ### 4 の snoc: 「junk 条件が `Stk C 2` 全体の上」の 3 の記録の頂上に `(h+1,4,0)` -/

/-- 複製 `(3 + J)↑j` を積んだ段は `StkF C 2 (i+n+1)`。 -/
theorem StkF_stage4 {C : ℕ → TrioSeq → Prop} {i c : ℕ} {Z J : TrioSeq}
    (hZ : StkF C 2 i c Z) (hJ : JkS (Stk C 2) 2 0 c J) :
    ∀ n : ℕ, StkF C 2 (i + n + 1) (c + 1 + n)
      (Mtw Z ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J) (n + 1))
  | 0 => by
      rw [Mtw_succ, Mtw_zero, shiftr01_zero]
      exact ⟨c, Z, J, by omega, hZ, rfl, hJ.1, hJ.2.1, fun t Y' hY' => hJ.2.2 t Y' ⟨i, hY'⟩⟩
  | (n + 1) => by
      rw [Mtw_succ]
      have ih := StkF_stage4 hZ hJ n
      have hJs := JkS_shift hJ (n + 1)
      rw [show c + (n + 1) = c + 1 + n from by omega] at hJs
      rw [shiftr01_append0, shift_col]
      refine ⟨c + 1 + n, _, shiftr01 (n + 1) 0 J, by omega, ih,
        by rw [show c + 1 + (n + 1) = c + 1 + n + 1 from by omega], hJs.1, hJs.2.1, ?_⟩
      intro t Y' hY'
      exact hJs.2.2 t Y' ⟨i + n + 1, hY'⟩

/-- ★★★ 4 の snoc。 -/
theorem StkF_snoc4 {C : ℕ → TrioSeq → Prop} (hC : BaseOk C) {h : ℕ} {A : TrioSeq}
    (hA : StkF (Stk C 2) 2 1 h A) : A ++ [((h + 1, 4, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  obtain ⟨c, Z, J, rfl, ⟨i, hZ⟩, rfl, hJ⟩ := hA
  have hJ' : JkS (Stk C 2) 2 0 c J := hJ
  have hZne : Z ≠ [] := ((BaseOk_StkF hC (by omega) i).aok _ _ hZ).ne
  have hM := JkS_mid (by omega) hJ'
  have htw : ∀ n, Mtw Z ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J) n ∈ W 0 := by
    intro n
    cases n with
    | zero => rw [Mtw_zero]; exact ((BaseOk_StkF hC (by omega) i).aok _ _ hZ).mem
    | succ n => exact ((BaseOk_StkF hC (by omega) _).aok _ _ (StkF_stage4 hZ hJ' n)).mem
  have h1 := snocY_mem (Y0 := Z) (M := [((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J) (L := c + 1) (y := 4)
    hZne (by rw [show c + 1 + 1 = c + 2 from by omega]; exact hM) (by simp [entry]) (by omega) htw
  simpa [List.append_assoc] using h1

/-! ### 層 `G C`（3 の上に 4）と `Cm m`、そしてシート行295 の次
`(0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,4,0)(5,4,0)` -/

theorem JkS_nil3 {C : ℕ → TrioSeq → Prop} (hC : Ifc3 C) (c : ℕ) : JkS (Stk C 2) 2 0 c [] := by
  refine ⟨by simp, by intro x hx; simp at hx, ?_⟩
  intro t Y' hY'
  have h := Ifc3_snoc3 (Ifc3_Stk hC (le_refl 2)) hY'
  simpa [shiftr01, show c + t + 1 = c + 1 + t from by omega] using h

theorem JkS_nil4 {C : ℕ → TrioSeq → Prop} (hC : BaseOk C) (c : ℕ) :
    JkS (StkF (Stk C 2) 2 1) 3 0 c [] := by
  refine ⟨by simp, by intro x hx; simp at hx, ?_⟩
  intro t Y' hY'
  have h := StkF_snoc4 hC hY'
  simpa [shiftr01, show c + t + 1 = c + 1 + t from by omega] using h

/-- 層: `C` の元の上に「3（junk 条件は `Stk C 2` の上）」、その上に「4」。 -/
def G (C : ℕ → TrioSeq → Prop) : ℕ → TrioSeq → Prop := StkF (StkF (Stk C 2) 2 1) 3 1

theorem Ifc3_G {C : ℕ → TrioSeq → Prop} (hC : Ifc3 C) : Ifc3 (G C) :=
  Ifc3_StkF (Ifc3_StkF (Ifc3_Stk hC (le_refl 2)) (le_refl 2) 1) (by omega) 1

theorem G_step {C : ℕ → TrioSeq → Prop} (hC : Ifc3 C) {h : ℕ} {A : TrioSeq} (hA : C h A) :
    G C (h + 2) (A ++ ([((h + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ [((h + 2, 4, 0) : ℕ × ℕ × ℕ)])) := by
  refine ⟨h + 1, A ++ ([((h + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ []), [], by omega,
    ⟨h, A, [], rfl, ⟨0, hA⟩, rfl, JkS_nil3 hC h⟩, ?_, JkS_nil4 hC.ifc.bok (h + 1)⟩
  simp [show h + 1 + 1 = h + 2 from by omega]

def Cm : ℕ → ℕ → TrioSeq → Prop
  | 0 => PkGA
  | (m + 1) => G (Cm m)

theorem Ifc3_Cm : ∀ m : ℕ, Ifc3 (Cm m)
  | 0 => Ifc3_PkGA
  | (m + 1) => Ifc3_G (Ifc3_Cm m)

/-- `M34 = (3,3,0)(4,4,0)`。 -/
def M34 : TrioSeq := [((3, 3, 0) : ℕ × ℕ × ℕ)] ++ [((4, 4, 0) : ℕ × ℕ × ℕ)]

/-- 塔の段 `D_2 (3,3,0)(4,4,0) [(5,3,0)(6,4,0)] … ∈ Cm (n+1)`。 -/
theorem M34_stage : ∀ n : ℕ, Cm (n + 1) (2 * n + 4) (Mtwd 2 (Tn 0) M34 (n + 1))
  | 0 => by
      rw [Mtwd_one]
      have h := G_step Ifc3_PkGA (Lk_Tn 0)
      simpa [M34] using h
  | (n + 1) => by
      rw [Mtwd_succ]
      have ih := M34_stage n
      have h := G_step (Ifc3_Cm (n + 1)) ih
      show G (Cm (n + 1)) (2 * (n + 1) + 4) _
      rw [M34, shiftr01_append0, shift_col, shift_col,
        show 3 + 2 * (n + 1) = 2 * n + 4 + 1 from by omega,
        show 4 + 2 * (n + 1) = 2 * n + 4 + 2 from by omega,
        show 2 * (n + 1) + 4 = 2 * n + 4 + 2 from by omega]
      exact h

/-- ★★★★★ `(0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,4,0)(5,4,0) ∈ W 0`。 -/
theorem R295_54_mem : R295 ++ [((5, 4, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := snocYd_mem (Y0 := Tn 0) (M := M34) (L := 3) (y := 4) (dl := 2)
    (by simp [Tn, D1, Q]) ?_ (by simp [entry, M34]) ?_ (by omega) (by omega) ?_
  · simpa [Tn, D1, Q, R295, R294, M34] using h
  · exact MidD_append (MidD_col 3 3 (by omega) (by omega)) (by simp) (by simp [Mono])
  · intro t ht1 htl _ _
    have : t = 1 := by simp [M34] at htl; omega
    subst this
    simp [entry, M34]
  · intro n
    cases n with
    | zero => rw [Mtwd_zero]; exact Tn_mem 0
    | succ n => exact ((Ifc3_Cm (n + 1)).ifc.bok.aok _ _ (M34_stage n)).mem

#print axioms R295_54_mem

/-! ### 任意の `Ifc3` 台座の上で良い junk `JkU3` と、3 の記録 1 本の集合 `P3U` -/

def JkU3 (c : ℕ) (J : TrioSeq) : Prop := ∀ (E : ℕ → TrioSeq → Prop), Ifc3 E → JkS E 2 0 c J

theorem JkU3_nil (c : ℕ) : JkU3 c [] := by
  intro E hE
  refine ⟨by simp, by intro x hx; simp at hx, ?_⟩
  intro t Y' hY'
  have h := Ifc3_snoc3 hE hY'
  simpa [shiftr01, show c + t + 1 = c + 1 + t from by omega] using h

theorem JkU3_shift {c : ℕ} {J : TrioSeq} (hJ : JkU3 c J) (u : ℕ) :
    JkU3 (c + u) (shiftr01 u 0 J) := fun E hE => JkS_shift (hJ E hE) u

theorem JkU3_mid {c : ℕ} {J : TrioSeq} (hJ : JkU3 c J) :
    MidD (c + 2) ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J) := JkS_mid (by omega) (hJ PkGA Ifc3_PkGA)

/-- 任意の `Ifc3` 台座の元の上に「3 + 普遍 junk」。レベルは 3 の高さ。 -/
def P3U (h : ℕ) (A : TrioSeq) : Prop :=
  ∃ (E : ℕ → TrioSeq → Prop) (c : ℕ) (Z J : TrioSeq), Ifc3 E ∧ h = c + 1 ∧ E c Z ∧
    A = Z ++ ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J) ∧ JkU3 c J

theorem BaseOk_P3U : BaseOk P3U := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro h A ⟨E, c, Z, J, hE, rfl, hZ, rfl, hJ⟩
    have hJ' : JkS E 2 0 c J := hJ E hE
    have hmem := hJ'.2.2 0 Z (by simpa using hZ)
    simp only [shiftr01_zero, Nat.add_zero] at hmem
    exact Aok_append_Mid (by omega) (hE.ifc.bok.aok c Z hZ) (JkU3_mid hJ) hmem
  · rintro h A ⟨E, c, Z, J, hE, rfl, hZ, rfl, hJ⟩
    exact Ancd_append_Mid (hE.ifc.bok.aok c Z hZ).ne (hE.ifc.bok.ancd c Z hZ) (JkU3_mid hJ)
  · rintro h A ⟨E, c, Z, J, hE, rfl, hZ, rfl, hJ⟩ Bk hBk
    have hJ' : JkS E 2 0 c J := hJ E hE
    have hB := hE.ifc.bok
    have hM := JkU3_mid hJ
    have hbase : ∀ (t : ℕ) (A : TrioSeq), Aok A → E (c + t) A →
        A ++ shiftr01 t 0 ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J) ∈ W 0 := by
      intro t A _ hA
      rw [shiftr01_append0, shift_col]
      exact hJ'.2.2 t A hA
    have hclose : ∀ (t : ℕ) (A' C' : TrioSeq), Aok A' → E (c + t) A' → Mono C' →
        (∀ (t' : ℕ) (A'' : TrioSeq), Aok A'' → E (c + t') A'' →
          A'' ++ BlkD (c + 2 + t') (shiftr01 t' 0 ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J)) C'
            ∈ W 0) →
        E (c + t) (A' ++ BlkD (c + 2 + t)
          (shiftr01 t 0 ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J)) C') := by
      intro t A' C' _ hA' hmoC' hIH
      have hNs : MidD (c + 2 + t) (shiftr01 t 0 ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J)) :=
        MidD_shift hM t
      refine hB.close (c + t) A' _ hA' ?_ (BlkD_mono hNs.mono hmoC') ?_
      · intro x hx
        rcases List.mem_append.mp hx with hh | hh
        · have := MidD_col_ge hNs x hh; omega
        · have := shiftD_col x hh; omega
      · intro t' Z hZ
        have heq : shiftr01 t' 0 (BlkD (c + 2 + t)
            (shiftr01 t 0 ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J)) C')
            = BlkD (c + 2 + (t + t')) (shiftr01 (t + t') 0
                ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J)) C' := by
          simp only [BlkD, shiftr01_append0, shiftr01_add0]
          congr 2
          omega
        rw [heq]
        have hZ' : E (c + (t + t')) Z := by
          rwa [show c + (t + t') = c + t + t' from by omega]
        exact hIH (t + t') Z (hB.aok _ _ hZ') hZ'
    have hkey := blkD_memS (d := c + 2) (by omega) _ hM hbase hclose Bk hBk.mem
      hBk.zroot hBk.mono hBk.root 0 Z (hB.aok c Z hZ) (by simpa using hZ)
    simp only [shiftr01_zero, Nat.add_zero] at hkey
    rw [BlkD_app] at hkey
    rwa [show c + 1 + 1 = c + 2 from by omega]
  · rintro h A Blk ⟨E, c, Z, J, hE, rfl, hZ, rfl, hJ⟩ hcol hmo hcl
    refine ⟨E, c, Z, J ++ Blk, hE, rfl, hZ, by simp [List.append_assoc], ?_⟩
    intro E' hE'
    have hJ' : JkS E' 2 0 c J := hJ E' hE'
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hh | hh
      · exact hJ'.1 x hh
      · have := hcol x hh; omega
    · intro x hx
      rcases List.mem_append.mp hx with hh | hh
      · exact hJ'.2.1 x hh
      · exact hmo x hh
    · intro t Y' hY'
      rw [shiftr01_append0, ← List.append_assoc, ← List.append_assoc]
      have hstep : P3U (c + 1 + t)
          (Y' ++ ([((c + 1 + t, 3, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J)) :=
        ⟨E', c + t, Y', shiftr01 t 0 J, hE', by omega, hY',
          by rw [show c + t + 1 = c + 1 + t from by omega], JkU3_shift hJ t⟩
      have h := hcl t _ hstep
      simpa only [List.append_assoc] using h

theorem Iface_P3U : Iface P3U where
  bok := BaseOk_P3U
  rebase := by
    rintro h A ⟨E, c, Z, J, hE, rfl, hZ, rfl, hJ⟩
    obtain ⟨b, Y0, M, rfl, hY0, hM, hM1, hlt, hvis, hre⟩ := hE.ifc.rebase c Z hZ
    have hM3 := JkU3_mid hJ
    refine ⟨b, Y0, M ++ ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J), by simp [List.append_assoc],
      hY0, ?_, ?_, by omega, ?_, ?_⟩
    · refine MidD_append hM ?_ hM3.mono
      intro x hx; have := MidD_col_ge hM3 x hx; omega
    · rw [entry_append_left (List.length_pos_iff.mpr hM.ne)]
      exact hM1
    · have e : entry ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J) 0 0 = c + 1 := by simp [entry]
      refine Vis2_append (by simp) ?_ (by simp [entry]) ?_
      · rw [e]; exact hvis
      · refine Vis2_high ?_
        intro t ht1 htl
        have := hM3.tail t ht1 htl
        omega
    · intro s Y0' hY0'
      rw [shiftr01_append0, shiftr01_append0, shift_col, ← List.append_assoc]
      exact ⟨E, c + s, Y0' ++ shiftr01 s 0 M, shiftr01 s 0 J, hE, by omega, hre s Y0' hY0',
        by rw [show c + s + 1 = c + 1 + s from by omega], JkU3_shift hJ s⟩

theorem Ifc3_P3U : Ifc3 P3U where
  ifc := Iface_P3U
  reb := by
    rintro h A ⟨E, c, Z, J, hE, rfl, hZ, rfl, hJ⟩
    obtain ⟨c0, X, U, rfl, hX, hU, hU1, hlt, hvis, hre⟩ := hE.reb c Z hZ
    have hM3 := JkU3_mid hJ
    refine ⟨c0, X, U ++ ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J), by simp [List.append_assoc],
      hX, ?_, ?_, by omega, ?_, ?_⟩
    · refine MidD_append hU ?_ hM3.mono
      intro x hx; have := MidD_col_ge hM3 x hx; omega
    · rw [entry_append_left (List.length_pos_iff.mpr hU.ne)]
      exact hU1
    · have e : entry ([((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J) 0 0 = c + 1 := by simp [entry]
      refine Vis3_append (by simp) ?_ (by simp [entry]) ?_
      · rw [e]; exact hvis
      · refine Vis3_high ?_
        intro t ht1 htl
        have := hM3.tail t ht1 htl
        omega
    · intro s E'' j'' X' hI'' hX'
      rw [shiftr01_append0, shiftr01_append0, shift_col, ← List.append_assoc]
      exact ⟨E, c + s, X' ++ shiftr01 s 0 U, shiftr01 s 0 J, hE, by omega,
        hre s E'' j'' X' hI'' hX', by rw [show c + s + 1 = c + 1 + s from by omega],
        JkU3_shift hJ s⟩

/-! ### 4 の snoc のための界面 `Ifc4` -/

def Vis4 (bd : ℕ) (M : TrioSeq) : Prop :=
  ∀ t, 1 ≤ t → t < M.length → entry M 0 t < bd →
    (∀ i, t < i → i < M.length → entry M 0 t < entry M 0 i) → 4 ≤ entry M 1 t

theorem Vis4_high {bd : ℕ} {N : TrioSeq}
    (h : ∀ t, 1 ≤ t → t < N.length → bd ≤ entry N 0 t) : Vis4 bd N := by
  intro t ht1 htl hlt _
  have := h t ht1 htl
  omega

theorem Vis4_append {bd : ℕ} {M N : TrioSeq} (hNlen : 0 < N.length)
    (hM : Vis4 (entry N 0 0) M) (hN0 : 4 ≤ entry N 1 0) (hN : Vis4 bd N) :
    Vis4 bd (M ++ N) := by
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

/-- 4 の snoc のための界面: `F` の元は「`Ifc3` 台座の元 `Z`」++「単位 `U`」で、
`U` の頭は 3、見える列は row1 ≥ 4、任意の `Ifc3` 台座の元の上に `U` を置き直しても `F`。 -/
structure Ifc4 (F : ℕ → TrioSeq → Prop) : Prop where
  ifc : Ifc3 F
  reb : ∀ (h : ℕ) (A : TrioSeq), F h A → ∃ (c : ℕ) (Z U : TrioSeq),
    A = Z ++ U ∧ (∃ E : ℕ → TrioSeq → Prop, Ifc3 E ∧ E c Z) ∧
    MidD (c + 2) U ∧ entry U 1 0 = 3 ∧ c < h ∧ Vis4 (h + 1) U ∧
    (∀ (s : ℕ) (E' : ℕ → TrioSeq → Prop) (Z' : TrioSeq), Ifc3 E' →
      E' (c + s) Z' → F (h + s) (Z' ++ shiftr01 s 0 U))

theorem Ifc4_tower {F : ℕ → TrioSeq → Prop} (hF : Ifc4 F) {h c : ℕ} {Z U : TrioSeq}
    (hZ : ∃ E : ℕ → TrioSeq → Prop, Ifc3 E ∧ E c Z)
    (hre : ∀ (s : ℕ) (E' : ℕ → TrioSeq → Prop) (Z' : TrioSeq), Ifc3 E' →
      E' (c + s) Z' → F (h + s) (Z' ++ shiftr01 s 0 U)) (hlt : c < h) :
    ∀ n : ℕ, F (h + n * (h - c)) (Mtwd (h - c) Z U (n + 1))
  | 0 => by
      rw [Mtwd_one]
      obtain ⟨E, hE, hZ'⟩ := hZ
      have := hre 0 E Z hE (by simpa using hZ')
      simpa using this
  | (n + 1) => by
      rw [Mtwd_succ]
      have ih := Ifc4_tower hF hZ hre hlt n
      have h1 := hre ((h - c) * (n + 1)) F _ hF.ifc
        (by
          show F (c + (h - c) * (n + 1)) (Mtwd (h - c) Z U (n + 1))
          rwa [show c + (h - c) * (n + 1) = h + n * (h - c) from by
            rw [Nat.mul_succ, Nat.mul_comm (h - c) n]; omega])
      rwa [show h + (h - c) * (n + 1) = h + (n + 1) * (h - c) from by
        rw [Nat.mul_comm (h - c) (n + 1)]] at h1

theorem Ifc4_tower_mem {F : ℕ → TrioSeq → Prop} (hF : Ifc4 F) {h c : ℕ} {Z U : TrioSeq}
    (hZ : ∃ E : ℕ → TrioSeq → Prop, Ifc3 E ∧ E c Z)
    (hre : ∀ (s : ℕ) (E' : ℕ → TrioSeq → Prop) (Z' : TrioSeq), Ifc3 E' →
      E' (c + s) Z' → F (h + s) (Z' ++ shiftr01 s 0 U)) (hlt : c < h) :
    ∀ n : ℕ, Mtwd (h - c) Z U n ∈ W 0
  | 0 => by
      rw [Mtwd_zero]
      obtain ⟨E, hE, hZ'⟩ := hZ
      exact (hE.ifc.bok.aok _ _ hZ').mem
  | (n + 1) => (hF.ifc.ifc.bok.aok _ _ (Ifc4_tower hF hZ hre hlt n)).mem

/-- ★★★ `Ifc4` の元の頂上に `(h+1,4,0)`。 -/
theorem Ifc4_snoc4 {F : ℕ → TrioSeq → Prop} (hF : Ifc4 F) {h : ℕ} {A : TrioSeq} (hA : F h A) :
    A ++ [((h + 1, 4, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  obtain ⟨c, Z, U, rfl, hZ, hU, hU1, hlt, hvis, hre⟩ := hF.reb h A hA
  have hne : Z ≠ [] := by
    obtain ⟨E, hE, hZ'⟩ := hZ
    exact (hE.ifc.bok.aok _ _ hZ').ne
  have h1 := snocYd_mem (Y0 := Z) (M := U) (L := c + 1) (y := 4) (dl := h - c) hne
    (by rw [show c + 1 + 1 = c + 2 from by omega]; exact hU) (by rw [hU1]; omega)
    (by rw [show c + 1 + (h - c) = h + 1 from by omega]; exact hvis)
    (by omega) (by omega) (Ifc4_tower_mem hF hZ hre hlt)
  rwa [show c + 1 + (h - c) = h + 1 from by omega] at h1

theorem Ifc4_P3U : Ifc4 P3U where
  ifc := Ifc3_P3U
  reb := by
    rintro h A ⟨E, c, Z, J, hE, rfl, hZ, rfl, hJ⟩
    have hM3 := JkU3_mid hJ
    refine ⟨c, Z, [((c + 1, 3, 0) : ℕ × ℕ × ℕ)] ++ J, rfl, ⟨E, hE, hZ⟩, hM3,
      entry_cons_append_1 _ _, by omega, ?_, ?_⟩
    · refine Vis4_high ?_
      intro t ht1 htl
      have := hM3.tail t ht1 htl
      omega
    · intro s E' Z' hE' hZ'
      rw [shiftr01_append0, shift_col]
      exact ⟨E', c + s, Z', shiftr01 s 0 J, hE', by omega, hZ',
        by rw [show c + s + 1 = c + 1 + s from by omega], JkU3_shift hJ s⟩

theorem Ifc4_StkF {F : ℕ → TrioSeq → Prop} (hF : Ifc4 F) {y : ℕ} (hy : 3 ≤ y) :
    ∀ k : ℕ, Ifc4 (StkF F y k)
  | 0 => hF
  | (k + 1) => by
      have hIk := Ifc4_StkF hF hy k
      refine ⟨Ifc3_StkF hF.ifc (by omega) (k + 1), ?_⟩
      rintro h A ⟨c, Y, J, rfl, hY, rfl, hJ⟩
      have hJ' : JkS F y k c J := hJ
      obtain ⟨c0, Z, U, rfl, hZ, hU, hU1, hlt, hvis, hre⟩ := hIk.reb c Y hY
      have hM3 := JkS_mid (by omega) hJ'
      refine ⟨c0, Z, U ++ ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J), by simp [List.append_assoc],
        hZ, ?_, ?_, by omega, ?_, ?_⟩
      · refine MidD_append hU ?_ hM3.mono
        intro x hx; have := MidD_col_ge hM3 x hx; omega
      · rw [entry_append_left (List.length_pos_iff.mpr hU.ne)]
        exact hU1
      · have e : entry ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J) 0 0 = c + 1 := by simp [entry]
        refine Vis4_append (by simp) ?_ (by simp [entry]; omega) ?_
        · rw [e]; exact hvis
        · refine Vis4_high ?_
          intro t ht1 htl
          have := hM3.tail t ht1 htl
          omega
      · intro s E' Z' hE' hZ'
        rw [shiftr01_append0, shiftr01_append0, shift_col, ← List.append_assoc]
        exact ⟨c + s, Z' ++ shiftr01 s 0 U, shiftr01 s 0 J, by omega, hre s E' Z' hE' hZ',
          by rw [show c + s + 1 = c + 1 + s from by omega], JkS_shift hJ' s⟩

/-! ### D_5 = `(0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,4,0)(5,5,0)` -/

theorem JkS_nil4U (n c : ℕ) : JkS (StkF P3U 3 n) 3 0 c [] := by
  refine ⟨by simp, by intro x hx; simp at hx, ?_⟩
  intro t Y' hY'
  have h := Ifc4_snoc4 (Ifc4_StkF Ifc4_P3U (le_refl 3) n) hY'
  simpa [shiftr01, show c + t + 1 = c + 1 + t from by omega] using h

/-- `T4 n = Tn 1 ++ (4,4,0)(5,4,0)…(n+3,4,0)`（4 が `n` 本）。 -/
def T4 : ℕ → TrioSeq
  | 0 => Tn 1
  | (n + 1) => T4 n ++ [((n + 4, 4, 0) : ℕ × ℕ × ℕ)]

theorem T4_mem : ∀ n : ℕ, StkF P3U 3 n (n + 3) (T4 n)
  | 0 => by
      show P3U (0 + 3) (Tn 0 ++ [((3, 3, 0) : ℕ × ℕ × ℕ)])
      exact ⟨PkGA, 2, Tn 0, [], Ifc3_PkGA, by omega, Lk_Tn 0, by simp, JkU3_nil 2⟩
  | (n + 1) => by
      refine ⟨n + 3, T4 n, [], by omega, T4_mem n, ?_, JkS_nil4U n (n + 3)⟩
      simp [T4, show n + 3 + 1 = n + 4 from by omega]

theorem Mtw_T4 : ∀ n : ℕ, Mtw (Tn 1) [((4, 4, 0) : ℕ × ℕ × ℕ)] n = T4 n
  | 0 => by rw [Mtw_zero]; rfl
  | (n + 1) => by
      rw [Mtw_succ, Mtw_T4 n, shift_col]
      simp [T4, show 4 + n = n + 4 from by omega]

/-- `D5 = (0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)(4,4,0)(5,5,0)`。 -/
def D5 : TrioSeq := R295 ++ [((5, 5, 0) : ℕ × ℕ × ℕ)]

/-- ★★★★★ `D5 ∈ W 0`。 -/
theorem D5_mem : D5 ∈ W 0 := by
  have h := snocY_mem (Y0 := Tn 1) (M := [((4, 4, 0) : ℕ × ℕ × ℕ)]) (L := 4) (y := 5)
    (by simp [Tn, D1, Q]) (MidD_col 4 4 (by omega) (by omega)) (by simp [entry]) (by omega)
    (fun n => by rw [Mtw_T4]; exact ((BaseOk_StkF BaseOk_P3U (by omega) n).aok _ _ (T4_mem n)).mem)
  simpa [Tn, D1, Q, D5, R295, R294] using h

#print axioms D5_mem

/-! ### 値 `v` で一様な界面 `IfcV v` と普遍 junk の記録の集合 `PU y`（∀ v の D_v へ） -/

/-- 見える列（頂上から辿れる祖先）は row1 ≥ `y`。 -/
def VisV (y bd : ℕ) (M : TrioSeq) : Prop :=
  ∀ t, 1 ≤ t → t < M.length → entry M 0 t < bd →
    (∀ i, t < i → i < M.length → entry M 0 t < entry M 0 i) → y ≤ entry M 1 t

theorem VisV_high {y bd : ℕ} {N : TrioSeq}
    (h : ∀ t, 1 ≤ t → t < N.length → bd ≤ entry N 0 t) : VisV y bd N := by
  intro t ht1 htl hlt _
  have := h t ht1 htl
  omega

theorem VisV_append {y bd : ℕ} {M N : TrioSeq} (hNlen : 0 < N.length)
    (hM : VisV y (entry N 0 0) M) (hN0 : y ≤ entry N 1 0) (hN : VisV y bd N) :
    VisV y bd (M ++ N) := by
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

/-- 置き直し可能性: `F` の元 = 台座（`B` を満たす集合の元）`Z` ++ 単位 `U`、`U` の頭の row1 = `v`、
見える列は row1 ≥ `v+1`、任意の `B` 台座の元の上に `U` を置き直しても `F`。 -/
def Reb (v : ℕ) (B : (ℕ → TrioSeq → Prop) → Prop) (F : ℕ → TrioSeq → Prop) : Prop :=
  ∀ (h : ℕ) (A : TrioSeq), F h A → ∃ (c : ℕ) (Z U : TrioSeq),
    A = Z ++ U ∧ (∃ E : ℕ → TrioSeq → Prop, B E ∧ E c Z) ∧
    MidD (c + 2) U ∧ entry U 1 0 = v ∧ c < h ∧ VisV (v + 1) (h + 1) U ∧
    (∀ (s : ℕ) (E' : ℕ → TrioSeq → Prop) (Z' : TrioSeq), B E' →
      E' (c + s) Z' → F (h + s) (Z' ++ shiftr01 s 0 U))

/-- 値 `v` の snoc ができる界面。`v ≤ 2` は `Iface`、`IfcV (v+1) F = IfcV v F ∧ Reb v (IfcV v) F`。 -/
def IfcV : ℕ → (ℕ → TrioSeq → Prop) → Prop
  | 0 => Iface
  | 1 => Iface
  | 2 => Iface
  | (v + 3) => fun F => IfcV (v + 2) F ∧ Reb (v + 2) (IfcV (v + 2)) F

theorem IfcV_succ3 (v : ℕ) (F : ℕ → TrioSeq → Prop) :
    IfcV (v + 3) F ↔ IfcV (v + 2) F ∧ Reb (v + 2) (IfcV (v + 2)) F := Iff.rfl

theorem IfcV_iface : ∀ (v : ℕ) {F : ℕ → TrioSeq → Prop}, IfcV v F → Iface F
  | 0, _, h => h
  | 1, _, h => h
  | 2, _, h => h
  | (v + 3), F, h => IfcV_iface (v + 2) ((IfcV_succ3 v F).mp h).1

theorem IfcV_le2 {v : ℕ} (hv : v ≤ 2) {F : ℕ → TrioSeq → Prop} : IfcV v F ↔ Iface F := by
  match v, hv with
  | 0, _ => exact Iff.rfl
  | 1, _ => exact Iff.rfl
  | 2, _ => exact Iff.rfl

theorem IfcV_down : ∀ (v : ℕ) {u : ℕ} {F : ℕ → TrioSeq → Prop}, IfcV v F → u ≤ v → IfcV u F
  | 0, u, F, h, hu => (IfcV_le2 (by omega)).mpr h
  | 1, u, F, h, hu => (IfcV_le2 (by omega)).mpr h
  | 2, u, F, h, hu => (IfcV_le2 (by omega)).mpr h
  | (v + 3), u, F, h, hu => by
      rcases Nat.lt_or_ge u (v + 3) with hlt | hge
      · exact IfcV_down (v + 2) ((IfcV_succ3 v F).mp h).1 (by omega)
      · have : u = v + 3 := by omega
        subst this; exact h

theorem Reb_tower {B : (ℕ → TrioSeq → Prop) → Prop} {F : ℕ → TrioSeq → Prop}
    (hBF : B F) {h c : ℕ} {Z U : TrioSeq}
    (hZ : ∃ E : ℕ → TrioSeq → Prop, B E ∧ E c Z)
    (hre : ∀ (s : ℕ) (E' : ℕ → TrioSeq → Prop) (Z' : TrioSeq), B E' →
      E' (c + s) Z' → F (h + s) (Z' ++ shiftr01 s 0 U)) (hlt : c < h) :
    ∀ n : ℕ, F (h + n * (h - c)) (Mtwd (h - c) Z U (n + 1))
  | 0 => by
      rw [Mtwd_one]
      obtain ⟨E, hE, hZ'⟩ := hZ
      have := hre 0 E Z hE (by simpa using hZ')
      simpa using this
  | (n + 1) => by
      rw [Mtwd_succ]
      have ih := Reb_tower hBF hZ hre hlt n
      have h1 := hre ((h - c) * (n + 1)) F _ hBF
        (by
          show F (c + (h - c) * (n + 1)) (Mtwd (h - c) Z U (n + 1))
          rwa [show c + (h - c) * (n + 1) = h + n * (h - c) from by
            rw [Nat.mul_succ, Nat.mul_comm (h - c) n]; omega])
      rwa [show h + (h - c) * (n + 1) = h + (n + 1) * (h - c) from by
        rw [Nat.mul_comm (h - c) (n + 1)]] at h1

theorem Reb_tower_mem {B : (ℕ → TrioSeq → Prop) → Prop} {F : ℕ → TrioSeq → Prop}
    (hBF : B F) (hBI : ∀ E, B E → Iface E) {h c : ℕ} {Z U : TrioSeq}
    (hZ : ∃ E : ℕ → TrioSeq → Prop, B E ∧ E c Z)
    (hre : ∀ (s : ℕ) (E' : ℕ → TrioSeq → Prop) (Z' : TrioSeq), B E' →
      E' (c + s) Z' → F (h + s) (Z' ++ shiftr01 s 0 U)) (hlt : c < h) :
    ∀ n : ℕ, Mtwd (h - c) Z U n ∈ W 0
  | 0 => by
      rw [Mtwd_zero]
      obtain ⟨E, hE, hZ'⟩ := hZ
      exact ((hBI E hE).bok.aok _ _ hZ').mem
  | (n + 1) => ((hBI F hBF).bok.aok _ _ (Reb_tower hBF hZ hre hlt n)).mem

/-- ★★★ 置き直し可能な `F` の元の頂上に `(h+1, v+1, 0)`。 -/
theorem Reb_snoc {v : ℕ} {B : (ℕ → TrioSeq → Prop) → Prop} {F : ℕ → TrioSeq → Prop}
    (hBF : B F) (hBI : ∀ E, B E → Iface E) (hreb : Reb v B F) {h : ℕ} {A : TrioSeq}
    (hA : F h A) : A ++ [((h + 1, v + 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  obtain ⟨c, Z, U, rfl, hZ, hU, hU1, hlt, hvis, hre⟩ := hreb h A hA
  have hne : Z ≠ [] := by
    obtain ⟨E, hE, hZ'⟩ := hZ
    exact ((hBI E hE).bok.aok _ _ hZ').ne
  have h1 := snocYd_mem (Y0 := Z) (M := U) (L := c + 1) (y := v + 1) (dl := h - c) hne
    (by rw [show c + 1 + 1 = c + 2 from by omega]; exact hU) (by rw [hU1]; omega)
    (by rw [show c + 1 + (h - c) = h + 1 from by omega]; exact hvis)
    (by omega) (by omega) (Reb_tower_mem hBF hBI hZ hre hlt)
  rwa [show c + 1 + (h - c) = h + 1 from by omega] at h1

/-- ★★★★ `IfcV (v+3)` の元の頂上に `(h+1, v+3, 0)`。 -/
theorem IfcV_snoc (v : ℕ) {F : ℕ → TrioSeq → Prop} (hF : IfcV (v + 3) F) {h : ℕ} {A : TrioSeq}
    (hA : F h A) : A ++ [((h + 1, v + 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  Reb_snoc ((IfcV_succ3 v F).mp hF).1 (fun E hE => IfcV_iface (v + 2) hE)
    ((IfcV_succ3 v F).mp hF).2 hA

theorem Ifc3_toIfcV {F : ℕ → TrioSeq → Prop} (hF : Ifc3 F) : IfcV 3 F := by
  refine ⟨hF.ifc, ?_⟩
  intro h A hA
  obtain ⟨c, X, U, rfl, ⟨E', j, hI', hX⟩, hU, hU1, hlt, hvis, hre⟩ := hF.reb h A hA
  exact ⟨c, X, U, rfl, ⟨RunG E' j, Iface_RunG hI' j, hX⟩, hU, hU1, hlt, hvis,
    fun s E'' Z' hI'' hZ' => hre s E'' 0 Z' hI'' hZ'⟩

/-- 任意の `IfcV (y+1)` 台座の上で良い junk（記録の値は `y+1`）。 -/
def JkU (y c : ℕ) (J : TrioSeq) : Prop :=
  (∀ x ∈ J, c + 2 ≤ x.1) ∧ Mono J ∧
  ∀ (E : ℕ → TrioSeq → Prop), IfcV (y + 1) E → ∀ (t : ℕ) (Z : TrioSeq), E (c + t) Z →
    Z ++ ([((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J) ∈ W 0

theorem JkU_toJkS {y c : ℕ} {J : TrioSeq} {E : ℕ → TrioSeq → Prop} (hJ : JkU y c J)
    (hE : IfcV (y + 1) E) : JkS E y 0 c J := ⟨hJ.1, hJ.2.1, hJ.2.2 E hE⟩

theorem JkU_nil (w c : ℕ) : JkU (w + 2) c [] := by
  refine ⟨by simp, by intro x hx; simp at hx, ?_⟩
  intro E hE t Z hZ
  have h := IfcV_snoc w hE hZ
  simpa [shiftr01, show c + t + 1 = c + 1 + t from by omega] using h

theorem JkU_shift {y c : ℕ} {J : TrioSeq} (hJ : JkU y c J) (u : ℕ) :
    JkU y (c + u) (shiftr01 u 0 J) := by
  refine ⟨?_, shiftD_mono hJ.2.1, ?_⟩
  · intro x hx
    simp only [shiftr01, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have := hJ.1 p hp
    dsimp only
    omega
  · intro E hE t Z hZ
    rw [shiftr01_add0]
    have hZ' : E (c + (u + t)) Z := by
      rw [show c + (u + t) = c + u + t from by omega]; exact hZ
    have h := hJ.2.2 E hE (u + t) Z hZ'
    rw [show c + u + 1 + t = c + 1 + (u + t) from by omega]
    exact h

theorem JkU_mid {y c : ℕ} {J : TrioSeq} (hJ : JkU y c J) :
    MidD (c + 2) ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J) := by
  have h := MidD_append (MidD_col (c + 1) (y + 1) (by omega) (by omega))
    (by intro x hx; have := hJ.1 x hx; omega) hJ.2.1
  rwa [show c + 1 + 1 = c + 2 from by omega] at h

/-- 任意の `IfcV (y+1)` 台座の元の上に「`y+1` の記録 + 普遍 junk」。レベルは記録の高さ。 -/
def PU (y : ℕ) (h : ℕ) (A : TrioSeq) : Prop :=
  ∃ (E : ℕ → TrioSeq → Prop) (c : ℕ) (Z J : TrioSeq), IfcV (y + 1) E ∧ h = c + 1 ∧ E c Z ∧
    A = Z ++ ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J) ∧ JkU y c J

theorem BaseOk_PU (y : ℕ) : BaseOk (PU y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro h A ⟨E, c, Z, J, hE, rfl, hZ, rfl, hJ⟩
    have hB := (IfcV_iface (y + 1) hE).bok
    have hJ' := JkU_toJkS hJ hE
    have hmem := hJ'.2.2 0 Z (by simpa using hZ)
    simp only [shiftr01_zero, Nat.add_zero] at hmem
    exact Aok_append_Mid (by omega) (hB.aok c Z hZ) (JkU_mid hJ) hmem
  · rintro h A ⟨E, c, Z, J, hE, rfl, hZ, rfl, hJ⟩
    have hB := (IfcV_iface (y + 1) hE).bok
    exact Ancd_append_Mid (hB.aok c Z hZ).ne (hB.ancd c Z hZ) (JkU_mid hJ)
  · rintro h A ⟨E, c, Z, J, hE, rfl, hZ, rfl, hJ⟩ Bk hBk
    have hB := (IfcV_iface (y + 1) hE).bok
    have hJ' := JkU_toJkS hJ hE
    have hM := JkU_mid hJ
    have hbase : ∀ (t : ℕ) (A : TrioSeq), Aok A → E (c + t) A →
        A ++ shiftr01 t 0 ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J) ∈ W 0 := by
      intro t A _ hA
      rw [shiftr01_append0, shift_col]
      exact hJ'.2.2 t A hA
    have hclose : ∀ (t : ℕ) (A' C' : TrioSeq), Aok A' → E (c + t) A' → Mono C' →
        (∀ (t' : ℕ) (A'' : TrioSeq), Aok A'' → E (c + t') A'' →
          A'' ++ BlkD (c + 2 + t') (shiftr01 t' 0 ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J)) C'
            ∈ W 0) →
        E (c + t) (A' ++ BlkD (c + 2 + t)
          (shiftr01 t 0 ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J)) C') := by
      intro t A' C' _ hA' hmoC' hIH
      have hNs : MidD (c + 2 + t) (shiftr01 t 0 ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J)) :=
        MidD_shift hM t
      refine hB.close (c + t) A' _ hA' ?_ (BlkD_mono hNs.mono hmoC') ?_
      · intro x hx
        rcases List.mem_append.mp hx with hh | hh
        · have := MidD_col_ge hNs x hh; omega
        · have := shiftD_col x hh; omega
      · intro t' Z hZ
        have heq : shiftr01 t' 0 (BlkD (c + 2 + t)
            (shiftr01 t 0 ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J)) C')
            = BlkD (c + 2 + (t + t')) (shiftr01 (t + t') 0
                ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J)) C' := by
          simp only [BlkD, shiftr01_append0, shiftr01_add0]
          congr 2
          omega
        rw [heq]
        have hZ' : E (c + (t + t')) Z := by
          rwa [show c + (t + t') = c + t + t' from by omega]
        exact hIH (t + t') Z (hB.aok _ _ hZ') hZ'
    have hkey := blkD_memS (d := c + 2) (by omega) _ hM hbase hclose Bk hBk.mem
      hBk.zroot hBk.mono hBk.root 0 Z (hB.aok c Z hZ) (by simpa using hZ)
    simp only [shiftr01_zero, Nat.add_zero] at hkey
    rw [BlkD_app] at hkey
    rwa [show c + 1 + 1 = c + 2 from by omega]
  · rintro h A Blk ⟨E, c, Z, J, hE, rfl, hZ, rfl, hJ⟩ hcol hmo hcl
    refine ⟨E, c, Z, J ++ Blk, hE, rfl, hZ, by simp [List.append_assoc], ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hh | hh
      · exact hJ.1 x hh
      · have := hcol x hh; omega
    · intro x hx
      rcases List.mem_append.mp hx with hh | hh
      · exact hJ.2.1 x hh
      · exact hmo x hh
    · intro E' hE' t Y' hY'
      rw [shiftr01_append0, ← List.append_assoc, ← List.append_assoc]
      have hstep : PU y (c + 1 + t)
          (Y' ++ ([((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 t 0 J)) :=
        ⟨E', c + t, Y', shiftr01 t 0 J, hE', by omega, hY',
          by rw [show c + t + 1 = c + 1 + t from by omega], JkU_shift hJ t⟩
      have h := hcl t _ hstep
      simpa only [List.append_assoc] using h

theorem Iface_PU {y : ℕ} (hy : 1 ≤ y) : Iface (PU y) where
  bok := BaseOk_PU y
  rebase := by
    rintro h A ⟨E, c, Z, J, hE, rfl, hZ, rfl, hJ⟩
    obtain ⟨b, Y0, M, rfl, hY0, hM, hM1, hlt, hvis, hre⟩ := (IfcV_iface (y + 1) hE).rebase c Z hZ
    have hM3 := JkU_mid hJ
    refine ⟨b, Y0, M ++ ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J), by simp [List.append_assoc],
      hY0, ?_, ?_, by omega, ?_, ?_⟩
    · refine MidD_append hM ?_ hM3.mono
      intro x hx; have := MidD_col_ge hM3 x hx; omega
    · rw [entry_append_left (List.length_pos_iff.mpr hM.ne)]
      exact hM1
    · have e : entry ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J) 0 0 = c + 1 := by simp [entry]
      refine Vis2_append (by simp) ?_ (by simp [entry]; omega) ?_
      · rw [e]; exact hvis
      · refine Vis2_high ?_
        intro t ht1 htl
        have := hM3.tail t ht1 htl
        omega
    · intro s Y0' hY0'
      rw [shiftr01_append0, shiftr01_append0, shift_col, ← List.append_assoc]
      exact ⟨E, c + s, Y0' ++ shiftr01 s 0 M, shiftr01 s 0 J, hE, by omega, hre s Y0' hY0',
        by rw [show c + s + 1 = c + 1 + s from by omega], JkU_shift hJ s⟩

/-- `PU y` は `w ≤ y+2` のすべての `w` で `IfcV w`（頂上が `y+1` なので `y+2` の snoc までできる）。 -/
theorem IfcV_PU {y : ℕ} (hy : 1 ≤ y) : ∀ w : ℕ, w ≤ y + 2 → IfcV w (PU y)
  | 0, _ => Iface_PU hy
  | 1, _ => Iface_PU hy
  | 2, _ => Iface_PU hy
  | (w + 3), hw => by
      refine ⟨IfcV_PU hy (w + 2) (by omega), ?_⟩
      rintro h A ⟨E, c, Z, J, hE, rfl, hZ, rfl, hJ⟩
      have hM3 := JkU_mid hJ
      by_cases hwy : w + 1 = y
      · -- 頂上の段: 台座 `E` 自身が `IfcV (w+2)`
        subst hwy
        refine ⟨c, Z, [((c + 1, w + 1 + 1, 0) : ℕ × ℕ × ℕ)] ++ J, rfl, ⟨E, hE, hZ⟩, hM3,
          entry_cons_append_1 _ _, by omega, ?_, ?_⟩
        · refine VisV_high ?_
          intro t ht1 htl
          have := hM3.tail t ht1 htl
          omega
        · intro s E' Z' hE' hZ'
          rw [shiftr01_append0, shift_col]
          exact ⟨E', c + s, Z', shiftr01 s 0 J, hE', by omega, hZ',
            by rw [show c + s + 1 = c + 1 + s from by omega], JkU_shift hJ s⟩
      · -- 下の段: 台座 `E` の置き直しに記録を足す
        have hE' : IfcV (w + 3) E := IfcV_down (y + 1) hE (by omega)
        obtain ⟨c0, Z0, U0, rfl, hZ0, hU0, hU01, hlt, hvis, hre⟩ :=
          ((IfcV_succ3 w E).mp hE').2 c Z hZ
        refine ⟨c0, Z0, U0 ++ ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J),
          by simp [List.append_assoc], hZ0, ?_, ?_, by omega, ?_, ?_⟩
        · refine MidD_append hU0 ?_ hM3.mono
          intro x hx; have := MidD_col_ge hM3 x hx; omega
        · rw [entry_append_left (List.length_pos_iff.mpr hU0.ne)]
          exact hU01
        · have e : entry ([((c + 1, y + 1, 0) : ℕ × ℕ × ℕ)] ++ J) 0 0 = c + 1 := by simp [entry]
          refine VisV_append (by simp) ?_ (by simp [entry]; omega) ?_
          · rw [e]; exact hvis
          · refine VisV_high ?_
            intro t ht1 htl
            have := hM3.tail t ht1 htl
            omega
        · intro s E'' Z' hE'' hZ'
          rw [shiftr01_append0, shiftr01_append0, shift_col, ← List.append_assoc]
          exact ⟨E, c + s, Z' ++ shiftr01 s 0 U0, shiftr01 s 0 J, hE, by omega,
            hre s E'' Z' hE'' hZ', by rw [show c + s + 1 = c + 1 + s from by omega],
            JkU_shift hJ s⟩

/-! ### ★★★★★ ∀ v: `Dv k = (0,0,0)(1,1,1)(1,1,0)(2,2,0)(3,3,0)…(k+2,k+2,0) ∈ W 0` -/

/-- `Dv 0 = Tn 0 = (0,0,0)(1,1,1)(1,1,0)(2,2,0)`、`Dv (k+1) = Dv k ++ (k+3,k+3,0)`。 -/
def Dv : ℕ → TrioSeq
  | 0 => Tn 0
  | (k + 1) => Dv k ++ [((k + 3, k + 3, 0) : ℕ × ℕ × ℕ)]

theorem Dv_PU : ∀ k : ℕ, PU (k + 2) (k + 3) (Dv (k + 1))
  | 0 => ⟨PkGA, 2, Tn 0, [], Ifc3_toIfcV Ifc3_PkGA, by omega, Lk_Tn 0, by simp [Dv],
      JkU_nil 0 2⟩
  | (k + 1) => ⟨PU (k + 2), k + 3, Dv (k + 1), [], IfcV_PU (by omega) (k + 4) (by omega),
      by omega, Dv_PU k, by simp [Dv, show k + 3 + 1 = k + 4 from by omega], JkU_nil (k + 1) (k + 3)⟩

/-- ★★★★★ 対角列 `D_v` はすべて `W 0`。 -/
theorem Dv_W (k : ℕ) : Dv k ∈ W 0 := by
  cases k with
  | zero => exact Tn_mem 0
  | succ k => exact ((BaseOk_PU (k + 2)).aok _ _ (Dv_PU k)).mem

#print axioms Dv_W

/-! ### ★★★★★ シート行296 `(0,0,0)(1,1,1)(1,1,0)(2,2,1) = psi(W_w + psi_1(W_w))` -/

def R296 : TrioSeq := [(0, 0, 0), (1, 1, 1), (1, 1, 0), (2, 2, 1)]

theorem R296_len : R296.length = 4 := by simp [R296]

theorem nextrel0_R296_23 : nextrel0 R296 2 3 := by
  refine ⟨by simp [R296], by simp [R296], by omega, by simp [R296, entry], ?_⟩
  intro j hj; omega

theorem le0_R296_23 : le0 R296 2 3 :=
  ⟨by simp [R296], by simp [R296], Relation.ReflTransGen.single nextrel0_R296_23⟩

theorem nextrel1_R296_23 : nextrel1 R296 2 3 := by
  refine ⟨by simp [R296], by simp [R296], by omega, by simp [R296, entry],
    le0_R296_23, ?_⟩
  intro j hj
  have hjl := hj.2.1
  rw [R296_len] at hjl
  have hj3 : j = 3 := by omega
  subst hj3
  omega

theorem nextrel2_R296_23 : nextrel2 R296 2 3 := by
  refine ⟨by simp [R296], by simp [R296], by omega, by simp [R296, entry],
    ⟨by simp [R296], by simp [R296], Relation.ReflTransGen.single nextrel1_R296_23⟩, ?_⟩
  intro j hj
  have hjl := hj.2.1
  rw [R296_len] at hjl
  have hj3 : j = 3 := by omega
  subst hj3
  omega

theorem R296_hasParent : hasParent R296 2 3 :=
  hasParent2_of_le1_witness (by rw [R296_len]; omega)
    (Relation.ReflTransGen.single nextrel1_R296_23) (by simp [R296, entry])

theorem R296_parent : parent R296 2 3 = 2 :=
  R296_hasParent.unique (parent_nextR R296_hasParent) nextrel2_R296_23

theorem R296_srow : srow R296 3 = 2 := by simp [srow, R296, entry]

theorem le0_R296_22 : le0 R296 2 2 :=
  ⟨by simp [R296], by simp [R296], Relation.ReflTransGen.refl⟩

theorem le1_R296_22 : le1 R296 2 2 :=
  ⟨by simp [R296], by simp [R296], Relation.ReflTransGen.refl⟩

/-- `Dm n = (0,0,0)(1,1,1)(1,1,0)(2,2,0)…(n,n,0)`（対角の列が `n` 本）。 -/
def Dm (n : ℕ) : TrioSeq := Q ++ (List.range n).map fun k => ((k + 1, k + 1, 0) : ℕ × ℕ × ℕ)

open Classical in
theorem oper_R296 (n : ℕ) : R296⟦n⟧ = Dm n := by
  rw [L53.oper_unfold (j1 := 3) (i1 := 2) (j0 := 2) (d0 := 1) (d1 := 1)
      (by simp [R296]) (by omega) (by simp [R296, entry]) R296_srow.symm
      R296_hasParent R296_parent.symm (by simp [R296, entry]) (by simp [R296, entry]) n]
  have hr : List.range' 2 (3 - 2) = [2] := rfl
  have htk : R296.take 2 = Q := rfl
  rw [hr, htk]
  have hbody : ∀ k : ℕ, ([2] : List ℕ).map
      (fun j => ((entry R296 0 j + (if le0 R296 2 j then k * 1 else 0),
        entry R296 1 j + (if le1 R296 2 j then k * 1 else 0),
        entry R296 2 j) : ℕ × ℕ × ℕ))
      = [((k + 1, k + 1, 0) : ℕ × ℕ × ℕ)] := by
    intro k
    simp only [List.map_cons, List.map_nil]
    rw [if_pos le0_R296_22, if_pos le1_R296_22]
    simp [R296, entry, Nat.add_comm]
  rw [List.flatMap_congr (fun k _ => hbody k)]
  simp [Dm, flatMap_singleton_map]

theorem Dm_succ (n : ℕ) : Dm (n + 1) = Dm n ++ [((n + 1, n + 1, 0) : ℕ × ℕ × ℕ)] := by
  simp [Dm, List.range_succ]

theorem Dm_one : Dm 1 = D1 := by simp [Dm, D1]

theorem Dm_Dv : ∀ n : ℕ, Dm (n + 2) = Dv n
  | 0 => by simp [Dm, Dv, Tn, D1, List.range_succ]
  | (n + 1) => by
      rw [show n + 1 + 2 = n + 2 + 1 from by omega, Dm_succ, Dm_Dv n]
      simp [Dv, show n + 2 + 1 = n + 3 from by omega]

theorem Dm_mem (n : ℕ) : Dm n ∈ W 0 := by
  match n with
  | 0 => simpa [Dm] using Q_mem
  | 1 => rw [Dm_one]; simpa [Dg, D1] using Dg_mem 1
  | (n + 2) => rw [Dm_Dv]; exact Dv_W n

/-- ★★★★★ シート行296 `(0,0,0)(1,1,1)(1,1,0)(2,2,1) ∈ W 0`（`psi(W_w + psi_1(W_w))`）。 -/
theorem R296_mem : R296 ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_R296 n]
  exact Dm_mem n

#print axioms R296_mem

/-! ### 対角の一般化: `DiaV h v k = (h+1,v+1,0)(h+2,v+2,0)…(h+k,v+k,0)` を任意の台座の上に -/

def DiaV (h v : ℕ) : ℕ → TrioSeq
  | 0 => []
  | (k + 1) => DiaV h v k ++ [((h + k + 1, v + k + 1, 0) : ℕ × ℕ × ℕ)]

theorem DiaV_split (h v a : ℕ) : ∀ b : ℕ, DiaV h v (a + b) = DiaV h v a ++ DiaV (h + a) (v + a) b
  | 0 => by simp [DiaV]
  | (b + 1) => by
      rw [show a + (b + 1) = (a + b) + 1 from by omega]
      simp only [DiaV, DiaV_split h v a b, List.append_assoc, Nat.add_assoc]

theorem JkU_nil' {y : ℕ} (hy : 2 ≤ y) (c : ℕ) : JkU y c [] := by
  obtain ⟨w, rfl⟩ : ∃ w, y = w + 2 := ⟨y - 2, by omega⟩
  exact JkU_nil w c

/-- ★★★ `IfcV (y+1)` 台座の元 `Z`（レベル `c`）の上の対角は `PU (y+k)`（レベル `c+k+1`）。 -/
theorem PU_DiaV {y : ℕ} (hy : 2 ≤ y) {E : ℕ → TrioSeq → Prop} (hE : IfcV (y + 1) E)
    {c : ℕ} {Z : TrioSeq} (hZ : E c Z) :
    ∀ k : ℕ, PU (y + k) (c + k + 1) (Z ++ DiaV c y (k + 1))
  | 0 => ⟨E, c, Z, [], hE, by omega, hZ, by simp [DiaV], JkU_nil' hy c⟩
  | (k + 1) => ⟨PU (y + k), c + k + 1, Z ++ DiaV c y (k + 1), [],
      IfcV_PU (by omega) (y + k + 1 + 1) (by omega), by omega, PU_DiaV hy hE hZ k,
      by simp [DiaV, List.append_assoc, show c + (k + 1) + 1 = c + k + 1 + 1 from by omega,
        show y + (k + 1) + 1 = y + k + 1 + 1 from by omega],
      JkU_nil' (by omega) (c + k + 1)⟩

theorem PkGA_DiaV1 {h : ℕ} {X : TrioSeq} (hX : RunA 0 h X) : PkGA (h + 1) (X ++ DiaV h 1 1) :=
  ⟨RunA 0, Iface_RunA0, 0, h, X, [], rfl, hX, by simp [DiaV], JkGU_nil h⟩

/-- ★★★ 走りの底 `RunA 0` の元の上の対角はすべて `W 0`。 -/
theorem RunA0_DiaV {h : ℕ} {X : TrioSeq} (hX : RunA 0 h X) : ∀ k : ℕ, X ++ DiaV h 1 k ∈ W 0
  | 0 => by simpa [DiaV] using ((BaseOk_RunA 0).aok _ _ hX).mem
  | 1 => (PkGA_Aok (PkGA_DiaV1 hX)).mem
  | (k + 2) => by
      have h1 := PU_DiaV (le_refl 2) (Ifc3_toIfcV Ifc3_PkGA) (PkGA_DiaV1 hX) k
      have h2 := ((BaseOk_PU (2 + k)).aok _ _ h1).mem
      rw [show k + 2 = 1 + (k + 1) from by omega, DiaV_split h 1 1 (k + 1), ← List.append_assoc]
      exact h2

/-! ### z=1 の列は対角の起点: `(Y0 ++ (a,b,0)(a+1,b+1,1))⟦n⟧ = Y0 ++ (a,b,0)(a+1,b+1,0)…(a+n-1,b+n-1,0)` -/

def Dtw (a b n : ℕ) : TrioSeq := (List.range n).map fun k => ((a + k, b + k, 0) : ℕ × ℕ × ℕ)

theorem Dtw_succ (a b n : ℕ) : Dtw a b (n + 1) = Dtw a b n ++ [((a + n, b + n, 0) : ℕ × ℕ × ℕ)] := by
  simp [Dtw, List.range_succ]

theorem Dtw_eq_DiaV (h v : ℕ) : ∀ k : ℕ, Dtw (h + 1) (v + 1) k = DiaV h v k
  | 0 => by simp [Dtw, DiaV]
  | (k + 1) => by
      rw [Dtw_succ, Dtw_eq_DiaV h v k, show h + 1 + k = h + k + 1 from by omega,
        show v + 1 + k = v + k + 1 from by omega]
      rfl

theorem Dtw_cons (a b : ℕ) : ∀ n : ℕ, Dtw a b (n + 1) = [((a, b, 0) : ℕ × ℕ × ℕ)] ++ Dtw (a + 1) (b + 1) n
  | 0 => by simp [Dtw]
  | (n + 1) => by
      rw [Dtw_succ, Dtw_cons a b n, Dtw_succ (a + 1) (b + 1) n, List.append_assoc,
        show a + (n + 1) = a + 1 + n from by omega, show b + (n + 1) = b + 1 + n from by omega]

open Classical in
theorem oper_z1 (Y0 : TrioSeq) (a b n : ℕ) :
    (Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ), ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)])⟦n⟧ = Y0 ++ Dtw a b n := by
  set T : TrioSeq := [((a, b, 0) : ℕ × ℕ × ℕ), ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] with hT
  set M : TrioSeq := Y0 ++ T with hM
  set p := Y0.length with hp
  have hlen : M.length = p + 2 := by simp [hM, hT, hp]
  have eT : ∀ i q, entry M i (p + q) = entry T i q := fun i q => entry_append_right Y0 T i q
  have e0p : entry M 0 p = a := by rw [show p = p + 0 from rfl, eT]; simp [hT, entry]
  have e1p : entry M 1 p = b := by rw [show p = p + 0 from rfl, eT]; simp [hT, entry]
  have e2p : entry M 2 p = 0 := by rw [show p = p + 0 from rfl, eT]; simp [hT, entry]
  have e0q : entry M 0 (p + 1) = a + 1 := by rw [eT]; simp [hT, entry]
  have e1q : entry M 1 (p + 1) = b + 1 := by rw [eT]; simp [hT, entry]
  have e2q : entry M 2 (p + 1) = 1 := by rw [eT]; simp [hT, entry]
  have hn0 : nextrel0 M p (p + 1) := by
    refine ⟨by omega, by omega, by omega, by rw [e0p, e0q]; omega, ?_⟩
    intro j hj; omega
  have hl0 : le0 M p (p + 1) := ⟨by omega, by omega, Relation.ReflTransGen.single hn0⟩
  have hn1 : nextrel1 M p (p + 1) := by
    refine ⟨by omega, by omega, by omega, by rw [e1p, e1q]; omega, hl0, ?_⟩
    intro j hj
    have hjl := hj.2.1
    have hj1 : j = p + 1 := by omega
    subst hj1
    omega
  have hn2 : nextrel2 M p (p + 1) := by
    refine ⟨by omega, by omega, by omega, by rw [e2p, e2q]; omega,
      ⟨by omega, by omega, Relation.ReflTransGen.single hn1⟩, ?_⟩
    intro j hj
    have hjl := hj.2.1
    have hj1 : j = p + 1 := by omega
    subst hj1
    omega
  have hpar : hasParent M 2 (p + 1) :=
    hasParent2_of_le1_witness (by omega) (Relation.ReflTransGen.single hn1) (by rw [e2p, e2q]; omega)
  have hparent : parent M 2 (p + 1) = p := hpar.unique (parent_nextR hpar) hn2
  have hsrow : srow M (p + 1) = 2 := by simp [srow, e2q]
  have hl00 : le0 M p p := ⟨by omega, by omega, Relation.ReflTransGen.refl⟩
  have hl11 : le1 M p p := ⟨by omega, by omega, Relation.ReflTransGen.refl⟩
  rw [L53.oper_unfold (j1 := p + 1) (i1 := 2) (j0 := p) (d0 := 1) (d1 := 1)
      (by omega) (by omega) (by rw [e0q]; omega) hsrow.symm hpar hparent.symm
      (by rw [if_pos (by omega : 0 < 2), e0q, e0p]; omega)
      (by rw [if_pos (by omega : 1 < 2), e1q, e1p]; omega) n]
  have hr : List.range' p (p + 1 - p) = [p] := by simp
  have htk : M.take p = Y0 := by rw [hM, hp, List.take_left]
  rw [hr, htk]
  have hbody : ∀ k : ℕ, ([p] : List ℕ).map
      (fun j => ((entry M 0 j + (if le0 M p j then k * 1 else 0),
        entry M 1 j + (if le1 M p j then k * 1 else 0),
        entry M 2 j) : ℕ × ℕ × ℕ))
      = [((a + k, b + k, 0) : ℕ × ℕ × ℕ)] := by
    intro k
    simp only [List.map_cons, List.map_nil]
    rw [if_pos hl00, if_pos hl11, e0p, e1p, e2p]
    simp
  rw [List.flatMap_congr (fun k _ => hbody k)]
  simp [Dtw, flatMap_singleton_map]

/-- ★★★ z=1 の列の継ぎ足し: 対角の塔がすべて `W 0` なら `Y0 ++ (a,b,0)(a+1,b+1,1) ∈ W 0`。 -/
theorem z1_mem {Y0 : TrioSeq} {a b : ℕ} (htw : ∀ n, Y0 ++ Dtw a b n ∈ W 0) :
    Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ), ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_z1]
  exact htw n

/-- ★★★ `RunA 0 h` の元（頂上が `(h,1,0)`）の上に `(h+1,2,1)`。 -/
theorem RunA0_z1 {h : ℕ} {Y0 : TrioSeq} (hX : RunA 0 h (Y0 ++ [((h, 1, 0) : ℕ × ℕ × ℕ)])) :
    Y0 ++ [((h, 1, 0) : ℕ × ℕ × ℕ), ((h + 1, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine z1_mem ?_
  intro n
  cases n with
  | zero =>
      have h1 := ((BaseOk_RunA 0).aok _ _ hX).mem
      simpa [Dtw] using W_dropLast h1
  | succ n =>
      rw [Dtw_cons, ← List.append_assoc, Dtw_eq_DiaV]
      exact RunA0_DiaV hX n

#print axioms RunA0_z1

/-! ### 単位 `(h+1,1,0)(h+2,2,1)` は絶対セグメント。`R296 ∈ RunA 0 1`、行 306/309/310 -/

theorem SegA_unit11 (h : ℕ) :
    SegA h [((h + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 1) : ℕ × ℕ × ℕ)] where
  mid := by
    have h1 := MidD_append (MidD_col (h + 1) 1 (by omega) (by omega))
      (N := [((h + 2, 2, 1) : ℕ × ℕ × ℕ)])
      (by intro c hc; simp only [List.mem_singleton] at hc; subst hc; show h + 1 + 1 ≤ h + 2; omega)
      (by intro c hc; simp only [List.mem_singleton] at hc; subst hc; show (1 : ℕ) ≤ 2; omega)
    simpa [show h + 1 + 1 = h + 2 from by omega] using h1
  head1 := by simp [entry]
  reapp := by
    intro P hP s A' hA'
    have hR : RunA 0 (h + s + 1) (A' ++ [((h + s + 1, 1, 0) : ℕ × ℕ × ℕ)]) :=
      ⟨h + s, A', _, rfl, rfl, ⟨P, hP, hA'⟩, SegA_one (h + s)⟩
    have h1 := RunA0_z1 hR
    have e : shiftr01 s 0 [((h + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 1) : ℕ × ℕ × ℕ)]
        = [((h + s + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + s + 1 + 1, 2, 1) : ℕ × ℕ × ℕ)] := by
      simp [shiftr01]; omega
    rw [e]
    exact h1

/-- 任意の梯子の元の上の単位は `RunA 0`。 -/
theorem LwA_unit11 {h : ℕ} {A : TrioSeq} (hA : LwA h A) :
    RunA 0 (h + 1) (A ++ [((h + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 1) : ℕ × ℕ × ℕ)]) :=
  ⟨h, A, _, rfl, rfl, hA, SegA_unit11 h⟩

theorem LwA_of_Aok {A : TrioSeq} (hA : Aok A) : LwA 0 A :=
  ⟨_, BaseOk_zero, LwB_of_base ⟨hA, rfl⟩⟩

theorem R296_eq : R296 = Q ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)] := rfl

/-- ★★★ `R296 = (0,0,0)(1,1,1)(1,1,0)(2,2,1)` は走りの底の元（レベル 1）。 -/
theorem R296_RunA0 : RunA 0 1 R296 := LwA_unit11 (LwA_of_Aok Aok_Q)

theorem Aok_R296 : Aok R296 := (BaseOk_RunA 0).aok _ _ R296_RunA0

/-- ★★★★ シート行306 `R296 (2,2,0) = psi(W_w + W_2)`。 -/
theorem R306_mem : R296 ++ [((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  RunG_snoc2 Iface_RunA0 0 1 R296 R296_RunA0

/-- ★★★★ シート行309 `R296 (2,2,0)(3,3,0) = psi(W_w + psi_2(W_3))`。 -/
theorem R309_mem : R296 ++ [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := RunA0_DiaV R296_RunA0 2
  simpa [DiaV] using h

/-- ★★★★ シート行310 `R296 (2,2,0)(3,3,1) = psi(W_w + psi_2(W_w))`。 -/
theorem R310_mem : R296 ++ [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine z1_mem (a := 2) (b := 2) ?_
  intro n
  cases n with
  | zero => simpa [Dtw] using R296_mem
  | succ n =>
      have e : Dtw 2 2 (n + 1) = DiaV 1 1 (n + 1) := Dtw_eq_DiaV 1 1 (n + 1)
      rw [e]
      exact RunA0_DiaV R296_RunA0 (n + 1)

#print axioms R310_mem

/-! ### z=1 の列を記録の junk として: `JkGU_z1`, `JkU_z1`。行 312〜316 -/

theorem PkGA_DiaV_W {h : ℕ} {Z : TrioSeq} (hZ : PkGA h Z) : ∀ k : ℕ, Z ++ DiaV h 2 k ∈ W 0
  | 0 => by simpa [DiaV] using (PkGA_Aok hZ).mem
  | (k + 1) => ((BaseOk_PU (2 + k)).aok _ _ (PU_DiaV (le_refl 2) (Ifc3_toIfcV Ifc3_PkGA) hZ k)).mem

/-- `PkGA` の元（頂上が `(h,2,0)`）の上に `(h+1,3,1)`。 -/
theorem PkGA_z1 {h : ℕ} {Y0 : TrioSeq} (hZ : PkGA h (Y0 ++ [((h, 2, 0) : ℕ × ℕ × ℕ)])) :
    Y0 ++ [((h, 2, 0) : ℕ × ℕ × ℕ), ((h + 1, 2 + 1, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine z1_mem ?_
  intro n
  cases n with
  | zero => simpa [Dtw] using W_dropLast (PkGA_Aok hZ).mem
  | succ n =>
      have e : Dtw (h + 1) (2 + 1) n = DiaV h 2 n := Dtw_eq_DiaV h 2 n
      rw [Dtw_cons, ← List.append_assoc, e]
      exact PkGA_DiaV_W hZ n

theorem PU_DiaV_W {y : ℕ} (hy : 1 ≤ y) {h : ℕ} {Z : TrioSeq} (hZ : PU y h Z) :
    ∀ k : ℕ, Z ++ DiaV h (y + 1) k ∈ W 0
  | 0 => by simpa [DiaV] using ((BaseOk_PU y).aok _ _ hZ).mem
  | (k + 1) => ((BaseOk_PU (y + 1 + k)).aok _ _
      (PU_DiaV (y := y + 1) (by omega) (IfcV_PU hy (y + 1 + 1) (le_refl _)) hZ k)).mem

/-- `PU y` の元（頂上が `(h,y+1,0)`）の上に `(h+1,y+2,1)`。 -/
theorem PU_z1 {y : ℕ} (hy : 1 ≤ y) {h : ℕ} {Y0 : TrioSeq}
    (hZ : PU y h (Y0 ++ [((h, y + 1, 0) : ℕ × ℕ × ℕ)])) :
    Y0 ++ [((h, y + 1, 0) : ℕ × ℕ × ℕ), ((h + 1, y + 1 + 1, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine z1_mem ?_
  intro n
  cases n with
  | zero => simpa [Dtw] using W_dropLast ((BaseOk_PU y).aok _ _ hZ).mem
  | succ n =>
      rw [Dtw_cons, ← List.append_assoc, Dtw_eq_DiaV]
      exact PU_DiaV_W hy hZ n

/-- ★★★ 2 の記録の直上の z=1 の列 `(c+2,3,1)` は普遍 junk。 -/
theorem JkGU_z1 (c : ℕ) : JkGU c [((c + 2, 3, 1) : ℕ × ℕ × ℕ)] := by
  intro E hI
  refine ⟨by simp, by intro x hx; simp only [List.mem_singleton] at hx; subst hx; show (1:ℕ) ≤ 3; omega, ?_⟩
  intro j t X hX
  have hP : PkGA (c + 1 + t) (X ++ [((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ)]) :=
    ⟨E, hI, j, c + t, X, [], by omega, hX, by rw [show c + t + 1 = c + 1 + t from by omega]; simp,
      JkGU_nil (c + t)⟩
  have h := PkGA_z1 hP
  have e : shiftr01 t 0 [((c + 2, 3, 1) : ℕ × ℕ × ℕ)] = [((c + 1 + t + 1, 2 + 1, 1) : ℕ × ℕ × ℕ)] := by
    simp [shiftr01]; omega
  rw [e]
  simpa using h

/-- ★★★ `y+1` の記録の直上の z=1 の列 `(c+2,y+2,1)` は普遍 junk。 -/
theorem JkU_z1 {y : ℕ} (hy : 2 ≤ y) (c : ℕ) : JkU y c [((c + 2, y + 2, 1) : ℕ × ℕ × ℕ)] := by
  refine ⟨by simp, by intro x hx; simp only [List.mem_singleton] at hx; subst hx; show (1:ℕ) ≤ y + 2; omega, ?_⟩
  intro E hE t Z hZ
  have hP : PU y (c + 1 + t) (Z ++ [((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)]) :=
    ⟨E, c + t, Z, [], hE, by omega, hZ, by rw [show c + t + 1 = c + 1 + t from by omega]; simp,
      JkU_nil' hy (c + t)⟩
  have h := PU_z1 (by omega) hP
  have e : shiftr01 t 0 [((c + 2, y + 2, 1) : ℕ × ℕ × ℕ)]
      = [((c + 1 + t + 1, y + 1 + 1, 1) : ℕ × ℕ × ℕ)] := by
    simp [shiftr01]; omega
  rw [e]
  simpa using h

/-! ### 行 312〜315 -/

def R310 : TrioSeq := R296 ++ [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ)]

theorem R310_PkGA : PkGA 2 R310 :=
  ⟨RunA 0, Iface_RunA0, 0, 1, R296, [((3, 3, 1) : ℕ × ℕ × ℕ)], rfl, R296_RunA0, rfl, JkGU_z1 1⟩

def R312 : TrioSeq := R310 ++ [((3, 3, 0) : ℕ × ℕ × ℕ)]

theorem R312_PU : PU 2 3 R312 :=
  ⟨PkGA, 2, R310, [], Ifc3_toIfcV Ifc3_PkGA, rfl, R310_PkGA, rfl, JkU_nil' (le_refl 2) 2⟩

/-- ★★★★ シート行312 `psi(W_w + W_3)`。 -/
theorem R312_mem : R312 ∈ W 0 := ((BaseOk_PU 2).aok _ _ R312_PU).mem

def R313 : TrioSeq := R312 ++ [((4, 4, 1) : ℕ × ℕ × ℕ)]

/-- ★★★★ シート行313 `psi(W_w + psi_3(W_w))`。 -/
theorem R313_mem : R313 ∈ W 0 := PU_z1 (y := 2) (h := 3) (Y0 := R310) (by omega) R312_PU

theorem R313_PU : PU 2 3 R313 :=
  ⟨PkGA, 2, R310, [((4, 4, 1) : ℕ × ℕ × ℕ)], Ifc3_toIfcV Ifc3_PkGA, rfl, R310_PkGA, rfl,
    JkU_z1 (le_refl 2) 2⟩

def R314 : TrioSeq := R313 ++ [((4, 4, 0) : ℕ × ℕ × ℕ)]

theorem R314_PU : PU 3 4 R314 :=
  ⟨PU 2, 3, R313, [], IfcV_PU (by omega) 4 (by omega), rfl, R313_PU, rfl, JkU_nil' (by omega) 3⟩

/-- ★★★★ シート行314 `psi(W_w + W_4)`。 -/
theorem R314_mem : R314 ∈ W 0 := ((BaseOk_PU 3).aok _ _ R314_PU).mem

theorem R314_51_mem : R314 ++ [((5, 5, 1) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  PU_z1 (y := 3) (h := 4) (Y0 := R313) (by omega) R314_PU

theorem R314_51_PU : PU 3 4 (R314 ++ [((5, 5, 1) : ℕ × ℕ × ℕ)]) :=
  ⟨PU 2, 3, R313, [((5, 5, 1) : ℕ × ℕ × ℕ)], IfcV_PU (by omega) 4 (by omega), rfl, R313_PU, rfl,
    JkU_z1 (by omega) 3⟩

def R315 : TrioSeq := R314 ++ [((5, 5, 1) : ℕ × ℕ × ℕ), ((5, 5, 0) : ℕ × ℕ × ℕ)]

theorem R315_PU : PU 4 5 R315 :=
  ⟨PU 3, 4, R314 ++ [((5, 5, 1) : ℕ × ℕ × ℕ)], [], IfcV_PU (by omega) 5 (by omega), rfl,
    R314_51_PU, rfl, JkU_nil' (by omega) 4⟩

/-- ★★★★ シート行315 `psi(W_w + W_5)`。 -/
theorem R315_mem : R315 ∈ W 0 := ((BaseOk_PU 4).aok _ _ R315_PU).mem

/-! ### 行 316 `(0,0,0)(1,1,1)(1,1,1) = psi(W_w*2)`: `Q` の複製が (1,1) ずつ上がる塔 -/

def R316 : TrioSeq := [(0, 0, 0), (1, 1, 1), (1, 1, 1)]

/-- 塔の段 `R316s n = (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,2,0)(3,3,1)…(n-1,n-1,0)(n,n,1)`。 -/
def R316s (n : ℕ) : TrioSeq :=
  (List.range n).flatMap fun k => [((k, k, 0) : ℕ × ℕ × ℕ), ((k + 1, k + 1, 1) : ℕ × ℕ × ℕ)]

theorem R316s_succ (n : ℕ) :
    R316s (n + 1) = R316s n ++ [((n, n, 0) : ℕ × ℕ × ℕ), ((n + 1, n + 1, 1) : ℕ × ℕ × ℕ)] := by
  simp [R316s, List.range_succ]

theorem R316s_three : R316s 3 = R310 := by
  simp [R316s, R310, R296, Q, List.range_succ]

theorem R316_len : R316.length = 3 := by simp [R316]

theorem nextrel0_R316_01 : nextrel0 R316 0 1 := by
  refine ⟨by simp [R316], by simp [R316], by omega, by simp [R316, entry], ?_⟩
  intro j hj; omega

theorem nextrel0_R316_02 : nextrel0 R316 0 2 := by
  refine ⟨by simp [R316], by simp [R316], by omega, by simp [R316, entry], ?_⟩
  intro j hj
  have hj1 : j = 1 := by omega
  subst hj1
  simp [R316, entry]

theorem le0_R316_01 : le0 R316 0 1 :=
  ⟨by simp [R316], by simp [R316], Relation.ReflTransGen.single nextrel0_R316_01⟩

theorem le0_R316_02 : le0 R316 0 2 :=
  ⟨by simp [R316], by simp [R316], Relation.ReflTransGen.single nextrel0_R316_02⟩

theorem nextrel1_R316_01 : nextrel1 R316 0 1 := by
  refine ⟨by simp [R316], by simp [R316], by omega, by simp [R316, entry], le0_R316_01, ?_⟩
  intro j hj
  have hjl := hj.2.1
  rw [R316_len] at hjl
  rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl <;> simp [R316, entry]

theorem nextrel1_R316_02 : nextrel1 R316 0 2 := by
  refine ⟨by simp [R316], by simp [R316], by omega, by simp [R316, entry], le0_R316_02, ?_⟩
  intro j hj
  have hjl := hj.2.1
  rw [R316_len] at hjl
  rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl <;> simp [R316, entry]

theorem le1_R316_01 : le1 R316 0 1 :=
  ⟨by simp [R316], by simp [R316], Relation.ReflTransGen.single nextrel1_R316_01⟩

theorem nextrel2_R316_02 : nextrel2 R316 0 2 := by
  refine ⟨by simp [R316], by simp [R316], by omega, by simp [R316, entry],
    ⟨by simp [R316], by simp [R316], Relation.ReflTransGen.single nextrel1_R316_02⟩, ?_⟩
  intro j hj
  have hjl := hj.2.1
  rw [R316_len] at hjl
  rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl <;> simp [R316, entry]

theorem R316_hasParent : hasParent R316 2 2 :=
  hasParent2_of_le1_witness (by rw [R316_len]; omega)
    (Relation.ReflTransGen.single nextrel1_R316_02) (by simp [R316, entry])

theorem R316_parent : parent R316 2 2 = 0 :=
  R316_hasParent.unique (parent_nextR R316_hasParent) nextrel2_R316_02

theorem R316_srow : srow R316 2 = 2 := by simp [srow, R316, entry]

theorem le0_R316_00 : le0 R316 0 0 :=
  ⟨by simp [R316], by simp [R316], Relation.ReflTransGen.refl⟩

theorem le1_R316_00 : le1 R316 0 0 :=
  ⟨by simp [R316], by simp [R316], Relation.ReflTransGen.refl⟩

open Classical in
theorem oper_R316 (n : ℕ) : R316⟦n⟧ = R316s n := by
  rw [L53.oper_unfold (j1 := 2) (i1 := 2) (j0 := 0) (d0 := 1) (d1 := 1)
      (by simp [R316]) (by omega) (by simp [R316, entry]) R316_srow.symm
      R316_hasParent R316_parent.symm (by simp [R316, entry]) (by simp [R316, entry]) n]
  have hr : List.range' 0 (2 - 0) = [0, 1] := rfl
  have htk : R316.take 0 = [] := rfl
  rw [hr, htk]
  have hbody : ∀ k : ℕ, ([0, 1] : List ℕ).map
      (fun j => ((entry R316 0 j + (if le0 R316 0 j then k * 1 else 0),
        entry R316 1 j + (if le1 R316 0 j then k * 1 else 0),
        entry R316 2 j) : ℕ × ℕ × ℕ))
      = [((k, k, 0) : ℕ × ℕ × ℕ), ((k + 1, k + 1, 1) : ℕ × ℕ × ℕ)] := by
    intro k
    simp only [List.map_cons, List.map_nil]
    rw [if_pos le0_R316_00, if_pos le1_R316_00, if_pos le0_R316_01, if_pos le1_R316_01]
    simp [R316, entry, Nat.add_comm]
  rw [List.flatMap_congr (fun k _ => hbody k)]
  simp [R316s]

/-- 段の連鎖: `R316s (n+3) ++ (n+3,n+3,0) + junk J ∈ PU (n+2)`。 -/
theorem R316s_chain : ∀ (n : ℕ) (J : TrioSeq), JkU (n + 2) (n + 2) J →
    PU (n + 2) (n + 3) (R316s (n + 3) ++ ([((n + 3, n + 2 + 1, 0) : ℕ × ℕ × ℕ)] ++ J))
  | 0, J, hJ => ⟨PkGA, 2, R316s 3, J, Ifc3_toIfcV Ifc3_PkGA, rfl, by rw [R316s_three]; exact R310_PkGA,
      rfl, hJ⟩
  | (n + 1), J, hJ => by
      have hZ := R316s_chain n [((n + 2 + 2, n + 2 + 2, 1) : ℕ × ℕ × ℕ)] (JkU_z1 (by omega) (n + 2))
      refine ⟨PU (n + 2), n + 3, _, J, IfcV_PU (by omega) (n + 1 + 2 + 1) (by omega), rfl, hZ, ?_, hJ⟩
      rw [R316s_succ (n + 3)]
      simp [List.append_assoc]

theorem R316s_mem : ∀ n : ℕ, R316s n ∈ W 0
  | 0 => by simpa [R316s] using W_nil 0
  | 1 => by simpa [R316s, Q] using Q_mem
  | 2 => by
      have h := R296_mem
      simpa [R316s, R296, List.range_succ] using h
  | 3 => by rw [R316s_three]; exact R310_mem
  | (n + 4) => by
      have h := PU_z1 (y := n + 2) (h := n + 3) (Y0 := R316s (n + 3)) (by omega)
        (by simpa using R316s_chain n [] (JkU_nil' (by omega) (n + 2)))
      rw [R316s_succ (n + 3)]
      simpa [show n + 3 + 1 = n + 4 from by omega, show n + 2 + 1 + 1 = n + 4 from by omega,
        show n + 2 + 1 = n + 3 from by omega] using h

/-- ★★★★★ シート行316 `(0,0,0)(1,1,1)(1,1,1) = psi(W_w*2) ∈ W 0`。 -/
theorem R316_mem : R316 ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_R316 n]
  exact R316s_mem n

#print axioms R316_mem

/-! ### 梯子の段としての単位 `(h+1,1,0)(h+2,2,1)`、`Yn`、行 297〜305, 308, 311 -/

def P0 : ℕ → TrioSeq → Prop := fun h A => Aok A ∧ h = 0

theorem BaseOk_P0 : BaseOk P0 := BaseOk_zero

/-- 梯子の元の上に単位を継ぐと段が 1 つ上がる。 -/
theorem LvB_unit11 {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) {r h : ℕ} {A : TrioSeq}
    (hA : LvB P r h A) :
    LvB P (r + 1) (h + 1) (A ++ [((h + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 1) : ℕ × ℕ × ℕ)]) := by
  refine ⟨(BaseOk_RunA 0).aok _ _ (LwA_unit11 ⟨P, hP, r, hA⟩), Or.inr ⟨h, A, _, rfl, rfl, hA,
    (SegA_unit11 h).mid, ?_⟩⟩
  intro s A' hA'
  exact (SegA_unit11 h).reapp P hP s A' ⟨r, hA'⟩

/-- `Yn n = Q (1,1,0)(2,2,1)(2,1,0)(3,2,1)…(n,1,0)(n+1,2,1)`。`Yn 1 = R296`。 -/
def Yn : ℕ → TrioSeq
  | 0 => Q
  | (n + 1) => Yn n ++ [((n + 1, 1, 0) : ℕ × ℕ × ℕ), ((n + 2, 2, 1) : ℕ × ℕ × ℕ)]

theorem Yn_LvB : ∀ n : ℕ, LvB P0 n n (Yn n)
  | 0 => ⟨Aok_Q, rfl⟩
  | (n + 1) => LvB_unit11 BaseOk_P0 (Yn_LvB n)

theorem Yn_one : Yn 1 = R296 := rfl

theorem Yn_LwA (n : ℕ) : LwA n (Yn n) := ⟨P0, BaseOk_P0, n, Yn_LvB n⟩

theorem Yn_Aok (n : ℕ) : Aok (Yn n) := LwA_Aok (Yn_LwA n)

/-- 塔 `TwD d Y n` は「レベル `d-1` の吊るし」があれば `W 0`。 -/
theorem TwD_mem_of_hang {Y : TrioSeq} {d : ℕ} (hd : 1 ≤ d) (hY : Aok Y)
    (hang : ∀ B : TrioSeq, Bok B → Y ++ shiftr01 d 0 B ∈ W 0) : ∀ n, TwD d Y n ∈ W 0
  | 0 => by simpa [TwD] using W_nil 0
  | (n + 1) => by
      rw [TwD_succ]
      exact hang (TwD d Y n) ⟨TwD_mem_of_hang hd hY hang n, TwD_zroot hd hY.zroot n,
        TwD_mono hY.mono n, TwD_root hY.ne hY.deep.1 n⟩

/-- 根以外の列の row1 が正なら `Ancd d`。 -/
theorem Ancd_of_row1 {Y : TrioSeq} (h : ∀ j, 0 < j → j < Y.length → 1 ≤ entry Y 1 j) (d : ℕ) :
    Ancd d Y := fun j hj0 hjl _ _ => h j hj0 hjl

theorem snocd_gen {Y : TrioSeq} {d : ℕ} (hd : 1 ≤ d) (hY : Aok Y) (hsh : Ancd d Y)
    (hang : ∀ B : TrioSeq, Bok B → Y ++ shiftr01 d 0 B ∈ W 0) :
    Y ++ [((d, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  snocd_mem hd hY.ne hY.deep hY.zroot hsh (TwD_mem_of_hang hd hY hang)

theorem R296_row1 : ∀ j, 0 < j → j < R296.length → 1 ≤ entry R296 1 j := by
  intro j hj0 hjl
  rw [R296_len] at hjl
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl <;> simp [R296, entry]

/-- ★★★★ シート行297 `R296 (1,1,0) = psi(W_w + psi_1(W_w) + W)`。 -/
theorem R297_mem : R296 ++ [((1, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  snocd_gen (by omega) Aok_R296 (Ancd_of_row1 R296_row1 1)
    (fun B hB => BaseOk_zero.hang 0 R296 ⟨Aok_R296, rfl⟩ B hB)

theorem R297_RunA0 : RunA 0 1 (R296 ++ [((1, 1, 0) : ℕ × ℕ × ℕ)]) :=
  ⟨0, R296, _, rfl, rfl, LwA_of_Aok Aok_R296, SegA_one 0⟩

/-- ★★★★ シート行298 `R296 (1,1,0)(2,2,1) = psi(W_w + psi_1(W_w)*2)`。 -/
theorem R298_mem : R296 ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  RunA0_z1 (h := 1) R297_RunA0

/-- ★★★★ シート行300 `R296 (2,1,0) = psi(W_w + psi_1(W_w)*W)`。 -/
theorem R300_mem : R296 ++ [((2, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  snocd_gen (by omega) Aok_R296 (Ancd_of_row1 R296_row1 2)
    (fun B hB => LvB_hang BaseOk_P0 1 1 R296 (Yn_LvB 1) B hB)

def R300 : TrioSeq := R296 ++ [((2, 1, 0) : ℕ × ℕ × ℕ)]

theorem R300_RunA0 : RunA 0 2 R300 := ⟨1, R296, _, rfl, rfl, Yn_LwA 1, SegA_one 1⟩

theorem Aok_R300 : Aok R300 := (BaseOk_RunA 0).aok _ _ R300_RunA0

theorem R300_row1 : ∀ j, 0 < j → j < R300.length → 1 ≤ entry R300 1 j := by
  intro j hj0 hjl
  simp only [R300, R296, List.length_append, List.length_cons, List.length_nil] at hjl
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl <;>
    simp [R300, R296, entry]

/-- ★★★★ シート行301 `R296 (2,1,0)(3,1,0) = psi(W_w + psi_1(W_w)*W^W)`。 -/
theorem R301_mem : R300 ++ [((3, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  snocd_gen (by omega) Aok_R300 (Ancd_of_row1 R300_row1 3)
    (fun B hB => (BaseOk_RunA 0).hang 2 R300 R300_RunA0 B hB)

/-- ★★★★ シート行302 `R296 (2,1,0)(3,2,0) = psi(W_w + psi_1(W_w)*psi_1(W_2))`。 -/
theorem R302_mem : R300 ++ [((3, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := snocY_mem (Y0 := R296) (M := [((2, 1, 0) : ℕ × ℕ × ℕ)]) (L := 2) (y := 2)
    Aok_R296.ne (MidD_col 2 1 (by omega) (by omega)) (by simp [entry]) (by omega)
    (fun n => by
      have h1 := LwB_tower BaseOk_P0 (SegA_toSegB (SegA_one 1) BaseOk_P0) ⟨1, Yn_LvB 1⟩ n
      exact (LwB_Aok BaseOk_P0 h1).mem)
  exact h

/-- ★★★★ シート行303 `R296 (2,1,0)(3,2,1) = psi(W_w + psi_1(W_w)^2)`。 -/
theorem R303_mem : R296 ++ [((2, 1, 0) : ℕ × ℕ × ℕ), ((3, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  RunA0_z1 (h := 2) R300_RunA0

theorem Yn_two : Yn 2 = R296 ++ [((2, 1, 0) : ℕ × ℕ × ℕ), ((3, 2, 1) : ℕ × ℕ × ℕ)] := rfl

theorem Yn2_row1 : ∀ j, 0 < j → j < (Yn 2).length → 1 ≤ entry (Yn 2) 1 j := by
  intro j hj0 hjl
  simp only [Yn, Q, List.length_append, List.length_cons, List.length_nil] at hjl
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with rfl | rfl | rfl | rfl | rfl <;>
    simp [Yn, Q, entry]

/-- ★★★★ シート行304 `R296 (2,1,0)(3,2,1)(3,1,0) = psi(W_w + psi_1(W_w)^W)`。 -/
theorem R304_mem : Yn 2 ++ [((3, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  snocd_gen (by omega) (Yn_Aok 2) (Ancd_of_row1 Yn2_row1 3)
    (fun B hB => LvB_hang BaseOk_P0 2 2 (Yn 2) (Yn_LvB 2) B hB)

theorem R304_RunA0 : RunA 0 3 (Yn 2 ++ [((3, 1, 0) : ℕ × ℕ × ℕ)]) :=
  ⟨2, Yn 2, _, rfl, rfl, Yn_LwA 2, SegA_one 2⟩

/-- ★★★★ シート行305 `R296 (2,1,0)(3,2,1)(3,1,0)(4,2,1) = psi(W_w + psi_1(W_w)^psi_1(W_w))`。 -/
theorem R305_mem : Yn 2 ++ [((3, 1, 0) : ℕ × ℕ × ℕ), ((4, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  RunA0_z1 (h := 3) R304_RunA0

/-! ### 行 299 `R296 (2,0,0)`: 平坦な複製 `Q ((1,1,0)(2,2,1))^n` -/

def R299 : TrioSeq := R296 ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]

theorem R299_len : R299.length = 5 := by simp [R299, R296]

theorem nextrel0_R299_24 : nextrel0 R299 2 4 := by
  refine ⟨by simp [R299, R296], by simp [R299, R296], by omega, by simp [R299, R296, entry], ?_⟩
  intro j hj
  have hj3 : j = 3 := by omega
  subst hj3
  simp [R299, R296, entry]

theorem hasParent0_R299 : hasParent R299 0 4 := by
  refine ⟨2, by show nextR R299 0 2 4; simp only [nextR, if_true]; exact nextrel0_R299_24, ?_⟩
  intro j0 hj0
  change nextR R299 0 j0 4 at hj0
  simp only [nextR, if_true] at hj0
  obtain ⟨hj0l, -, hlt, hlt2, hall⟩ := hj0
  rw [R299_len] at hj0l
  rcases j0 with _ | _ | _ | _ | j0
  · exfalso; have := hall 2 ⟨by omega, by omega⟩; simp [R299, R296, entry] at this
  · exfalso; have := hall 2 ⟨by omega, by omega⟩; simp [R299, R296, entry] at this
  · rfl
  · exfalso; simp [R299, R296, entry] at hlt2
  · omega

theorem parent0_R299 : parent R299 0 4 = 2 :=
  hasParent0_R299.unique (parent_nextR hasParent0_R299)
    (by show nextR R299 0 2 4; simp only [nextR, if_true]; exact nextrel0_R299_24)

/-- `Un n = Q ((1,1,0)(2,2,1))^n`。 -/
def Un (n : ℕ) : TrioSeq :=
  Q ++ (List.range n).flatMap fun _ => [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)]

theorem Un_succ (n : ℕ) : Un (n + 1) = Un n ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)] := by
  simp [Un, List.range_succ]

open Classical in
theorem oper_R299 (n : ℕ) : R299⟦n⟧ = Un n := by
  rw [L53.oper_flat (j1 := 4) (j0 := 2) (by rw [R299_len]) (by omega)
    (by simp [R299, R296, entry]) (by simp [srow, R299, R296, entry])
    hasParent0_R299 parent0_R299.symm n]
  simp [R299, R296, Q, Un, entry, List.range']

theorem Un_Aok : ∀ n : ℕ, Aok (Un n)
  | 0 => by simpa [Un] using Aok_Q
  | (n + 1) => by
      rw [Un_succ]
      have hR : RunA 0 1 (Un n ++ [((1, 1, 0) : ℕ × ℕ × ℕ)]) :=
        ⟨0, Un n, _, rfl, rfl, LwA_of_Aok (Un_Aok n), SegA_one 0⟩
      exact Aok_append_Mid (by omega) (Un_Aok n) (SegA_unit11 0).mid (RunA0_z1 (h := 1) hR)

/-- ★★★★ シート行299 `R296 (2,0,0) = psi(W_w + psi_1(W_w)*w)`。 -/
theorem R299_mem : R299 ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_R299 n]
  exact (Un_Aok n).mem

/-! ### 行 308 `R296 (2,2,0)(3,2,0)`、行 311 `R296 (2,2,0)(3,3,1)(3,2,0)`: 歩幅 2 の塔 -/

def M308 : TrioSeq := [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ)]

theorem MidD_M308 : MidD 2 M308 := by
  refine MidD_append (MidD_col 1 1 (by omega) (by omega)) ?_ ?_
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp

theorem R308_stage : ∀ n : ℕ, PkGA (2 * n + 2) (Mtwd 2 Q M308 (n + 1))
  | 0 => by
      rw [Mtwd_one]
      exact ⟨RunA 0, Iface_RunA0, 0, 1, R296, [], rfl, R296_RunA0, rfl, JkGU_nil 1⟩
  | (n + 1) => by
      rw [Mtwd_succ]
      have ih := R308_stage n
      have hR := LwA_unit11 (h := 2 * n + 2) ⟨PkGA, BaseOk_PkGA, LwB_of_base ih⟩
      have hP : PkGA (2 * n + 2 + 1 + 1) (Mtwd 2 Q M308 (n + 1) ++
          [((2 * n + 2 + 1, 1, 0) : ℕ × ℕ × ℕ), ((2 * n + 2 + 2, 2, 1) : ℕ × ℕ × ℕ)] ++
          ([((2 * n + 2 + 1 + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ [])) :=
        ⟨RunA 0, Iface_RunA0, 0, 2 * n + 2 + 1, _, [], rfl, hR, rfl, JkGU_nil _⟩
      have e : shiftr01 (2 * (n + 1)) 0 M308 =
          [((2 * n + 2 + 1, 1, 0) : ℕ × ℕ × ℕ), ((2 * n + 2 + 2, 2, 1) : ℕ × ℕ × ℕ)] ++
          ([((2 * n + 2 + 1 + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ []) := by
        simp [M308, shiftr01]; omega
      rw [e, ← List.append_assoc, show 2 * (n + 1) + 2 = 2 * n + 2 + 1 + 1 from by omega]
      exact hP

/-- ★★★★ シート行308 `R296 (2,2,0)(3,2,0) = psi(W_w + W_2^2)`。 -/
theorem R308_mem : R296 ++ [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := snocYd_mem (Y0 := Q) (M := M308) (L := 1) (y := 2) (dl := 2) Q_ne MidD_M308
    (by simp [M308, entry]) ?_ (by omega) (by omega) ?_
  · simpa [M308, R296, Q] using h
  · intro t ht1 htl hlt hrec
    simp only [M308, List.length_cons, List.length_nil] at htl
    rcases (show t = 1 ∨ t = 2 by omega) with rfl | rfl
    · exfalso
      have := hrec 2 (by omega) (by simp [M308])
      simp [M308, entry] at this
    · simp [M308, entry]
  · intro n
    cases n with
    | zero => rw [Mtwd_zero]; exact Q_mem
    | succ n => exact (PkGA_Aok (R308_stage n)).mem

def M311 : TrioSeq := M308 ++ [((3, 3, 1) : ℕ × ℕ × ℕ)]

theorem MidD_M311 : MidD 2 M311 := by
  refine MidD_append MidD_M308 ?_ ?_
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp

theorem R311_stage : ∀ n : ℕ, PkGA (2 * n + 2) (Mtwd 2 Q M311 (n + 1))
  | 0 => by
      rw [Mtwd_one]
      exact ⟨RunA 0, Iface_RunA0, 0, 1, R296, [((3, 3, 1) : ℕ × ℕ × ℕ)], rfl, R296_RunA0, rfl,
        JkGU_z1 1⟩
  | (n + 1) => by
      rw [Mtwd_succ]
      have ih := R311_stage n
      have hR := LwA_unit11 (h := 2 * n + 2) ⟨PkGA, BaseOk_PkGA, LwB_of_base ih⟩
      have hP : PkGA (2 * n + 2 + 1 + 1) (Mtwd 2 Q M311 (n + 1) ++
          [((2 * n + 2 + 1, 1, 0) : ℕ × ℕ × ℕ), ((2 * n + 2 + 2, 2, 1) : ℕ × ℕ × ℕ)] ++
          ([((2 * n + 2 + 1 + 1, 2, 0) : ℕ × ℕ × ℕ)] ++
            [((2 * n + 2 + 1 + 2, 3, 1) : ℕ × ℕ × ℕ)])) :=
        ⟨RunA 0, Iface_RunA0, 0, 2 * n + 2 + 1, _, [((2 * n + 2 + 1 + 2, 3, 1) : ℕ × ℕ × ℕ)], rfl,
          hR, rfl, JkGU_z1 _⟩
      have e : shiftr01 (2 * (n + 1)) 0 M311 =
          [((2 * n + 2 + 1, 1, 0) : ℕ × ℕ × ℕ), ((2 * n + 2 + 2, 2, 1) : ℕ × ℕ × ℕ)] ++
          ([((2 * n + 2 + 1 + 1, 2, 0) : ℕ × ℕ × ℕ)] ++
            [((2 * n + 2 + 1 + 2, 3, 1) : ℕ × ℕ × ℕ)]) := by
        simp [M311, M308, shiftr01]; omega
      rw [e, ← List.append_assoc, show 2 * (n + 1) + 2 = 2 * n + 2 + 1 + 1 from by omega]
      exact hP

/-- ★★★★ シート行311 `R296 (2,2,0)(3,3,1)(3,2,0) = psi(W_w + psi_2(W_w)*W_2)`。 -/
theorem R311_mem : R310 ++ [((3, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := snocYd_mem (Y0 := Q) (M := M311) (L := 1) (y := 2) (dl := 2) Q_ne MidD_M311
    (by simp [M311, M308, entry]) ?_ (by omega) (by omega) ?_
  · simpa [M311, M308, R310, R296, Q] using h
  · intro t ht1 htl hlt hrec
    simp only [M311, M308, List.length_append, List.length_cons, List.length_nil] at htl
    rcases (show t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl
    · exfalso
      have := hrec 2 (by omega) (by simp [M311, M308])
      simp [M311, M308, entry] at this
    · simp [M311, M308, entry]
    · exfalso; simp [M311, M308, entry] at hlt
  · intro n
    cases n with
    | zero => rw [Mtwd_zero]; exact Q_mem
    | succ n => exact (PkGA_Aok (R311_stage n)).mem

#print axioms R299_mem
#print axioms R305_mem
#print axioms R308_mem
#print axioms R311_mem

/-! ### 行306 の上の 2 本目のブロック `R306 (2,1,0)(3,2,1)(3,2,0)`

シート行306 `psi(W_w + W_2)` と行307 `psi(W_w + W_2*2)` の間にある標準形
（シートは主脈だけなので飛ばしている）。`(1,1,0)` の下にブロックが 2 本ぶら下がる:

    X (1,1,0) [ (2,2,1)(2,2,0) ] [ (2,1,0)(3,2,1)(3,2,0) ]

台座 `R306 = Q ++ M308` を梯子 `LvB P0 1 1` の元として捉えれば、
行300 → 行303 → 行302 と同じ 3 手（`snocd_gen` → `RunA0_z1` → `snocYd_mem`）で閉じる。 -/

def R306 : TrioSeq := R296 ++ [((2, 2, 0) : ℕ × ℕ × ℕ)]

theorem R306_QM : R306 = Q ++ M308 := by simp [R306, R296, Q, M308]

theorem R306_len : R306.length = 5 := by simp [R306, R296]

theorem Aok_R306 : Aok R306 :=
  Aok_append_Mid (by omega) Aok_R296 (MidD_col 2 2 (by omega) (by omega)) R306_mem

/-- ★ どの梯子の頭 `LwA h A` の上にも `M308` を（高さ `h` だけ持ち上げて）継げる。 -/
theorem M308_reattach_gen {h : ℕ} {A : TrioSeq} (hA : LwA h A) :
    A ++ shiftr01 h 0 M308 ∈ W 0 := by
  have hz := RunG_snoc2 Iface_RunA0 0 (h + 1)
    (A ++ [((h + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 1) : ℕ × ℕ × ℕ)])
    (LwA_unit11 hA)
  have e : shiftr01 h 0 M308
      = [((h + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 1) : ℕ × ℕ × ℕ)]
        ++ [((h + 1 + 1, 2, 0) : ℕ × ℕ × ℕ)] := by
    simp only [M308, shiftr01, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.cons.injEq, Prod.mk.injEq, and_true, and_self]
    omega
  rw [e, ← List.append_assoc]
  exact hz

/-- どの `Aok` の頭の上にも `M308 = (1,1,0)(2,2,1)(2,2,0)` を継げる。 -/
theorem M308_reattach {A : TrioSeq} (hA : Aok A) : A ++ M308 ∈ W 0 := by
  simpa using M308_reattach_gen (LwA_of_Aok hA)

/-- ★ `R306` は梯子のレベル 1 の元（台座 `Q`、単位 `M308`）。 -/
theorem R306_LvB : LvB P0 1 1 R306 := by
  refine ⟨Aok_R306, Or.inr ⟨0, Q, M308, rfl, R306_QM, ⟨Aok_Q, rfl⟩, MidD_M308, ?_⟩⟩
  rintro s A' ⟨hA', hs⟩
  have hs0 : s = 0 := by omega
  subst hs0
  simpa using M308_reattach hA'

theorem R306_LwA : LwA 1 R306 := ⟨P0, BaseOk_P0, 1, R306_LvB⟩

theorem R306_row1 : ∀ j, 0 < j → j < R306.length → 1 ≤ entry R306 1 j := by
  intro j hj0 hjl
  rw [R306_len] at hjl
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl <;>
    simp [R306, R296, entry]

/-- `R306 (2,1,0)`。 -/
theorem R306a_mem : R306 ++ [((2, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  snocd_gen (by omega) Aok_R306 (Ancd_of_row1 R306_row1 2)
    (fun B hB => LvB_hang BaseOk_P0 1 1 R306 R306_LvB B hB)

theorem R306a_RunA0 : RunA 0 2 (R306 ++ [((2, 1, 0) : ℕ × ℕ × ℕ)]) :=
  ⟨1, R306, _, rfl, rfl, R306_LwA, SegA_one 1⟩

/-- `R306 (2,1,0)(3,2,1)`。 -/
theorem R306b_mem :
    R306 ++ [((2, 1, 0) : ℕ × ℕ × ℕ), ((3, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  RunA0_z1 (h := 2) R306a_RunA0

/-- 2 本目のブロックの繰り返し単位。 -/
def MzB : TrioSeq := [((2, 1, 0) : ℕ × ℕ × ℕ), ((3, 2, 1) : ℕ × ℕ × ℕ)]

theorem MidD_MzB : MidD 3 MzB := by
  refine MidD_append (MidD_col 2 1 (by omega) (by omega)) ?_ ?_
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp
  · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp

/-- 塔 `Zn n = R306 (2,1,0)(3,2,1)(3,1,0)(4,2,1)…(n+1,1,0)(n+2,2,1)`。 -/
def Zn : ℕ → TrioSeq
  | 0 => R306
  | (n + 1) => Zn n ++ [((n + 2, 1, 0) : ℕ × ℕ × ℕ), ((n + 3, 2, 1) : ℕ × ℕ × ℕ)]

theorem Zn_LvB : ∀ n : ℕ, LvB P0 (n + 1) (n + 1) (Zn n)
  | 0 => R306_LvB
  | (n + 1) => LvB_unit11 BaseOk_P0 (Zn_LvB n)

theorem Zn_mem (n : ℕ) : Zn n ∈ W 0 := (LwA_Aok ⟨P0, BaseOk_P0, n + 1, Zn_LvB n⟩).mem

theorem Zn_eq : ∀ n : ℕ, Mtwd 1 R306 MzB n = Zn n
  | 0 => by simp [Mtwd, Zn]
  | (n + 1) => by
      rw [Mtwd_succ, Zn_eq n]
      show Zn n ++ shiftr01 (1 * n) 0 MzB
        = Zn n ++ [((n + 2, 1, 0) : ℕ × ℕ × ℕ), ((n + 3, 2, 1) : ℕ × ℕ × ℕ)]
      congr 1
      simp only [MzB, shiftr01, List.map_cons, List.map_nil]
      rw [show 2 + 1 * n = n + 2 from by omega, show 3 + 1 * n = n + 3 from by omega]

/-- ★★★★ `R306 (2,1,0)(3,2,1)(3,2,0)`（シート行306 と行307 の間）。 -/
theorem R306c_mem :
    R306 ++ [((2, 1, 0) : ℕ × ℕ × ℕ), ((3, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ)]
      ∈ W 0 := by
  have h := snocYd_mem (Y0 := R306) (M := MzB) (L := 2) (y := 2) (dl := 1)
    Aok_R306.ne MidD_MzB (by simp [MzB, entry]) ?_ (by omega) (by omega) ?_
  · simpa [MzB, List.append_assoc] using h
  · intro t ht1 htl hlt _
    exfalso
    rcases (show t = 1 by simp only [MzB, List.length_cons, List.length_nil] at htl; omega) with rfl
    simp [MzB, entry] at hlt
  · intro n
    rw [Zn_eq]
    exact Zn_mem n

#print axioms R306c_mem

/-- 塔の 3 段目。`Zn 3` を展開して書いたもの。 -/
theorem Zn_three : Zn 3 =
    [((0, 0, 0) : ℕ × ℕ × ℕ), (1, 1, 1), (1, 1, 0), (2, 2, 1), (2, 2, 0),
     (2, 1, 0), (3, 2, 1), (3, 1, 0), (4, 2, 1), (4, 1, 0), (5, 2, 1)] := by
  simp [Zn, R306, R296]

/-- ★★★★ `R306 (2,1,0)(3,2,1)(3,1,0)(4,2,1)(4,1,0)(5,2,1)`（塔の 3 段目）。 -/
theorem R306d_mem :
    ([((0, 0, 0) : ℕ × ℕ × ℕ), (1, 1, 1), (1, 1, 0), (2, 2, 1), (2, 2, 0),
      (2, 1, 0), (3, 2, 1), (3, 1, 0), (4, 2, 1), (4, 1, 0), (5, 2, 1)] : TrioSeq) ∈ W 0 := by
  rw [← Zn_three]
  exact Zn_mem 3

#print axioms R306d_mem

/-! ### シート行307 `R296 (2,2,0)(2,2,0) = psi(W_w + W_2*2)`

展開は「単位 `M308 = (1,1,0)(2,2,1)(2,2,0)` を歩幅 1 で積む」塔
`Mtwd 1 Q M308 n`。各段は `M308_reattach_gen` で 1 段ずつ伸び、
同時に梯子の段 `LvB P0 n n` も 1 つ上がる。 -/

/-- 塔 `Wn n = Q ++ M308 ++ M308↑1 ++ … ++ M308↑(n-1)`。 -/
def Wn : ℕ → TrioSeq
  | 0 => Q
  | (n + 1) => Wn n ++ shiftr01 n 0 M308

theorem MidD_M308_shift (n : ℕ) : MidD (n + 2) (shiftr01 n 0 M308) := by
  have h := MidD_shift MidD_M308 n
  rwa [show 2 + n = n + 2 from by omega] at h

theorem Wn_LvB : ∀ n : ℕ, LvB P0 n n (Wn n)
  | 0 => ⟨Aok_Q, rfl⟩
  | (n + 1) => by
      have hlw : LwA n (Wn n) := ⟨P0, BaseOk_P0, n, Wn_LvB n⟩
      have hmem : Wn n ++ shiftr01 n 0 M308 ∈ W 0 := M308_reattach_gen hlw
      refine ⟨Aok_append_Mid (by omega) (LwA_Aok hlw) (MidD_M308_shift n) hmem, Or.inr
        ⟨n, Wn n, shiftr01 n 0 M308, rfl, rfl, Wn_LvB n, MidD_M308_shift n, ?_⟩⟩
      intro s A' hA'
      rw [shiftr01_add0]
      exact M308_reattach_gen ⟨P0, BaseOk_P0, n, hA'⟩

theorem Wn_mem (n : ℕ) : Wn n ∈ W 0 := (LwA_Aok ⟨P0, BaseOk_P0, n, Wn_LvB n⟩).mem

theorem Wn_eq : ∀ n : ℕ, Mtwd 1 Q M308 n = Wn n
  | 0 => by simp [Mtwd, Wn]
  | (n + 1) => by
      rw [Mtwd_succ, Wn_eq n, Nat.one_mul]
      rfl

/-- ★★★★ シート行307 `R296 (2,2,0)(2,2,0) = psi(W_w + W_2*2)`。 -/
theorem R307_mem : R306 ++ [((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := snocYd_mem (Y0 := Q) (M := M308) (L := 1) (y := 2) (dl := 1)
    Q_ne MidD_M308 (by simp [M308, entry]) ?_ (by omega) (by omega) ?_
  · rw [R306_QM]; simpa using h
  · intro t ht1 htl hlt _
    exfalso
    simp only [M308, List.length_cons, List.length_nil] at htl
    rcases (show t = 1 ∨ t = 2 by omega) with rfl | rfl <;> simp [M308, entry] at hlt
  · intro n
    rw [Wn_eq]
    exact Wn_mem n

#print axioms R307_mem

/-! ### z=1 の列 `m` 本: `(Y0 ++ (a,b,0) ++ (a+1,b+1,1)^(m+1))⟦n⟧ = Y0 ++ Dzm a b m n` -/

/-- `Dzm a b m n = ⋃_{k<n} (a+k,b+k,0) (a+1+k,b+1+k,1)^m`。 -/
def Dzm (a b m n : ℕ) : TrioSeq :=
  (List.range n).flatMap fun k =>
    ((a + k, b + k, 0) : ℕ × ℕ × ℕ) :: List.replicate m ((a + 1 + k, b + 1 + k, 1) : ℕ × ℕ × ℕ)

theorem Dzm_succ (a b m n : ℕ) : Dzm a b m (n + 1) = Dzm a b m n ++
    (((a + n, b + n, 0) : ℕ × ℕ × ℕ) :: List.replicate m ((a + 1 + n, b + 1 + n, 1) : ℕ × ℕ × ℕ)) := by
  simp [Dzm, List.range_succ]

theorem Dzm_cons (a b m : ℕ) : ∀ n : ℕ, Dzm a b m (n + 1) =
    (((a, b, 0) : ℕ × ℕ × ℕ) :: List.replicate m ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)) ++
      Dzm (a + 1) (b + 1) m n
  | 0 => by simp [Dzm]
  | (n + 1) => by
      rw [Dzm_succ, Dzm_cons a b m n, Dzm_succ (a + 1) (b + 1) m n, List.append_assoc,
        show a + (n + 1) = a + 1 + n from by omega, show b + (n + 1) = b + 1 + n from by omega,
        show a + 1 + (n + 1) = a + 1 + 1 + n from by omega,
        show b + 1 + (n + 1) = b + 1 + 1 + n from by omega]

theorem entry_replicate_lt {c : ℕ × ℕ × ℕ} {n q : ℕ} (hq : q < n) (i : ℕ) :
    entry (List.replicate n c) i q = entry [c] i 0 := by
  simp [entry, List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt hq]

open Classical in
theorem oper_z1m (Y0 : TrioSeq) (a b m n : ℕ) :
    (Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: List.replicate (m + 1) ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)))⟦n⟧
      = Y0 ++ Dzm a b m n := by
  set T : TrioSeq := ((a, b, 0) : ℕ × ℕ × ℕ) :: List.replicate (m + 1) ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)
    with hT
  set M : TrioSeq := Y0 ++ T with hM
  set p := Y0.length with hp
  have hlen : M.length = p + m + 2 := by simp [hM, hT, hp]; omega
  have eT : ∀ i q, entry M i (p + q) = entry T i q := fun i q => entry_append_right Y0 T i q
  have e0p : entry M 0 p = a := by rw [show p = p + 0 from rfl, eT]; simp [hT, entry]
  have e1p : entry M 1 p = b := by rw [show p = p + 0 from rfl, eT]; simp [hT, entry]
  have e2p : entry M 2 p = 0 := by rw [show p = p + 0 from rfl, eT]; simp [hT, entry]
  have eq : ∀ i, i < m + 1 → entry M 0 (p + 1 + i) = a + 1 ∧ entry M 1 (p + 1 + i) = b + 1 ∧
      entry M 2 (p + 1 + i) = 1 := by
    intro i hi
    rw [show p + 1 + i = p + (i + 1) from by omega, eT, eT, eT]
    simp only [hT, entry, List.getD_cons_succ]
    simp [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt hi]
  have hn0 : ∀ i, i < m + 1 → nextrel0 M p (p + 1 + i) := by
    intro i hi
    refine ⟨by omega, by omega, by omega, by rw [e0p, (eq i hi).1]; omega, ?_⟩
    intro j hj
    obtain ⟨i', hi', rfl⟩ : ∃ i', i' < m + 1 ∧ j = p + 1 + i' := ⟨j - (p + 1), by omega, by omega⟩
    rw [(eq i hi).1, (eq i' hi').1]
  have hl0 : ∀ i, i < m + 1 → le0 M p (p + 1 + i) := fun i hi =>
    ⟨by omega, by omega, Relation.ReflTransGen.single (hn0 i hi)⟩
  have hn1 : ∀ i, i < m + 1 → nextrel1 M p (p + 1 + i) := by
    intro i hi
    refine ⟨by omega, by omega, by omega, by rw [e1p, (eq i hi).2.1]; omega, hl0 i hi, ?_⟩
    intro j hj
    have hjl := hj.2.1
    obtain ⟨i', hi', rfl⟩ : ∃ i', i' < m + 1 ∧ j = p + 1 + i' := ⟨j - (p + 1), by omega, by omega⟩
    rw [(eq i hi).2.1, (eq i' hi').2.1]
  have hl1 : ∀ i, i < m + 1 → le1 M p (p + 1 + i) := fun i hi =>
    ⟨by omega, by omega, Relation.ReflTransGen.single (hn1 i hi)⟩
  have hn2 : nextrel2 M p (p + 1 + m) := by
    refine ⟨by omega, by omega, by omega, by rw [e2p, (eq m (by omega)).2.2]; omega,
      hl1 m (by omega), ?_⟩
    intro j hj
    have hjl := hj.2.1
    obtain ⟨i', hi', rfl⟩ : ∃ i', i' < m + 1 ∧ j = p + 1 + i' := ⟨j - (p + 1), by omega, by omega⟩
    rw [(eq m (by omega)).2.2, (eq i' hi').2.2]
  have hpar : hasParent M 2 (p + 1 + m) :=
    hasParent2_of_le1_witness (by omega) (Relation.ReflTransGen.single (hn1 m (by omega)))
      (by rw [e2p, (eq m (by omega)).2.2]; omega)
  have hparent : parent M 2 (p + 1 + m) = p := hpar.unique (parent_nextR hpar) hn2
  have hsrow : srow M (p + 1 + m) = 2 := by simp [srow, (eq m (by omega)).2.2]
  have hl00 : le0 M p p := ⟨by omega, by omega, Relation.ReflTransGen.refl⟩
  have hl11 : le1 M p p := ⟨by omega, by omega, Relation.ReflTransGen.refl⟩
  rw [L53.oper_unfold (j1 := p + 1 + m) (i1 := 2) (j0 := p) (d0 := 1) (d1 := 1)
      (by omega) (by omega) (by rw [(eq m (by omega)).1]; omega) hsrow.symm hpar hparent.symm
      (by rw [if_pos (by omega : 0 < 2), (eq m (by omega)).1, e0p]; omega)
      (by rw [if_pos (by omega : 1 < 2), (eq m (by omega)).2.1, e1p]; omega) n]
  have hr : List.range' p (p + 1 + m - p) = p :: List.range' (p + 1) m := by
    rw [show p + 1 + m - p = m + 1 from by omega, List.range'_succ]
  have htk : M.take p = Y0 := by rw [hM, hp, List.take_left]
  rw [hr, htk]
  have hbody : ∀ k : ℕ, (p :: List.range' (p + 1) m).map
      (fun j => ((entry M 0 j + (if le0 M p j then k * 1 else 0),
        entry M 1 j + (if le1 M p j then k * 1 else 0),
        entry M 2 j) : ℕ × ℕ × ℕ))
      = ((a + k, b + k, 0) : ℕ × ℕ × ℕ) :: List.replicate m ((a + 1 + k, b + 1 + k, 1) : ℕ × ℕ × ℕ) := by
    intro k
    rw [List.map_cons]
    congr 1
    · rw [if_pos hl00, if_pos hl11, e0p, e1p, e2p]; simp
    · refine List.eq_replicate_iff.mpr ⟨by simp, ?_⟩
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      rw [List.mem_range'_1] at hj
      obtain ⟨i, hi, rfl⟩ : ∃ i, i < m ∧ j = p + 1 + i := ⟨j - (p + 1), by omega, by omega⟩
      rw [if_pos (hl0 i (by omega)), if_pos (hl1 i (by omega)), (eq i (by omega)).1,
        (eq i (by omega)).2.1, (eq i (by omega)).2.2]
      simp
  rw [List.flatMap_congr (fun k _ => hbody k)]
  rfl

theorem z1m_mem {Y0 : TrioSeq} {a b m : ℕ} (htw : ∀ n, Y0 ++ Dzm a b m n ∈ W 0) :
    Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: List.replicate (m + 1) ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)) ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_z1m]
  exact htw n

/-! ### 塔の段: `IfcV (y+1)` 台座の上の `Dzm` の連鎖は `PU` の連鎖 -/

/-- `hJm`: z=1 の列 `m` 本は普遍 junk（`m` についての帰納法の仮定）。 -/
theorem Dzm_chainU {m : ℕ}
    (hJm : ∀ (y' c' : ℕ), 2 ≤ y' → JkU y' c' (List.replicate m ((c' + 2, y' + 2, 1) : ℕ × ℕ × ℕ)))
    {y : ℕ} (hy : 2 ≤ y) {E : ℕ → TrioSeq → Prop} (hE : IfcV (y + 1) E)
    {c : ℕ} {Z : TrioSeq} (hZ : E c Z) :
    ∀ (n : ℕ) (J : TrioSeq), JkU (y + n + 1) (c + n + 1) J →
      PU (y + n + 1) (c + n + 2)
        (Z ++ Dzm (c + 1) (y + 1) m (n + 1) ++ ([((c + n + 2, y + n + 2, 0) : ℕ × ℕ × ℕ)] ++ J))
  | 0, J, hJ => by
      have h1 : PU y (c + 1) (Z ++ Dzm (c + 1) (y + 1) m 1) :=
        ⟨E, c, Z, List.replicate m ((c + 2, y + 2, 1) : ℕ × ℕ × ℕ), hE, rfl, hZ,
          by simp [Dzm, show c + 1 + 1 = c + 2 from by omega, show y + 1 + 1 = y + 2 from by omega],
          hJm y c hy⟩
      exact ⟨PU y, c + 1, _, J, IfcV_PU (by omega) (y + 0 + 1 + 1) (by omega), by omega, h1,
        by simp, hJ⟩
  | (n + 1), J, hJ => by
      have ih := Dzm_chainU hJm hy hE hZ n
        (List.replicate m ((c + n + 1 + 2, y + n + 1 + 2, 1) : ℕ × ℕ × ℕ))
        (hJm (y + n + 1) (c + n + 1) (by omega))
      refine ⟨PU (y + n + 1), c + n + 2, _, J, IfcV_PU (by omega) (y + (n + 1) + 1 + 1) (by omega),
        by omega, ih, ?_, by simpa [show y + (n + 1) + 1 = y + n + 1 + 1 from by omega,
          show c + (n + 1) + 1 = c + n + 1 + 1 from by omega] using hJ⟩
      rw [Dzm_succ (c + 1) (y + 1) m (n + 1)]
      simp [List.append_assoc, show c + 1 + (n + 1) = c + n + 2 from by omega,
        show y + 1 + (n + 1) = y + n + 2 from by omega,
        show c + 1 + 1 + (n + 1) = c + n + 1 + 2 from by omega,
        show y + 1 + 1 + (n + 1) = y + n + 1 + 2 from by omega,
        show c + (n + 1) + 2 = c + n + 3 from by omega,
        show y + (n + 1) + 2 = y + n + 3 from by omega,
        show c + n + 2 + 1 = c + n + 3 from by omega,
        show y + n + 1 + 1 + 1 = y + n + 3 from by omega]

theorem Dzm_W {m : ℕ}
    (hJm : ∀ (y' c' : ℕ), 2 ≤ y' → JkU y' c' (List.replicate m ((c' + 2, y' + 2, 1) : ℕ × ℕ × ℕ)))
    {y : ℕ} (hy : 2 ≤ y) {E : ℕ → TrioSeq → Prop} (hE : IfcV (y + 1) E)
    {c : ℕ} {Z : TrioSeq} (hZ : E c Z) : ∀ n : ℕ, Z ++ Dzm (c + 1) (y + 1) m n ∈ W 0
  | 0 => by simpa [Dzm] using ((IfcV_iface (y + 1) hE).bok.aok _ _ hZ).mem
  | 1 => by
      have h1 : PU y (c + 1) (Z ++ Dzm (c + 1) (y + 1) m 1) :=
        ⟨E, c, Z, List.replicate m ((c + 2, y + 2, 1) : ℕ × ℕ × ℕ), hE, rfl, hZ,
          by simp [Dzm, show c + 1 + 1 = c + 2 from by omega, show y + 1 + 1 = y + 2 from by omega],
          hJm y c hy⟩
      exact ((BaseOk_PU y).aok _ _ h1).mem
  | (n + 2) => by
      have h := Dzm_chainU hJm hy hE hZ n
        (List.replicate m ((c + n + 1 + 2, y + n + 1 + 2, 1) : ℕ × ℕ × ℕ))
        (hJm (y + n + 1) (c + n + 1) (by omega))
      have h2 := ((BaseOk_PU (y + n + 1)).aok _ _ h).mem
      rw [Dzm_succ (c + 1) (y + 1) m (n + 1)]
      simpa [List.append_assoc, show c + 1 + (n + 1) = c + n + 2 from by omega,
        show y + 1 + (n + 1) = y + n + 2 from by omega,
        show c + 1 + 1 + (n + 1) = c + n + 1 + 2 from by omega,
        show y + 1 + 1 + (n + 1) = y + n + 1 + 2 from by omega] using h2

/-- ★★★ `y+1` の記録の直上の z=1 の列 `m` 本は普遍 junk。 -/
theorem JkU_z1m : ∀ (m y c : ℕ), 2 ≤ y → JkU y c (List.replicate m ((c + 2, y + 2, 1) : ℕ × ℕ × ℕ))
  | 0, y, c, hy => by simpa using JkU_nil' hy c
  | (m + 1), y, c, hy => by
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rw [List.mem_replicate] at hx
        simp [hx.2]
      · intro x hx
        rw [List.mem_replicate] at hx
        rw [hx.2]; show (1 : ℕ) ≤ y + 2; omega
      · intro E hE t Z hZ
        have h := z1m_mem (Y0 := Z) (a := c + 1 + t) (b := y + 1) (m := m)
          (fun n => by
            have := Dzm_W (fun y' c' hy' => JkU_z1m m y' c' hy') hy hE
              (c := c + t) (by simpa using hZ) n
            simpa [show c + t + 1 = c + 1 + t from by omega] using this)
        have e : shiftr01 t 0 (List.replicate (m + 1) ((c + 2, y + 2, 1) : ℕ × ℕ × ℕ))
            = List.replicate (m + 1) ((c + 1 + t + 1, y + 1 + 1, 1) : ℕ × ℕ × ℕ) := by
          simp [shiftr01, List.map_replicate]; omega
        rw [e]
        simpa using h

#print axioms JkU_z1m

/-! ### `PkGA` 段の z=1 junk `m` 本、単位 `(h+1,1,0)(h+2,2,1)^m` の絶対セグメント化、`(0,0,0)(1,1,1)^m` -/

/-- `PkGA` の元（レベル `h`）の上の `Dzm (h+1) 3 m n`（3 の記録から始まる連鎖）は `W 0`。 -/
theorem Dzm_W_PkGA (m : ℕ) {h : ℕ} {Z : TrioSeq} (hZ : PkGA h Z) (n : ℕ) :
    Z ++ Dzm (h + 1) 3 m n ∈ W 0 :=
  Dzm_W (fun y' c' hy' => JkU_z1m m y' c' hy') (le_refl 2) (Ifc3_toIfcV Ifc3_PkGA) hZ n

/-- ★★★ 2 の記録の直上の z=1 の列 `m` 本は普遍 junk。 -/
theorem JkGU_z1m : ∀ (m c : ℕ), JkGU c (List.replicate m ((c + 2, 3, 1) : ℕ × ℕ × ℕ))
  | 0, c => by simpa using JkGU_nil c
  | (m + 1), c => by
      intro E hI
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rw [List.mem_replicate] at hx
        simp [hx.2]
      · intro x hx
        rw [List.mem_replicate] at hx
        simp [hx.2]
      · intro j t X hX
        have hP : PkGA (c + 1 + t) (X ++ (((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ) ::
            List.replicate m ((c + 1 + t + 1, 3, 1) : ℕ × ℕ × ℕ))) :=
          ⟨E, hI, j, c + t, X, List.replicate m ((c + t + 2, 3, 1) : ℕ × ℕ × ℕ), by omega, hX,
            by simp [show c + t + 1 = c + 1 + t from by omega,
              show c + t + 2 = c + 1 + t + 1 from by omega], JkGU_z1m m (c + t)⟩
        have htw : ∀ n, X ++ Dzm (c + 1 + t) 2 m n ∈ W 0 := by
          intro n
          match n with
          | 0 => simpa [Dzm] using ((BaseOk_RunG hI.bok j).aok _ _ hX).mem
          | 1 =>
              have := (PkGA_Aok hP).mem
              simpa [Dzm] using this
          | (n + 2) =>
              rw [Dzm_cons, ← List.append_assoc]
              have h2 := Dzm_W_PkGA m hP (n + 1)
              simpa using h2
        have h := z1m_mem htw
        have e : shiftr01 t 0 (List.replicate (m + 1) ((c + 2, 3, 1) : ℕ × ℕ × ℕ))
            = List.replicate (m + 1) ((c + 1 + t + 1, 2 + 1, 1) : ℕ × ℕ × ℕ) := by
          simp [shiftr01, List.map_replicate]; omega
        rw [e]
        simpa using h

/-- 単位 `U11 h m = (h+1,1,0) (h+2,2,1)^m`。 -/
def U11 (h m : ℕ) : TrioSeq :=
  ((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: List.replicate m ((h + 2, 2, 1) : ℕ × ℕ × ℕ)

theorem MidD_U11 (h m : ℕ) : MidD (h + 2) (U11 h m) := by
  have h1 := MidD_append (MidD_col (h + 1) 1 (by omega) (by omega))
    (N := List.replicate m ((h + 2, 2, 1) : ℕ × ℕ × ℕ))
    (by intro c hc; rw [List.mem_replicate] at hc; obtain ⟨_, rfl⟩ := hc; show h + 1 + 1 ≤ h + 2; omega)
    (by intro c hc; rw [List.mem_replicate] at hc; obtain ⟨_, rfl⟩ := hc; show (1 : ℕ) ≤ 2; omega)
  simpa [U11, show h + 1 + 1 = h + 2 from by omega] using h1

theorem shift_U11 (h m s : ℕ) : shiftr01 s 0 (U11 h m) = U11 (h + s) m := by
  simp [U11, shiftr01, List.map_replicate]; omega

/-- `LwA h` の元の上の `Dzm (h+1) 1 m n`（1 の列から始まる連鎖）。単位の絶対性を仮定に持つ版。 -/
theorem Dzm_W_LwA_of (m : ℕ) (hS : ∀ h, SegA h (U11 h m)) {h : ℕ} {A : TrioSeq}
    (hA : LwA h A) (n : ℕ) : A ++ Dzm (h + 1) 1 m n ∈ W 0 := by
  have hX : RunA 0 (h + 1) (A ++ U11 h m) := ⟨h, A, _, rfl, rfl, hA, hS h⟩
  have hP : PkGA (h + 2) (A ++ U11 h m ++ (((h + 2, 2, 0) : ℕ × ℕ × ℕ) ::
      List.replicate m ((h + 3, 3, 1) : ℕ × ℕ × ℕ))) :=
    ⟨RunA 0, Iface_RunA0, 0, h + 1, A ++ U11 h m, List.replicate m ((h + 3, 3, 1) : ℕ × ℕ × ℕ),
      rfl, hX, by simp, by simpa using JkGU_z1m m (h + 1)⟩
  match n with
  | 0 => simpa [Dzm] using (LwA_Aok hA).mem
  | 1 =>
      have e1 : Dzm (h + 1) 1 m 1 = U11 h m := by
        simp [Dzm, U11, show h + 1 + 1 = h + 2 from by omega]
      rw [e1]; exact ((BaseOk_RunA 0).aok _ _ hX).mem
  | 2 =>
      have e2 : Dzm (h + 1) 1 m 2 = U11 h m ++ (((h + 2, 2, 0) : ℕ × ℕ × ℕ) ::
          List.replicate m ((h + 3, 3, 1) : ℕ × ℕ × ℕ)) := by
        simp [Dzm, U11, List.range_succ, show h + 1 + 1 = h + 2 from by omega,
          show h + 1 + 1 + 1 = h + 3 from by omega]
      rw [e2, ← List.append_assoc]
      exact (PkGA_Aok hP).mem
  | (n + 3) =>
      have e3 : Dzm (h + 1) 1 m (n + 3) = U11 h m ++ (((h + 2, 2, 0) : ℕ × ℕ × ℕ) ::
          List.replicate m ((h + 3, 3, 1) : ℕ × ℕ × ℕ)) ++ Dzm (h + 2 + 1) 3 m (n + 1) := by
        rw [Dzm_cons, Dzm_cons]
        simp [U11, List.append_assoc, show h + 1 + 1 = h + 2 from by omega,
          show h + 1 + 1 + 1 = h + 3 from by omega]
      rw [e3, ← List.append_assoc, ← List.append_assoc]
      exact Dzm_W_PkGA m hP (n + 1)

/-- ★★★ 単位 `(h+1,1,0)(h+2,2,1)^m` は絶対セグメント。 -/
theorem SegA_U11 : ∀ (m h : ℕ), SegA h (U11 h m)
  | 0, h => by simpa [U11] using SegA_one h
  | (m + 1), h =>
      { mid := MidD_U11 h (m + 1)
        head1 := by simp [U11, entry]
        reapp := by
          intro P hP s A' hA'
          rw [shift_U11]
          have hz := z1m_mem (Y0 := A') (a := h + s + 1) (b := 1) (m := m)
            (fun n => Dzm_W_LwA_of m (SegA_U11 m) ⟨P, hP, hA'⟩ n)
          simpa [U11, show h + s + 1 + 1 = h + s + 2 from by omega] using hz }

theorem Dzm_W_LwA (m : ℕ) {h : ℕ} {A : TrioSeq} (hA : LwA h A) (n : ℕ) :
    A ++ Dzm (h + 1) 1 m n ∈ W 0 := Dzm_W_LwA_of m (SegA_U11 m) hA n

theorem LwA_U11 {h : ℕ} {A : TrioSeq} (hA : LwA h A) (m : ℕ) : RunA 0 (h + 1) (A ++ U11 h m) :=
  ⟨h, A, _, rfl, rfl, hA, SegA_U11 m h⟩

/-- 梯子の元の上に単位 `U11 h m` を継ぐと段が 1 つ上がる。 -/
theorem LvB_U11 {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) {r h : ℕ} {A : TrioSeq}
    (hA : LvB P r h A) (m : ℕ) : LvB P (r + 1) (h + 1) (A ++ U11 h m) := by
  refine ⟨(BaseOk_RunA 0).aok _ _ (LwA_U11 ⟨P, hP, r, hA⟩ m), Or.inr ⟨h, A, _, rfl, rfl, hA,
    (SegA_U11 m h).mid, ?_⟩⟩
  intro s A' hA'
  exact (SegA_U11 m h).reapp P hP s A' ⟨r, hA'⟩

/-! ### `Am m = (0,0,0)(1,1,1)^m` はすべて `Aok`（行 316, 323, 324 と行 325 の段） -/

def Am (m : ℕ) : TrioSeq := ((0, 0, 0) : ℕ × ℕ × ℕ) :: List.replicate m ((1, 1, 1) : ℕ × ℕ × ℕ)

theorem Am_zero_mem : Am 0 ∈ W 0 := by
  refine A1_intro (Or.inl ⟨by simp [Am], ?_⟩)
  simp [Am, lev, entry]

theorem Am_Aok_of_mem {m : ℕ} (hmem : Am m ∈ W 0) : Aok (Am m) := by
  refine ⟨hmem, by simp [Am], ⟨by simp [Am, entry], ?_⟩, ?_, ?_⟩
  · intro j hj hjl
    simp only [Am, List.length_cons, List.length_replicate] at hjl
    obtain ⟨q, rfl⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
    simp only [Am, entry, List.getD_cons_succ]
    simp [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt (show q < m from by omega)]
  · intro c hc h0
    simp only [Am, List.mem_cons, List.mem_replicate] at hc
    rcases hc with rfl | ⟨_, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact absurd h0 (by simp)
  · intro c hc
    simp only [Am, List.mem_cons, List.mem_replicate] at hc
    rcases hc with rfl | ⟨_, rfl⟩ <;> simp

theorem Am_Aok : ∀ m : ℕ, Aok (Am m)
  | 0 => Am_Aok_of_mem Am_zero_mem
  | (m + 1) => by
      refine Am_Aok_of_mem ?_
      have h := z1m_mem (Y0 := []) (a := 0) (b := 0) (m := m) (fun n => by
        match n with
        | 0 => simpa [Dzm] using W_nil 0
        | (n + 1) =>
            rw [Dzm_cons]
            have h1 := Dzm_W_LwA m (h := 0) (LwA_of_Aok (Am_Aok m)) n
            simpa [Am] using h1)
      simpa [Am] using h

theorem Am_mem (m : ℕ) : Am m ∈ W 0 := (Am_Aok m).mem

#print axioms Am_mem
#print axioms LvB_U11

/-! ### 行 317〜325（台座 `R316 = (0,0,0)(1,1,1)(1,1,1)`） -/

theorem Aok_R316 : Aok R316 := Am_Aok 2

theorem R316_row1 : ∀ j, 0 < j → j < R316.length → 1 ≤ entry R316 1 j := by
  intro j hj0 hjl
  rw [R316_len] at hjl
  rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl <;> simp [R316, entry]

/-- ★★★★ シート行317 `R316 (1,1,0) = psi(W_w*2 + W)`。 -/
theorem R317_mem : R316 ++ [((1, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  snocd_gen (by omega) Aok_R316 (Ancd_of_row1 R316_row1 1)
    (fun B hB => BaseOk_zero.hang 0 R316 ⟨Aok_R316, rfl⟩ B hB)

/-- ★★★★ シート行318 `R316 (1,1,0)(2,2,1) = psi(W_w*2 + psi_1(W_w))`。 -/
theorem R318_mem : R316 ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  RunA0_z1 (h := 1) ⟨0, R316, _, rfl, rfl, LwA_of_Aok Aok_R316, SegA_one 0⟩

/-- `R319 = R316 (1,1,0)(2,2,1)(2,2,1)`。 -/
def R319 : TrioSeq := R316 ++ U11 0 2

theorem R319_RunA0 : RunA 0 1 R319 := LwA_U11 (LwA_of_Aok Aok_R316) 2

theorem Aok_R319 : Aok R319 := (BaseOk_RunA 0).aok _ _ R319_RunA0

/-- ★★★★ シート行319 `psi(W_w*2 + psi_1(W_w*2))`。 -/
theorem R319_mem : R319 ∈ W 0 := Aok_R319.mem

theorem R319_row1 : ∀ j, 0 < j → j < R319.length → 1 ≤ entry R319 1 j := by
  intro j hj0 hjl
  simp only [R319, R316, U11, List.length_append, List.length_cons, List.length_replicate,
    List.length_nil] at hjl
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with rfl | rfl | rfl | rfl | rfl <;>
    simp [R319, R316, U11, entry]

/-- ★★★★ シート行320 `R319 (2,1,0) = psi(W_w*2 + psi_1(W_w*2)*W)`。 -/
theorem R320_mem : R319 ++ [((2, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  snocd_gen (by omega) Aok_R319 (Ancd_of_row1 R319_row1 2)
    (fun B hB => LvB_hang BaseOk_P0 1 1 R319 (LvB_U11 BaseOk_P0 (r := 0) (h := 0)
      ⟨Aok_R316, rfl⟩ 2) B hB)

/-- ★★★★ シート行321 `R319 (2,2,0) = psi(W_w*2 + W_2)`。 -/
theorem R321_mem : R319 ++ [((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  RunG_snoc2 Iface_RunA0 0 1 R319 R319_RunA0

theorem R321_33_PkGA : PkGA 2 (R319 ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++
    List.replicate 2 ((3, 3, 1) : ℕ × ℕ × ℕ))) :=
  ⟨RunA 0, Iface_RunA0, 0, 1, R319, List.replicate 2 ((3, 3, 1) : ℕ × ℕ × ℕ), rfl, R319_RunA0, rfl,
    JkGU_z1m 2 1⟩

/-- ★★★★ シート行322 `R319 (2,2,0)(3,3,1)(3,3,1)(3,3,0) = psi(W_w*2 + W_3)`。 -/
theorem R322_mem : R319 ++ [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ),
    ((3, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  ((BaseOk_PU 2).aok _ _ (⟨PkGA, 2, _, [], Ifc3_toIfcV Ifc3_PkGA, rfl, R321_33_PkGA, rfl,
    JkU_nil' (le_refl 2) 2⟩ : PU 2 3 (R319 ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++
      List.replicate 2 ((3, 3, 1) : ℕ × ℕ × ℕ)) ++ ([((3, 3, 0) : ℕ × ℕ × ℕ)] ++ [])))).mem

/-- ★★★★ シート行323 `(0,0,0)(1,1,1)(1,1,1)(1,1,1) = psi(W_w*3)`、行324 `psi(W_w*4)`。 -/
theorem R323_mem : [(0, 0, 0), (1, 1, 1), (1, 1, 1), (1, 1, 1)] ∈ W 0 := Am_mem 3

theorem R324_mem : [(0, 0, 0), (1, 1, 1), (1, 1, 1), (1, 1, 1), (1, 1, 1)] ∈ W 0 := Am_mem 4

/-! ### 行 325 `(0,0,0)(1,1,1)(2,0,0) = psi(W_w*w)`: 平坦な複製 `(0,0,0)(1,1,1)^n` -/

def R325 : TrioSeq := [(0, 0, 0), (1, 1, 1), (2, 0, 0)]

theorem R325_len : R325.length = 3 := by simp [R325]

theorem nextrel0_R325_12 : nextrel0 R325 1 2 := by
  refine ⟨by simp [R325], by simp [R325], by omega, by simp [R325, entry], ?_⟩
  intro j hj; omega

theorem hasParent0_R325 : hasParent R325 0 2 := by
  refine ⟨1, by show nextR R325 0 1 2; simp only [nextR, if_true]; exact nextrel0_R325_12, ?_⟩
  intro j0 hj0
  change nextR R325 0 j0 2 at hj0
  simp only [nextR, if_true] at hj0
  obtain ⟨hj0l, -, hlt, hlt2, hall⟩ := hj0
  rw [R325_len] at hj0l
  rcases j0 with _ | _ | j0
  · exfalso; have := hall 1 ⟨by omega, by omega⟩; simp [R325, entry] at this
  · rfl
  · omega

theorem parent0_R325 : parent R325 0 2 = 1 :=
  hasParent0_R325.unique (parent_nextR hasParent0_R325)
    (by show nextR R325 0 1 2; simp only [nextR, if_true]; exact nextrel0_R325_12)

theorem flatMap_const_singleton {α : Type _} (n : ℕ) (c : α) :
    (List.range n).flatMap (fun _ => [c]) = List.replicate n c := by
  rw [flatMap_singleton_map, List.map_const', List.length_range]

open Classical in
theorem oper_R325 (n : ℕ) : R325⟦n⟧ = Am n := by
  rw [L53.oper_flat (j1 := 2) (j0 := 1) (by rw [R325_len]) (by omega)
    (by simp [R325, entry]) (by simp [srow, R325, entry])
    hasParent0_R325 parent0_R325.symm n]
  simp [R325, Am, entry, List.range', flatMap_const_singleton]

/-- ★★★★★ シート行325 `(0,0,0)(1,1,1)(2,0,0) = psi(W_w*w) ∈ W 0`。 -/
theorem R325_mem : R325 ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_R325 n]
  exact Am_mem n

#print axioms R325_mem
#print axioms R322_mem
/-! ### 平坦な列の一般展開: `(Y0 ++ M ++ (d,0,0))⟦n⟧ = Y0 ++ M^n`（`MidD d M`）。行 326〜330 -/

open Classical in
theorem oper_snoc00 (Y0 : TrioSeq) {M : TrioSeq} {d : ℕ} (hM : MidD d M) (n : ℕ) :
    (Y0 ++ M ++ [((d, 0, 0) : ℕ × ℕ × ℕ)])⟦n⟧ = Y0 ++ (List.range n).flatMap fun _ => M := by
  set c : ℕ × ℕ × ℕ := (d, 0, 0) with hc
  have hq1 : 1 ≤ M.length := List.length_pos_iff.mpr hM.ne
  have hd1 : 1 ≤ d := by have := hM.head; omega
  have hlen : (Y0 ++ M ++ [c]).length = Y0.length + M.length + 1 := by simp; omega
  have eT : ∀ i r, entry (Y0 ++ M ++ [c]) i (Y0.length + r) = entry (M ++ [c]) i r := by
    intro i r; rw [List.append_assoc]; exact entry_append_right Y0 (M ++ [c]) i r
  have eM : ∀ i r, r < M.length → entry (Y0 ++ M ++ [c]) i (Y0.length + r) = entry M i r := by
    intro i r hr; rw [eT]; exact entry_append_left hr
  have e0p : entry (Y0 ++ M ++ [c]) 0 Y0.length = d - 1 := by
    rw [show Y0.length = Y0.length + 0 from rfl, eM 0 0 (by omega)]; have := hM.head; omega
  have e0q : entry (Y0 ++ M ++ [c]) 0 (Y0.length + M.length) = d := by
    rw [eT]; exact (entry_append_last (P := M) (c := c)).1
  have e1q : entry (Y0 ++ M ++ [c]) 1 (Y0.length + M.length) = 0 := by
    rw [eT]; exact (entry_append_last (P := M) (c := c)).2.1
  have e2q : entry (Y0 ++ M ++ [c]) 2 (Y0.length + M.length) = 0 := by
    rw [eT]; exact (entry_append_last (P := M) (c := c)).2.2
  have etail : ∀ r, 1 ≤ r → r < M.length → d ≤ entry (Y0 ++ M ++ [c]) 0 (Y0.length + r) := by
    intro r hr1 hrq; rw [eM 0 r hrq]; exact hM.tail r hr1 hrq
  have hn0 : nextrel0 (Y0 ++ M ++ [c]) Y0.length (Y0.length + M.length) := by
    refine ⟨by omega, by omega, by omega, by rw [e0p, e0q]; omega, ?_⟩
    intro j hj
    obtain ⟨r, hr1, hrq, rfl⟩ : ∃ r, 1 ≤ r ∧ r < M.length ∧ j = Y0.length + r :=
      ⟨j - Y0.length, by omega, by omega, by omega⟩
    rw [e0q]; exact etail r hr1 hrq
  have hpar : hasParent (Y0 ++ M ++ [c]) 0 (Y0.length + M.length) := by
    refine ⟨Y0.length, by show nextR _ 0 Y0.length (Y0.length + M.length); simp only [nextR, if_true]; exact hn0, ?_⟩
    intro j0 hj0
    change nextR _ 0 j0 (Y0.length + M.length) at hj0
    simp only [nextR, if_true] at hj0
    obtain ⟨hj0l, -, hlt, hlt2, hall⟩ := hj0
    rcases Nat.lt_trichotomy j0 Y0.length with h | h | h
    · exfalso
      have := hall Y0.length ⟨h, by omega⟩
      rw [e0p, e0q] at this; omega
    · exact h
    · exfalso
      obtain ⟨r, hr1, hrq, rfl⟩ : ∃ r, 1 ≤ r ∧ r < M.length ∧ j0 = Y0.length + r :=
        ⟨j0 - Y0.length, by omega, by omega, by omega⟩
      have := etail r hr1 hrq
      rw [e0q] at hlt2; omega
  have hparent : parent (Y0 ++ M ++ [c]) 0 (Y0.length + M.length) = Y0.length :=
    hpar.unique (parent_nextR hpar) (by show nextR _ 0 Y0.length (Y0.length + M.length); simp only [nextR, if_true]; exact hn0)
  have hsrow : srow (Y0 ++ M ++ [c]) (Y0.length + M.length) = 0 := by
    simp only [srow]; rw [e2q, e1q]; simp
  rw [L53.oper_flat (j1 := Y0.length + M.length) (j0 := Y0.length) (by omega) (by omega)
    (by rw [e0q]; omega) hsrow hpar hparent.symm n]
  rw [map_range'_entry_drop (by omega) (by omega)]
  have htk : (Y0 ++ M ++ [c]).take Y0.length = Y0 := by
    rw [List.append_assoc, List.take_left]
  have hseg : ((Y0 ++ M ++ [c]).take (Y0.length + M.length)).drop Y0.length = M := by
    rw [show Y0.length + M.length = (Y0 ++ M).length from by simp, List.take_left, List.drop_left]
  rw [htk, hseg]

theorem flat_mem {Y0 M : TrioSeq} {d : ℕ} (hM : MidD d M)
    (htw : ∀ n, Y0 ++ (List.range n).flatMap (fun _ => M) ∈ W 0) :
    Y0 ++ M ++ [((d, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_snoc00 Y0 hM n]
  exact htw n

theorem MidD_col1 (d v : ℕ) (hd : 1 ≤ d) (hv : 1 ≤ v) :
    MidD (d + 1) [((d, v, 1) : ℕ × ℕ × ℕ)] := by
  refine ⟨by simp, ?_, by simp [entry], by simp [entry]; omega, ?_, ?_⟩
  · intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact hd
  · intro j hj1 hjl; simp at hjl; omega
  · intro c hc; simp only [List.mem_singleton] at hc; subst hc; show (1 : ℕ) ≤ v; omega

/-- `LwA h` の元の上の `(h+1,1,0)(h+2,2,1)(h+3,0,0)`。 -/
theorem U11_00_mem {h : ℕ} {A : TrioSeq} (hA : LwA h A) :
    A ++ U11 h 1 ++ [((h + 3, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h1 := flat_mem (Y0 := A ++ [((h + 1, 1, 0) : ℕ × ℕ × ℕ)])
    (M := [((h + 2, 2, 1) : ℕ × ℕ × ℕ)]) (d := h + 3)
    (by have := MidD_col1 (h + 2) 2 (by omega) (by omega); simpa using this)
    (fun n => by
      rw [flatMap_const_singleton, List.append_assoc]
      exact ((BaseOk_RunA 0).aok _ _ (LwA_U11 hA n)).mem)
  simpa [U11, List.append_assoc] using h1

theorem SegA_U11_00 (h : ℕ) : SegA h (U11 h 1 ++ [((h + 3, 0, 0) : ℕ × ℕ × ℕ)]) where
  mid := MidD_append (MidD_U11 h 1)
    (by intro c hc; simp only [List.mem_singleton] at hc; subst hc; show h + 2 ≤ h + 3; omega)
    (by intro c hc; simp only [List.mem_singleton] at hc; subst hc; simp)
  head1 := by simp [U11, entry]
  reapp := by
    intro P hP s A' hA'
    rw [shiftr01_append0, shift_U11, shift_col, show h + 3 + s = h + s + 3 from by omega,
      ← List.append_assoc]
    exact U11_00_mem ⟨P, hP, hA'⟩

/-- 2 の記録の直上の junk `(c+2,3,1)(c+3,0,0)` は普遍 junk。 -/
theorem JkGU_z1_00 (c : ℕ) : JkGU c [((c + 2, 3, 1) : ℕ × ℕ × ℕ), ((c + 3, 0, 0) : ℕ × ℕ × ℕ)] := by
  intro E hI
  refine ⟨by simp, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp
  intro j t X hX
  have h1 := flat_mem (Y0 := X ++ [((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ)])
    (M := [((c + 2 + t, 3, 1) : ℕ × ℕ × ℕ)]) (d := c + 3 + t)
    (by have := MidD_col1 (c + 2 + t) 3 (by omega) (by omega)
        simpa [show c + 2 + t + 1 = c + 3 + t from by omega] using this)
    (fun n => by
      rw [flatMap_const_singleton, List.append_assoc]
      have hP : PkGA (c + 1 + t) (X ++ ([((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ)] ++
          List.replicate n ((c + 2 + t, 3, 1) : ℕ × ℕ × ℕ))) :=
        ⟨E, hI, j, c + t, X, List.replicate n ((c + t + 2, 3, 1) : ℕ × ℕ × ℕ), by omega, hX,
          by simp [show c + t + 1 = c + 1 + t from by omega, show c + t + 2 = c + 2 + t from by omega],
          JkGU_z1m n (c + t)⟩
      exact (PkGA_Aok hP).mem)
  have e : shiftr01 t 0 [((c + 2, 3, 1) : ℕ × ℕ × ℕ), ((c + 3, 0, 0) : ℕ × ℕ × ℕ)]
      = [((c + 2 + t, 3, 1) : ℕ × ℕ × ℕ), ((c + 3 + t, 0, 0) : ℕ × ℕ × ℕ)] := by
    simp [shiftr01]
  rw [e]
  simpa [List.append_assoc] using h1

/-! ### 行 326〜330（台座 `R325 = (0,0,0)(1,1,1)(2,0,0)`） -/

theorem Aok_R325 : Aok R325 := by
  refine ⟨R325_mem, by simp [R325], ⟨by simp [R325, entry], ?_⟩, ?_, ?_⟩
  · intro j hj hjl
    rw [R325_len] at hjl
    rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl <;> simp [R325, entry]
  · intro c hc h0; simp only [R325, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exact absurd h0 (by simp)
    · exact absurd h0 (by simp)
  · intro c hc; simp only [R325, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> simp

theorem Ancd_one_of_deep {Y : TrioSeq} (hY : Deep Y) : Ancd 1 Y := by
  intro j hj0 hjl hlt _
  have := hY.2 j hj0 hjl
  omega

/-- ★★★★ シート行326 `R325 (1,1,0) = psi(W_w*w + W)`。 -/
theorem R326_mem : R325 ++ [((1, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  snocd_gen (by omega) Aok_R325 (Ancd_one_of_deep Aok_R325.deep)
    (fun B hB => BaseOk_zero.hang 0 R325 ⟨Aok_R325, rfl⟩ B hB)

/-- ★★★★ シート行327 `R325 (1,1,0)(2,2,1) = psi(W_w*w + psi_1(W_w))`。 -/
theorem R327_mem : R325 ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  RunA0_z1 (h := 1) ⟨0, R325, _, rfl, rfl, LwA_of_Aok Aok_R325, SegA_one 0⟩

/-- `R328 = R325 (1,1,0)(2,2,1)(3,0,0)`。 -/
def R328 : TrioSeq := R325 ++ (U11 0 1 ++ [((3, 0, 0) : ℕ × ℕ × ℕ)])

theorem R328_RunA0 : RunA 0 1 R328 := ⟨0, R325, _, rfl, rfl, LwA_of_Aok Aok_R325, SegA_U11_00 0⟩

/-- ★★★★ シート行328 `psi(W_w*w + psi_1(W_w*w))`。 -/
theorem R328_mem : R328 ∈ W 0 := ((BaseOk_RunA 0).aok _ _ R328_RunA0).mem

/-- ★★★★ シート行329 `R328 (2,2,0) = psi(W_w*w + W_2)`。 -/
theorem R329_mem : R328 ++ [((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  RunG_snoc2 Iface_RunA0 0 1 R328 R328_RunA0

theorem R329_PkGA : PkGA 2 (R328 ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++
    [((3, 3, 1) : ℕ × ℕ × ℕ), ((4, 0, 0) : ℕ × ℕ × ℕ)])) :=
  ⟨RunA 0, Iface_RunA0, 0, 1, R328, _, rfl, R328_RunA0, rfl, JkGU_z1_00 1⟩

/-- ★★★★ シート行330 `R328 (2,2,0)(3,3,1)(4,0,0)(3,3,0) = psi(W_w*w + W_3)`。 -/
theorem R330_mem : R328 ++ [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ), ((4, 0, 0) : ℕ × ℕ × ℕ),
    ((3, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  ((BaseOk_PU 2).aok _ _ (⟨PkGA, 2, _, [], Ifc3_toIfcV Ifc3_PkGA, rfl, R329_PkGA, rfl,
    JkU_nil' (le_refl 2) 2⟩ : PU 2 3 (R328 ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++
      [((3, 3, 1) : ℕ × ℕ × ℕ), ((4, 0, 0) : ℕ × ℕ × ℕ)]) ++ ([((3, 3, 0) : ℕ × ℕ × ℕ)] ++ [])))).mem

#print axioms R330_mem
/-! ### junk の語: `col a b true = (a+1,b+1,1)`（z）、`col a b false = (a+2,0,0)`（f）。
記録 `(a,b,0)` の junk は `ks.map (col a b)`（`ks : List Bool`、先頭は z）。 -/

def col (a b : ℕ) : Bool → ℕ × ℕ × ℕ
  | true => (a + 1, b + 1, 1)
  | false => (a + 2, 0, 0)

/-- 塔 `Dzw a b ks n = ⋃_{k<n} (a+k,b+k,0) :: ks.map (col (a+k) (b+k))`。 -/
def Dzw (a b : ℕ) (ks : List Bool) (n : ℕ) : TrioSeq :=
  (List.range n).flatMap fun k => ((a + k, b + k, 0) : ℕ × ℕ × ℕ) :: ks.map (col (a + k) (b + k))

theorem Dzw_succ (a b : ℕ) (ks : List Bool) (n : ℕ) : Dzw a b ks (n + 1) =
    Dzw a b ks n ++ (((a + n, b + n, 0) : ℕ × ℕ × ℕ) :: ks.map (col (a + n) (b + n))) := by
  simp [Dzw, List.range_succ]

theorem col_shift (a b s : ℕ) (t : Bool) : shiftr01 s 0 [col a b t] = [col (a + s) b t] := by
  cases t <;> simp [col, shiftr01, Nat.add_right_comm]

theorem shift_map_col (a b s : ℕ) (ks : List Bool) :
    shiftr01 s 0 (ks.map (col a b)) = ks.map (col (a + s) b) := by
  induction ks with
  | nil => simp [shiftr01]
  | cons t ks ih =>
      rw [List.map_cons, List.map_cons, show (col a b t :: ks.map (col a b)) = [col a b t] ++ ks.map (col a b) from rfl,
        shiftr01_append0, col_shift, ih]
      rfl

theorem entry_map_lt {α : Type _} (f : α → ℕ × ℕ × ℕ) (ks : List α) {i : ℕ} (hi : i < ks.length) (r : ℕ) :
    entry (ks.map f) r i = entry [f ks[i]] r 0 := by
  simp [entry, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]

theorem entry_col_true (a b r : ℕ) : entry [col a b true] r 0 = entry [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] r 0 := rfl
theorem entry_col_false (a b r : ℕ) : entry [col a b false] r 0 = entry [((a + 2, 0, 0) : ℕ × ℕ × ℕ)] r 0 := rfl

theorem le0_le' {M : TrioSeq} {i j : ℕ} (h : le0 M i j) : i ≤ j := by
  obtain ⟨-, -, h⟩ := h
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => exact le_trans ih (le_of_lt h2.2.2.1)

theorem rtg0_of_rtg1 {M : TrioSeq} {i j : ℕ} (h : Relation.ReflTransGen (nextrel1 M) i j) :
    Relation.ReflTransGen (nextrel0 M) i j := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h2 ih => exact ih.trans h2.2.2.2.2.1.2.2

theorem le0_of_le1 {M : TrioSeq} {i j : ℕ} (h : le1 M i j) : le0 M i j :=
  ⟨h.1, h.2.1, rtg0_of_rtg1 h.2.2⟩

theorem not_le1_of_row1_zero {M : TrioSeq} {i j : ℕ} (hj : entry M 1 j = 0) (hne : i ≠ j) :
    ¬ le1 M i j := by
  rintro ⟨-, -, h⟩
  rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, -, hc⟩
  · exact hne h1.symm
  · have := hc.2.2.2.1; omega

/-- 語の先頭が z なら、f の直前に最後の z がある。 -/
theorem last_true_before {ks : List Bool} (h0 : ∀ h : 0 < ks.length, ks[0] = true) :
    ∀ i (hi : i < ks.length), ks[i] = false →
      ∃ i', ∃ hi' : i' < ks.length, i' < i ∧ ks[i'] = true ∧
        ∀ j (hj : j < ks.length), i' < j → j < i → ks[j] = false := by
  intro i
  induction i with
  | zero => intro hi hf; rw [h0 hi] at hf; cases hf
  | succ i ih =>
      intro hi hf
      by_cases hz : ks[i]'(by omega) = true
      · exact ⟨i, by omega, by omega, hz, fun j hj h1 h2 => by omega⟩
      · obtain ⟨i', hi', hlt, hz', hall⟩ := ih (by omega) (by simpa using hz)
        refine ⟨i', hi', by omega, hz', ?_⟩
        intro j hj h1 h2
        rcases Nat.lt_or_ge j i with h | h
        · exact hall j hj h1 h
        · have : j = i := by omega
          subst this; simpa using hz

open Classical in
theorem oper_z1w (Y0 : TrioSeq) (a b : ℕ) (ks : List Bool)
    (h0 : ∀ h : 0 < ks.length, ks[0] = true) (n : ℕ) :
    (Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: ks.map (col a b) ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]))⟦n⟧
      = Y0 ++ Dzw a b ks n := by
  set C : TrioSeq := ks.map (col a b) with hC
  set T : TrioSeq := ((a, b, 0) : ℕ × ℕ × ℕ) :: C ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] with hT
  set M : TrioSeq := Y0 ++ T with hM
  set p := Y0.length with hp
  set L := ks.length with hL
  have hCL : C.length = L := by simp [hC, hL]
  have hlen : M.length = p + L + 2 := by simp [hM, hT, hC, hp, hL]; omega
  have eT : ∀ i q, entry M i (p + q) = entry T i q := fun i q => entry_append_right Y0 T i q
  have e0p : entry M 0 p = a := by rw [show p = p + 0 from rfl, eT]; simp [hT, entry]
  have e1p : entry M 1 p = b := by rw [show p = p + 0 from rfl, eT]; simp [hT, entry]
  have e2p : entry M 2 p = 0 := by rw [show p = p + 0 from rfl, eT]; simp [hT, entry]
  have eC : ∀ r i (hi : i < L), entry M r (p + 1 + i) = entry [col a b (ks[i]'(by omega))] r 0 := by
    intro r i hi
    rw [show p + 1 + i = p + (i + 1) from by omega, eT]
    have : entry T r (i + 1) = entry C r i := by
      simp only [hT, entry, List.cons_append, List.getD_cons_succ]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simpa [hC, hL] using hi)]
    rw [this, hC, entry_map_lt (col a b) ks hi r]
  have eq : ∀ r, entry M r (p + 1 + L) = entry [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] r 0 := by
    intro r
    rw [show p + 1 + L = p + (L + 1) from by omega, eT]
    simp only [hT, entry, List.cons_append, List.getD_cons_succ]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), hCL, Nat.sub_self]
  -- 列の種類ごとの成分
  have ez : ∀ i (hi : i < L), ks[i] = true →
      entry M 0 (p + 1 + i) = a + 1 ∧ entry M 1 (p + 1 + i) = b + 1 ∧ entry M 2 (p + 1 + i) = 1 := by
    intro i hi ht
    rw [eC 0 i hi, eC 1 i hi, eC 2 i hi]
    simp [ht, col, entry]
  have ef : ∀ i (hi : i < L), ks[i] = false →
      entry M 0 (p + 1 + i) = a + 2 ∧ entry M 1 (p + 1 + i) = 0 ∧ entry M 2 (p + 1 + i) = 0 := by
    intro i hi ht
    rw [eC 0 i hi, eC 1 i hi, eC 2 i hi]
    simp [ht, col, entry]
  have ege : ∀ i, i < L → a + 1 ≤ entry M 0 (p + 1 + i) := by
    intro i hi
    cases hks : ks[i]'(by omega)
    · have := (ef i hi hks).1; omega
    · have := (ez i hi hks).1; omega
  have ege' : ∀ j, p < j → j < p + 1 + L → a + 1 ≤ entry M 0 j := by
    intro j hj1 hj2
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < L ∧ j = p + 1 + i := ⟨j - (p + 1), by omega, by omega⟩
    exact ege i hi
  have eqL : entry M 0 (p + 1 + L) = a + 1 ∧ entry M 1 (p + 1 + L) = b + 1 ∧
      entry M 2 (p + 1 + L) = 1 := by
    rw [eq 0, eq 1, eq 2]; simp [entry]
  -- 「p より上の列の le0 先祖は自分だけ」
  have hanc : ∀ j j', p < j' → le0 M j' j → entry M 0 j = a + 1 →
      (∀ j'', p < j'' → j'' < j → a + 1 ≤ entry M 0 j'') → j' = j := by
    intro j j' hj' hle hj hbetween
    obtain ⟨hj'l, hjl, hch⟩ := hle
    rcases Relation.ReflTransGen.cases_tail hch with h1 | ⟨c, hc1, hc2⟩
    · exact h1.symm
    · exfalso
      have hcj : c < j := hc2.2.2.1
      have hcle : j' ≤ c := le0_le' ⟨hj'l, hc2.1, hc1⟩
      have hlt : entry M 0 c < entry M 0 j := hc2.2.2.2.1
      have := hbetween c (by omega) hcj
      omega
  -- z 列: le0 と le1
  have hn0z : ∀ i (hi : i < L), ks[i] = true → nextrel0 M p (p + 1 + i) := by
    intro i hi ht
    refine ⟨by omega, by omega, by omega, by rw [e0p, (ez i hi ht).1]; omega, ?_⟩
    intro j hj
    rw [(ez i hi ht).1]; exact ege' j hj.1 (by omega)
  have hl0z : ∀ i (hi : i < L), ks[i] = true → le0 M p (p + 1 + i) := fun i hi ht =>
    ⟨by omega, by omega, Relation.ReflTransGen.single (hn0z i hi ht)⟩
  have hn1z : ∀ i (hi : i < L), ks[i] = true → nextrel1 M p (p + 1 + i) := by
    intro i hi ht
    refine ⟨by omega, by omega, by omega, by rw [e1p, (ez i hi ht).2.1]; omega, hl0z i hi ht, ?_⟩
    intro j hj
    have := hanc (p + 1 + i) j hj.1 hj.2 (ez i hi ht).1
      (fun j'' h1 h2 => ege' j'' h1 (by omega))
    subst this; exact le_rfl
  have hl1z : ∀ i (hi : i < L), ks[i] = true → le1 M p (p + 1 + i) := fun i hi ht =>
    ⟨by omega, by omega, Relation.ReflTransGen.single (hn1z i hi ht)⟩
  -- f 列: le0（直前の z 経由）、¬le1
  have hl0f : ∀ i (hi : i < L), ks[i] = false → le0 M p (p + 1 + i) := by
    intro i hi hf
    obtain ⟨i', hi', hlt, hz', hall⟩ := last_true_before h0 i hi hf
    have hn : nextrel0 M (p + 1 + i') (p + 1 + i) := by
      refine ⟨by omega, by omega, by omega, by rw [(ez i' hi' hz').1, (ef i hi hf).1]; omega, ?_⟩
      intro j hj
      obtain ⟨i'', hi'', rfl⟩ : ∃ i'', i'' < L ∧ j = p + 1 + i'' := ⟨j - (p + 1), by omega, by omega⟩
      have := hall i'' hi'' (by omega) (by omega)
      rw [(ef i hi hf).1, (ef i'' hi'' this).1]
    exact ⟨by omega, by omega, (hl0z i' hi' hz').2.2.trans (Relation.ReflTransGen.single hn)⟩
  have hnl1f : ∀ i (hi : i < L), ks[i] = false → ¬ le1 M p (p + 1 + i) := fun i hi hf =>
    not_le1_of_row1_zero (ef i hi hf).2.1 (by omega)
  -- 最後の列
  have hn0L : nextrel0 M p (p + 1 + L) := by
    refine ⟨by omega, by omega, by omega, by rw [e0p, eqL.1]; omega, ?_⟩
    intro j hj
    rw [eqL.1]; exact ege' j hj.1 hj.2
  have hl0L : le0 M p (p + 1 + L) := ⟨by omega, by omega, Relation.ReflTransGen.single hn0L⟩
  have hn1L : nextrel1 M p (p + 1 + L) := by
    refine ⟨by omega, by omega, by omega, by rw [e1p, eqL.2.1]; omega, hl0L, ?_⟩
    intro j hj
    have := hanc (p + 1 + L) j hj.1 hj.2 eqL.1 (fun j'' h1 h2 => ege' j'' h1 h2)
    subst this; exact le_rfl
  have hn2L : nextrel2 M p (p + 1 + L) := by
    refine ⟨by omega, by omega, by omega, by rw [e2p, eqL.2.2]; omega,
      ⟨by omega, by omega, Relation.ReflTransGen.single hn1L⟩, ?_⟩
    intro j hj
    have := hanc (p + 1 + L) j hj.1 (le0_of_le1 hj.2) eqL.1
      (fun j'' h1 h2 => ege' j'' h1 h2)
    subst this; rw [eqL.2.2]
  have hpar : hasParent M 2 (p + 1 + L) :=
    hasParent2_of_le1_witness (by omega) (Relation.ReflTransGen.single hn1L)
      (by rw [e2p, eqL.2.2]; omega)
  have hparent : parent M 2 (p + 1 + L) = p := hpar.unique (parent_nextR hpar) hn2L
  have hsrow : srow M (p + 1 + L) = 2 := by simp [srow, eqL.2.2]
  have hl00 : le0 M p p := ⟨by omega, by omega, Relation.ReflTransGen.refl⟩
  have hl11 : le1 M p p := ⟨by omega, by omega, Relation.ReflTransGen.refl⟩
  rw [L53.oper_unfold (j1 := p + 1 + L) (i1 := 2) (j0 := p) (d0 := 1) (d1 := 1)
      (by omega) (by omega) (by rw [eqL.1]; omega) hsrow.symm hpar hparent.symm
      (by rw [if_pos (by omega : 0 < 2), eqL.1, e0p]; omega)
      (by rw [if_pos (by omega : 1 < 2), eqL.2.1, e1p]; omega) n]
  have hr : List.range' p (p + 1 + L - p) = p :: List.range' (p + 1) L := by
    rw [show p + 1 + L - p = L + 1 from by omega, List.range'_succ]
  have htk : M.take p = Y0 := by rw [hM, hp, List.take_left]
  rw [hr, htk]
  have hbody : ∀ k : ℕ, (p :: List.range' (p + 1) L).map
      (fun j => ((entry M 0 j + (if le0 M p j then k * 1 else 0),
        entry M 1 j + (if le1 M p j then k * 1 else 0),
        entry M 2 j) : ℕ × ℕ × ℕ))
      = ((a + k, b + k, 0) : ℕ × ℕ × ℕ) :: ks.map (col (a + k) (b + k)) := by
    intro k
    rw [List.map_cons]
    congr 1
    · rw [if_pos hl00, if_pos hl11, e0p, e1p, e2p]; simp
    · apply List.ext_getElem
      · simp [hL]
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_range'_1]
        have hi : i < L := by simpa [hL] using h2
        cases hks : ks[i]'(by omega)
        · obtain ⟨e0, e1, e2⟩ := ef i hi hks
          rw [show p + 1 + i = p + 1 + i from rfl, if_pos (hl0f i hi hks), if_neg (hnl1f i hi hks), e0, e1, e2]
          simp [col]; omega
        · obtain ⟨e0, e1, e2⟩ := ez i hi hks
          rw [if_pos (hl0z i hi hks), if_pos (hl1z i hi hks), e0, e1, e2]
          simp [col]; omega
  rw [List.flatMap_congr (fun k _ => hbody k)]
  rfl

theorem z1w_mem {Y0 : TrioSeq} {a b : ℕ} {ks : List Bool} (h0 : ∀ h : 0 < ks.length, ks[0] = true)
    (htw : ∀ n, Y0 ++ Dzw a b ks n ∈ W 0) :
    Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: ks.map (col a b) ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]) ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_z1w Y0 a b ks h0]
  exact htw n

#print axioms z1w_mem
/-! ### 語つきの塔 `Dzw` の連鎖（IfcV 台座 / RunG 台座 / LwA 台座 / 根） -/

theorem col_ge (a b : ℕ) (t : Bool) : a + 1 ≤ (col a b t).1 := by
  cases t <;> simp [col]

theorem col_mono (a b : ℕ) (t : Bool) : (col a b t).2.2 ≤ (col a b t).2.1 := by
  cases t <;> simp [col]

theorem map_col_ge {a b : ℕ} {ks : List Bool} : ∀ x ∈ ks.map (col a b), a + 1 ≤ x.1 := by
  intro x hx
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
  exact col_ge a b t

theorem map_col_mono {a b : ℕ} {ks : List Bool} : Mono (ks.map (col a b)) := by
  intro x hx
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
  exact col_mono a b t

/-- 記録 `(a,v,0)`（`1 ≤ v`）と語の junk は `MidD (a+1)`。 -/
theorem MidD_word (a v : ℕ) (ha : 1 ≤ a) (hv : 1 ≤ v) (ks : List Bool) :
    MidD (a + 1) (((a, v, 0) : ℕ × ℕ × ℕ) :: ks.map (col a v)) := by
  have h := MidD_append (MidD_col a v ha hv) (N := ks.map (col a v)) map_col_ge map_col_mono
  simpa using h

/-- `Good ks`: 語 `ks` は 4 つの段で普遍。 -/
structure Good (ks : List Bool) : Prop where
  pu : ∀ (y c : ℕ), 2 ≤ y → JkU y c (ks.map (col (c + 1) (y + 1)))
  pk : ∀ c : ℕ, JkGU c (ks.map (col (c + 1) 2))
  seg : ∀ h : ℕ, SegA h (((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: ks.map (col (h + 1) 1))
  root : Aok (((0, 0, 0) : ℕ × ℕ × ℕ) :: ks.map (col 0 0))

/-- `IfcV (y+1)` 台座の上の `Dzw` の連鎖は `PU` の連鎖。 -/
theorem Dzw_chainU {ks : List Bool} (hG : Good ks)
    {y : ℕ} (hy : 2 ≤ y) {E : ℕ → TrioSeq → Prop} (hE : IfcV (y + 1) E)
    {c : ℕ} {Z : TrioSeq} (hZ : E c Z) :
    ∀ (n : ℕ) (J : TrioSeq), JkU (y + n + 1) (c + n + 1) J →
      PU (y + n + 1) (c + n + 2)
        (Z ++ Dzw (c + 1) (y + 1) ks (n + 1) ++ ([((c + n + 2, y + n + 2, 0) : ℕ × ℕ × ℕ)] ++ J))
  | 0, J, hJ => by
      have h1 : PU y (c + 1) (Z ++ Dzw (c + 1) (y + 1) ks 1) :=
        ⟨E, c, Z, ks.map (col (c + 1) (y + 1)), hE, rfl, hZ, by simp [Dzw], hG.pu y c hy⟩
      exact ⟨PU y, c + 1, _, J, IfcV_PU (by omega) (y + 0 + 1 + 1) (by omega), by omega, h1,
        by simp, hJ⟩
  | (n + 1), J, hJ => by
      have ih := Dzw_chainU hG hy hE hZ n (ks.map (col (c + n + 2) (y + n + 2)))
        (hG.pu (y + n + 1) (c + n + 1) (by omega))
      refine ⟨PU (y + n + 1), c + n + 2, _, J, IfcV_PU (by omega) (y + (n + 1) + 1 + 1) (by omega),
        by omega, ih, ?_, by simpa [show y + (n + 1) + 1 = y + n + 1 + 1 from by omega,
          show c + (n + 1) + 1 = c + n + 1 + 1 from by omega] using hJ⟩
      rw [Dzw_succ (c + 1) (y + 1) ks (n + 1)]
      simp [List.append_assoc, show c + 1 + (n + 1) = c + n + 2 from by omega,
        show y + 1 + (n + 1) = y + n + 2 from by omega,
        show c + (n + 1) + 2 = c + n + 3 from by omega,
        show y + (n + 1) + 2 = y + n + 3 from by omega,
        show c + n + 2 + 1 = c + n + 3 from by omega,
        show y + n + 1 + 1 + 1 = y + n + 3 from by omega]

theorem Dzw_W {ks : List Bool} (hG : Good ks)
    {y : ℕ} (hy : 2 ≤ y) {E : ℕ → TrioSeq → Prop} (hE : IfcV (y + 1) E)
    {c : ℕ} {Z : TrioSeq} (hZ : E c Z) : ∀ n : ℕ, Z ++ Dzw (c + 1) (y + 1) ks n ∈ W 0
  | 0 => by simpa [Dzw] using ((IfcV_iface (y + 1) hE).bok.aok _ _ hZ).mem
  | 1 => by
      have h1 : PU y (c + 1) (Z ++ Dzw (c + 1) (y + 1) ks 1) :=
        ⟨E, c, Z, ks.map (col (c + 1) (y + 1)), hE, rfl, hZ, by simp [Dzw], hG.pu y c hy⟩
      exact ((BaseOk_PU y).aok _ _ h1).mem
  | (n + 2) => by
      have h := Dzw_chainU hG hy hE hZ n (ks.map (col (c + n + 2) (y + n + 2)))
        (hG.pu (y + n + 1) (c + n + 1) (by omega))
      have h2 := ((BaseOk_PU (y + n + 1)).aok _ _ h).mem
      rw [Dzw_succ (c + 1) (y + 1) ks (n + 1)]
      simpa [List.append_assoc, show c + 1 + (n + 1) = c + n + 2 from by omega,
        show y + 1 + (n + 1) = y + n + 2 from by omega] using h2

/-- `RunG` 台座（2 の記録から始まる）の上の連鎖。 -/
theorem Dzw_W_RunG {ks : List Bool} (hG : Good ks) {E : ℕ → TrioSeq → Prop} (hI : Iface E)
    {j c : ℕ} {X : TrioSeq} (hX : RunG E j c X) : ∀ n : ℕ, X ++ Dzw (c + 1) 2 ks n ∈ W 0 := by
  have hP : PkGA (c + 1) (X ++ Dzw (c + 1) 2 ks 1) :=
    ⟨E, hI, j, c, X, ks.map (col (c + 1) 2), rfl, hX, by simp [Dzw], hG.pk c⟩
  intro n
  match n with
  | 0 => simpa [Dzw] using ((BaseOk_RunG hI.bok j).aok _ _ hX).mem
  | 1 => exact (PkGA_Aok hP).mem
  | (n + 2) =>
      have e : Dzw (c + 1) 2 ks (n + 2) = Dzw (c + 1) 2 ks 1 ++ Dzw (c + 1 + 1) 3 ks (n + 1) := by
        simp only [Dzw]
        rw [show n + 2 = 1 + (n + 1) from by omega, List.range_add, List.flatMap_append,
          List.flatMap_map]
        congr 1
        apply List.flatMap_congr
        intro k _
        simp [show c + 1 + (1 + k) = c + 1 + 1 + k from by omega, show 2 + (1 + k) = 3 + k from by omega]
      rw [e, ← List.append_assoc]
      exact Dzw_W hG (le_refl 2) (Ifc3_toIfcV Ifc3_PkGA) hP (n + 1)

/-- `LwA` 台座（1 の列から始まる）の上の連鎖。 -/
theorem Dzw_W_LwA {ks : List Bool} (hG : Good ks) {h : ℕ} {A : TrioSeq} (hA : LwA h A) :
    ∀ n : ℕ, A ++ Dzw (h + 1) 1 ks n ∈ W 0 := by
  have hX : RunA 0 (h + 1) (A ++ Dzw (h + 1) 1 ks 1) :=
    ⟨h, A, _, rfl, rfl, hA, by simpa [Dzw] using hG.seg h⟩
  intro n
  match n with
  | 0 => simpa [Dzw] using (LwA_Aok hA).mem
  | 1 => exact ((BaseOk_RunA 0).aok _ _ hX).mem
  | (n + 2) =>
      have e : Dzw (h + 1) 1 ks (n + 2) = Dzw (h + 1) 1 ks 1 ++ Dzw (h + 1 + 1) 2 ks (n + 1) := by
        simp only [Dzw]
        rw [show n + 2 = 1 + (n + 1) from by omega, List.range_add, List.flatMap_append,
          List.flatMap_map]
        congr 1
        apply List.flatMap_congr
        intro k _
        simp [show h + 1 + (1 + k) = h + 1 + 1 + k from by omega, show 1 + (1 + k) = 2 + k from by omega]
      rw [e, ← List.append_assoc]
      exact Dzw_W_RunG hG Iface_RunA0 (j := 0) hX (n + 1)

/-- 根から始まる連鎖 `Dzw 0 0 ks n`。 -/
theorem Dzw_W_root {ks : List Bool} (hG : Good ks) : ∀ n : ℕ, Dzw 0 0 ks n ∈ W 0
  | 0 => by simpa [Dzw] using W_nil 0
  | (n + 1) => by
      have e : Dzw 0 0 ks (n + 1) = Dzw 0 0 ks 1 ++ Dzw (0 + 1) 1 ks n := by
        simp only [Dzw]
        rw [show n + 1 = 1 + n from by omega, List.range_add, List.flatMap_append, List.flatMap_map]
        congr 1
        apply List.flatMap_congr
        intro k _
        simp [Nat.add_comm]
      rw [e]
      have h1 := Dzw_W_LwA hG (h := 0) (LwA_of_Aok hG.root) n
      simpa [Dzw] using h1

#print axioms Dzw_W_root
/-! ### 語の普遍性: 補題 A（最後に z）、補題 B（最後に f）、二重帰納法。行 331〜335 -/

/-- 根と語だけの行列は `W 0` に入れば `Aok`。 -/
theorem Aok_root_of_mem {ks : List Bool}
    (hmem : (((0, 0, 0) : ℕ × ℕ × ℕ) :: ks.map (col 0 0)) ∈ W 0) :
    Aok (((0, 0, 0) : ℕ × ℕ × ℕ) :: ks.map (col 0 0)) := by
  refine ⟨hmem, by simp, ⟨by simp [entry], ?_⟩, ?_, ?_⟩
  · intro j hj hjl
    simp only [List.length_cons, List.length_map] at hjl
    obtain ⟨q, rfl⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
    have : entry (((0, 0, 0) : ℕ × ℕ × ℕ) :: ks.map (col 0 0)) 0 (q + 1)
        = entry (ks.map (col 0 0)) 0 q := by simp [entry]
    rw [this, entry_map_lt (col 0 0) ks (by omega) 0]
    cases ks[q] <;> simp [col, entry]
  · intro c hc h0
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨rfl, rfl⟩
    · exfalso; have := map_col_ge c hc; omega
  · intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp
    · exact map_col_mono c hc

theorem Good_nil : Good [] where
  pu := fun y c hy => by simpa using JkU_nil' hy c
  pk := fun c => by simpa using JkGU_nil c
  seg := fun h => by simpa using SegA_one h
  root := by simpa using Am_Aok 0

theorem shift_zcol (a b t : ℕ) :
    shiftr01 t 0 [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] = [((a + 1 + t, b + 1, 1) : ℕ × ℕ × ℕ)] := by
  simp [shiftr01]

/-- 補題 A: 語の最後に z を足しても普遍。 -/
theorem Good_snocz {ks : List Bool} (h0 : ∀ h : 0 < ks.length, ks[0] = true) (hG : Good ks) :
    Good (ks ++ [true]) where
  pu := by
    intro y c hy
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [List.map_append] at hx
      rcases List.mem_append.mp hx with h | h
      · have := map_col_ge x h; omega
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h; subst h; simp [col]
    · rw [List.map_append]; exact fun x hx => by
        rcases List.mem_append.mp hx with h | h
        · exact map_col_mono x h
        · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h; subst h; simp [col]
    · intro E hE t Z hZ
      have h := z1w_mem (Y0 := Z) (a := c + 1 + t) (b := y + 1) h0
        (fun n => by
          have := Dzw_W hG hy hE (c := c + t) (by simpa using hZ) n
          simpa [show c + t + 1 = c + 1 + t from by omega] using this)
      rw [List.map_append, shiftr01_append0, shift_map_col]
      simp only [List.map_cons, List.map_nil, col]
      rw [shift_zcol]
      simpa [List.append_assoc, show c + 1 + 1 + t = c + 1 + t + 1 from by omega] using h
  pk := by
    intro c E hI
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [List.map_append] at hx
      rcases List.mem_append.mp hx with h | h
      · have := map_col_ge x h; omega
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h; subst h; simp [col]
    · rw [List.map_append]; exact fun x hx => by
        rcases List.mem_append.mp hx with h | h
        · exact map_col_mono x h
        · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h; subst h; simp [col]
    · intro j t X hX
      have h := z1w_mem (Y0 := X) (a := c + 1 + t) (b := 2) h0
        (fun n => by
          have := Dzw_W_RunG hG hI (c := c + t) hX n
          simpa [show c + t + 1 = c + 1 + t from by omega] using this)
      rw [List.map_append, shiftr01_append0, shift_map_col]
      simp only [List.map_cons, List.map_nil, col]
      rw [shift_zcol]
      simpa [List.append_assoc, show c + 1 + 1 + t = c + 1 + t + 1 from by omega] using h
  seg := by
    intro h
    refine ⟨?_, by simp [entry], ?_⟩
    · have h1 := MidD_append (MidD_word (h + 1) 1 (by omega) (by omega) ks)
        (N := [((h + 2, 2, 1) : ℕ × ℕ × ℕ)])
        (by intro x hx; simp only [List.mem_singleton] at hx; subst hx; show h + 1 + 1 ≤ h + 2; omega)
        (by intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp)
      simpa [show h + 1 + 1 = h + 2 from by omega, col] using h1
    · intro P hP s A' hA'
      have hz := z1w_mem (Y0 := A') (a := h + s + 1) (b := 1) h0
        (fun n => Dzw_W_LwA hG (h := h + s) ⟨P, hP, hA'⟩ n)
      rw [List.map_append]
      simp only [List.map_cons, List.map_nil, col]
      rw [show ((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: (ks.map (col (h + 1) 1) ++ [((h + 1 + 1, 1 + 1, 1) : ℕ × ℕ × ℕ)])
          = [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ ks.map (col (h + 1) 1) ++ [((h + 1 + 1, 1 + 1, 1) : ℕ × ℕ × ℕ)] from rfl,
        shiftr01_append0, shiftr01_append0, shift_col, shift_map_col, shift_zcol]
      simpa [List.append_assoc, show h + 1 + s = h + s + 1 from by omega,
        show h + 1 + 1 + s = h + s + 1 + 1 from by omega] using hz
  root := by
    have hmem := z1w_mem (Y0 := []) (a := 0) (b := 0) h0 (fun n => by simpa using Dzw_W_root hG n)
    exact Aok_root_of_mem (ks := ks ++ [true]) (by simpa [col] using hmem)

/-- `zf i = z f^i`（1 ブロック）。 -/
def zf (i : ℕ) : List Bool := true :: List.replicate i false

theorem map_zf (a b i : ℕ) : (zf i).map (col a b) =
    ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ) :: List.replicate i ((a + 2, 0, 0) : ℕ × ℕ × ℕ) := by
  simp [zf, col, List.map_replicate]

theorem MidD_zf (a b i : ℕ) : MidD (a + 2) ((zf i).map (col a b)) := by
  rw [map_zf]
  have h := MidD_append (MidD_col1 (a + 1) (b + 1) (by omega) (by omega))
    (N := List.replicate i ((a + 2, 0, 0) : ℕ × ℕ × ℕ))
    (by intro x hx; rw [List.mem_replicate] at hx; obtain ⟨_, rfl⟩ := hx; show a + 1 + 1 ≤ a + 2; omega)
    (by intro x hx; rw [List.mem_replicate] at hx; obtain ⟨_, rfl⟩ := hx; simp)
  simpa [show a + 1 + 1 = a + 2 from by omega] using h

/-- 語 `ks ++ (zf i)^n`。 -/
def wordN (ks : List Bool) (i n : ℕ) : List Bool := ks ++ (List.range n).flatMap fun _ => zf i

theorem map_wordN (f : Bool → ℕ × ℕ × ℕ) (ks : List Bool) (i n : ℕ) :
    (wordN ks i n).map f = ks.map f ++ (List.range n).flatMap fun _ => (zf i).map f := by
  simp [wordN, List.map_flatMap]

theorem map_snocf (f : Bool → ℕ × ℕ × ℕ) (ks : List Bool) (i : ℕ) :
    (ks ++ (zf i ++ [false])).map f = ks.map f ++ (zf i).map f ++ [f false] := by
  simp [List.map_append]

/-- 補題 B: `ks ++ (zf i)^n` が全部普遍なら `ks ++ zf i ++ [f]` も普遍。 -/
theorem Good_snocf {ks : List Bool} (i : ℕ) (hm : ∀ n, Good (wordN ks i n)) :
    Good (ks ++ (zf i ++ [false])) where
  pu := by
    intro y c hy
    refine ⟨?_, ?_, ?_⟩
    · intro x hx; have := map_col_ge x hx; omega
    · exact map_col_mono
    · intro E hE t Z hZ
      rw [shift_map_col, map_snocf]
      simp only [col]
      have h := flat_mem (Y0 := Z ++ [((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)] ++ ks.map (col (c + 1 + t) (y + 1)))
        (M := (zf i).map (col (c + 1 + t) (y + 1))) (d := c + 1 + t + 2) (MidD_zf _ _ i)
        (fun n => by
          have hP : PU y (c + 1 + t) (Z ++ ([((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)] ++
              (wordN ks i n).map (col (c + 1 + t) (y + 1)))) :=
            ⟨E, c + t, Z, _, hE, by omega, hZ, by rw [show c + t + 1 = c + 1 + t from by omega],
              (hm n).pu y (c + t) hy⟩
          have := ((BaseOk_PU y).aok _ _ hP).mem
          rw [map_wordN] at this
          simpa [List.append_assoc] using this)
      simpa [List.append_assoc] using h
  pk := by
    intro c E hI
    refine ⟨?_, ?_, ?_⟩
    · intro x hx; have := map_col_ge x hx; omega
    · exact map_col_mono
    · intro j t X hX
      rw [shift_map_col, map_snocf]
      simp only [col]
      have h := flat_mem (Y0 := X ++ [((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ)] ++ ks.map (col (c + 1 + t) 2))
        (M := (zf i).map (col (c + 1 + t) 2)) (d := c + 1 + t + 2) (MidD_zf _ _ i)
        (fun n => by
          have hP : PkGA (c + 1 + t) (X ++ ([((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ)] ++
              (wordN ks i n).map (col (c + 1 + t) 2))) :=
            ⟨E, hI, j, c + t, X, _, by omega, hX, by rw [show c + t + 1 = c + 1 + t from by omega],
              (hm n).pk (c + t)⟩
          have := (PkGA_Aok hP).mem
          rw [map_wordN] at this
          simpa [List.append_assoc] using this)
      simpa [List.append_assoc] using h
  seg := by
    intro h
    refine ⟨?_, by simp [entry], ?_⟩
    · have h1 := MidD_word (h + 1) 1 (by omega) (by omega) (ks ++ (zf i ++ [false]))
      simpa [show h + 1 + 1 = h + 2 from by omega] using h1
    · intro P hP s A' hA'
      rw [show ((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: (ks ++ (zf i ++ [false])).map (col (h + 1) 1)
          = [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ (ks ++ (zf i ++ [false])).map (col (h + 1) 1) from rfl,
        shiftr01_append0, shift_col, shift_map_col, map_snocf]
      simp only [col]
      have hR : ∀ n, RunA 0 (h + s + 1) (A' ++ (((h + s + 1, 1, 0) : ℕ × ℕ × ℕ) ::
          (wordN ks i n).map (col (h + s + 1) 1))) :=
        fun n => ⟨h + s, A', _, rfl, rfl, ⟨P, hP, hA'⟩, (hm n).seg (h + s)⟩
      have h1 := flat_mem (Y0 := A' ++ [((h + 1 + s, 1, 0) : ℕ × ℕ × ℕ)] ++ ks.map (col (h + 1 + s) 1))
        (M := (zf i).map (col (h + 1 + s) 1)) (d := h + 1 + s + 2) (MidD_zf _ _ i)
        (fun n => by
          have := ((BaseOk_RunA 0).aok _ _ (hR n)).mem
          rw [map_wordN] at this
          simpa [List.append_assoc, show h + s + 1 = h + 1 + s from by omega] using this)
      simpa [List.append_assoc] using h1
  root := by
    have h1 := flat_mem (Y0 := [((0, 0, 0) : ℕ × ℕ × ℕ)] ++ ks.map (col 0 0))
      (M := (zf i).map (col 0 0)) (d := 0 + 2) (MidD_zf 0 0 i)
      (fun n => by
        have := (hm n).root.mem
        rw [map_wordN] at this
        simpa [List.append_assoc] using this)
    refine Aok_root_of_mem ?_
    rw [map_snocf]
    simpa [col, List.append_assoc] using h1

/-! ### 二重帰納法: すべての語が普遍 -/

def blocks (rs : List ℕ) : List Bool := rs.flatMap zf

theorem blocks_append (rs1 rs2 : List ℕ) : blocks (rs1 ++ rs2) = blocks rs1 ++ blocks rs2 := by
  simp [blocks]

theorem blocks_head (rs : List ℕ) : ∀ h : 0 < (blocks rs).length, (blocks rs)[0] = true := by
  intro h
  cases rs with
  | nil => simp [blocks] at h
  | cons i rs => simp [blocks, zf]

theorem blocks_snoc0 (rs : List ℕ) : blocks (rs ++ [0]) = blocks rs ++ [true] := by
  simp [blocks, zf]

theorem blocks_snoc_succ (rs : List ℕ) (i : ℕ) :
    blocks (rs ++ [i + 1]) = blocks rs ++ (zf i ++ [false]) := by
  simp [blocks, zf, List.replicate_succ']

theorem blocks_replicate (rs : List ℕ) (i : ℕ) : ∀ m,
    blocks (rs ++ List.replicate m i) = wordN (blocks rs) i m
  | 0 => by simp [blocks, wordN]
  | (m + 1) => by
      rw [List.replicate_succ', ← List.append_assoc, blocks_append, blocks_replicate rs i m]
      simp [wordN, blocks, List.range_succ, List.append_assoc]

theorem split_last {a : ℕ} : ∀ {S : List ℕ}, a ∈ S → ∃ S1 S2, S = S1 ++ a :: S2 ∧ a ∉ S2
  | [], h => by simp at h
  | b :: S', h => by
      by_cases ha : a ∈ S'
      · obtain ⟨S1, S2, rfl, hn⟩ := split_last ha
        exact ⟨b :: S1, S2, by simp, hn⟩
      · have : a = b := by
          rcases List.mem_cons.mp h with h1 | h1
          · exact h1
          · exact absurd h1 ha
        subst this
        exact ⟨[], S', rfl, ha⟩

theorem Good_rep0 {P : List ℕ} (hP : Good (blocks P)) : ∀ n, Good (blocks (P ++ List.replicate n 0))
  | 0 => by simpa using hP
  | (n + 1) => by
      rw [List.replicate_succ', ← List.append_assoc, blocks_snoc0]
      exact Good_snocz (blocks_head _) (Good_rep0 hP n)

/-- 二重帰納法の本体。 -/
theorem Good_Q : ∀ (K cnt : ℕ) (P S : List ℕ), Good (blocks P) → (∀ i ∈ S, i ≤ K) →
    S.count K = cnt → Good (blocks (P ++ S))
  | 0, _, P, S, hP, hle, _ => by
      have hS : S = List.replicate S.length 0 :=
        List.eq_replicate_iff.mpr ⟨rfl, fun i hi => by have := hle i hi; omega⟩
      rw [hS]
      exact Good_rep0 hP _
  | (K + 1), 0, P, S, hP, hle, hcnt => by
      have hnot : (K + 1) ∉ S := List.count_eq_zero.mp hcnt
      refine Good_Q K (S.count K) P S hP ?_ rfl
      intro i hi
      have := hle i hi
      have : i ≠ K + 1 := fun h => hnot (h ▸ hi)
      omega
  | (K + 1), (cnt + 1), P, S, hP, hle, hcnt => by
      have hmem : (K + 1) ∈ S := by
        rw [← List.count_pos_iff]; omega
      obtain ⟨S1, S2, rfl, hn⟩ := split_last hmem
      have hc1 : S1.count (K + 1) = cnt := by
        rw [List.count_append, List.count_cons_self] at hcnt
        have : S2.count (K + 1) = 0 := List.count_eq_zero.mpr hn
        omega
      have hall : ∀ m, Good (blocks (P ++ S1 ++ List.replicate m K)) := by
        intro m
        rw [List.append_assoc]
        refine Good_Q (K + 1) cnt P (S1 ++ List.replicate m K) hP ?_ ?_
        · intro i hi
          rcases List.mem_append.mp hi with h | h
          · exact hle i (by simp [h])
          · rw [List.mem_replicate] at h; omega
        · rw [List.count_append, hc1, List.count_replicate]
          simp
      have hB : Good (blocks (P ++ S1 ++ [K + 1])) := by
        rw [blocks_snoc_succ]
        refine Good_snocf K ?_
        intro n
        rw [← blocks_replicate]
        exact hall n
      have h2 := Good_Q K (S2.count K) (P ++ S1 ++ [K + 1]) S2 hB (by
        intro i hi
        have := hle i (by simp [hi])
        have : i ≠ K + 1 := fun h => hn (h ▸ hi)
        omega) rfl
      simpa [List.append_assoc] using h2

theorem le_sum_of_mem : ∀ {rs : List ℕ} {i : ℕ}, i ∈ rs → i ≤ rs.sum
  | [], _, h => by simp at h
  | b :: rs, i, h => by
      rcases List.mem_cons.mp h with rfl | h
      · simp
      · have := le_sum_of_mem h; simp; omega

/-- ★★★★★ すべての語 `z f^{i_1} … z f^{i_r}` は普遍 junk。 -/
theorem Good_blocks (rs : List ℕ) : Good (blocks rs) := by
  have h := Good_Q rs.sum (rs.count rs.sum) [] rs (by simpa [blocks] using Good_nil)
    (fun i hi => le_sum_of_mem hi) rfl
  simpa using h

/-! ### 行 331〜335 -/

/-- ★★★★ シート行331 `(0,0,0)(1,1,1)(2,0,0)(1,1,1) = psi(W_w*w + W_w)`。 -/
theorem R331_mem : [(0, 0, 0), (1, 1, 1), (2, 0, 0), (1, 1, 1)] ∈ W 0 := (Good_blocks [1, 0]).root.mem

/-- ★★★★ シート行332 `psi(W_w*w + W_w*2)`。 -/
theorem R332_mem : [(0, 0, 0), (1, 1, 1), (2, 0, 0), (1, 1, 1), (1, 1, 1)] ∈ W 0 :=
  (Good_blocks [1, 0, 0]).root.mem

/-- ★★★★ シート行333 `psi(W_w*w2)`。 -/
theorem R333_mem : [(0, 0, 0), (1, 1, 1), (2, 0, 0), (1, 1, 1), (2, 0, 0)] ∈ W 0 :=
  (Good_blocks [1, 1]).root.mem

/-- ★★★★ シート行334 `psi(W_w*w^2)`。 -/
theorem R334_mem : [(0, 0, 0), (1, 1, 1), (2, 0, 0), (2, 0, 0)] ∈ W 0 := (Good_blocks [2]).root.mem

open Classical in
/-- 平坦な列の一般展開（`MidD` の代わりに頭と尾の高さだけ）。 -/
theorem oper_snoc00' (Y0 : TrioSeq) {M : TrioSeq} {d : ℕ} (hne : M ≠ [])
    (hhead : entry M 0 0 + 1 = d) (htail : ∀ r, 1 ≤ r → r < M.length → d ≤ entry M 0 r) (n : ℕ) :
    (Y0 ++ M ++ [((d, 0, 0) : ℕ × ℕ × ℕ)])⟦n⟧ = Y0 ++ (List.range n).flatMap fun _ => M := by
  set c : ℕ × ℕ × ℕ := (d, 0, 0) with hc
  have hq1 : 1 ≤ M.length := List.length_pos_iff.mpr hne
  have hd1 : 1 ≤ d := by omega
  have hlen : (Y0 ++ M ++ [c]).length = Y0.length + M.length + 1 := by simp; omega
  have eT : ∀ i r, entry (Y0 ++ M ++ [c]) i (Y0.length + r) = entry (M ++ [c]) i r := by
    intro i r; rw [List.append_assoc]; exact entry_append_right Y0 (M ++ [c]) i r
  have eM : ∀ i r, r < M.length → entry (Y0 ++ M ++ [c]) i (Y0.length + r) = entry M i r := by
    intro i r hr; rw [eT]; exact entry_append_left hr
  have e0p : entry (Y0 ++ M ++ [c]) 0 Y0.length = d - 1 := by
    rw [show Y0.length = Y0.length + 0 from rfl, eM 0 0 (by omega)]; omega
  have e0q : entry (Y0 ++ M ++ [c]) 0 (Y0.length + M.length) = d := by
    rw [eT]; exact (entry_append_last (P := M) (c := c)).1
  have e1q : entry (Y0 ++ M ++ [c]) 1 (Y0.length + M.length) = 0 := by
    rw [eT]; exact (entry_append_last (P := M) (c := c)).2.1
  have e2q : entry (Y0 ++ M ++ [c]) 2 (Y0.length + M.length) = 0 := by
    rw [eT]; exact (entry_append_last (P := M) (c := c)).2.2
  have etail : ∀ r, 1 ≤ r → r < M.length → d ≤ entry (Y0 ++ M ++ [c]) 0 (Y0.length + r) := by
    intro r hr1 hrq; rw [eM 0 r hrq]; exact htail r hr1 hrq
  have hn0 : nextrel0 (Y0 ++ M ++ [c]) Y0.length (Y0.length + M.length) := by
    refine ⟨by omega, by omega, by omega, by rw [e0p, e0q]; omega, ?_⟩
    intro j hj
    obtain ⟨r, hr1, hrq, rfl⟩ : ∃ r, 1 ≤ r ∧ r < M.length ∧ j = Y0.length + r :=
      ⟨j - Y0.length, by omega, by omega, by omega⟩
    rw [e0q]; exact etail r hr1 hrq
  have hpar : hasParent (Y0 ++ M ++ [c]) 0 (Y0.length + M.length) := by
    refine ⟨Y0.length, by show nextR _ 0 Y0.length (Y0.length + M.length); simp only [nextR, if_true]; exact hn0, ?_⟩
    intro j0 hj0
    change nextR _ 0 j0 (Y0.length + M.length) at hj0
    simp only [nextR, if_true] at hj0
    obtain ⟨hj0l, -, hlt, hlt2, hall⟩ := hj0
    rcases Nat.lt_trichotomy j0 Y0.length with h | h | h
    · exfalso
      have := hall Y0.length ⟨h, by omega⟩
      rw [e0p, e0q] at this; omega
    · exact h
    · exfalso
      obtain ⟨r, hr1, hrq, rfl⟩ : ∃ r, 1 ≤ r ∧ r < M.length ∧ j0 = Y0.length + r :=
        ⟨j0 - Y0.length, by omega, by omega, by omega⟩
      have := etail r hr1 hrq
      rw [e0q] at hlt2; omega
  have hparent : parent (Y0 ++ M ++ [c]) 0 (Y0.length + M.length) = Y0.length :=
    hpar.unique (parent_nextR hpar) (by show nextR _ 0 Y0.length (Y0.length + M.length); simp only [nextR, if_true]; exact hn0)
  have hsrow : srow (Y0 ++ M ++ [c]) (Y0.length + M.length) = 0 := by
    simp only [srow]; rw [e2q, e1q]; simp
  rw [L53.oper_flat (j1 := Y0.length + M.length) (j0 := Y0.length) (by omega) (by omega)
    (by rw [e0q]; omega) hsrow hpar hparent.symm n]
  rw [map_range'_entry_drop (by omega) (by omega)]
  have htk : (Y0 ++ M ++ [c]).take Y0.length = Y0 := by
    rw [List.append_assoc, List.take_left]
  have hseg : ((Y0 ++ M ++ [c]).take (Y0.length + M.length)).drop Y0.length = M := by
    rw [show Y0.length + M.length = (Y0 ++ M).length from by simp, List.take_left, List.drop_left]
  rw [htk, hseg]

/-- ★★★★ シート行335 `(0,0,0)(1,1,1)(2,0,0)(3,0,0) = psi(W_w*w^w)`。 -/
theorem R335_mem : R325 ++ [((3, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  have e := oper_snoc00' (Y0 := Q) (M := [((2, 0, 0) : ℕ × ℕ × ℕ)]) (d := 3) (by simp)
    (by simp [entry]) (by intro r hr1 hrl; simp at hrl; omega) n
  rw [show R325 ++ [((3, 0, 0) : ℕ × ℕ × ℕ)] = Q ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] ++ [((3, 0, 0) : ℕ × ℕ × ℕ)] from rfl, e,
    flatMap_const_singleton]
  have h := (Good_blocks [n]).root.mem
  simpa [blocks, zf, col, Q, List.map_replicate] using h

#print axioms R335_mem
#print axioms Good_blocks
/-! ### 語の一般化: `colG a b none = (a+1,b+1,1)`（z）、`colG a b (some e) = (a+e,0,0)`（高さ `e ≥ 2` の平坦な列） -/

def colG (a b : ℕ) : Option ℕ → ℕ × ℕ × ℕ
  | none => (a + 1, b + 1, 1)
  | some e => (a + e, 0, 0)

def hgt : Option ℕ → ℕ
  | none => 1
  | some e => e

/-- 語の妥当性: 先頭は z、平坦な列の高さは 2 以上。 -/
structure Wv (ws : List (Option ℕ)) : Prop where
  head : ∀ h : 0 < ws.length, ws[0] = none
  flat : ∀ e, some e ∈ ws → 2 ≤ e

theorem Wv_nil : Wv [] := ⟨fun h => by simp at h, fun e h => by simp at h⟩

def DzwG (a b : ℕ) (ws : List (Option ℕ)) (n : ℕ) : TrioSeq :=
  (List.range n).flatMap fun k => ((a + k, b + k, 0) : ℕ × ℕ × ℕ) :: ws.map (colG (a + k) (b + k))

theorem DzwG_succ (a b : ℕ) (ws : List (Option ℕ)) (n : ℕ) : DzwG a b ws (n + 1) =
    DzwG a b ws n ++ (((a + n, b + n, 0) : ℕ × ℕ × ℕ) :: ws.map (colG (a + n) (b + n))) := by
  simp [DzwG, List.range_succ]

theorem colG_shift (a b s : ℕ) (t : Option ℕ) : shiftr01 s 0 [colG a b t] = [colG (a + s) b t] := by
  cases t <;> simp [colG, shiftr01] <;> omega

theorem shift_map_colG (a b s : ℕ) (ws : List (Option ℕ)) :
    shiftr01 s 0 (ws.map (colG a b)) = ws.map (colG (a + s) b) := by
  induction ws with
  | nil => simp [shiftr01]
  | cons t ws ih =>
      rw [List.map_cons, List.map_cons, show (colG a b t :: ws.map (colG a b)) = [colG a b t] ++ ws.map (colG a b) from rfl,
        shiftr01_append0, colG_shift, ih]
      rfl

theorem colG_ge {a b : ℕ} {t : Option ℕ} (ht : ∀ e, t = some e → 2 ≤ e) : a + 1 ≤ (colG a b t).1 := by
  cases t with
  | none => simp [colG]
  | some e => have := ht e rfl; simp [colG]; omega

theorem colG_mono (a b : ℕ) (t : Option ℕ) : (colG a b t).2.2 ≤ (colG a b t).2.1 := by
  cases t <;> simp [colG]

theorem map_colG_ge {a b : ℕ} {ws : List (Option ℕ)} (hv : Wv ws) : ∀ x ∈ ws.map (colG a b), a + 1 ≤ x.1 := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  exact colG_ge (fun e he => hv.flat e (he ▸ ht))

theorem map_colG_mono {a b : ℕ} {ws : List (Option ℕ)} : Mono (ws.map (colG a b)) := by
  intro x hx
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
  exact colG_mono a b t

/-- 最も近い低い列（一般形）。 -/
theorem nearest_lower {f : ℕ → ℕ} {v : ℕ} : ∀ i : ℕ, (∃ i' < i, f i' < v) →
    ∃ i' < i, f i' < v ∧ ∀ j, i' < j → j < i → v ≤ f j
  | 0, h => by obtain ⟨i', hi', -⟩ := h; omega
  | (i + 1), h => by
      by_cases hi : f i < v
      · exact ⟨i, by omega, hi, fun j h1 h2 => by omega⟩
      · obtain ⟨i', hi', hf⟩ := h
        have hi'' : i' < i := by
          rcases Nat.lt_or_ge i' i with h1 | h1
          · exact h1
          · have : i' = i := by omega
            subst this; exact absurd hf hi
        obtain ⟨j', hj', hfj', hall⟩ := nearest_lower i ⟨i', hi'', hf⟩
        refine ⟨j', by omega, hfj', ?_⟩
        intro j h1 h2
        rcases Nat.lt_or_ge j i with h3 | h3
        · exact hall j h1 h3
        · have : j = i := by omega
          subst this; omega

open Classical in
theorem oper_z1wG (Y0 : TrioSeq) (a b : ℕ) (ws : List (Option ℕ)) (hv : Wv ws) (n : ℕ) :
    (Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: ws.map (colG a b) ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]))⟦n⟧
      = Y0 ++ DzwG a b ws n := by
  set C : TrioSeq := ws.map (colG a b) with hC
  set T : TrioSeq := ((a, b, 0) : ℕ × ℕ × ℕ) :: C ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] with hT
  set M : TrioSeq := Y0 ++ T with hM
  set p := Y0.length with hp
  set L := ws.length with hL
  have hCL : C.length = L := by simp [hC, hL]
  have hlen : M.length = p + L + 2 := by simp [hM, hT, hC, hp, hL]; omega
  have eT : ∀ i q, entry M i (p + q) = entry T i q := fun i q => entry_append_right Y0 T i q
  have e0p : entry M 0 p = a := by rw [show p = p + 0 from rfl, eT]; simp [hT, entry]
  have e1p : entry M 1 p = b := by rw [show p = p + 0 from rfl, eT]; simp [hT, entry]
  have e2p : entry M 2 p = 0 := by rw [show p = p + 0 from rfl, eT]; simp [hT, entry]
  have eC : ∀ r i (hi : i < L), entry M r (p + 1 + i) = entry [colG a b (ws[i]'(by omega))] r 0 := by
    intro r i hi
    rw [show p + 1 + i = p + (i + 1) from by omega, eT]
    have : entry T r (i + 1) = entry C r i := by
      simp only [hT, entry, List.cons_append, List.getD_cons_succ]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simpa [hC, hL] using hi)]
    rw [this, hC, entry_map_lt (colG a b) ws hi r]
  have eq : ∀ r, entry M r (p + 1 + L) = entry [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] r 0 := by
    intro r
    rw [show p + 1 + L = p + (L + 1) from by omega, eT]
    simp only [hT, entry, List.cons_append, List.getD_cons_succ]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), hCL, Nat.sub_self]
  have ez : ∀ i (hi : i < L), ws[i] = none →
      entry M 0 (p + 1 + i) = a + 1 ∧ entry M 1 (p + 1 + i) = b + 1 ∧ entry M 2 (p + 1 + i) = 1 := by
    intro i hi ht
    rw [eC 0 i hi, eC 1 i hi, eC 2 i hi]
    simp [ht, colG, entry]
  have ef : ∀ i (hi : i < L) e, ws[i] = some e →
      entry M 0 (p + 1 + i) = a + e ∧ entry M 1 (p + 1 + i) = 0 ∧ entry M 2 (p + 1 + i) = 0 := by
    intro i hi e ht
    rw [eC 0 i hi, eC 1 i hi, eC 2 i hi]
    simp [ht, colG, entry]
  have hge2 : ∀ i (hi : i < L) e, ws[i] = some e → 2 ≤ e := fun i hi e ht =>
    hv.flat e (ht ▸ List.getElem_mem hi)
  have ege : ∀ i, i < L → a + 1 ≤ entry M 0 (p + 1 + i) := by
    intro i hi
    cases hks : ws[i]'(by omega) with
    | none => have := (ez i hi hks).1; omega
    | some e => have := (ef i hi e hks).1; have := hge2 i hi e hks; omega
  have ege' : ∀ j, p < j → j < p + 1 + L → a + 1 ≤ entry M 0 j := by
    intro j hj1 hj2
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < L ∧ j = p + 1 + i := ⟨j - (p + 1), by omega, by omega⟩
    exact ege i hi
  have eqL : entry M 0 (p + 1 + L) = a + 1 ∧ entry M 1 (p + 1 + L) = b + 1 ∧
      entry M 2 (p + 1 + L) = 1 := by
    rw [eq 0, eq 1, eq 2]; simp [entry]
  have hanc : ∀ j j', p < j' → le0 M j' j → entry M 0 j = a + 1 →
      (∀ j'', p < j'' → j'' < j → a + 1 ≤ entry M 0 j'') → j' = j := by
    intro j j' hj' hle hj hbetween
    obtain ⟨hj'l, hjl, hch⟩ := hle
    rcases Relation.ReflTransGen.cases_tail hch with h1 | ⟨c, hc1, hc2⟩
    · exact h1.symm
    · exfalso
      have hcj : c < j := hc2.2.2.1
      have hcle : j' ≤ c := le0_le' ⟨hj'l, hc2.1, hc1⟩
      have hlt : entry M 0 c < entry M 0 j := hc2.2.2.2.1
      have := hbetween c (by omega) hcj
      omega
  -- z 列
  have hn0z : ∀ i (hi : i < L), ws[i] = none → nextrel0 M p (p + 1 + i) := by
    intro i hi ht
    refine ⟨by omega, by omega, by omega, by rw [e0p, (ez i hi ht).1]; omega, ?_⟩
    intro j hj
    rw [(ez i hi ht).1]; exact ege' j hj.1 (by omega)
  have hl0z : ∀ i (hi : i < L), ws[i] = none → le0 M p (p + 1 + i) := fun i hi ht =>
    ⟨by omega, by omega, Relation.ReflTransGen.single (hn0z i hi ht)⟩
  have hn1z : ∀ i (hi : i < L), ws[i] = none → nextrel1 M p (p + 1 + i) := by
    intro i hi ht
    refine ⟨by omega, by omega, by omega, by rw [e1p, (ez i hi ht).2.1]; omega, hl0z i hi ht, ?_⟩
    intro j hj
    have := hanc (p + 1 + i) j hj.1 hj.2 (ez i hi ht).1
      (fun j'' h1 h2 => ege' j'' h1 (by omega))
    subst this; exact le_rfl
  have hl1z : ∀ i (hi : i < L), ws[i] = none → le1 M p (p + 1 + i) := fun i hi ht =>
    ⟨by omega, by omega, Relation.ReflTransGen.single (hn1z i hi ht)⟩
  -- 全部の列: le0（平坦な列は最も近い低い列経由の強い帰納法）
  have hl0 : ∀ i (hi : i < L), le0 M p (p + 1 + i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      cases hks : ws[i]'(by omega) with
      | none => exact hl0z i hi hks
      | some e =>
        have he := hge2 i hi e hks
        have hi0 : 0 < i := by
          rcases Nat.eq_zero_or_pos i with h0 | h0
          · subst h0; rw [hv.head (by omega)] at hks; cases hks
          · exact h0
        have hz0 : entry M 0 (p + 1 + 0) = a + 1 := (ez 0 (by omega) (hv.head (by omega))).1
        obtain ⟨i', hi'i, hlt, hall⟩ := nearest_lower (f := fun j => entry M 0 (p + 1 + j)) (v := a + e) i
          ⟨0, hi0, by simp only; rw [hz0]; omega⟩
        have hn : nextrel0 M (p + 1 + i') (p + 1 + i) := by
          refine ⟨by omega, by omega, by omega, by rw [(ef i hi e hks).1]; exact hlt, ?_⟩
          intro j hj
          obtain ⟨i'', hi'', rfl⟩ : ∃ i'', i'' < L ∧ j = p + 1 + i'' := ⟨j - (p + 1), by omega, by omega⟩
          rw [(ef i hi e hks).1]; exact hall i'' (by omega) (by omega)
        have := ih i' hi'i (by omega)
        exact ⟨by omega, by omega, this.2.2.trans (Relation.ReflTransGen.single hn)⟩
  have hnl1f : ∀ i (hi : i < L) e, ws[i] = some e → ¬ le1 M p (p + 1 + i) := fun i hi e hf =>
    not_le1_of_row1_zero (ef i hi e hf).2.1 (by omega)
  -- 最後の列
  have hn0L : nextrel0 M p (p + 1 + L) := by
    refine ⟨by omega, by omega, by omega, by rw [e0p, eqL.1]; omega, ?_⟩
    intro j hj
    rw [eqL.1]; exact ege' j hj.1 hj.2
  have hl0L : le0 M p (p + 1 + L) := ⟨by omega, by omega, Relation.ReflTransGen.single hn0L⟩
  have hn1L : nextrel1 M p (p + 1 + L) := by
    refine ⟨by omega, by omega, by omega, by rw [e1p, eqL.2.1]; omega, hl0L, ?_⟩
    intro j hj
    have := hanc (p + 1 + L) j hj.1 hj.2 eqL.1 (fun j'' h1 h2 => ege' j'' h1 h2)
    subst this; exact le_rfl
  have hn2L : nextrel2 M p (p + 1 + L) := by
    refine ⟨by omega, by omega, by omega, by rw [e2p, eqL.2.2]; omega,
      ⟨by omega, by omega, Relation.ReflTransGen.single hn1L⟩, ?_⟩
    intro j hj
    have := hanc (p + 1 + L) j hj.1 (le0_of_le1 hj.2) eqL.1 (fun j'' h1 h2 => ege' j'' h1 h2)
    subst this; rw [eqL.2.2]
  have hpar : hasParent M 2 (p + 1 + L) :=
    hasParent2_of_le1_witness (by omega) (Relation.ReflTransGen.single hn1L)
      (by rw [e2p, eqL.2.2]; omega)
  have hparent : parent M 2 (p + 1 + L) = p := hpar.unique (parent_nextR hpar) hn2L
  have hsrow : srow M (p + 1 + L) = 2 := by simp [srow, eqL.2.2]
  have hl00 : le0 M p p := ⟨by omega, by omega, Relation.ReflTransGen.refl⟩
  have hl11 : le1 M p p := ⟨by omega, by omega, Relation.ReflTransGen.refl⟩
  rw [L53.oper_unfold (j1 := p + 1 + L) (i1 := 2) (j0 := p) (d0 := 1) (d1 := 1)
      (by omega) (by omega) (by rw [eqL.1]; omega) hsrow.symm hpar hparent.symm
      (by rw [if_pos (by omega : 0 < 2), eqL.1, e0p]; omega)
      (by rw [if_pos (by omega : 1 < 2), eqL.2.1, e1p]; omega) n]
  have hr : List.range' p (p + 1 + L - p) = p :: List.range' (p + 1) L := by
    rw [show p + 1 + L - p = L + 1 from by omega, List.range'_succ]
  have htk : M.take p = Y0 := by rw [hM, hp, List.take_left]
  rw [hr, htk]
  have hbody : ∀ k : ℕ, (p :: List.range' (p + 1) L).map
      (fun j => ((entry M 0 j + (if le0 M p j then k * 1 else 0),
        entry M 1 j + (if le1 M p j then k * 1 else 0),
        entry M 2 j) : ℕ × ℕ × ℕ))
      = ((a + k, b + k, 0) : ℕ × ℕ × ℕ) :: ws.map (colG (a + k) (b + k)) := by
    intro k
    rw [List.map_cons]
    congr 1
    · rw [if_pos hl00, if_pos hl11, e0p, e1p, e2p]; simp
    · apply List.ext_getElem
      · simp [hL]
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_range'_1]
        have hi : i < L := by simpa [hL] using h2
        cases hks : ws[i]'(by omega) with
        | none =>
          obtain ⟨e0, e1, e2⟩ := ez i hi hks
          rw [if_pos (hl0 i hi), if_pos (hl1z i hi hks), e0, e1, e2]
          simp [colG]; omega
        | some e =>
          obtain ⟨e0, e1, e2⟩ := ef i hi e hks
          rw [if_pos (hl0 i hi), if_neg (hnl1f i hi e hks), e0, e1, e2]
          simp [colG]; omega
  rw [List.flatMap_congr (fun k _ => hbody k)]
  rfl

theorem z1wG_mem {Y0 : TrioSeq} {a b : ℕ} {ws : List (Option ℕ)} (hv : Wv ws)
    (htw : ∀ n, Y0 ++ DzwG a b ws n ∈ W 0) :
    Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: ws.map (colG a b) ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]) ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_z1wG Y0 a b ws hv]
  exact htw n

open Classical in
/-- 平坦な列の一般展開（頭 `< d`、尾 `≥ d` だけ）。 -/
theorem oper_snoc00'' (Y0 : TrioSeq) {M : TrioSeq} {d : ℕ} (hne : M ≠ [])
    (hhead : entry M 0 0 < d) (htail : ∀ r, 1 ≤ r → r < M.length → d ≤ entry M 0 r) (n : ℕ) :
    (Y0 ++ M ++ [((d, 0, 0) : ℕ × ℕ × ℕ)])⟦n⟧ = Y0 ++ (List.range n).flatMap fun _ => M := by
  set c : ℕ × ℕ × ℕ := (d, 0, 0) with hc
  have hq1 : 1 ≤ M.length := List.length_pos_iff.mpr hne
  have hd1 : 1 ≤ d := by omega
  have hlen : (Y0 ++ M ++ [c]).length = Y0.length + M.length + 1 := by simp; omega
  have eT : ∀ i r, entry (Y0 ++ M ++ [c]) i (Y0.length + r) = entry (M ++ [c]) i r := by
    intro i r; rw [List.append_assoc]; exact entry_append_right Y0 (M ++ [c]) i r
  have eM : ∀ i r, r < M.length → entry (Y0 ++ M ++ [c]) i (Y0.length + r) = entry M i r := by
    intro i r hr; rw [eT]; exact entry_append_left hr
  have e0p : entry (Y0 ++ M ++ [c]) 0 Y0.length < d := by
    rw [show Y0.length = Y0.length + 0 from rfl, eM 0 0 (by omega)]; exact hhead
  have e0q : entry (Y0 ++ M ++ [c]) 0 (Y0.length + M.length) = d := by
    rw [eT]; exact (entry_append_last (P := M) (c := c)).1
  have e1q : entry (Y0 ++ M ++ [c]) 1 (Y0.length + M.length) = 0 := by
    rw [eT]; exact (entry_append_last (P := M) (c := c)).2.1
  have e2q : entry (Y0 ++ M ++ [c]) 2 (Y0.length + M.length) = 0 := by
    rw [eT]; exact (entry_append_last (P := M) (c := c)).2.2
  have etail : ∀ r, 1 ≤ r → r < M.length → d ≤ entry (Y0 ++ M ++ [c]) 0 (Y0.length + r) := by
    intro r hr1 hrq; rw [eM 0 r hrq]; exact htail r hr1 hrq
  have hn0 : nextrel0 (Y0 ++ M ++ [c]) Y0.length (Y0.length + M.length) := by
    refine ⟨by omega, by omega, by omega, by rw [e0q]; exact e0p, ?_⟩
    intro j hj
    obtain ⟨r, hr1, hrq, rfl⟩ : ∃ r, 1 ≤ r ∧ r < M.length ∧ j = Y0.length + r :=
      ⟨j - Y0.length, by omega, by omega, by omega⟩
    rw [e0q]; exact etail r hr1 hrq
  have hpar : hasParent (Y0 ++ M ++ [c]) 0 (Y0.length + M.length) := by
    refine ⟨Y0.length, by show nextR _ 0 Y0.length (Y0.length + M.length); simp only [nextR, if_true]; exact hn0, ?_⟩
    intro j0 hj0
    change nextR _ 0 j0 (Y0.length + M.length) at hj0
    simp only [nextR, if_true] at hj0
    obtain ⟨hj0l, -, hlt, hlt2, hall⟩ := hj0
    rcases Nat.lt_trichotomy j0 Y0.length with h | h | h
    · exfalso
      have := hall Y0.length ⟨h, by omega⟩
      rw [e0q] at this; omega
    · exact h
    · exfalso
      obtain ⟨r, hr1, hrq, rfl⟩ : ∃ r, 1 ≤ r ∧ r < M.length ∧ j0 = Y0.length + r :=
        ⟨j0 - Y0.length, by omega, by omega, by omega⟩
      have := etail r hr1 hrq
      rw [e0q] at hlt2; omega
  have hparent : parent (Y0 ++ M ++ [c]) 0 (Y0.length + M.length) = Y0.length :=
    hpar.unique (parent_nextR hpar) (by show nextR _ 0 Y0.length (Y0.length + M.length); simp only [nextR, if_true]; exact hn0)
  have hsrow : srow (Y0 ++ M ++ [c]) (Y0.length + M.length) = 0 := by
    simp only [srow]; rw [e2q, e1q]; simp
  rw [L53.oper_flat (j1 := Y0.length + M.length) (j0 := Y0.length) (by omega) (by omega)
    (by rw [e0q]; omega) hsrow hpar hparent.symm n]
  rw [map_range'_entry_drop (by omega) (by omega)]
  have htk : (Y0 ++ M ++ [c]).take Y0.length = Y0 := by
    rw [List.append_assoc, List.take_left]
  have hseg : ((Y0 ++ M ++ [c]).take (Y0.length + M.length)).drop Y0.length = M := by
    rw [show Y0.length + M.length = (Y0 ++ M).length from by simp, List.take_left, List.drop_left]
  rw [htk, hseg]

theorem flat_mem'' {Y0 M : TrioSeq} {d : ℕ} (hne : M ≠ []) (hhead : entry M 0 0 < d)
    (htail : ∀ r, 1 ≤ r → r < M.length → d ≤ entry M 0 r)
    (htw : ∀ n, Y0 ++ (List.range n).flatMap (fun _ => M) ∈ W 0) :
    Y0 ++ M ++ [((d, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_snoc00'' Y0 hne hhead htail n]
  exact htw n

#print axioms z1wG_mem
#print axioms flat_mem''
/-! ### 一般化した語の普遍性 `GoodG`（影の W 帰納法）と行 336 -/

theorem colG_fst (a b : ℕ) (t : Option ℕ) : (colG a b t).1 = a + hgt t := by
  cases t <;> simp [colG, hgt]

/-- 記録 `(a,v,0)`（`1 ≤ v`）と語の junk は `MidD (a+1)`。 -/
theorem MidD_wordG (a v : ℕ) (ha : 1 ≤ a) (hv : 1 ≤ v) {ws : List (Option ℕ)} (hw : Wv ws) :
    MidD (a + 1) (((a, v, 0) : ℕ × ℕ × ℕ) :: ws.map (colG a v)) := by
  have h := MidD_append (MidD_col a v ha hv) (N := ws.map (colG a v)) (map_colG_ge hw) map_colG_mono
  simpa using h

theorem Aok_rootG_of_mem {ws : List (Option ℕ)} (hw : Wv ws)
    (hmem : (((0, 0, 0) : ℕ × ℕ × ℕ) :: ws.map (colG 0 0)) ∈ W 0) :
    Aok (((0, 0, 0) : ℕ × ℕ × ℕ) :: ws.map (colG 0 0)) := by
  refine ⟨hmem, by simp, ⟨by simp [entry], ?_⟩, ?_, ?_⟩
  · intro j hj hjl
    simp only [List.length_cons, List.length_map] at hjl
    obtain ⟨q, rfl⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
    have : entry (((0, 0, 0) : ℕ × ℕ × ℕ) :: ws.map (colG 0 0)) 0 (q + 1)
        = entry (ws.map (colG 0 0)) 0 q := by simp [entry]
    rw [this, entry_map_lt (colG 0 0) ws (by omega) 0]
    have := colG_ge (a := 0) (b := 0) (t := ws[q]) (fun e he => hw.flat e (he ▸ List.getElem_mem (by omega)))
    simp [entry]; omega
  · intro c hc h0
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨rfl, rfl⟩
    · exfalso; have := map_colG_ge hw c hc; omega
  · intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp
    · exact map_colG_mono c hc

structure GoodG (ws : List (Option ℕ)) : Prop where
  pu : ∀ (y c : ℕ), 2 ≤ y → JkU y c (ws.map (colG (c + 1) (y + 1)))
  pk : ∀ c : ℕ, JkGU c (ws.map (colG (c + 1) 2))
  seg : ∀ h : ℕ, SegA h (((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: ws.map (colG (h + 1) 1))
  root : Aok (((0, 0, 0) : ℕ × ℕ × ℕ) :: ws.map (colG 0 0))

theorem GoodG_nil : GoodG [] where
  pu := fun y c hy => by simpa using JkU_nil' hy c
  pk := fun c => by simpa using JkGU_nil c
  seg := fun h => by simpa using SegA_one h
  root := by simpa using Am_Aok 0

theorem DzwG_chainU {ws : List (Option ℕ)} (hG : GoodG ws)
    {y : ℕ} (hy : 2 ≤ y) {E : ℕ → TrioSeq → Prop} (hE : IfcV (y + 1) E)
    {c : ℕ} {Z : TrioSeq} (hZ : E c Z) :
    ∀ (n : ℕ) (J : TrioSeq), JkU (y + n + 1) (c + n + 1) J →
      PU (y + n + 1) (c + n + 2)
        (Z ++ DzwG (c + 1) (y + 1) ws (n + 1) ++ ([((c + n + 2, y + n + 2, 0) : ℕ × ℕ × ℕ)] ++ J))
  | 0, J, hJ => by
      have h1 : PU y (c + 1) (Z ++ DzwG (c + 1) (y + 1) ws 1) :=
        ⟨E, c, Z, ws.map (colG (c + 1) (y + 1)), hE, rfl, hZ, by simp [DzwG], hG.pu y c hy⟩
      exact ⟨PU y, c + 1, _, J, IfcV_PU (by omega) (y + 0 + 1 + 1) (by omega), by omega, h1,
        by simp, hJ⟩
  | (n + 1), J, hJ => by
      have ih := DzwG_chainU hG hy hE hZ n (ws.map (colG (c + n + 2) (y + n + 2)))
        (hG.pu (y + n + 1) (c + n + 1) (by omega))
      refine ⟨PU (y + n + 1), c + n + 2, _, J, IfcV_PU (by omega) (y + (n + 1) + 1 + 1) (by omega),
        by omega, ih, ?_, by simpa [show y + (n + 1) + 1 = y + n + 1 + 1 from by omega,
          show c + (n + 1) + 1 = c + n + 1 + 1 from by omega] using hJ⟩
      rw [DzwG_succ (c + 1) (y + 1) ws (n + 1)]
      simp [List.append_assoc, show c + 1 + (n + 1) = c + n + 2 from by omega,
        show y + 1 + (n + 1) = y + n + 2 from by omega,
        show c + (n + 1) + 2 = c + n + 3 from by omega,
        show y + (n + 1) + 2 = y + n + 3 from by omega,
        show c + n + 2 + 1 = c + n + 3 from by omega,
        show y + n + 1 + 1 + 1 = y + n + 3 from by omega]

theorem DzwG_W {ws : List (Option ℕ)} (hG : GoodG ws)
    {y : ℕ} (hy : 2 ≤ y) {E : ℕ → TrioSeq → Prop} (hE : IfcV (y + 1) E)
    {c : ℕ} {Z : TrioSeq} (hZ : E c Z) : ∀ n : ℕ, Z ++ DzwG (c + 1) (y + 1) ws n ∈ W 0
  | 0 => by simpa [DzwG] using ((IfcV_iface (y + 1) hE).bok.aok _ _ hZ).mem
  | 1 => by
      have h1 : PU y (c + 1) (Z ++ DzwG (c + 1) (y + 1) ws 1) :=
        ⟨E, c, Z, ws.map (colG (c + 1) (y + 1)), hE, rfl, hZ, by simp [DzwG], hG.pu y c hy⟩
      exact ((BaseOk_PU y).aok _ _ h1).mem
  | (n + 2) => by
      have h := DzwG_chainU hG hy hE hZ n (ws.map (colG (c + n + 2) (y + n + 2)))
        (hG.pu (y + n + 1) (c + n + 1) (by omega))
      have h2 := ((BaseOk_PU (y + n + 1)).aok _ _ h).mem
      rw [DzwG_succ (c + 1) (y + 1) ws (n + 1)]
      simpa [List.append_assoc, show c + 1 + (n + 1) = c + n + 2 from by omega,
        show y + 1 + (n + 1) = y + n + 2 from by omega] using h2

theorem DzwG_W_RunG {ws : List (Option ℕ)} (hG : GoodG ws) {E : ℕ → TrioSeq → Prop} (hI : Iface E)
    {j c : ℕ} {X : TrioSeq} (hX : RunG E j c X) : ∀ n : ℕ, X ++ DzwG (c + 1) 2 ws n ∈ W 0 := by
  have hP : PkGA (c + 1) (X ++ DzwG (c + 1) 2 ws 1) :=
    ⟨E, hI, j, c, X, ws.map (colG (c + 1) 2), rfl, hX, by simp [DzwG], hG.pk c⟩
  intro n
  match n with
  | 0 => simpa [DzwG] using ((BaseOk_RunG hI.bok j).aok _ _ hX).mem
  | 1 => exact (PkGA_Aok hP).mem
  | (n + 2) =>
      have e : DzwG (c + 1) 2 ws (n + 2) = DzwG (c + 1) 2 ws 1 ++ DzwG (c + 1 + 1) 3 ws (n + 1) := by
        simp only [DzwG]
        rw [show n + 2 = 1 + (n + 1) from by omega, List.range_add, List.flatMap_append,
          List.flatMap_map]
        congr 1
        apply List.flatMap_congr
        intro k _
        simp [show c + 1 + (1 + k) = c + 1 + 1 + k from by omega, show 2 + (1 + k) = 3 + k from by omega]
      rw [e, ← List.append_assoc]
      exact DzwG_W hG (le_refl 2) (Ifc3_toIfcV Ifc3_PkGA) hP (n + 1)

theorem DzwG_W_LwA {ws : List (Option ℕ)} (hG : GoodG ws) {h : ℕ} {A : TrioSeq} (hA : LwA h A) :
    ∀ n : ℕ, A ++ DzwG (h + 1) 1 ws n ∈ W 0 := by
  have hX : RunA 0 (h + 1) (A ++ DzwG (h + 1) 1 ws 1) :=
    ⟨h, A, _, rfl, rfl, hA, by simpa [DzwG] using hG.seg h⟩
  intro n
  match n with
  | 0 => simpa [DzwG] using (LwA_Aok hA).mem
  | 1 => exact ((BaseOk_RunA 0).aok _ _ hX).mem
  | (n + 2) =>
      have e : DzwG (h + 1) 1 ws (n + 2) = DzwG (h + 1) 1 ws 1 ++ DzwG (h + 1 + 1) 2 ws (n + 1) := by
        simp only [DzwG]
        rw [show n + 2 = 1 + (n + 1) from by omega, List.range_add, List.flatMap_append,
          List.flatMap_map]
        congr 1
        apply List.flatMap_congr
        intro k _
        simp [show h + 1 + (1 + k) = h + 1 + 1 + k from by omega, show 1 + (1 + k) = 2 + k from by omega]
      rw [e, ← List.append_assoc]
      exact DzwG_W_RunG hG Iface_RunA0 (j := 0) hX (n + 1)

theorem DzwG_W_root {ws : List (Option ℕ)} (hG : GoodG ws) : ∀ n : ℕ, DzwG 0 0 ws n ∈ W 0
  | 0 => by simpa [DzwG] using W_nil 0
  | (n + 1) => by
      have e : DzwG 0 0 ws (n + 1) = DzwG 0 0 ws 1 ++ DzwG (0 + 1) 1 ws n := by
        simp only [DzwG]
        rw [show n + 1 = 1 + n from by omega, List.range_add, List.flatMap_append, List.flatMap_map]
        congr 1
        apply List.flatMap_congr
        intro k _
        simp [Nat.add_comm]
      rw [e]
      have h1 := DzwG_W_LwA hG (h := 0) (LwA_of_Aok hG.root) n
      simpa [DzwG] using h1

theorem Wv_snocz {ws : List (Option ℕ)} (hv : Wv ws) : Wv (ws ++ [none]) where
  head := by
    intro h
    cases ws with
    | nil => simp
    | cons t ws => simpa using hv.head (by simp)
  flat := fun e he => hv.flat e (by simpa using he)

/-- 補題 A（一般形）: 最後に z。 -/
theorem GoodG_snocz {ws : List (Option ℕ)} (hv : Wv ws) (hG : GoodG ws) :
    GoodG (ws ++ [none]) where
  pu := by
    intro y c hy
    refine ⟨fun x hx => by have := map_colG_ge (a := c + 1) (b := y + 1) (Wv_snocz hv) x hx; omega,
      map_colG_mono, ?_⟩
    intro E hE t Z hZ
    have h := z1wG_mem (Y0 := Z) (a := c + 1 + t) (b := y + 1) hv
      (fun n => by
        have := DzwG_W hG hy hE (c := c + t) (by simpa using hZ) n
        simpa [show c + t + 1 = c + 1 + t from by omega] using this)
    rw [List.map_append, shiftr01_append0, shift_map_colG]
    simp only [List.map_cons, List.map_nil, colG]
    rw [shift_zcol]
    simpa [List.append_assoc, show c + 1 + 1 + t = c + 1 + t + 1 from by omega] using h
  pk := by
    intro c E hI
    refine ⟨fun x hx => by have := map_colG_ge (a := c + 1) (b := 2) (Wv_snocz hv) x hx; omega,
      map_colG_mono, ?_⟩
    intro j t X hX
    have h := z1wG_mem (Y0 := X) (a := c + 1 + t) (b := 2) hv
      (fun n => by
        have := DzwG_W_RunG hG hI (c := c + t) hX n
        simpa [show c + t + 1 = c + 1 + t from by omega] using this)
    rw [List.map_append, shiftr01_append0, shift_map_colG]
    simp only [List.map_cons, List.map_nil, colG]
    rw [shift_zcol]
    simpa [List.append_assoc, show c + 1 + 1 + t = c + 1 + t + 1 from by omega] using h
  seg := by
    intro h
    refine ⟨?_, by simp [entry], ?_⟩
    · have h1 := MidD_wordG (h + 1) 1 (by omega) (by omega) (Wv_snocz hv)
      simpa [show h + 1 + 1 = h + 2 from by omega] using h1
    · intro P hP s A' hA'
      have hz := z1wG_mem (Y0 := A') (a := h + s + 1) (b := 1) hv
        (fun n => DzwG_W_LwA hG (h := h + s) ⟨P, hP, hA'⟩ n)
      rw [List.map_append]
      simp only [List.map_cons, List.map_nil, colG]
      rw [show ((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: (ws.map (colG (h + 1) 1) ++ [((h + 1 + 1, 1 + 1, 1) : ℕ × ℕ × ℕ)])
          = [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ ws.map (colG (h + 1) 1) ++ [((h + 1 + 1, 1 + 1, 1) : ℕ × ℕ × ℕ)] from rfl,
        shiftr01_append0, shiftr01_append0, shift_col, shift_map_colG, shift_zcol]
      simpa [List.append_assoc, show h + 1 + s = h + s + 1 from by omega,
        show h + 1 + 1 + s = h + s + 1 + 1 from by omega] using hz
  root := by
    have hmem := z1wG_mem (Y0 := []) (a := 0) (b := 0) hv (fun n => by simpa using DzwG_W_root hG n)
    exact Aok_rootG_of_mem (Wv_snocz hv) (by simpa [colG] using hmem)

/-- 語 `ws1 ++ seg^n`。 -/
def wordG (ws1 seg : List (Option ℕ)) (n : ℕ) : List (Option ℕ) :=
  ws1 ++ (List.range n).flatMap fun _ => seg

theorem map_wordG (f : Option ℕ → ℕ × ℕ × ℕ) (ws1 seg : List (Option ℕ)) (n : ℕ) :
    (wordG ws1 seg n).map f = ws1.map f ++ (List.range n).flatMap fun _ => seg.map f := by
  simp [wordG, List.map_flatMap]

theorem entry_map_colG_fst {a b : ℕ} {seg : List (Option ℕ)} {r : ℕ} (hr : r < seg.length) :
    entry (seg.map (colG a b)) 0 r = a + hgt seg[r] := by
  rw [entry_map_lt (colG a b) seg hr 0]
  cases hs : seg[r] <;> simp [colG, hgt, entry]

/-- 補題 B（一般形）: 最後が平坦な列 `some e`。`seg` は最も近い低い列からの区間。 -/
theorem GoodG_flat {ws1 seg : List (Option ℕ)} {e : ℕ} (hv : Wv (ws1 ++ seg ++ [some e]))
    (hne : seg ≠ []) (hhead : ∀ h0 : 0 < seg.length, hgt seg[0] < e)
    (htail : ∀ r (hr : r < seg.length), 1 ≤ r → e ≤ hgt seg[r])
    (hIH : ∀ n, 1 ≤ n → GoodG (wordG ws1 seg n)) :
    GoodG (ws1 ++ seg ++ [some e]) := by
  have hseglen : 0 < seg.length := List.length_pos_iff.mpr hne
  -- 共通: 台座つきの塔
  have key : ∀ (Y : TrioSeq) (a b : ℕ),
      (∀ n, 1 ≤ n → Y ++ (wordG ws1 seg n).map (colG a b) ∈ W 0) →
      Y ++ (ws1 ++ seg ++ [some e]).map (colG a b) ∈ W 0 := by
    intro Y a b hn
    have hmne : seg.map (colG a b) ≠ [] := by simpa using hne
    have h := flat_mem'' (Y0 := Y ++ ws1.map (colG a b)) (M := seg.map (colG a b)) (d := a + e)
      hmne (by rw [entry_map_colG_fst hseglen]; have := hhead hseglen; omega)
      (by intro r hr1 hrl
          rw [List.length_map] at hrl
          rw [entry_map_colG_fst hrl]; have := htail r hrl hr1; omega)
      (fun n => by
        match n with
        | 0 =>
            have h1 := hn 1 (le_refl 1)
            rw [map_wordG] at h1
            simp only [List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil] at h1
            have h2 := W_take (by rw [← List.append_assoc] at h1; exact h1) (Y ++ ws1.map (colG a b)).length
            rw [List.take_left] at h2
            simpa using h2
        | (n + 1) =>
            have h1 := hn (n + 1) (by omega)
            rw [map_wordG] at h1
            simpa [List.append_assoc] using h1)
    simpa [List.map_append, colG, List.append_assoc] using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y c hy
    refine ⟨fun x hx => by have := map_colG_ge (a := c + 1) (b := y + 1) hv x hx; omega,
      map_colG_mono, ?_⟩
    intro E hE t Z hZ
    rw [shift_map_colG]
    have := key (Z ++ [((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)]) (c + 1 + t) (y + 1) (fun n hn => by
      have hP : PU y (c + 1 + t) (Z ++ ([((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)] ++
          (wordG ws1 seg n).map (colG (c + 1 + t) (y + 1)))) :=
        ⟨E, c + t, Z, _, hE, by omega, hZ, by rw [show c + t + 1 = c + 1 + t from by omega],
          (hIH n hn).pu y (c + t) hy⟩
      simpa [List.append_assoc] using ((BaseOk_PU y).aok _ _ hP).mem)
    simpa [List.append_assoc] using this
  · intro c E hI
    refine ⟨fun x hx => by have := map_colG_ge (a := c + 1) (b := 2) hv x hx; omega,
      map_colG_mono, ?_⟩
    intro j t X hX
    rw [shift_map_colG]
    have := key (X ++ [((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ)]) (c + 1 + t) 2 (fun n hn => by
      have hP : PkGA (c + 1 + t) (X ++ ([((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ)] ++
          (wordG ws1 seg n).map (colG (c + 1 + t) 2))) :=
        ⟨E, hI, j, c + t, X, _, by omega, hX, by rw [show c + t + 1 = c + 1 + t from by omega],
          (hIH n hn).pk (c + t)⟩
      simpa [List.append_assoc] using (PkGA_Aok hP).mem)
    simpa [List.append_assoc] using this
  · intro h
    refine ⟨?_, by simp [entry], ?_⟩
    · have h1 := MidD_wordG (h + 1) 1 (by omega) (by omega) hv
      simpa [show h + 1 + 1 = h + 2 from by omega] using h1
    · intro P hP s A' hA'
      rw [show ((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: (ws1 ++ seg ++ [some e]).map (colG (h + 1) 1)
          = [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ (ws1 ++ seg ++ [some e]).map (colG (h + 1) 1) from rfl,
        shiftr01_append0, shift_col, shift_map_colG]
      have := key (A' ++ [((h + 1 + s, 1, 0) : ℕ × ℕ × ℕ)]) (h + 1 + s) 1 (fun n hn => by
        have hR : RunA 0 (h + s + 1) (A' ++ (((h + s + 1, 1, 0) : ℕ × ℕ × ℕ) ::
            (wordG ws1 seg n).map (colG (h + s + 1) 1))) :=
          ⟨h + s, A', _, rfl, rfl, ⟨P, hP, hA'⟩, (hIH n hn).seg (h + s)⟩
        have := ((BaseOk_RunA 0).aok _ _ hR).mem
        simpa [List.append_assoc, show h + s + 1 = h + 1 + s from by omega] using this)
      simpa [List.append_assoc] using this
  · refine Aok_rootG_of_mem hv ?_
    have := key [((0, 0, 0) : ℕ × ℕ × ℕ)] 0 0 (fun n hn => by simpa using (hIH n hn).root.mem)
    simpa using this

/-- 影: z を `(1,0,0)`、平坦な列をそのままにした平坦な行列。 -/
def shw (ws : List (Option ℕ)) : TrioSeq := ws.map fun t => ((hgt t, 0, 0) : ℕ × ℕ × ℕ)

theorem Flat_shw (ws : List (Option ℕ)) : Flat (((0, 0, 0) : ℕ × ℕ × ℕ) :: shw ws) := by
  intro c hc
  simp only [List.mem_cons, shw, List.mem_map] at hc
  rcases hc with rfl | ⟨t, -, rfl⟩ <;> simp

theorem Wv_sub {ws ws2 : List (Option ℕ)} (hv : Wv ws) (hsub : ∀ t ∈ ws2, t ∈ ws)
    (hhead : ∀ h : 0 < ws2.length, ws2[0] = none) : Wv ws2 :=
  ⟨hhead, fun e he => hv.flat e (hsub _ he)⟩

theorem Wv_of_append_left {ws1 ws2 : List (Option ℕ)} (hv : Wv (ws1 ++ ws2)) : Wv ws1 := by
  refine Wv_sub hv (fun t ht => List.mem_append_left _ ht) ?_
  intro h
  have := hv.head (by simp; omega)
  rwa [List.getElem_append_left h] at this

theorem entry_shw_fst {ws : List (Option ℕ)} {r : ℕ} (hr : r < ws.length) :
    entry (shw ws) 0 r = hgt ws[r] := by
  simp only [shw]
  rw [entry_map_lt _ ws hr 0]
  simp [entry]

/-- ★★★★★ 妥当な語はすべて普遍（影の W 帰納法）。 -/
theorem GoodG_all : ∀ ws : List (Option ℕ), Wv ws → GoodG ws := by
  have key : W 0 ⊆ {Fl : TrioSeq | ∀ ws : List (Option ℕ), Wv ws →
      Fl = ((0, 0, 0) : ℕ × ℕ × ℕ) :: shw ws → GoodG ws} := by
    refine A2' ?_
    intro Fl hFl
    simp only [Set.mem_setOf_eq]
    intro ws hv hFl_eq
    rcases hFl with ⟨hlen, -⟩ | h2 | ⟨m, hm, -⟩
    · -- 長さ 1: ws = []
      subst hFl_eq
      have : ws = [] := by
        simp only [List.length_cons, shw, List.length_map] at hlen
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst this; exact GoodG_nil
    · subst hFl_eq
      rcases List.eq_nil_or_concat ws with hnil | ⟨ws', t, hws⟩
      · subst hnil; exact GoodG_nil
      · rw [List.concat_eq_append] at hws
        subst hws
        have hv' : Wv ws' := Wv_of_append_left hv
        have hL : 1 < (((0, 0, 0) : ℕ × ℕ × ℕ) :: shw (ws' ++ [t])).length := by
          simp [shw]
        have hdrop : (((0, 0, 0) : ℕ × ℕ × ℕ) :: shw (ws' ++ [t]))⟦1⟧
            = ((0, 0, 0) : ℕ × ℕ × ℕ) :: shw ws' := by
          rw [oper_one_eq_dropLast hL,
            show (((0, 0, 0) : ℕ × ℕ × ℕ) :: shw (ws' ++ [t])) = (((0, 0, 0) : ℕ × ℕ × ℕ) :: shw ws') ++ [((hgt t, 0, 0) : ℕ × ℕ × ℕ)] from by simp [shw],
            List.dropLast_concat]
        have hG' : GoodG ws' := h2 1 (le_refl 1) ws' hv' hdrop
        cases t with
        | none => exact GoodG_snocz hv' hG'
        | some e =>
          -- 最も近い低い列
          have hws'ne : ws' ≠ [] := by
            rintro rfl
            have := hv.head (by simp)
            simp at this
          have hlen' : 0 < ws'.length := List.length_pos_iff.mpr hws'ne
          have hhead0 : ws'[0] = none := by
            have := hv.head (by simp)
            rwa [List.getElem_append_left hlen'] at this
          have he2 : 2 ≤ e := hv.flat e (by simp)
          obtain ⟨i', hi', hlt, hall⟩ := nearest_lower (f := fun j => hgt (ws'.getD j none)) (v := e)
            ws'.length ⟨0, hlen', by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen', hhead0, hgt]; omega⟩
          set ws1 := ws'.take i' with hws1
          set seg := ws'.drop i' with hseg
          have hsplit : ws' = ws1 ++ seg := by simp [hws1, hseg]
          have hsegne : seg ≠ [] := by
            intro h
            have := congrArg List.length h
            simp [hseg] at this; omega
          have hseglen : 0 < seg.length := List.length_pos_iff.mpr hsegne
          have hseg_get : ∀ r (hr : r < seg.length), seg[r] = ws'[i' + r]'(by simp [hseg] at hr; omega) := by
            intro r hr
            simp [hseg]
          have hlt' : hgt ws'[i'] < e := by
            simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi'] using hlt
          have hsegh : ∀ h0 : 0 < seg.length, hgt seg[0] < e := by
            intro h0
            rw [hseg_get 0 h0]
            simpa using hlt'
          have hsegt : ∀ r (hr : r < seg.length), 1 ≤ r → e ≤ hgt seg[r] := by
            intro r hr hr1
            have hlt2 : i' + r < ws'.length := by simp [hseg] at hr; omega
            rw [hseg_get r hr]
            have := hall (i' + r) (by omega) hlt2
            simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt2] using this
          rw [hsplit] at hv ⊢
          refine GoodG_flat hv hsegne hsegh hsegt ?_
          intro n hn
          -- 影の展開 = wordG の影
          have hFl : ((0, 0, 0) : ℕ × ℕ × ℕ) :: shw (ws1 ++ seg ++ [some e])
              = (((0, 0, 0) : ℕ × ℕ × ℕ) :: shw ws1) ++ shw seg ++ [((e, 0, 0) : ℕ × ℕ × ℕ)] := by
            simp [shw, List.map_append, hgt]
          have hop : (((0, 0, 0) : ℕ × ℕ × ℕ) :: shw (ws1 ++ seg ++ [some e]))⟦n⟧
              = ((0, 0, 0) : ℕ × ℕ × ℕ) :: shw (wordG ws1 seg n) := by
            rw [hFl, oper_snoc00'' _ (by simpa [shw] using hsegne)
              (by rw [entry_shw_fst hseglen]; exact hsegh hseglen)
              (by intro r hr1 hrl
                  rw [shw, List.length_map] at hrl
                  rw [entry_shw_fst hrl]; exact hsegt r hrl hr1)]
            simp [shw, wordG, List.map_flatMap]
          have hvn : Wv (wordG ws1 seg n) := by
            refine Wv_sub hv ?_ ?_
            · intro t ht
              simp only [wordG, List.mem_append, List.mem_flatMap, List.mem_range] at ht
              rcases ht with h | ⟨-, -, h⟩
              · simp [h]
              · simp [h]
            · intro h
              obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
              have hw : wordG ws1 seg (n' + 1) = ws' ++ (List.range n').flatMap (fun _ => seg) := by
                simp only [wordG]
                rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, hsplit]
                simp [List.append_assoc]
              rw [List.getElem_of_eq hw, List.getElem_append_left hlen']
              exact hhead0
          rw [← hsplit] at hop
          exact h2 n hn (wordG ws1 seg n) hvn hop
    · omega
  intro ws hv
  exact key (Flat_mem_W (Flat_shw ws)) ws hv rfl

#print axioms GoodG_all
/-! ### `MidD` の `head1` なし版 `MidH` と、平坦な列を bad root にする 1 の列の展開。行 336 -/

structure MidH (d : ℕ) (M : TrioSeq) : Prop where
  ne : M ≠ []
  head : entry M 0 0 + 1 = d
  tail : ∀ j, 1 ≤ j → j < M.length → d ≤ entry M 0 j

theorem MidD.toMidH {d : ℕ} {M : TrioSeq} (h : MidD d M) : MidH d M := ⟨h.ne, h.head, h.tail⟩

open Classical in
/-- 内部アンカーでの継ぎ足しの展開（head1 なし版）。 -/
theorem oper_snocYH {Y0 M : TrioSeq} {L y : ℕ} (hY0ne : Y0 ≠ [])
    (hM : MidH (L + 1) M) (hMe : entry M 1 0 < y) (hy : 1 ≤ y) (n : ℕ) :
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


theorem snocYH_mem {Y0 M : TrioSeq} {L y : ℕ} (hY0ne : Y0 ≠ [])
    (hM : MidH (L + 1) M) (hMe : entry M 1 0 < y) (hy : 1 ≤ y)
    (htw : ∀ n, Mtw Y0 M n ∈ W 0) :
    (Y0 ++ M) ++ [((L + 1, y, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_snocYH hY0ne hM hMe hy n]
  exact htw n

/-- 行 336 の塔の段の語: `[z, flat 2, flat 3, …, flat (n+1)]`。 -/
def wf336 (n : ℕ) : List (Option ℕ) := none :: (List.range n).map fun k => some (k + 2)

theorem Wv_wf336 (n : ℕ) : Wv (wf336 n) where
  head := fun _ => rfl
  flat := by
    intro e he
    simp only [wf336, List.mem_cons, List.mem_map, List.mem_range] at he
    rcases he with h | ⟨k, -, h⟩
    · cases h
    · cases h; omega

theorem Mtw_Q200 (n : ℕ) : Mtw Q [((2, 0, 0) : ℕ × ℕ × ℕ)] n
    = ((0, 0, 0) : ℕ × ℕ × ℕ) :: (wf336 n).map (colG 0 0) := by
  simp [Mtw, Q, wf336, colG, shiftr01, flatMap_singleton_map, Function.comp_def, Nat.add_comm]

/-- ★★★★★ シート行336 `(0,0,0)(1,1,1)(2,0,0)(3,1,0) = psi(W_w*psi(W))`。 -/
theorem R336_mem : R325 ++ [((3, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := snocYH_mem (Y0 := Q) (M := [((2, 0, 0) : ℕ × ℕ × ℕ)]) (L := 2) (y := 1) Q_ne
    ⟨by simp, by simp [entry], by intro j hj hjl; simp at hjl; omega⟩ (by simp [entry]) (le_refl 1)
    (fun n => by rw [Mtw_Q200]; exact (GoodG_all _ (Wv_wf336 n)).root.mem)
  simpa [R325, Q] using h

#print axioms R336_mem

/-! ### 荷（payload）つきの字 `zY := (a+1,b+1,1) :: Y↑(a+2)` の語 `wordP`。行 337〜345 -/

/-- 字 `zY`。`Y = []` は裸の z。 -/
def colP (a b : ℕ) (Y : TrioSeq) : TrioSeq :=
  ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 (a + 2) 0 Y

/-- 語（字の列の連結）。 -/
def wordP (a b : ℕ) (ws : List TrioSeq) : TrioSeq := ws.flatMap (colP a b)

/-- 荷はすべて `Bok`。 -/
def Wpl (ws : List TrioSeq) : Prop := ∀ Y ∈ ws, Bok Y

theorem Wp_nil : Wpl [] := fun _ h => by simp at h

theorem Wp_of_append_left {ws1 ws2 : List TrioSeq} (h : Wpl (ws1 ++ ws2)) : Wpl ws1 :=
  fun Y hY => h Y (List.mem_append_left _ hY)

theorem Wp_append {ws1 ws2 : List TrioSeq} (h1 : Wpl ws1) (h2 : Wpl ws2) : Wpl (ws1 ++ ws2) := by
  intro Y hY
  rcases List.mem_append.mp hY with h | h
  · exact h1 Y h
  · exact h2 Y h

theorem Wp_singleton {Y : TrioSeq} (hY : Bok Y) : Wpl [Y] := by
  intro Y' hY'
  simp only [List.mem_singleton] at hY'
  subst hY'; exact hY

theorem wordP_nil (a b : ℕ) : wordP a b [] = [] := rfl

theorem wordP_append (a b : ℕ) (ws1 ws2 : List TrioSeq) :
    wordP a b (ws1 ++ ws2) = wordP a b ws1 ++ wordP a b ws2 := by
  simp [wordP]

theorem wordP_singleton (a b : ℕ) (Y : TrioSeq) : wordP a b [Y] = colP a b Y := by
  simp [wordP]

theorem wordP_cons (a b : ℕ) (Y : TrioSeq) (ws : List TrioSeq) :
    wordP a b (Y :: ws) = colP a b Y ++ wordP a b ws := by
  simp [wordP]

theorem colP_shift (a b s : ℕ) (Y : TrioSeq) : shiftr01 s 0 (colP a b Y) = colP (a + s) b Y := by
  rw [colP, show ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 (a + 2) 0 Y
      = [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] ++ shiftr01 (a + 2) 0 Y from rfl,
    shiftr01_append0, shift_zcol, shiftr01_add0, show a + 2 + s = a + s + 2 from by omega,
    show a + 1 + s = a + s + 1 from by omega]
  rfl

theorem wordP_shift (a b s : ℕ) (ws : List TrioSeq) :
    shiftr01 s 0 (wordP a b ws) = wordP (a + s) b ws := by
  induction ws with
  | nil => simp [wordP, shiftr01]
  | cons Y ws ih => rw [wordP_cons, wordP_cons, shiftr01_append0, colP_shift, ih]

theorem colP_ge (a b : ℕ) (Y : TrioSeq) : ∀ x ∈ colP a b Y, a + 1 ≤ x.1 := by
  intro x hx
  simp only [colP, List.mem_cons, shiftr01, List.mem_map] at hx
  rcases hx with rfl | ⟨p, -, rfl⟩
  · exact le_refl _
  · show a + 1 ≤ p.1 + (a + 2); omega

theorem wordP_ge (a b : ℕ) (ws : List TrioSeq) : ∀ x ∈ wordP a b ws, a + 1 ≤ x.1 := by
  intro x hx
  simp only [wordP, List.mem_flatMap] at hx
  obtain ⟨Y, -, hx⟩ := hx
  exact colP_ge a b Y x hx

theorem colP_mono {a b : ℕ} {Y : TrioSeq} (hY : Mono Y) : Mono (colP a b Y) := by
  intro x hx
  simp only [colP, List.mem_cons, shiftr01, List.mem_map] at hx
  rcases hx with rfl | ⟨p, hp, rfl⟩
  · show 1 ≤ b + 1; omega
  · simpa using hY p hp

theorem wordP_mono {a b : ℕ} {ws : List TrioSeq} (hw : Wpl ws) : Mono (wordP a b ws) := by
  intro x hx
  simp only [wordP, List.mem_flatMap] at hx
  obtain ⟨Y, hY, hx⟩ := hx
  exact colP_mono (hw Y hY).mono x hx

theorem MidD_wordP (a v : ℕ) (ha : 1 ≤ a) (hv : 1 ≤ v) {ws : List TrioSeq} (hw : Wpl ws) :
    MidD (a + 1) (((a, v, 0) : ℕ × ℕ × ℕ) :: wordP a v ws) := by
  have h := MidD_append (MidD_col a v ha hv) (N := wordP a v ws) (wordP_ge a v ws) (wordP_mono hw)
  simpa using h

theorem Aok_rootP_of_mem {ws : List TrioSeq} (hw : Wpl ws)
    (hmem : (((0, 0, 0) : ℕ × ℕ × ℕ) :: wordP 0 0 ws) ∈ W 0) :
    Aok (((0, 0, 0) : ℕ × ℕ × ℕ) :: wordP 0 0 ws) := by
  refine ⟨hmem, by simp, ⟨by simp [entry], ?_⟩, ?_, ?_⟩
  · intro j hj hjl
    obtain ⟨q, rfl⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
    have hql : q < (wordP 0 0 ws).length := by simp at hjl; omega
    have : entry (((0, 0, 0) : ℕ × ℕ × ℕ) :: wordP 0 0 ws) 0 (q + 1)
        = entry (wordP 0 0 ws) 0 q := by simp [entry]
    rw [this]
    have hge := wordP_ge 0 0 ws _ (List.getElem_mem hql)
    have he : entry (wordP 0 0 ws) 0 q = ((wordP 0 0 ws)[q]).1 := by
      simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hql]
    omega
  · intro c hc h0
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨rfl, rfl⟩
    · exfalso; have := wordP_ge 0 0 ws c hc; omega
  · intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp
    · exact wordP_mono hw c hc

/-- 語つきの対角の塔。 -/
def DzwP (a b : ℕ) (ws : List TrioSeq) (n : ℕ) : TrioSeq :=
  (List.range n).flatMap fun k => ((a + k, b + k, 0) : ℕ × ℕ × ℕ) :: wordP (a + k) (b + k) ws

theorem DzwP_succ (a b : ℕ) (ws : List TrioSeq) (n : ℕ) : DzwP a b ws (n + 1) =
    DzwP a b ws n ++ (((a + n, b + n, 0) : ℕ × ℕ × ℕ) :: wordP (a + n) (b + n) ws) := by
  simp [DzwP, List.range_succ]

/-- `GoodP ws`: 荷つきの語 `ws` は 4 つの段で普遍。 -/
structure GoodP (ws : List TrioSeq) : Prop where
  pu : ∀ (y c : ℕ), 2 ≤ y → JkU y c (wordP (c + 1) (y + 1) ws)
  pk : ∀ c : ℕ, JkGU c (wordP (c + 1) 2 ws)
  seg : ∀ h : ℕ, SegA h (((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordP (h + 1) 1 ws)
  root : Aok (((0, 0, 0) : ℕ × ℕ × ℕ) :: wordP 0 0 ws)

theorem GoodP_nil : GoodP [] where
  pu := fun y c hy => by simpa [wordP] using JkU_nil' hy c
  pk := fun c => by simpa [wordP] using JkGU_nil c
  seg := fun h => by simpa [wordP] using SegA_one h
  root := by simpa [wordP] using Am_Aok 0

theorem DzwP_chainU {ws : List TrioSeq} (hG : GoodP ws)
    {y : ℕ} (hy : 2 ≤ y) {E : ℕ → TrioSeq → Prop} (hE : IfcV (y + 1) E)
    {c : ℕ} {Z : TrioSeq} (hZ : E c Z) :
    ∀ (n : ℕ) (J : TrioSeq), JkU (y + n + 1) (c + n + 1) J →
      PU (y + n + 1) (c + n + 2)
        (Z ++ DzwP (c + 1) (y + 1) ws (n + 1) ++ ([((c + n + 2, y + n + 2, 0) : ℕ × ℕ × ℕ)] ++ J))
  | 0, J, hJ => by
      have h1 : PU y (c + 1) (Z ++ DzwP (c + 1) (y + 1) ws 1) :=
        ⟨E, c, Z, wordP (c + 1) (y + 1) ws, hE, rfl, hZ, by simp [DzwP], hG.pu y c hy⟩
      exact ⟨PU y, c + 1, _, J, IfcV_PU (by omega) (y + 0 + 1 + 1) (by omega), by omega, h1,
        by simp, hJ⟩
  | (n + 1), J, hJ => by
      have ih := DzwP_chainU hG hy hE hZ n (wordP (c + n + 2) (y + n + 2) ws)
        (hG.pu (y + n + 1) (c + n + 1) (by omega))
      refine ⟨PU (y + n + 1), c + n + 2, _, J, IfcV_PU (by omega) (y + (n + 1) + 1 + 1) (by omega),
        by omega, ih, ?_, by simpa [show y + (n + 1) + 1 = y + n + 1 + 1 from by omega,
          show c + (n + 1) + 1 = c + n + 1 + 1 from by omega] using hJ⟩
      rw [DzwP_succ (c + 1) (y + 1) ws (n + 1)]
      simp [List.append_assoc, show c + 1 + (n + 1) = c + n + 2 from by omega,
        show y + 1 + (n + 1) = y + n + 2 from by omega,
        show c + (n + 1) + 2 = c + n + 3 from by omega,
        show y + (n + 1) + 2 = y + n + 3 from by omega,
        show c + n + 2 + 1 = c + n + 3 from by omega]

theorem DzwP_W {ws : List TrioSeq} (hG : GoodP ws)
    {y : ℕ} (hy : 2 ≤ y) {E : ℕ → TrioSeq → Prop} (hE : IfcV (y + 1) E)
    {c : ℕ} {Z : TrioSeq} (hZ : E c Z) : ∀ n : ℕ, Z ++ DzwP (c + 1) (y + 1) ws n ∈ W 0
  | 0 => by simpa [DzwP] using ((IfcV_iface (y + 1) hE).bok.aok _ _ hZ).mem
  | 1 => by
      have h1 : PU y (c + 1) (Z ++ DzwP (c + 1) (y + 1) ws 1) :=
        ⟨E, c, Z, wordP (c + 1) (y + 1) ws, hE, rfl, hZ, by simp [DzwP], hG.pu y c hy⟩
      exact ((BaseOk_PU y).aok _ _ h1).mem
  | (n + 2) => by
      have h := DzwP_chainU hG hy hE hZ n (wordP (c + n + 2) (y + n + 2) ws)
        (hG.pu (y + n + 1) (c + n + 1) (by omega))
      have h2 := ((BaseOk_PU (y + n + 1)).aok _ _ h).mem
      rw [DzwP_succ (c + 1) (y + 1) ws (n + 1)]
      simpa [List.append_assoc, show c + 1 + (n + 1) = c + n + 2 from by omega,
        show y + 1 + (n + 1) = y + n + 2 from by omega] using h2

theorem DzwP_W_RunG {ws : List TrioSeq} (hG : GoodP ws) {E : ℕ → TrioSeq → Prop} (hI : Iface E)
    {j c : ℕ} {X : TrioSeq} (hX : RunG E j c X) : ∀ n : ℕ, X ++ DzwP (c + 1) 2 ws n ∈ W 0 := by
  have hP : PkGA (c + 1) (X ++ DzwP (c + 1) 2 ws 1) :=
    ⟨E, hI, j, c, X, wordP (c + 1) 2 ws, rfl, hX, by simp [DzwP], hG.pk c⟩
  intro n
  match n with
  | 0 => simpa [DzwP] using ((BaseOk_RunG hI.bok j).aok _ _ hX).mem
  | 1 => exact (PkGA_Aok hP).mem
  | (n + 2) =>
      have e : DzwP (c + 1) 2 ws (n + 2) = DzwP (c + 1) 2 ws 1 ++ DzwP (c + 1 + 1) 3 ws (n + 1) := by
        simp only [DzwP]
        rw [show n + 2 = 1 + (n + 1) from by omega, List.range_add, List.flatMap_append,
          List.flatMap_map]
        congr 1
        apply List.flatMap_congr
        intro k _
        simp [show c + 1 + (1 + k) = c + 1 + 1 + k from by omega, show 2 + (1 + k) = 3 + k from by omega]
      rw [e, ← List.append_assoc]
      exact DzwP_W hG (le_refl 2) (Ifc3_toIfcV Ifc3_PkGA) hP (n + 1)

theorem DzwP_W_LwA {ws : List TrioSeq} (hG : GoodP ws) {h : ℕ} {A : TrioSeq} (hA : LwA h A) :
    ∀ n : ℕ, A ++ DzwP (h + 1) 1 ws n ∈ W 0 := by
  have hX : RunA 0 (h + 1) (A ++ DzwP (h + 1) 1 ws 1) :=
    ⟨h, A, _, rfl, rfl, hA, by simpa [DzwP] using hG.seg h⟩
  intro n
  match n with
  | 0 => simpa [DzwP] using (LwA_Aok hA).mem
  | 1 => exact ((BaseOk_RunA 0).aok _ _ hX).mem
  | (n + 2) =>
      have e : DzwP (h + 1) 1 ws (n + 2) = DzwP (h + 1) 1 ws 1 ++ DzwP (h + 1 + 1) 2 ws (n + 1) := by
        simp only [DzwP]
        rw [show n + 2 = 1 + (n + 1) from by omega, List.range_add, List.flatMap_append,
          List.flatMap_map]
        congr 1
        apply List.flatMap_congr
        intro k _
        simp [show h + 1 + (1 + k) = h + 1 + 1 + k from by omega, show 1 + (1 + k) = 2 + k from by omega]
      rw [e, ← List.append_assoc]
      exact DzwP_W_RunG hG Iface_RunA0 (j := 0) hX (n + 1)

theorem DzwP_W_root {ws : List TrioSeq} (hG : GoodP ws) : ∀ n : ℕ, DzwP 0 0 ws n ∈ W 0
  | 0 => by simpa [DzwP] using W_nil 0
  | (n + 1) => by
      have e : DzwP 0 0 ws (n + 1) = DzwP 0 0 ws 1 ++ DzwP (0 + 1) 1 ws n := by
        simp only [DzwP]
        rw [show n + 1 = 1 + n from by omega, List.range_add, List.flatMap_append, List.flatMap_map]
        congr 1
        apply List.flatMap_congr
        intro k _
        simp [Nat.add_comm]
      rw [e]
      have h1 := DzwP_W_LwA hG (h := 0) (LwA_of_Aok hG.root) n
      simpa [DzwP] using h1


/-! ### z=1 の列の展開のマスク付き一般形。間の列 `C` は高さ ≥ a+1 なら何でもよく、
行 1 の上昇は `le1` のまま残す。 -/

open Classical in
theorem oper_z1_mask (Y0 : TrioSeq) (a b : ℕ) (C : TrioSeq) (hge : ∀ x ∈ C, a + 1 ≤ x.1) (n : ℕ) :
    (Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: C ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]))⟦n⟧
      = Y0 ++ (List.range n).flatMap fun k => ((a + k, b + k, 0) : ℕ × ℕ × ℕ) ::
          (List.range C.length).map fun i =>
            ((entry C 0 i + k, entry C 1 i +
              (if le1 (Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: C ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]))
                Y0.length (Y0.length + 1 + i) then k else 0), entry C 2 i) : ℕ × ℕ × ℕ) := by
  set T : TrioSeq := ((a, b, 0) : ℕ × ℕ × ℕ) :: C ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] with hT
  set M : TrioSeq := Y0 ++ T with hM
  set p := Y0.length with hp
  set L := C.length with hL
  have hlen : M.length = p + L + 2 := by simp [hM, hT, hp, hL]; omega
  have eT : ∀ i q, entry M i (p + q) = entry T i q := fun i q => entry_append_right Y0 T i q
  have e0p : entry M 0 p = a := by rw [show p = p + 0 from rfl, eT]; simp [hT, entry]
  have e1p : entry M 1 p = b := by rw [show p = p + 0 from rfl, eT]; simp [hT, entry]
  have e2p : entry M 2 p = 0 := by rw [show p = p + 0 from rfl, eT]; simp [hT, entry]
  have eC : ∀ r i, i < L → entry M r (p + 1 + i) = entry C r i := by
    intro r i hi
    rw [show p + 1 + i = p + (i + 1) from by omega, eT]
    simp only [hT, entry, List.cons_append, List.getD_cons_succ]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]
  have eq : ∀ r, entry M r (p + 1 + L) = entry [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] r 0 := by
    intro r
    rw [show p + 1 + L = p + (L + 1) from by omega, eT]
    simp only [hT, entry, List.cons_append, List.getD_cons_succ]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega)]
    simp [hL]
  have ege : ∀ i, i < L → a + 1 ≤ entry M 0 (p + 1 + i) := by
    intro i hi
    rw [eC 0 i hi]
    have hi' : i < C.length := by omega
    have := hge (C[i]'hi') (List.getElem_mem hi')
    have he : entry C 0 i = (C[i]'hi').1 := by
      simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    omega
  have ege' : ∀ j, p < j → j < p + 1 + L → a + 1 ≤ entry M 0 j := by
    intro j hj1 hj2
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < L ∧ j = p + 1 + i := ⟨j - (p + 1), by omega, by omega⟩
    exact ege i hi
  have eqL : entry M 0 (p + 1 + L) = a + 1 ∧ entry M 1 (p + 1 + L) = b + 1 ∧
      entry M 2 (p + 1 + L) = 1 := by
    rw [eq 0, eq 1, eq 2]; simp [entry]
  have hanc : ∀ j j', p < j' → le0 M j' j → entry M 0 j = a + 1 →
      (∀ j'', p < j'' → j'' < j → a + 1 ≤ entry M 0 j'') → j' = j := by
    intro j j' hj' hle hj hbetween
    obtain ⟨hj'l, hjl, hch⟩ := hle
    rcases Relation.ReflTransGen.cases_tail hch with h1 | ⟨c, hc1, hc2⟩
    · exact h1.symm
    · exfalso
      have hcj : c < j := hc2.2.2.1
      have hcle : j' ≤ c := le0_le' ⟨hj'l, hc2.1, hc1⟩
      have hlt : entry M 0 c < entry M 0 j := hc2.2.2.2.1
      have := hbetween c (by omega) hcj
      omega
  -- 語の列はすべて p の行 0 の子孫
  have hl0 : ∀ j, p < j → j < p + 1 + L → le0 M p j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj1 hj2
      obtain ⟨j', hj'1, hlt, hall⟩ := nearest_lower (f := fun i => entry M 0 i) (v := entry M 0 j) j
        ⟨p, hj1, by show entry M 0 p < entry M 0 j; rw [e0p]; have := ege' j hj1 hj2; omega⟩
      have hlt' : entry M 0 j' < entry M 0 j := hlt
      have hall' : ∀ i, j' < i → i < j → entry M 0 j ≤ entry M 0 i := hall
      have hn : nextrel0 M j' j :=
        ⟨by omega, by omega, hj'1, hlt', fun i hi => hall' i hi.1 hi.2⟩
      rcases Nat.lt_or_ge p j' with hpj | hpj
      · have := ih j' hj'1 hpj (by omega)
        exact ⟨by omega, by omega, this.2.2.trans (Relation.ReflTransGen.single hn)⟩
      · have : j' = p := by
          rcases Nat.lt_or_ge j' p with h | h
          · exfalso
            have := hall' p h hj1
            rw [e0p] at this
            have := ege' j hj1 hj2
            omega
          · omega
        subst this
        exact ⟨by omega, by omega, Relation.ReflTransGen.single hn⟩
  -- 最後の列
  have hn0L : nextrel0 M p (p + 1 + L) := by
    refine ⟨by omega, by omega, by omega, by rw [e0p, eqL.1]; omega, ?_⟩
    intro j hj
    rw [eqL.1]; exact ege' j hj.1 hj.2
  have hl0L : le0 M p (p + 1 + L) := ⟨by omega, by omega, Relation.ReflTransGen.single hn0L⟩
  have hn1L : nextrel1 M p (p + 1 + L) := by
    refine ⟨by omega, by omega, by omega, by rw [e1p, eqL.2.1]; omega, hl0L, ?_⟩
    intro j hj
    have := hanc (p + 1 + L) j hj.1 hj.2 eqL.1 (fun j'' h1 h2 => ege' j'' h1 h2)
    subst this; exact le_rfl
  have hn2L : nextrel2 M p (p + 1 + L) := by
    refine ⟨by omega, by omega, by omega, by rw [e2p, eqL.2.2]; omega,
      ⟨by omega, by omega, Relation.ReflTransGen.single hn1L⟩, ?_⟩
    intro j hj
    have := hanc (p + 1 + L) j hj.1 (le0_of_le1 hj.2) eqL.1 (fun j'' h1 h2 => ege' j'' h1 h2)
    subst this; rw [eqL.2.2]
  have hpar : hasParent M 2 (p + 1 + L) :=
    hasParent2_of_le1_witness (by omega) (Relation.ReflTransGen.single hn1L)
      (by rw [e2p, eqL.2.2]; omega)
  have hparent : parent M 2 (p + 1 + L) = p := hpar.unique (parent_nextR hpar) hn2L
  have hsrow : srow M (p + 1 + L) = 2 := by simp [srow, eqL.2.2]
  have hl00 : le0 M p p := ⟨by omega, by omega, Relation.ReflTransGen.refl⟩
  have hl11 : le1 M p p := ⟨by omega, by omega, Relation.ReflTransGen.refl⟩
  rw [L53.oper_unfold (j1 := p + 1 + L) (i1 := 2) (j0 := p) (d0 := 1) (d1 := 1)
      (by omega) (by omega) (by rw [eqL.1]; omega) hsrow.symm hpar hparent.symm
      (by rw [if_pos (by omega : 0 < 2), eqL.1, e0p]; omega)
      (by rw [if_pos (by omega : 1 < 2), eqL.2.1, e1p]; omega) n]
  have hr : List.range' p (p + 1 + L - p) = p :: List.range' (p + 1) L := by
    rw [show p + 1 + L - p = L + 1 from by omega, List.range'_succ]
  have htk : M.take p = Y0 := by rw [hM, hp, List.take_left]
  rw [hr, htk]
  have hbody : ∀ k : ℕ, (p :: List.range' (p + 1) L).map
      (fun j => ((entry M 0 j + (if le0 M p j then k * 1 else 0),
        entry M 1 j + (if le1 M p j then k * 1 else 0),
        entry M 2 j) : ℕ × ℕ × ℕ))
      = ((a + k, b + k, 0) : ℕ × ℕ × ℕ) :: (List.range L).map fun i =>
          ((entry C 0 i + k, entry C 1 i + (if le1 M p (p + 1 + i) then k else 0),
            entry C 2 i) : ℕ × ℕ × ℕ) := by
    intro k
    rw [List.map_cons]
    congr 1
    · rw [if_pos hl00, if_pos hl11, e0p, e1p, e2p]; simp
    · apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_range'_1, List.getElem_range]
        have hi : i < L := by simpa using h2
        rw [if_pos (hl0 (p + 1 + i) (by omega) (by omega)), eC 0 i hi, eC 1 i hi, eC 2 i hi]
        simp
  rw [List.flatMap_congr (fun k _ => hbody k)]

/-- 行 1 の親鎖は「行 1 が 0 の行 0 祖先を区間内に持つ」区間 `[s, e)` から下へ出ない。 -/
theorem le1_lower_bound {M : TrioSeq} {s e : ℕ}
    (hroot : ∀ j, s ≤ j → j < e → ∃ r, s ≤ r ∧ r ≤ j ∧ le0 M r j ∧ entry M 1 r = 0) :
    ∀ x j, le1 M x j → s ≤ j → j < e → s ≤ x := by
  intro x j hx
  obtain ⟨-, -, h⟩ := hx
  induction h with
  | refl => intro h1 _; exact h1
  | @tail y j' _ hyj ih =>
      intro hj1 hj2
      obtain ⟨r, hr1, hr2, hr3, hr4⟩ := hroot j' hj1 hj2
      have hry : r ≤ y := by
        by_contra hc
        have hc' : y < r := Nat.lt_of_not_le hc
        have h1 := hyj.2.2.2.2.2 r ⟨hc', hr3⟩
        have h2 := hyj.2.2.2.1
        omega
      exact ih (by omega) (by have := hyj.2.2.1; omega)

/-- 荷のブロック `[s, e)`（先頭が高さ `d`、他は高さ ≥ d、高さ d の列は行 1 が 0）では、
どの列も行 1 が 0 の行 0 祖先をブロック内に持つ。 -/
theorem block_root {M : TrioSeq} {s e d : ℕ} (he : e ≤ M.length)
    (hs : entry M 0 s = d)
    (hge : ∀ j, s ≤ j → j < e → d ≤ entry M 0 j)
    (hz : ∀ j, s ≤ j → j < e → entry M 0 j = d → entry M 1 j = 0) :
    ∀ j, s ≤ j → j < e → ∃ r, s ≤ r ∧ r ≤ j ∧ le0 M r j ∧ entry M 1 r = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj1 hj2
    by_cases hd : entry M 0 j = d
    · exact ⟨j, hj1, le_rfl, ⟨by omega, by omega, Relation.ReflTransGen.refl⟩, hz j hj1 hj2 hd⟩
    · have hgt : d < entry M 0 j := lt_of_le_of_ne (hge j hj1 hj2) (Ne.symm hd)
      have hsj : s < j := by
        rcases Nat.lt_or_ge s j with h | h
        · exact h
        · exfalso
          have : j = s := by omega
          subst this
          exact hd hs
      obtain ⟨j', hj'1, hlt, hall⟩ := nearest_lower (f := fun i => entry M 0 i) (v := entry M 0 j) j
        ⟨s, hsj, by show entry M 0 s < entry M 0 j; omega⟩
      have hlt' : entry M 0 j' < entry M 0 j := hlt
      have hall' : ∀ i, j' < i → i < j → entry M 0 j ≤ entry M 0 i := hall
      have hsj' : s ≤ j' := by
        by_contra hc
        have hc' : j' < s := Nat.lt_of_not_le hc
        have := hall' s hc' hsj
        omega
      have hn : nextrel0 M j' j := ⟨by omega, by omega, hj'1, hlt', fun i hi => hall' i hi.1 hi.2⟩
      obtain ⟨r, hr1, hr2, hr3, hr4⟩ := ih j' hj'1 hsj' (by omega)
      exact ⟨r, hr1, by omega, ⟨by omega, by omega, hr3.2.2.trans (Relation.ReflTransGen.single hn)⟩, hr4⟩


/-! ### 語の位置ごとの行 1 の上昇: z の位置は上がり、荷の列は上がらない。`oper_z1wP` -/

/-- `(a,b,0)` の上に語と z=1 の列を載せた行列。 -/
def Mz (Y0 : TrioSeq) (a b : ℕ) (ws : List TrioSeq) : TrioSeq :=
  Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordP a b ws ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)])

theorem colP_length (a b : ℕ) (Y : TrioSeq) : (colP a b Y).length = Y.length + 1 := by
  simp [colP, shiftr01]

theorem wordP_length (a b a' b' : ℕ) (ws : List TrioSeq) :
    (wordP a' b' ws).length = (wordP a b ws).length := by
  induction ws with
  | nil => rfl
  | cons Y ws ih => simp [wordP_cons, colP_length, ih]

theorem Mz_length (Y0 : TrioSeq) (a b : ℕ) (ws : List TrioSeq) :
    (Mz Y0 a b ws).length = Y0.length + 1 + (wordP a b ws).length + 1 := by
  simp [Mz]; omega

theorem entry_colP_zero (a b : ℕ) (Y : TrioSeq) (r : ℕ) :
    entry (colP a b Y) r 0 = entry [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] r 0 := by
  simp [colP, entry]

theorem entry_colP_succ (a b : ℕ) (Y : TrioSeq) (r t : ℕ) :
    entry (colP a b Y) r (t + 1) = entry (shiftr01 (a + 2) 0 Y) r t := by
  simp [colP, entry]

theorem entry_Mz_p (Y0 : TrioSeq) (a b : ℕ) (ws : List TrioSeq) (r : ℕ) :
    entry (Mz Y0 a b ws) r Y0.length = entry [((a, b, 0) : ℕ × ℕ × ℕ)] r 0 := by
  rw [Mz, show Y0.length = Y0.length + 0 from rfl, entry_append_right]
  simp [entry]

theorem entry_Mz_word (Y0 : TrioSeq) (a b : ℕ) (ws : List TrioSeq) (r i : ℕ)
    (hi : i < (wordP a b ws).length) :
    entry (Mz Y0 a b ws) r (Y0.length + 1 + i) = entry (wordP a b ws) r i := by
  have e : Mz Y0 a b ws = (Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)]) ++
      (wordP a b ws ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]) := by
    simp [Mz]
  rw [e, show Y0.length + 1 + i = (Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)]).length + i from by
      simp only [List.length_append, List.length_singleton],
    entry_append_right, entry_append_left hi]

theorem entry_Mz_last (Y0 : TrioSeq) (a b : ℕ) (ws : List TrioSeq) (r : ℕ) :
    entry (Mz Y0 a b ws) r (Y0.length + 1 + (wordP a b ws).length)
      = entry [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] r 0 := by
  have e : Mz Y0 a b ws = (Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)] ++ wordP a b ws) ++
      [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] := by
    simp [Mz]
  rw [e, show Y0.length + 1 + (wordP a b ws).length
      = (Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)] ++ wordP a b ws).length + 0 from by
      simp only [List.length_append, List.length_singleton, Nat.add_zero],
    entry_append_right]

theorem entry_wordP_pos (Y0 : TrioSeq) (a b : ℕ) (ws1 ws3 : List TrioSeq) (Y : TrioSeq) (r t : ℕ)
    (ht : t < (colP a b Y).length) :
    entry (Mz Y0 a b (ws1 ++ Y :: ws3)) r (Y0.length + 1 + (wordP a b ws1).length + t)
      = entry (colP a b Y) r t := by
  have e : Mz Y0 a b (ws1 ++ Y :: ws3)
      = (Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)] ++ wordP a b ws1) ++
        (colP a b Y ++ (wordP a b ws3 ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)])) := by
    simp [Mz, wordP_append, wordP_cons, List.append_assoc]
  rw [e, show Y0.length + 1 + (wordP a b ws1).length + t
      = (Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)] ++ wordP a b ws1).length + t from by
        simp only [List.length_append, List.length_singleton],
    entry_append_right, entry_append_left ht]

theorem entry_wordP_ge (a b : ℕ) (ws : List TrioSeq) {i : ℕ} (hi : i < (wordP a b ws).length) :
    a + 1 ≤ entry (wordP a b ws) 0 i := by
  have := wordP_ge a b ws _ (List.getElem_mem hi)
  have he : entry (wordP a b ws) 0 i = ((wordP a b ws)[i]).1 := by
    simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  omega

/-- 行 0 の祖先（一般形）: `p` の高さが `a`、`(p, j]` の列がすべて高さ ≥ a+1 なら `le0 M p j`。 -/
theorem le0_of_between {M : TrioSeq} {p a : ℕ} (hp : entry M 0 p = a) :
    ∀ j, p < j → j < M.length → (∀ j', p < j' → j' ≤ j → a + 1 ≤ entry M 0 j') → le0 M p j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj1 hj2 hall
    obtain ⟨j', hj'1, hlt, hallj⟩ := nearest_lower (f := fun i => entry M 0 i) (v := entry M 0 j) j
      ⟨p, hj1, by show entry M 0 p < entry M 0 j; rw [hp]; have := hall j hj1 le_rfl; omega⟩
    have hlt' : entry M 0 j' < entry M 0 j := hlt
    have hallj' : ∀ i, j' < i → i < j → entry M 0 j ≤ entry M 0 i := hallj
    have hn : nextrel0 M j' j :=
      ⟨by omega, by omega, hj'1, hlt', fun i hi => hallj' i hi.1 hi.2⟩
    rcases Nat.lt_or_ge p j' with hpj | hpj
    · have := ih j' hj'1 hpj (by omega) (fun j'' h1 h2 => hall j'' h1 (by omega))
      exact ⟨by omega, by omega, this.2.2.trans (Relation.ReflTransGen.single hn)⟩
    · have : j' = p := by
        rcases Nat.lt_or_ge j' p with h | h
        · exfalso
          have := hallj' p h hj1
          rw [hp] at this
          have := hall j hj1 le_rfl
          omega
        · omega
      subst this
      exact ⟨by omega, by omega, Relation.ReflTransGen.single hn⟩

/-- 高さ `a+1` の列 `j` の行 0 の祖先で `p` より右のものは `j` 自身に限る（間の列は高さ ≥ a+1）。 -/
theorem le0_eq_of_min {M : TrioSeq} {p a j j' : ℕ} (hj' : p < j') (hle : le0 M j' j)
    (hj : entry M 0 j = a + 1) (hbetween : ∀ j'', p < j'' → j'' < j → a + 1 ≤ entry M 0 j'') :
    j' = j := by
  obtain ⟨hj'l, hjl, hch⟩ := hle
  rcases Relation.ReflTransGen.cases_tail hch with h1 | ⟨c, hc1, hc2⟩
  · exact h1.symm
  · exfalso
    have hcj : c < j := hc2.2.2.1
    have hcle : j' ≤ c := le0_le' ⟨hj'l, hc2.1, hc1⟩
    have hlt : entry M 0 c < entry M 0 j := hc2.2.2.2.1
    have := hbetween c (by omega) hcj
    omega

/-- z の位置は `p` の行 1 の子。 -/
theorem le1_zpos (Y0 : TrioSeq) (a b : ℕ) (ws1 ws3 : List TrioSeq) (Y : TrioSeq) :
    le1 (Mz Y0 a b (ws1 ++ Y :: ws3)) Y0.length (Y0.length + 1 + (wordP a b ws1).length) := by
  set M := Mz Y0 a b (ws1 ++ Y :: ws3) with hM
  set p := Y0.length with hp
  set q := p + 1 + (wordP a b ws1).length with hq
  have hlenw : (wordP a b (ws1 ++ Y :: ws3)).length = (wordP a b ws1).length + (Y.length + 1) +
      (wordP a b ws3).length := by
    rw [wordP_append, wordP_cons, List.length_append, List.length_append, colP_length]; omega
  have hlen : M.length = p + 1 + (wordP a b (ws1 ++ Y :: ws3)).length + 1 := Mz_length Y0 a b _
  have hql : q < M.length := by omega
  have e0p : entry M 0 p = a := by rw [hM, hp, entry_Mz_p]; simp [entry]
  have e1p : entry M 1 p = b := by rw [hM, hp, entry_Mz_p]; simp [entry]
  have eq0 : entry M 0 q = a + 1 := by
    have h := entry_wordP_pos Y0 a b ws1 ws3 Y 0 0 (by rw [colP_length]; omega)
    rw [entry_colP_zero] at h
    simp only [Nat.add_zero] at h
    rw [hM, hq, hp, h]; simp [entry]
  have eq1 : entry M 1 q = b + 1 := by
    have h := entry_wordP_pos Y0 a b ws1 ws3 Y 1 0 (by rw [colP_length]; omega)
    rw [entry_colP_zero] at h
    simp only [Nat.add_zero] at h
    rw [hM, hq, hp, h]; simp [entry]
  have hge : ∀ j', p < j' → j' ≤ q → a + 1 ≤ entry M 0 j' := by
    intro j' h1 h2
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < (wordP a b (ws1 ++ Y :: ws3)).length ∧ j' = p + 1 + i :=
      ⟨j' - (p + 1), by omega, by omega⟩
    rw [hM, hp, entry_Mz_word Y0 a b _ 0 i hi]
    exact entry_wordP_ge a b _ hi
  have hl0 : le0 M p q := le0_of_between e0p q (by omega) hql hge
  refine ⟨by omega, hql, Relation.ReflTransGen.single ?_⟩
  refine ⟨by omega, hql, by omega, by rw [e1p, eq1]; omega, hl0, ?_⟩
  intro j hj
  have := le0_eq_of_min hj.1 hj.2 eq0 (fun j'' h1 h2 => hge j'' h1 (by omega))
  subst this; exact le_rfl

/-- 荷の列は `p` の行 1 の子孫ではない（荷の木の根 `(a+2,0,0)` で鎖が止まる）。 -/
theorem not_le1_ppos (Y0 : TrioSeq) (a b : ℕ) (ws1 ws3 : List TrioSeq) {Y : TrioSeq} (hY : Bok Y)
    (t : ℕ) (ht1 : 1 ≤ t) (ht : t < (colP a b Y).length) :
    ¬ le1 (Mz Y0 a b (ws1 ++ Y :: ws3)) Y0.length (Y0.length + 1 + (wordP a b ws1).length + t) := by
  set M := Mz Y0 a b (ws1 ++ Y :: ws3) with hM
  set p := Y0.length with hp
  set q := p + 1 + (wordP a b ws1).length with hq
  rw [colP_length] at ht
  have hlenw : (wordP a b (ws1 ++ Y :: ws3)).length = (wordP a b ws1).length + (Y.length + 1) +
      (wordP a b ws3).length := by
    rw [wordP_append, wordP_cons, List.length_append, List.length_append, colP_length]; omega
  have hlen : M.length = p + 1 + (wordP a b (ws1 ++ Y :: ws3)).length + 1 := Mz_length Y0 a b _
  have hY0 : 0 < Y.length := by omega
  -- ブロック [q+1, q+1+|Y|) の列
  have eblk : ∀ r u, u < Y.length → entry M r (q + 1 + u) = entry (shiftr01 (a + 2) 0 Y) r u := by
    intro r u hu
    rw [hM, hq, hp, show Y0.length + 1 + (wordP a b ws1).length + 1 + u
      = Y0.length + 1 + (wordP a b ws1).length + (u + 1) from by omega,
      entry_wordP_pos Y0 a b ws1 ws3 Y r (u + 1) (by rw [colP_length]; omega), entry_colP_succ]
  have hroot := block_root (M := M) (s := q + 1) (e := q + 1 + Y.length) (d := a + 2) (by omega)
    (by rw [show q + 1 = q + 1 + 0 from rfl, eblk 0 0 hY0, entry0_shiftr01 hY0, hY.root]; omega)
    (by intro j hj1 hj2
        obtain ⟨u, hu, rfl⟩ : ∃ u, u < Y.length ∧ j = q + 1 + u := ⟨j - (q + 1), by omega, by omega⟩
        rw [eblk 0 u hu, entry0_shiftr01 hu]; omega)
    (by intro j hj1 hj2 hd
        obtain ⟨u, hu, rfl⟩ : ∃ u, u < Y.length ∧ j = q + 1 + u := ⟨j - (q + 1), by omega, by omega⟩
        rw [eblk 0 u hu, entry0_shiftr01 hu] at hd
        rw [eblk 1 u hu, entry1_shiftr01]
        exact (Zroot_entry hY.zroot (by omega)).1)
  intro hle
  have := le1_lower_bound hroot p (q + t) hle (by omega) (by omega)
  omega

/-- 字 1 つ分の上昇: 先頭（z）だけ行 1 が上がる。 -/
theorem rise_colP (a b k : ℕ) (Y : TrioSeq) (P : ℕ → Prop) [DecidablePred P]
    (hP0 : P 0) (hP : ∀ t, 1 ≤ t → t < (colP a b Y).length → ¬ P t) :
    (List.range (colP a b Y).length).map (fun t =>
      ((entry (colP a b Y) 0 t + k, entry (colP a b Y) 1 t + (if P t then k else 0),
        entry (colP a b Y) 2 t) : ℕ × ℕ × ℕ)) = colP (a + k) (b + k) Y := by
  apply List.ext_getElem
  · simp [colP_length]
  · intro t h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have h1' : t < (colP a b Y).length := by simpa using h1
    clear h1
    have h1 := h1'
    cases t with
    | zero =>
        rw [entry_colP_zero, entry_colP_zero, entry_colP_zero, if_pos hP0]
        simp [colP, entry]
        try omega
    | succ u =>
        have hu : u < Y.length := by rw [colP_length] at h1; omega
        rw [entry_colP_succ, entry_colP_succ, entry_colP_succ, if_neg (hP (u + 1) (by omega) h1),
          entry0_shiftr01 hu, entry1_shiftr01, entry2_shiftr01]
        simp [colP, shiftr01, entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu]
        try omega

open Classical in
/-- 語全体の上昇（接頭辞 `ws1` を蓄積する帰納法）。 -/
theorem rise_wordP (Y0 : TrioSeq) (a b k : ℕ) {ws : List TrioSeq} (hw : Wpl ws) :
    ∀ (ws2 ws1 ws3 : List TrioSeq), ws = ws1 ++ ws2 ++ ws3 →
      (List.range (wordP a b ws2).length).map (fun i =>
        ((entry (wordP a b ws2) 0 i + k, entry (wordP a b ws2) 1 i +
          (if le1 (Mz Y0 a b ws) Y0.length (Y0.length + 1 + (wordP a b ws1).length + i) then k else 0),
          entry (wordP a b ws2) 2 i) : ℕ × ℕ × ℕ))
      = wordP (a + k) (b + k) ws2
  | [], _, _, _ => by simp [wordP]
  | Y :: ws2, ws1, ws3, hws => by
      have hws' : ws = (ws1 ++ [Y]) ++ ws2 ++ ws3 := by rw [hws]; simp
      have hws'' : ws = ws1 ++ Y :: (ws2 ++ ws3) := by rw [hws]; simp
      have hY : Bok Y := hw Y (by rw [hws]; simp)
      have ih := rise_wordP Y0 a b k hw ws2 (ws1 ++ [Y]) ws3 hws'
      rw [wordP_cons, wordP_cons, List.length_append, List.range_add, List.map_append, List.map_map]
      congr 1
      · rw [← rise_colP a b k Y (fun t => le1 (Mz Y0 a b ws) Y0.length
            (Y0.length + 1 + (wordP a b ws1).length + t))
            (by rw [hws'']; simpa using le1_zpos Y0 a b ws1 (ws2 ++ ws3) Y)
            (by intro t ht1 ht; rw [hws'']; exact not_le1_ppos Y0 a b ws1 (ws2 ++ ws3) hY t ht1 ht)]
        apply List.map_congr_left
        intro t ht
        rw [List.mem_range] at ht
        rw [entry_append_left ht, entry_append_left ht, entry_append_left ht]
      · rw [← ih]
        apply List.map_congr_left
        intro i hi
        simp only [Function.comp]
        rw [entry_append_right, entry_append_right, entry_append_right, wordP_append,
          wordP_singleton, List.length_append,
          show Y0.length + 1 + (wordP a b ws1).length + ((colP a b Y).length + i)
            = Y0.length + 1 + ((wordP a b ws1).length + (colP a b Y).length) + i from by omega]

/-- ★ 荷つきの語の上の z=1 の列の展開: 対角の塔 `DzwP`。 -/
theorem oper_z1wP (Y0 : TrioSeq) (a b : ℕ) {ws : List TrioSeq} (hw : Wpl ws) (n : ℕ) :
    (Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordP a b ws ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]))⟦n⟧
      = Y0 ++ DzwP a b ws n := by
  rw [oper_z1_mask Y0 a b (wordP a b ws) (wordP_ge a b ws) n]
  congr 1
  apply List.flatMap_congr
  intro k _
  congr 1
  have := rise_wordP Y0 a b k hw ws [] [] (by simp)
  simpa [wordP, Mz] using this

theorem z1wP_mem {Y0 : TrioSeq} {a b : ℕ} {ws : List TrioSeq} (hw : Wpl ws)
    (htw : ∀ n, Y0 ++ DzwP a b ws n ∈ W 0) :
    Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordP a b ws ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]) ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_z1wP Y0 a b hw]
  exact htw n

#print axioms z1wP_mem


/-! ### 和: `A ++ B`（`B` は根が高さ 0）と、荷つきの語の影 `shwP` -/

/-- 末尾に `(0,0,0)` を継ぐ。展開は前者。 -/
theorem snoc_zero {A : TrioSeq} (hA : A ∈ W 0) (hne : A ≠ []) :
    A ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hAlen : 0 < A.length := List.length_pos_iff.mpr hne
  have hlast : (A ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]).length - 1 = A.length := by simp
  have hz : entry (A ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]) 0 ((A ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) = 0 ∧
      entry (A ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]) 1 ((A ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) = 0 ∧
      entry (A ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]) 2 ((A ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) = 0 := by
    rw [hlast]
    refine ⟨?_, ?_, ?_⟩ <;>
      · rw [show A.length = A.length + 0 from rfl, entry_append_right]
        simp [entry]
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_eq_pred_of_zero n (by rw [hlast]; omega) hz]
  unfold Pred
  rw [if_neg (by simp; omega), List.dropLast_concat]
  exact hA

/-- **和**: 根が高さ 0 の `B` は、`Aok` でなくても右に継げる。 -/
theorem sum_mem : ∀ B ∈ W 0, Zroot B → Mono B → entry B 0 0 = 0 →
    ∀ A : TrioSeq, A ∈ W 0 → A ≠ [] → A ++ B ∈ W 0 := by
  have key : W 0 ⊆ {B : TrioSeq | Zroot B → Mono B → entry B 0 0 = 0 →
      ∀ A : TrioSeq, A ∈ W 0 → A ≠ [] → A ++ B ∈ W 0} := by
    refine A2' ?_
    intro B hB
    simp only [Set.mem_setOf_eq]
    intro hzr hmo hroot A hA hAne
    by_cases hshort : B.length ≤ 1
    · rcases (by omega : B.length = 0 ∨ B.length = 1) with h0 | h1
      · have hnil : B = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        simpa using hA
      · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
        have hc0 : c.1 = 0 := hroot
        obtain ⟨hc1, hc2⟩ := hzr c (by simp) hc0
        have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1 hc2)
        subst hcz
        exact snoc_zero hA hAne
    have hlen2 : 2 ≤ B.length := by omega
    have hBne : B ≠ [] := by intro hc; rw [hc] at hlen2; simp at hlen2
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
          rw [List.dropLast_eq_take, Wset.entry_take (show (0 : ℕ) < B.length - 1 by omega)]
          exact hroot
        have hIH := hdl (fun c hc => hzr c (List.dropLast_subset _ hc))
          (fun c hc => hmo c (List.dropLast_subset _ hc)) hdl0 A hA hAne
        have e : A ++ B = (A ++ B.dropLast) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
          rw [List.append_assoc, ← hsplit]
        rw [e]
        exact snoc_zero hIH (by simp [List.append_eq_nil_iff, hAne])
      · have hnz : ¬ (entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
            entry B 2 (B.length - 1) = 0) := fun h => hlast h.1
        have hp := hasParent_of_ZrootMono hzr hmo hroot hlen2 hnz
        refine A1_intro (Or.inr (Or.inl ?_))
        intro n hn
        rw [oper_append_right_of A B n hlen2 hp]
        obtain ⟨hzr', hmo'⟩ := ZM_oper hzr hmo n
        exact hnat n hn hzr' hmo' (by rw [Wset.oper_head_eq hn]; exact hroot) A hA hAne
    · exact absurd hm (Nat.not_lt_zero m)
  intro B hB
  exact key hB

theorem sum_Bok {A B : TrioSeq} (hA : Aok A) (hB : Bok B) : A ++ B ∈ W 0 :=
  sum_mem B hB.mem hB.zroot hB.mono hB.root A hA.mem hA.ne

/-- 影の字: `(1,0,0) :: Y↑2`。 -/
def shP (Y : TrioSeq) : TrioSeq := ((1, 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 2 0 Y

/-- 影の語: `(0,0,0)` の上に影の字を並べたもの。 -/
def shwP (ws : List TrioSeq) : TrioSeq := ((0, 0, 0) : ℕ × ℕ × ℕ) :: ws.flatMap shP

/-- 影の中身（`bump` の内側）。 -/
def Fw (ws : List TrioSeq) : TrioSeq := ws.flatMap fun Y => ((0, 0, 0) : ℕ × ℕ × ℕ) :: bump Y

theorem bump_shP (Y : TrioSeq) : bump (((0, 0, 0) : ℕ × ℕ × ℕ) :: bump Y) = shP Y := by
  simp [bump, shP, shiftr01, List.map_map, Function.comp_def]

theorem bump_Fw (ws : List TrioSeq) : bump (Fw ws) = ws.flatMap shP := by
  induction ws with
  | nil => simp [Fw, bump, shiftr01]
  | cons Y ws ih =>
      rw [Fw, List.flatMap_cons, bump_append, bump_shP, List.flatMap_cons]
      rw [show ws.flatMap (fun Y => ((0, 0, 0) : ℕ × ℕ × ℕ) :: bump Y) = Fw ws from rfl, ih]

theorem shwP_eq (ws : List TrioSeq) : shwP ws = [((0, 0, 0) : ℕ × ℕ × ℕ)] ++ bump (Fw ws) := by
  rw [bump_Fw]; rfl

theorem Bok_Fw : ∀ {ws : List TrioSeq}, Wpl ws → Bok (Fw ws)
  | [], _ => by simpa [Fw] using Bok_nil
  | (Y :: ws), hw => by
      have hY : Bok Y := hw Y (by simp)
      have hws : Wpl ws := fun Y' hY' => hw Y' (by simp [hY'])
      have hIH := Bok_Fw hws
      have hAok : Aok (((0, 0, 0) : ℕ × ℕ × ℕ) :: bump Y) := by
        have := Aok_zero.append_bump hY
        simpa using this
      refine ⟨?_, ?_, ?_, ?_⟩
      · have h := sum_Bok hAok hIH
        rw [Fw, List.flatMap_cons]
        simpa using h
      · intro c hc h0
        rw [Fw, List.flatMap_cons] at hc
        rcases List.mem_append.mp hc with h | h
        · rcases List.mem_cons.mp h with rfl | h'
          · exact ⟨rfl, rfl⟩
          · exfalso; have := bump_col c h'; omega
        · exact hIH.zroot c h h0
      · intro c hc
        rw [Fw, List.flatMap_cons] at hc
        rcases List.mem_append.mp hc with h | h
        · rcases List.mem_cons.mp h with rfl | h'
          · simp
          · exact bump_mono hY.mono c h'
        · exact hIH.mono c h
      · rw [Fw, List.flatMap_cons]
        simp [entry]

theorem shwP_mem {ws : List TrioSeq} (hw : Wpl ws) : shwP ws ∈ W 0 := by
  rw [shwP_eq]
  exact Bok.append Aok_zero (Bok_Fw hw)

#print axioms shwP_mem


/-! ### 語の 3 つの場合。共通の骨組み `GoodP_of_key` -/

/-- 4 段すべてを、台座つきの「語の membership」1 本から出す。 -/
theorem GoodP_of_key {ws : List TrioSeq} (hw : Wpl ws)
    {newws : ℕ → List TrioSeq} (hnew : ∀ n, 1 ≤ n → GoodP (newws n))
    (key : ∀ (Z : TrioSeq) (a b : ℕ),
      (∀ n, 1 ≤ n → Z ++ wordP a b (newws n) ∈ W 0) → Z ++ wordP a b ws ∈ W 0) :
    GoodP ws := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y c hy
    refine ⟨fun x hx => by have := wordP_ge (c + 1) (y + 1) ws x hx; omega, wordP_mono hw, ?_⟩
    intro E hE t Z hZ
    rw [wordP_shift]
    have := key (Z ++ [((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)]) (c + 1 + t) (y + 1) (fun n hn => by
      have hP : PU y (c + 1 + t) (Z ++ ([((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)] ++
          wordP (c + 1 + t) (y + 1) (newws n))) :=
        ⟨E, c + t, Z, _, hE, by omega, hZ, by rw [show c + t + 1 = c + 1 + t from by omega],
          (hnew n hn).pu y (c + t) hy⟩
      simpa [List.append_assoc] using ((BaseOk_PU y).aok _ _ hP).mem)
    simpa [List.append_assoc] using this
  · intro c E hI
    refine ⟨fun x hx => by have := wordP_ge (c + 1) 2 ws x hx; omega, wordP_mono hw, ?_⟩
    intro j t X hX
    rw [wordP_shift]
    have := key (X ++ [((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ)]) (c + 1 + t) 2 (fun n hn => by
      have hP : PkGA (c + 1 + t) (X ++ ([((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ)] ++
          wordP (c + 1 + t) 2 (newws n))) :=
        ⟨E, hI, j, c + t, X, _, by omega, hX, by rw [show c + t + 1 = c + 1 + t from by omega],
          (hnew n hn).pk (c + t)⟩
      simpa [List.append_assoc] using (PkGA_Aok hP).mem)
    simpa [List.append_assoc] using this
  · intro h
    refine ⟨?_, by simp [entry], ?_⟩
    · have h1 := MidD_wordP (h + 1) 1 (by omega) (by omega) hw
      simpa [show h + 1 + 1 = h + 2 from by omega] using h1
    · intro P hP s A' hA'
      rw [show ((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordP (h + 1) 1 ws
          = [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ wordP (h + 1) 1 ws from rfl,
        shiftr01_append0, shift_col, wordP_shift]
      have := key (A' ++ [((h + 1 + s, 1, 0) : ℕ × ℕ × ℕ)]) (h + 1 + s) 1 (fun n hn => by
        have hR : RunA 0 (h + s + 1) (A' ++ (((h + s + 1, 1, 0) : ℕ × ℕ × ℕ) ::
            wordP (h + s + 1) 1 (newws n))) :=
          ⟨h + s, A', _, rfl, rfl, ⟨P, hP, hA'⟩, (hnew n hn).seg (h + s)⟩
        have := ((BaseOk_RunA 0).aok _ _ hR).mem
        simpa [List.append_assoc, show h + s + 1 = h + 1 + s from by omega] using this)
      simpa [List.append_assoc] using this
  · refine Aok_rootP_of_mem hw ?_
    have := key [((0, 0, 0) : ℕ × ℕ × ℕ)] 0 0 (fun n hn => by simpa using (hnew n hn).root.mem)
    simpa using this

theorem Wpl_snocz {ws : List TrioSeq} (hw : Wpl ws) : Wpl (ws ++ [[]]) :=
  Wp_append hw (Wp_singleton Bok_nil)

/-- 場合 A: 語の最後が裸の z。 -/
theorem GoodP_snocz {ws : List TrioSeq} (hw : Wpl ws) (hG : GoodP ws) : GoodP (ws ++ [[]]) where
  pu := by
    intro y c hy
    refine ⟨fun x hx => by have := wordP_ge (c + 1) (y + 1) (ws ++ [[]]) x hx; omega,
      wordP_mono (Wpl_snocz hw), ?_⟩
    intro E hE t Z hZ
    have h := z1wP_mem (Y0 := Z) (a := c + 1 + t) (b := y + 1) hw
      (fun n => by
        have := DzwP_W hG hy hE (c := c + t) (by simpa using hZ) n
        simpa [show c + t + 1 = c + 1 + t from by omega] using this)
    rw [wordP_shift, wordP_append, wordP_singleton]
    simpa [colP, List.append_assoc] using h
  pk := by
    intro c E hI
    refine ⟨fun x hx => by have := wordP_ge (c + 1) 2 (ws ++ [[]]) x hx; omega,
      wordP_mono (Wpl_snocz hw), ?_⟩
    intro j t X hX
    have h := z1wP_mem (Y0 := X) (a := c + 1 + t) (b := 2) hw
      (fun n => by
        have := DzwP_W_RunG hG hI (c := c + t) hX n
        simpa [show c + t + 1 = c + 1 + t from by omega] using this)
    rw [wordP_shift, wordP_append, wordP_singleton]
    simpa [colP, List.append_assoc] using h
  seg := by
    intro h
    refine ⟨?_, by simp [entry], ?_⟩
    · have h1 := MidD_wordP (h + 1) 1 (by omega) (by omega) (Wpl_snocz hw)
      simpa [show h + 1 + 1 = h + 2 from by omega] using h1
    · intro P hP s A' hA'
      have hz := z1wP_mem (Y0 := A') (a := h + s + 1) (b := 1) hw
        (fun n => DzwP_W_LwA hG (h := h + s) ⟨P, hP, hA'⟩ n)
      rw [show ((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordP (h + 1) 1 (ws ++ [[]])
          = [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ wordP (h + 1) 1 (ws ++ [[]]) from rfl,
        shiftr01_append0, shift_col, wordP_shift, wordP_append, wordP_singleton]
      simpa [colP, List.append_assoc, show h + 1 + s = h + s + 1 from by omega] using hz
  root := by
    have hmem := z1wP_mem (Y0 := []) (a := 0) (b := 0) hw
      (fun n => by simpa using DzwP_W_root hG n)
    refine Aok_rootP_of_mem (Wpl_snocz hw) ?_
    rw [wordP_append, wordP_singleton]
    simpa [colP, List.append_assoc] using hmem

theorem colP_ne (a b : ℕ) (Y : TrioSeq) : colP a b Y ≠ [] := by simp [colP]

theorem colP_snoc_zero (a b : ℕ) (Y : TrioSeq) :
    colP a b (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]) = colP a b Y ++ [((a + 2, 0, 0) : ℕ × ℕ × ℕ)] := by
  simp [colP, shiftr01]

theorem wordP_replicate (a b : ℕ) (Y : TrioSeq) : ∀ n : ℕ,
    wordP a b (List.replicate n Y) = (List.range n).flatMap fun _ => colP a b Y
  | 0 => by simp [wordP]
  | (n + 1) => by
      rw [List.replicate_succ, wordP_cons, wordP_replicate a b Y n,
        show ((List.range (n + 1)).flatMap fun _ => colP a b Y) = copies (colP a b Y) (n + 1) from rfl,
        copies_succ]
      rfl

/-- 場合 B: 語の最後の荷の末尾が `(0,0,0)`（字が `n` 個に複製される）。 -/
theorem GoodP_dup {ws' : List TrioSeq} {Y : TrioSeq}
    (hw : Wpl (ws' ++ [Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]]))
    (hIH : ∀ n, 1 ≤ n → GoodP (ws' ++ List.replicate n Y)) :
    GoodP (ws' ++ [Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]]) := by
  refine GoodP_of_key hw hIH ?_
  intro Z a b hn
  have hhead : entry (colP a b Y) 0 0 < a + 2 := by
    rw [entry_colP_zero]; simp [entry]
  have htail : ∀ r, 1 ≤ r → r < (colP a b Y).length → a + 2 ≤ entry (colP a b Y) 0 r := by
    intro r hr1 hrl
    obtain ⟨u, rfl⟩ : ∃ u, r = u + 1 := ⟨r - 1, by omega⟩
    rw [colP_length] at hrl
    rw [entry_colP_succ, entry0_shiftr01 (by omega)]
    omega
  have h := flat_mem'' (Y0 := Z ++ wordP a b ws') (M := colP a b Y) (d := a + 2)
    (colP_ne a b Y) hhead htail
    (fun n => by
      match n with
      | 0 =>
          have h1 := hn 1 (le_refl 1)
          rw [wordP_append, wordP_replicate] at h1
          simp only [List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil] at h1
          have h2 := W_take (by rw [← List.append_assoc] at h1; exact h1) (Z ++ wordP a b ws').length
          rw [List.take_left] at h2
          simpa using h2
      | (n + 1) =>
          have h1 := hn (n + 1) (by omega)
          rw [wordP_append, wordP_replicate] at h1
          simpa [List.append_assoc] using h1)
  rw [wordP_append, wordP_singleton, colP_snoc_zero]
  simpa [List.append_assoc] using h

/-- 場合 C: 語の最後の荷の末尾が非零（荷の中だけが展開される）。 -/
theorem GoodP_inner {ws' : List TrioSeq} {Y : TrioSeq} (hlen : 2 ≤ Y.length)
    (hp : hasParent Y (srow Y (Y.length - 1)) (Y.length - 1))
    (hw : Wpl (ws' ++ [Y]))
    (hIH : ∀ n, 1 ≤ n → GoodP (ws' ++ [Y⟦n⟧])) :
    GoodP (ws' ++ [Y]) := by
  refine GoodP_of_key hw hIH ?_
  intro Z a b hn
  have e : ∀ Y' : TrioSeq, Z ++ wordP a b (ws' ++ [Y'])
      = (Z ++ wordP a b ws' ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]) ++ shiftr01 (a + 2) 0 Y' := by
    intro Y'
    simp [wordP_append, wordP_singleton, colP, List.append_assoc]
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n hn'
  rw [e Y, oper_shift _ Y (a + 2) n hlen hp, ← e (Y⟦n⟧)]
  exact hn n hn'


/-! ### 影の展開と `GoodP_all`（影の W 帰納法） -/

theorem shwP_snoc (ws : List TrioSeq) (Y : TrioSeq) : shwP (ws ++ [Y]) = shwP ws ++ shP Y := by
  simp [shwP, List.flatMap_append]

theorem shP_nil : shP [] = [((1, 0, 0) : ℕ × ℕ × ℕ)] := by simp [shP, shiftr01]

theorem shP_snoc_zero (Y : TrioSeq) :
    shP (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]) = shP Y ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] := by
  simp [shP, shiftr01]

theorem flatMap_replicate {α β : Type _} (f : α → List β) (Y : α) : ∀ n : ℕ,
    (List.replicate n Y).flatMap f = (List.range n).flatMap fun _ => f Y
  | 0 => by simp
  | (n + 1) => by
      rw [List.replicate_succ, List.flatMap_cons, flatMap_replicate f Y n,
        List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]

theorem shwP_replicate (ws : List TrioSeq) (Y : TrioSeq) (n : ℕ) :
    shwP (ws ++ List.replicate n Y) = shwP ws ++ (List.range n).flatMap fun _ => shP Y := by
  simp [shwP, List.flatMap_append, flatMap_replicate]

theorem entry_shP_zero (Y : TrioSeq) : entry (shP Y) 0 0 = 1 := by simp [shP, entry]

theorem entry_shP_succ (Y : TrioSeq) (r : ℕ) :
    entry (shP Y) 0 (r + 1) = entry (shiftr01 2 0 Y) 0 r := by simp [shP, entry]

theorem shP_length (Y : TrioSeq) : (shP Y).length = Y.length + 1 := by simp [shP, shiftr01]

/-- 場合 A の影: 末尾の `(1,0,0)` を落とす。 -/
theorem oper_shwP_z (ws : List TrioSeq) : (shwP (ws ++ [[]]))⟦1⟧ = shwP ws := by
  rw [shwP_snoc, shP_nil, oper_one_eq_dropLast
    (by simp only [shwP, List.length_append, List.length_cons]; omega),
    List.dropLast_concat]

/-- 場合 B の影: 影の字が `n` 個に複製される。 -/
theorem oper_shwP_dup (ws : List TrioSeq) (Y : TrioSeq) (n : ℕ) :
    (shwP (ws ++ [Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]]))⟦n⟧ = shwP (ws ++ List.replicate n Y) := by
  rw [shwP_snoc, shP_snoc_zero, ← List.append_assoc,
    oper_snoc00'' (shwP ws) (M := shP Y) (d := 2) (by simp [shP])
      (by rw [entry_shP_zero]; omega)
      (by intro r hr1 hrl
          obtain ⟨u, rfl⟩ : ∃ u, r = u + 1 := ⟨r - 1, by omega⟩
          have hu : u < Y.length := by rw [shP_length] at hrl; omega
          rw [entry_shP_succ, entry0_shiftr01 hu]; omega) n,
    shwP_replicate]

/-- 場合 C の影: 荷だけが展開される。 -/
theorem oper_shwP_inner (ws : List TrioSeq) {Y : TrioSeq} (hlen : 2 ≤ Y.length)
    (hp : hasParent Y (srow Y (Y.length - 1)) (Y.length - 1)) (n : ℕ) :
    (shwP (ws ++ [Y]))⟦n⟧ = shwP (ws ++ [Y⟦n⟧]) := by
  have e : ∀ Y' : TrioSeq, shwP (ws ++ [Y'])
      = (shwP ws ++ [((1, 0, 0) : ℕ × ℕ × ℕ)]) ++ shiftr01 2 0 Y' := by
    intro Y'
    rw [shwP_snoc, shP]
    simp [List.append_assoc]
  rw [e Y, oper_shift _ Y 2 n hlen hp, ← e (Y⟦n⟧)]

theorem Wp_replicate {Y : TrioSeq} (hY : Bok Y) (n : ℕ) : Wpl (List.replicate n Y) := by
  intro Y' hY'
  rw [List.eq_of_mem_replicate hY']
  exact hY

theorem Bok_dropLast {Y : TrioSeq} (hY : Bok Y) : Bok Y.dropLast := by
  refine ⟨W_dropLast hY.mem, fun c hc => hY.zroot c (List.dropLast_subset _ hc),
    fun c hc => hY.mono c (List.dropLast_subset _ hc), ?_⟩
  by_cases h : 0 < Y.length - 1
  · rw [List.dropLast_eq_take, Wset.entry_take h]
    exact hY.root
  · have hnil : Y.dropLast = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [List.length_dropLast]
      omega
    rw [hnil]
    simp [entry]

theorem Bok_oper {Y : TrioSeq} (hY : Bok Y) {n : ℕ} (hn : 1 ≤ n) : Bok (Y⟦n⟧) :=
  ⟨oper_closed hY.mem hn, (ZM_oper hY.zroot hY.mono n).1, (ZM_oper hY.zroot hY.mono n).2,
    by rw [Wset.oper_head_eq hn]; exact hY.root⟩

/-- ★★★★★ 荷が `Bok` の語はすべて普遍（影の W 帰納法）。 -/
theorem GoodP_all : ∀ ws : List TrioSeq, Wpl ws → GoodP ws := by
  have key : W 0 ⊆ {Fl : TrioSeq | ∀ ws : List TrioSeq, Wpl ws → Fl = shwP ws → GoodP ws} := by
    refine A2' ?_
    intro Fl hFl
    simp only [Set.mem_setOf_eq]
    intro ws hw hFl_eq
    rcases hFl with ⟨hlen, -⟩ | h2 | ⟨m, hm, -⟩
    · subst hFl_eq
      cases ws with
      | nil => exact GoodP_nil
      | cons Y ws'' =>
          exfalso
          simp [shwP, shP, List.flatMap_cons] at hlen
    · subst hFl_eq
      rcases List.eq_nil_or_concat ws with hnil | ⟨ws', Y, hws⟩
      · subst hnil; exact GoodP_nil
      · rw [List.concat_eq_append] at hws
        subst hws
        have hw' : Wpl ws' := Wp_of_append_left hw
        have hY : Bok Y := hw Y (by simp)
        by_cases hYnil : Y = []
        · subst hYnil
          exact GoodP_snocz hw' (h2 1 (le_refl 1) ws' hw' (oper_shwP_z ws'))
        · have hYlen : 0 < Y.length := List.length_pos_iff.mpr hYnil
          by_cases hz : entry Y 0 (Y.length - 1) = 0
          · -- 場合 B: 末尾の列は (0,0,0)
            obtain ⟨he1, he2⟩ := Zroot_entry hY.zroot hz
            have hcol : Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) = ((0, 0, 0) : ℕ × ℕ × ℕ) :=
              Prod.ext hz (Prod.ext he1 he2)
            have hgl : Y.getLast hYnil = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
              have h1 : Y.getLast hYnil = Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
                rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
                  List.getElem?_eq_getElem (show Y.length - 1 < Y.length by omega)]
                rfl
              rw [h1, hcol]
            have hsplit : Y = Y.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
              rw [← hgl]
              exact (List.dropLast_append_getLast hYnil).symm
            have hd : Bok Y.dropLast := Bok_dropLast hY
            rw [hsplit]
            refine GoodP_dup (by rw [← hsplit]; exact hw) ?_
            intro n hn
            refine h2 n hn (ws' ++ List.replicate n Y.dropLast)
              (Wp_append hw' (Wp_replicate hd n)) ?_
            rw [← oper_shwP_dup ws' Y.dropLast n, ← hsplit]
          · -- 場合 C: 末尾の列は非零
            have hlen2 : 2 ≤ Y.length := by
              rcases (by omega : Y.length = 1 ∨ 2 ≤ Y.length) with h1 | h1
              · exfalso
                rw [h1] at hz
                simp only [Nat.sub_self] at hz
                exact hz hY.root
              · exact h1
            have hnz : ¬ (entry Y 0 (Y.length - 1) = 0 ∧ entry Y 1 (Y.length - 1) = 0 ∧
                entry Y 2 (Y.length - 1) = 0) := fun h => hz h.1
            have hp := hasParent_of_ZrootMono hY.zroot hY.mono hY.root hlen2 hnz
            refine GoodP_inner hlen2 hp hw ?_
            intro n hn
            exact h2 n hn (ws' ++ [Y⟦n⟧]) (Wp_append hw' (Wp_singleton (Bok_oper hY hn)))
              (oper_shwP_inner ws' hlen2 hp n)
    · omega
  intro ws hw
  exact key (shwP_mem hw) ws hw rfl

#print axioms GoodP_all


/-! ### シート行 337〜345 -/

theorem Bok_Q : Bok Q := Aok_Q.toBok

/-- 高さ 2 で任意の `Bok` ブロックを吊るす: `Q ++ B↑2 = (0,0,0) :: (z の荷が B の字)`。 -/
theorem hangQ {B : TrioSeq} (hB : Bok B) : Q ++ shiftr01 2 0 B ∈ W 0 := by
  have h := (GoodP_all [B] (Wp_singleton hB)).root.mem
  simpa [wordP, colP, Q] using h

/-- ★★★★★ シート行337 `(0,0,0)(1,1,1)(2,0,0)(3,1,1) = psi(W_w*psi(W_w))`。 -/
theorem R337_mem : ([(0, 0, 0), (1, 1, 1), (2, 0, 0), (3, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := hangQ Bok_Q
  simpa [Q, shiftr01] using h

/-- ★★★★★ シート行338 `(0,0,0)(1,1,1)(2,1,0) = psi(W_w*W)`。 -/
theorem R338_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have hrow : ∀ j, 0 < j → j < Q.length → 1 ≤ entry Q 1 j := by
    intro j hj0 hjl
    simp only [Q, List.length_cons, List.length_nil] at hjl
    have hj : j = 1 := by omega
    subst hj
    simp [Q, entry]
  have h := snocd_gen (Y := Q) (d := 2) (by omega) Aok_Q (Ancd_of_row1 hrow 2)
    (fun B hB => hangQ hB)
  simpa [Q] using h

def R338 : TrioSeq := [(0, 0, 0), (1, 1, 1), (2, 1, 0)]

theorem Aok_R338 : Aok R338 := by
  refine ⟨R338_mem, by simp [R338], ⟨by simp [R338, entry], ?_⟩, ?_, ?_⟩
  · intro j hj hjl
    simp only [R338, List.length_cons, List.length_nil] at hjl
    rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl <;> simp [R338, entry]
  · intro c hc h0
    simp only [R338, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> simp_all
  · intro c hc
    simp only [R338, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> simp

theorem R338_row1 : ∀ j, 0 < j → j < R338.length → 1 ≤ entry R338 1 j := by
  intro j hj0 hjl
  simp only [R338, List.length_cons, List.length_nil] at hjl
  rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl <;> simp [R338, entry]

/-- ★★★★★ シート行339 `R338 (1,1,0) = psi(W_w*W+W)`。 -/
theorem R339_mem : R338 ++ [((1, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  snocd_gen (by omega) Aok_R338 (Ancd_of_row1 R338_row1 1)
    (fun B hB => by simpa [bump] using Bok.append Aok_R338 hB)

def R339 : TrioSeq := R338 ++ [((1, 1, 0) : ℕ × ℕ × ℕ)]

theorem R339_RunA0 : RunA 0 1 R339 :=
  ⟨0, R338, _, rfl, rfl, LwA_of_Aok Aok_R338, by simpa using SegA_one 0⟩

/-- ★★★★★ シート行340 `R339 (2,2,0) = psi(W_w*W+psi_1(W_2))`。 -/
theorem R340_mem : R339 ++ [((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  RunG_snoc2 Iface_RunA0 0 1 R339 R339_RunA0

/-- ★★★★★ シート行341 `R338 (1,1,0)(2,2,1) = psi(W_w*W+psi_1(W_w))`。 -/
theorem R341_mem : R338 ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  ((BaseOk_RunA 0).aok _ _ (LwA_unit11 (LwA_of_Aok Aok_R338))).mem

def R341 : TrioSeq := R338 ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)]

/-- 梯子の元 `A`（レベル `h`）の上の単位の上に、高さ `h+3` で任意の `Bok` を吊るす。 -/
theorem hangU11 {h : ℕ} {A : TrioSeq} (hA : LwA h A) {B : TrioSeq} (hB : Bok B) :
    A ++ ([((h + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 1) : ℕ × ℕ × ℕ)] ++
      shiftr01 (h + 3) 0 B) ∈ W 0 := by
  obtain ⟨P, hP, hL⟩ := hA
  have h1 := ((GoodP_all [B] (Wp_singleton hB)).seg h).reapp P hP 0 A (by simpa using hL)
  simpa [wordP, colP, shiftr01_zero, List.append_assoc,
    show h + 1 + 1 = h + 2 from by omega, show h + 1 + 2 = h + 3 from by omega] using h1

/-- ★★★★★ シート行342 `R341 (3,0,0) = psi(W_w*W+psi_1(W_w*w))`。 -/
theorem R342_mem : R341 ++ [((3, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := hangU11 (h := 0) (LwA_of_Aok Aok_R338) Bok_zero
  simpa [R341, shiftr01, List.append_assoc] using h

/-- ★★★★★ シート行343 `R341 (3,0,0)(4,1,1) = psi(W_w*W+psi_1(W_w*psi(W_w)))`。 -/
theorem R343_mem : R341 ++ [((3, 0, 0) : ℕ × ℕ × ℕ), ((4, 1, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := hangU11 (h := 0) (LwA_of_Aok Aok_R338) Bok_Q
  simpa [R341, Q, shiftr01, List.append_assoc] using h

theorem Aok_R341 : Aok R341 := (BaseOk_RunA 0).aok _ _ (LwA_unit11 (LwA_of_Aok Aok_R338))

theorem R341_row1 : ∀ j, 0 < j → j < R341.length → 1 ≤ entry R341 1 j := by
  intro j hj0 hjl
  simp only [R341, R338, List.length_append, List.length_cons, List.length_nil] at hjl
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl <;>
    simp [R341, R338, entry]

/-- ★★★★★ シート行344 `R341 (3,1,0) = psi(W_w*W+psi_1(W_w*W))`。 -/
theorem R344_mem : R341 ++ [((3, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine snocd_gen (Y := R341) (d := 3) (by omega) Aok_R341 (Ancd_of_row1 R341_row1 3) ?_
  intro B hB
  have h := hangU11 (h := 0) (LwA_of_Aok Aok_R338) hB
  simpa [R341, List.append_assoc] using h

def R344 : TrioSeq := R341 ++ [((3, 1, 0) : ℕ × ℕ × ℕ)]

theorem Aok_R344 : Aok R344 := by
  refine ⟨R344_mem, by simp [R344, R341, R338], ⟨by simp [R344, R341, R338, entry], ?_⟩, ?_, ?_⟩
  · intro j hj hjl
    simp only [R344, R341, R338, List.length_append, List.length_cons, List.length_nil] at hjl
    rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with rfl | rfl | rfl | rfl | rfl <;>
      simp [R344, R341, R338, entry]
  · intro c hc h0
    simp only [R344, R341, R338, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro c hc
    simp only [R344, R341, R338, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem R345_row1 : ∀ j, 0 < j →
    j < (R344 ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)]).length →
    1 ≤ entry (R344 ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)]) 1 j := by
  intro j hj0 hjl
  simp only [R344, R341, R338, List.length_append, List.length_cons, List.length_nil] at hjl
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [R344, R341, R338, entry]

/-- ★★★★★ シート行345 `R344 (1,1,0)(2,2,1)(3,1,0) = psi(W_w*W+psi_1(W_w*W)*2)`。 -/
theorem R345_mem : R344 ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hbase : Aok (R344 ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)]) :=
    (BaseOk_RunA 0).aok _ _ (LwA_unit11 (LwA_of_Aok Aok_R344))
  have h := snocd_gen (Y := R344 ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)])
    (d := 3) (by omega) hbase (Ancd_of_row1 R345_row1 3) ?_
  · simpa [List.append_assoc] using h
  · intro B hB
    have h1 := hangU11 (h := 0) (LwA_of_Aok Aok_R344) hB
    simpa [List.append_assoc] using h1

#print axioms R337_mem
#print axioms R345_mem


/-! ### 行 344 の 3 列をセグメントに一般化して、`R344` を走りの底の元にする -/

/-- 梯子の元の上の `(h+1,1,0)(h+2,2,1)` の右の列は、高さ `h+3` 未満で可視なら行 1 が 1 以上。 -/
theorem Ancd_unit11_3 {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) {s : ℕ} {A : TrioSeq}
    (hA : LwB P s A) :
    Ancd (s + 3) (A ++ [((s + 1, 1, 0) : ℕ × ℕ × ℕ), ((s + 2, 2, 1) : ℕ × ℕ × ℕ)]) := by
  have hAnc : Ancd (s + 1) A := LwB_Ancd hP hA
  set N : TrioSeq := [((s + 1, 1, 0) : ℕ × ℕ × ℕ), ((s + 2, 2, 1) : ℕ × ℕ × ℕ)] with hN
  intro j hj0 hjl hlt hvis
  rcases Nat.lt_or_ge j A.length with hjA | hjA
  · have e0 : entry (A ++ N) 0 j = entry A 0 j := entry_append_left hjA
    have e1 : entry (A ++ N) 1 j = entry A 1 j := entry_append_left hjA
    have hNl : A.length < (A ++ N).length := by simp [hN]
    have hlt1 : entry A 0 j < s + 1 := by
      have h1 := hvis A.length hjA hNl
      have h2 : entry (A ++ N) 0 A.length = s + 1 := by
        rw [show A.length = A.length + 0 from rfl, entry_append_right]
        simp [hN, entry]
      rw [e0] at h1
      omega
    rw [e1]
    refine hAnc j hj0 hjA hlt1 ?_
    intro i hi hil
    have := hvis i hi (by simp [hN]; omega)
    rwa [e0, entry_append_left hil] at this
  · obtain ⟨u, hu, rfl⟩ : ∃ u, u < 2 ∧ j = A.length + u := ⟨j - A.length, by simp [hN] at hjl; omega, by omega⟩
    rw [entry_append_right]
    rcases (show u = 0 ∨ u = 1 by omega) with rfl | rfl <;> simp [hN, entry]

/-- ★ 行 344 の 3 列は、どの梯子の元の上でも通るセグメント。 -/
theorem SegA_unit11_1 (h : ℕ) : SegA h [((h + 1, 1, 0) : ℕ × ℕ × ℕ),
    ((h + 2, 2, 1) : ℕ × ℕ × ℕ), ((h + 3, 1, 0) : ℕ × ℕ × ℕ)] where
  mid := by
    refine ⟨by simp, ?_, by simp [entry], by simp [entry], ?_, ?_⟩
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp
    · intro j hj1 hjl
      simp only [List.length_cons, List.length_nil] at hjl
      rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl <;> simp [entry] <;> omega
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp
  head1 := by simp [entry]
  reapp := by
    intro P hP s A' hA'
    have hLw : LwA (h + s) A' := ⟨P, hP, hA'⟩
    have hbase : Aok (A' ++ [((h + s + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + s + 2, 2, 1) : ℕ × ℕ × ℕ)]) :=
      (BaseOk_RunA 0).aok _ _ (LwA_unit11 hLw)
    have hanc := Ancd_unit11_3 hP (s := h + s) (A := A') (by
      obtain ⟨r, hr⟩ := hA'
      exact ⟨r, hr⟩)
    have h1 := snocd_gen (d := h + s + 3) (by omega) hbase hanc ?_
    · have e : shiftr01 s 0 [((h + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 1) : ℕ × ℕ × ℕ),
          ((h + 3, 1, 0) : ℕ × ℕ × ℕ)]
          = [((h + s + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + s + 2, 2, 1) : ℕ × ℕ × ℕ),
            ((h + s + 3, 1, 0) : ℕ × ℕ × ℕ)] := by
        simp [shiftr01]; omega
      rw [e]
      simpa [List.append_assoc] using h1
    · intro B hB
      have h2 := hangU11 hLw hB
      simpa [List.append_assoc] using h2

/-- ★★★ `R344` は走りの底の元（レベル 1）。 -/
theorem R344_RunA0 : RunA 0 1 R344 :=
  ⟨0, R338, _, rfl, rfl, LwA_of_Aok Aok_R338, by simpa [R344, R341] using SegA_unit11_1 0⟩

/-- ★★★★★ シート行346 `R344 (2,1,0) = psi(W_w*W+psi_1(W_w*W)*w)`。 -/
theorem R346_mem : R344 ++ [((2, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hR : RunA 0 2 (R344 ++ [((2, 1, 0) : ℕ × ℕ × ℕ)]) :=
    ⟨1, R344, _, rfl, rfl, RunA0_LwA R344_RunA0, by simpa using SegA_one 1⟩
  exact ((BaseOk_RunA 0).aok _ _ hR).mem

/-- ★★★★★ シート行347 `R344 (2,2,0) = psi(W_w*W+W_2)`。 -/
theorem R347_mem : R344 ++ [((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  RunG_snoc2 Iface_RunA0 0 1 R344 R344_RunA0

/-- ★★★★★ シート行348 `R344 (2,2,0)(3,3,1) = psi(W_w*W+psi_2(W_w))`。 -/
theorem R348_mem : R344 ++ [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine z1_mem (a := 2) (b := 2) ?_
  intro n
  cases n with
  | zero => simpa [Dtw] using R344_mem
  | succ n =>
      have e : Dtw 2 2 (n + 1) = DiaV 1 1 (n + 1) := Dtw_eq_DiaV 1 1 (n + 1)
      rw [e]
      exact RunA0_DiaV R344_RunA0 (n + 1)

#print axioms R348_mem


/-! ### junk の族の抽象化 `GoodF`（記録の右に付ける junk が 4 段すべてで普遍） -/

/-- 根を除いた 3 段（`PU` / `PkGA` / `SegA`）で普遍な junk の族。`J a b` = 記録 `(a,b,0)` の右の junk。 -/
structure GoodFb (J : ℕ → ℕ → TrioSeq) : Prop where
  ge : ∀ a b, ∀ x ∈ J a b, a + 1 ≤ x.1
  mono : ∀ a b, Mono (J a b)
  shift : ∀ a b s, shiftr01 s 0 (J a b) = J (a + s) b
  pu : ∀ y c : ℕ, 2 ≤ y → JkU y c (J (c + 1) (y + 1))
  pk : ∀ c : ℕ, JkGU c (J (c + 1) 2)
  seg : ∀ h : ℕ, SegA h (((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: J (h + 1) 1)

/-- 4 段（`GoodFb` に根を足したもの）。 -/
structure GoodF (J : ℕ → ℕ → TrioSeq) : Prop where
  ge : ∀ a b, ∀ x ∈ J a b, a + 1 ≤ x.1
  mono : ∀ a b, Mono (J a b)
  shift : ∀ a b s, shiftr01 s 0 (J a b) = J (a + s) b
  pu : ∀ y c : ℕ, 2 ≤ y → JkU y c (J (c + 1) (y + 1))
  pk : ∀ c : ℕ, JkGU c (J (c + 1) 2)
  seg : ∀ h : ℕ, SegA h (((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: J (h + 1) 1)
  root : Aok (((0, 0, 0) : ℕ × ℕ × ℕ) :: J 0 0)

theorem GoodF.toGoodFb {J : ℕ → ℕ → TrioSeq} (h : GoodF J) : GoodFb J :=
  ⟨h.ge, h.mono, h.shift, h.pu, h.pk, h.seg⟩

/-- 語 `ws` の junk の族。 -/
theorem GoodF_wordP {ws : List TrioSeq} (hw : Wpl ws) (hG : GoodP ws) :
    GoodF (fun a b => wordP a b ws) where
  ge := fun a b => wordP_ge a b ws
  mono := fun a b => wordP_mono hw
  shift := fun a b s => wordP_shift a b s ws
  pu := hG.pu
  pk := hG.pk
  seg := hG.seg
  root := hG.root

/-- 記録と junk の対角の塔。 -/
def Dzf (J : ℕ → ℕ → TrioSeq) (a b : ℕ) (n : ℕ) : TrioSeq :=
  (List.range n).flatMap fun k => ((a + k, b + k, 0) : ℕ × ℕ × ℕ) :: J (a + k) (b + k)

theorem Dzf_succ (J : ℕ → ℕ → TrioSeq) (a b : ℕ) (n : ℕ) : Dzf J a b (n + 1) =
    Dzf J a b n ++ (((a + n, b + n, 0) : ℕ × ℕ × ℕ) :: J (a + n) (b + n)) := by
  simp [Dzf, List.range_succ]

theorem Dzf_chainU {J : ℕ → ℕ → TrioSeq} (hG : GoodFb J)
    {y : ℕ} (hy : 2 ≤ y) {E : ℕ → TrioSeq → Prop} (hE : IfcV (y + 1) E)
    {c : ℕ} {Z : TrioSeq} (hZ : E c Z) :
    ∀ (n : ℕ) (Jt : TrioSeq), JkU (y + n + 1) (c + n + 1) Jt →
      PU (y + n + 1) (c + n + 2)
        (Z ++ Dzf J (c + 1) (y + 1) (n + 1) ++ ([((c + n + 2, y + n + 2, 0) : ℕ × ℕ × ℕ)] ++ Jt))
  | 0, Jt, hJ => by
      have h1 : PU y (c + 1) (Z ++ Dzf J (c + 1) (y + 1) 1) :=
        ⟨E, c, Z, J (c + 1) (y + 1), hE, rfl, hZ, by simp [Dzf], hG.pu y c hy⟩
      exact ⟨PU y, c + 1, _, Jt, IfcV_PU (by omega) (y + 0 + 1 + 1) (by omega), by omega, h1,
        by simp, hJ⟩
  | (n + 1), Jt, hJ => by
      have ih := Dzf_chainU hG hy hE hZ n (J (c + n + 2) (y + n + 2))
        (hG.pu (y + n + 1) (c + n + 1) (by omega))
      refine ⟨PU (y + n + 1), c + n + 2, _, Jt, IfcV_PU (by omega) (y + (n + 1) + 1 + 1) (by omega),
        by omega, ih, ?_, by simpa [show y + (n + 1) + 1 = y + n + 1 + 1 from by omega,
          show c + (n + 1) + 1 = c + n + 1 + 1 from by omega] using hJ⟩
      rw [Dzf_succ J (c + 1) (y + 1) (n + 1)]
      simp [List.append_assoc, show c + 1 + (n + 1) = c + n + 2 from by omega,
        show y + 1 + (n + 1) = y + n + 2 from by omega,
        show c + (n + 1) + 2 = c + n + 3 from by omega,
        show y + (n + 1) + 2 = y + n + 3 from by omega,
        show c + n + 2 + 1 = c + n + 3 from by omega]

theorem Dzf_W {J : ℕ → ℕ → TrioSeq} (hG : GoodFb J)
    {y : ℕ} (hy : 2 ≤ y) {E : ℕ → TrioSeq → Prop} (hE : IfcV (y + 1) E)
    {c : ℕ} {Z : TrioSeq} (hZ : E c Z) : ∀ n : ℕ, Z ++ Dzf J (c + 1) (y + 1) n ∈ W 0
  | 0 => by simpa [Dzf] using ((IfcV_iface (y + 1) hE).bok.aok _ _ hZ).mem
  | 1 => by
      have h1 : PU y (c + 1) (Z ++ Dzf J (c + 1) (y + 1) 1) :=
        ⟨E, c, Z, J (c + 1) (y + 1), hE, rfl, hZ, by simp [Dzf], hG.pu y c hy⟩
      exact ((BaseOk_PU y).aok _ _ h1).mem
  | (n + 2) => by
      have h := Dzf_chainU hG hy hE hZ n (J (c + n + 2) (y + n + 2))
        (hG.pu (y + n + 1) (c + n + 1) (by omega))
      have h2 := ((BaseOk_PU (y + n + 1)).aok _ _ h).mem
      rw [Dzf_succ J (c + 1) (y + 1) (n + 1)]
      simpa [List.append_assoc, show c + 1 + (n + 1) = c + n + 2 from by omega,
        show y + 1 + (n + 1) = y + n + 2 from by omega] using h2

theorem Dzf_W_RunG {J : ℕ → ℕ → TrioSeq} (hG : GoodFb J) {E : ℕ → TrioSeq → Prop} (hI : Iface E)
    {j c : ℕ} {X : TrioSeq} (hX : RunG E j c X) : ∀ n : ℕ, X ++ Dzf J (c + 1) 2 n ∈ W 0 := by
  have hP : PkGA (c + 1) (X ++ Dzf J (c + 1) 2 1) :=
    ⟨E, hI, j, c, X, J (c + 1) 2, rfl, hX, by simp [Dzf], hG.pk c⟩
  intro n
  match n with
  | 0 => simpa [Dzf] using ((BaseOk_RunG hI.bok j).aok _ _ hX).mem
  | 1 => exact (PkGA_Aok hP).mem
  | (n + 2) =>
      have e : Dzf J (c + 1) 2 (n + 2) = Dzf J (c + 1) 2 1 ++ Dzf J (c + 1 + 1) 3 (n + 1) := by
        simp only [Dzf]
        rw [show n + 2 = 1 + (n + 1) from by omega, List.range_add, List.flatMap_append,
          List.flatMap_map]
        congr 1
        apply List.flatMap_congr
        intro k _
        simp [show c + 1 + (1 + k) = c + 1 + 1 + k from by omega, show 2 + (1 + k) = 3 + k from by omega]
      rw [e, ← List.append_assoc]
      exact Dzf_W hG (le_refl 2) (Ifc3_toIfcV Ifc3_PkGA) hP (n + 1)

theorem Dzf_W_LwA {J : ℕ → ℕ → TrioSeq} (hG : GoodFb J) {h : ℕ} {A : TrioSeq} (hA : LwA h A) :
    ∀ n : ℕ, A ++ Dzf J (h + 1) 1 n ∈ W 0 := by
  have hX : RunA 0 (h + 1) (A ++ Dzf J (h + 1) 1 1) :=
    ⟨h, A, _, rfl, rfl, hA, by simpa [Dzf] using hG.seg h⟩
  intro n
  match n with
  | 0 => simpa [Dzf] using (LwA_Aok hA).mem
  | 1 => exact ((BaseOk_RunA 0).aok _ _ hX).mem
  | (n + 2) =>
      have e : Dzf J (h + 1) 1 (n + 2) = Dzf J (h + 1) 1 1 ++ Dzf J (h + 1 + 1) 2 (n + 1) := by
        simp only [Dzf]
        rw [show n + 2 = 1 + (n + 1) from by omega, List.range_add, List.flatMap_append,
          List.flatMap_map]
        congr 1
        apply List.flatMap_congr
        intro k _
        simp [show h + 1 + (1 + k) = h + 1 + 1 + k from by omega, show 1 + (1 + k) = 2 + k from by omega]
      rw [e, ← List.append_assoc]
      exact Dzf_W_RunG hG Iface_RunA0 (j := 0) hX (n + 1)

theorem Dzf_W_root {J : ℕ → ℕ → TrioSeq} (hG : GoodF J) : ∀ n : ℕ, Dzf J 0 0 n ∈ W 0
  | 0 => by simpa [Dzf] using W_nil 0
  | (n + 1) => by
      have e : Dzf J 0 0 (n + 1) = Dzf J 0 0 1 ++ Dzf J (0 + 1) 1 n := by
        simp only [Dzf]
        rw [show n + 1 = 1 + n from by omega, List.range_add, List.flatMap_append, List.flatMap_map]
        congr 1
        apply List.flatMap_congr
        intro k _
        simp [Nat.add_comm]
      rw [e]
      have h1 := Dzf_W_LwA hG.toGoodFb (h := 0) (LwA_of_Aok hG.root) n
      simpa [Dzf] using h1

#print axioms Dzf_W_root


/-! ### junk の族「z の列 + 1 の列」`Jz1c` と、行 349, 350 -/

/-- 台座の右に記録と z を継ぐと、祖先条件が 2 段上がる。 -/
theorem Ancd_snoc2 {s : ℕ} {A : TrioSeq} (hA : Ancd (s + 1) A) {v1 v2 z2 : ℕ}
    (hv1 : 1 ≤ v1) (hv2 : 1 ≤ v2) :
    Ancd (s + 3) (A ++ [((s + 1, v1, 0) : ℕ × ℕ × ℕ), ((s + 2, v2, z2) : ℕ × ℕ × ℕ)]) := by
  set N : TrioSeq := [((s + 1, v1, 0) : ℕ × ℕ × ℕ), ((s + 2, v2, z2) : ℕ × ℕ × ℕ)] with hN
  intro j hj0 hjl hlt hvis
  rcases Nat.lt_or_ge j A.length with hjA | hjA
  · have e0 : entry (A ++ N) 0 j = entry A 0 j := entry_append_left hjA
    have e1 : entry (A ++ N) 1 j = entry A 1 j := entry_append_left hjA
    have hNl : A.length < (A ++ N).length := by simp [hN]
    have hlt1 : entry A 0 j < s + 1 := by
      have h1 := hvis A.length hjA hNl
      have h2 : entry (A ++ N) 0 A.length = s + 1 := by
        rw [show A.length = A.length + 0 from rfl, entry_append_right]
        simp [hN, entry]
      rw [e0] at h1
      omega
    rw [e1]
    refine hA j hj0 hjA hlt1 ?_
    intro i hi hil
    have := hvis i hi (by simp [hN]; omega)
    rwa [e0, entry_append_left hil] at this
  · obtain ⟨u, hu, rfl⟩ : ∃ u, u < 2 ∧ j = A.length + u :=
      ⟨j - A.length, by simp [hN] at hjl; omega, by omega⟩
    rw [entry_append_right]
    rcases (show u = 0 ∨ u = 1 by omega) with rfl | rfl <;> simp [hN, entry] <;> omega

/-- 記録 `(a,b,0)` の右の junk「z の列 + 1 の列」。 -/
def Jz1c (a b : ℕ) : TrioSeq := [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ), ((a + 2, 1, 0) : ℕ × ℕ × ℕ)]

theorem Jz1c_shift (a b s : ℕ) : shiftr01 s 0 (Jz1c a b) = Jz1c (a + s) b := by
  simp [Jz1c, shiftr01]
  omega

/-- ★★★ 「z の列 + 1 の列」は 4 段すべてで普遍な junk。 -/
theorem GoodF_z1c : GoodF Jz1c where
  ge := by
    intro a b x hx
    simp only [Jz1c, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp
  mono := by
    intro a b x hx
    simp only [Jz1c, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp
  shift := Jz1c_shift
  pu := by
    intro y c hy
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [Jz1c, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp <;> omega
    · intro x hx
      simp only [Jz1c, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp <;> omega
    intro E hE t Z hZ
    have hPU : PU y (c + 1 + t) (Z ++ ([((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)] ++
        [((c + 1 + t + 1, y + 1 + 1, 1) : ℕ × ℕ × ℕ)])) :=
      ⟨E, c + t, Z, _, hE, by omega, hZ, by
        rw [show c + t + 1 = c + 1 + t from by omega, show c + t + 2 = c + 1 + t + 1 from by omega,
          show y + 2 = y + 1 + 1 from by omega], JkU_z1 hy (c + t)⟩
    have hbase := (BaseOk_PU y).aok _ _ hPU
    have hancZ : Ancd (c + t + 1) Z := (IfcV_iface (y + 1) hE).bok.ancd (c + t) Z hZ
    have hanc : Ancd (c + t + 3) (Z ++ [((c + t + 1, y + 1, 0) : ℕ × ℕ × ℕ),
        ((c + t + 2, y + 2, 1) : ℕ × ℕ × ℕ)]) :=
      Ancd_snoc2 hancZ (by omega) (by omega)
    have h1 := snocd_gen (Y := Z ++ [((c + t + 1, y + 1, 0) : ℕ × ℕ × ℕ),
        ((c + t + 2, y + 2, 1) : ℕ × ℕ × ℕ)]) (d := c + t + 3) (by omega)
      (by simpa [show c + 1 + t = c + t + 1 from by omega,
        show c + 1 + t + 1 = c + t + 2 from by omega,
        show y + 1 + 1 = y + 2 from by omega] using hbase) hanc ?_
    · rw [Jz1c_shift]
      simpa [Jz1c, List.append_assoc, show c + 1 + t = c + t + 1 from by omega,
        show c + 2 + t = c + t + 2 from by omega, show c + 3 + t = c + t + 3 from by omega,
        show y + 1 + 1 = y + 2 from by omega] using h1
    · intro B hB
      have h2 := (GoodP_all [B] (Wp_singleton hB)).pu y c hy
      have h3 := h2.2.2 E hE t Z hZ
      rw [wordP_shift] at h3
      simpa [wordP, colP, List.append_assoc, show c + 1 + t = c + t + 1 from by omega,
        show c + 1 + t + 1 = c + t + 2 from by omega, show c + 1 + t + 2 = c + t + 3 from by omega,
        show y + 1 + 1 = y + 2 from by omega] using h3
  pk := by
    intro c E hI
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [Jz1c, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp <;> omega
    · intro x hx
      simp only [Jz1c, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp <;> omega
    intro j t X hX
    have hPk : PkGA (c + 1 + t) (X ++ ([((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ)] ++
        [((c + 1 + t + 1, 2 + 1, 1) : ℕ × ℕ × ℕ)])) :=
      ⟨E, hI, j, c + t, X, _, by omega, hX, by
        rw [show c + t + 1 = c + 1 + t from by omega, show c + t + 2 = c + 1 + t + 1 from by omega,
          show (3 : ℕ) = 2 + 1 from by omega], JkGU_z1 (c + t)⟩
    have hbase := PkGA_Aok hPk
    have hancX : Ancd (c + t + 1) X := (BaseOk_RunG hI.bok j).ancd (c + t) X hX
    have hanc : Ancd (c + t + 3) (X ++ [((c + t + 1, 2, 0) : ℕ × ℕ × ℕ),
        ((c + t + 2, 3, 1) : ℕ × ℕ × ℕ)]) :=
      Ancd_snoc2 hancX (by omega) (by omega)
    have h1 := snocd_gen (Y := X ++ [((c + t + 1, 2, 0) : ℕ × ℕ × ℕ),
        ((c + t + 2, 3, 1) : ℕ × ℕ × ℕ)]) (d := c + t + 3) (by omega)
      (by simpa [show c + 1 + t = c + t + 1 from by omega,
        show c + 1 + t + 1 = c + t + 2 from by omega] using hbase) hanc ?_
    · rw [Jz1c_shift]
      simpa [Jz1c, List.append_assoc, show c + 1 + t = c + t + 1 from by omega,
        show c + 2 + t = c + t + 2 from by omega, show c + 3 + t = c + t + 3 from by omega] using h1
    · intro B hB
      have h2 := (GoodP_all [B] (Wp_singleton hB)).pk c E hI
      have h3 := h2.2.2 j t X hX
      rw [wordP_shift] at h3
      simpa [wordP, colP, List.append_assoc, show c + 1 + t = c + t + 1 from by omega,
        show c + 1 + t + 1 = c + t + 2 from by omega, show c + 1 + t + 2 = c + t + 3 from by omega]
        using h3
  seg := by
    intro h
    simpa [Jz1c, show h + 1 + 1 = h + 2 from by omega,
      show h + 1 + 2 = h + 3 from by omega] using SegA_unit11_1 h
  root := by simpa [Jz1c, R338] using Aok_R338

def R348 : TrioSeq := R344 ++ [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ)]

def R349 : TrioSeq := R348 ++ [((4, 1, 0) : ℕ × ℕ × ℕ)]

theorem R349_PkGA : PkGA 2 R349 :=
  ⟨RunA 0, Iface_RunA0, 0, 1, R344, Jz1c 2 2, rfl, R344_RunA0, by simp [R349, R348, Jz1c],
    GoodF_z1c.pk 1⟩

/-- ★★★★★ シート行349 `R348 (4,1,0) = psi(W_w*W+psi_2(W_w*W))`。 -/
theorem R349_mem : R349 ∈ W 0 := (PkGA_Aok R349_PkGA).mem

theorem R350_PU : PU 2 3 (R349 ++ [((3, 3, 0) : ℕ × ℕ × ℕ)]) :=
  ⟨PkGA, 2, R349, [], Ifc3_toIfcV Ifc3_PkGA, rfl, R349_PkGA, by simp, JkU_nil' (le_refl 2) 2⟩

/-- ★★★★★ シート行350 `R349 (3,3,0) = psi(W_w*W+W_3)`。 -/
theorem R350_mem : R349 ++ [((3, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  ((BaseOk_PU 2).aok _ _ R350_PU).mem

#print axioms R350_mem


/-! ### 「z の列 + 1 の列」の junk の上の z の列の展開。行 351 -/

theorem le1_row1_le {M : TrioSeq} {i j : ℕ} (h : Relation.ReflTransGen (nextrel1 M) i j) :
    entry M 1 i ≤ entry M 1 j := by
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => exact le_trans ih (le_of_lt h2.2.2.2.1)

/-- 行 1 の親鎖は行 1 を狭義に増やす。 -/
theorem le1_row1_lt {M : TrioSeq} {i j : ℕ} (h : le1 M i j) (hne : i ≠ j) :
    entry M 1 i < entry M 1 j := by
  obtain ⟨-, -, hch⟩ := h
  rcases Relation.ReflTransGen.cases_tail hch with h1 | ⟨c, hc1, hc2⟩
  · exact absurd h1.symm hne
  · have h3 := le1_row1_le hc1
    have h4 := hc2.2.2.2.1
    omega

open Classical in
/-- `Jz1c` の junk の上の z の列の展開は、記録と junk の対角の塔。 -/
theorem oper_z1_Jz1c (Y0 : TrioSeq) (a b : ℕ) (hb : 1 ≤ b) (n : ℕ) :
    (Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: Jz1c a b ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]))⟦n⟧
      = Y0 ++ Dzf Jz1c a b n := by
  set T : TrioSeq := ((a, b, 0) : ℕ × ℕ × ℕ) :: Jz1c a b ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] with hT
  set M : TrioSeq := Y0 ++ T with hM
  set p := Y0.length with hp
  have eT : ∀ i q, entry M i (p + q) = entry T i q := fun i q => entry_append_right Y0 T i q
  have hlen : M.length = p + 4 := by simp [hM, hT, Jz1c, hp]
  have e0 : entry M 0 p = a ∧ entry M 1 p = b ∧ entry M 2 p = 0 := by
    refine ⟨?_, ?_, ?_⟩ <;> · rw [show p = p + 0 from rfl, eT]; simp [hT, Jz1c, entry]
  have e1 : entry M 0 (p + 1) = a + 1 ∧ entry M 1 (p + 1) = b + 1 ∧ entry M 2 (p + 1) = 1 := by
    refine ⟨?_, ?_, ?_⟩ <;> · rw [eT]; simp [hT, Jz1c, entry]
  have e2 : entry M 0 (p + 2) = a + 2 ∧ entry M 1 (p + 2) = 1 ∧ entry M 2 (p + 2) = 0 := by
    refine ⟨?_, ?_, ?_⟩ <;> · rw [eT]; simp [hT, Jz1c, entry]
  -- z の位置は行 1 の子
  have hl0z : le0 M p (p + 1) := by
    refine ⟨by omega, by omega, Relation.ReflTransGen.single ?_⟩
    exact ⟨by omega, by omega, by omega, by rw [e0.1, e1.1]; omega, by intro j hj; omega⟩
  have hl1z : le1 M p (p + 1) := by
    refine ⟨by omega, by omega, Relation.ReflTransGen.single ?_⟩
    refine ⟨by omega, by omega, by omega, by rw [e0.2.1, e1.2.1]; omega, hl0z, ?_⟩
    intro j hj
    have hjle : j ≤ p + 1 := le0_le' hj.2
    have : j = p + 1 := by omega
    subst this
    exact le_rfl
  have hnl1 : ¬ le1 M p (p + 2) := by
    intro hc
    have := le1_row1_lt hc (by omega)
    rw [e0.2.1, e2.2.1] at this
    omega
  have hge : ∀ x ∈ Jz1c a b, a + 1 ≤ x.1 := GoodF_z1c.ge a b
  rw [oper_z1_mask Y0 a b (Jz1c a b) hge n]
  congr 1
  apply List.flatMap_congr
  intro k _
  congr 1
  have hL : (Jz1c a b).length = 2 := by simp [Jz1c]
  rw [hL]
  show (List.range 2).map _ = Jz1c (a + k) (b + k)
  rw [show (2 : ℕ) = 1 + 1 from rfl, List.range_add]
  simp only [List.map_append, List.range_one, List.map_cons, List.map_nil, List.map_map]
  rw [if_pos (by simpa using hl1z), if_neg (by simpa using hnl1)]
  simp [Jz1c, entry]
  omega

/-- ★★★★★ シート行351 `R344 (2,2,1) = psi(W_w*W+W_w)`。 -/
theorem R351_mem : R344 ++ [((2, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  have e : R344 ++ [((2, 2, 1) : ℕ × ℕ × ℕ)]
      = R338 ++ (((1, 1, 0) : ℕ × ℕ × ℕ) :: Jz1c 1 1 ++ [((1 + 1, 1 + 1, 1) : ℕ × ℕ × ℕ)]) := by
    simp [R344, R341, Jz1c]
  rw [e, oper_z1_Jz1c R338 1 1 (by omega) n]
  exact Dzf_W_LwA GoodF_z1c.toGoodFb (LwA_of_Aok Aok_R338) n

#print axioms R351_mem


/-! ### 行 351 の 4 列をセグメントに一般化して、行 352〜356 -/

/-- ★ 行 351 の 4 列は、どの梯子の元の上でも通るセグメント。 -/
theorem SegA_z1c (h : ℕ) :
    SegA h [((h + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 1) : ℕ × ℕ × ℕ),
      ((h + 3, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 1) : ℕ × ℕ × ℕ)] where
  mid := by
    refine ⟨by simp, ?_, by simp [entry], by simp [entry], ?_, ?_⟩
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> simp
    · intro j hj1 hjl
      simp only [List.length_cons, List.length_nil] at hjl
      rcases (show j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl <;>
        simp [entry] <;> omega
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> simp
  head1 := by simp [entry]
  reapp := by
    intro P hP s A' hA'
    have e : shiftr01 s 0 [((h + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 1) : ℕ × ℕ × ℕ),
        ((h + 3, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 1) : ℕ × ℕ × ℕ)]
        = ((h + s + 1, 1, 0) : ℕ × ℕ × ℕ) :: Jz1c (h + s + 1) 1 ++
          [((h + s + 1 + 1, 1 + 1, 1) : ℕ × ℕ × ℕ)] := by
      simp [Jz1c, shiftr01]
      omega
    rw [e]
    refine A1_intro (Or.inr (Or.inl ?_))
    intro n _
    rw [oper_z1_Jz1c A' (h + s + 1) 1 (by omega) n]
    exact Dzf_W_LwA GoodF_z1c.toGoodFb (h := h + s) ⟨P, hP, hA'⟩ n

def R351 : TrioSeq := R344 ++ [((2, 2, 1) : ℕ × ℕ × ℕ)]

theorem R351_RunA0 : RunA 0 1 R351 :=
  ⟨0, R338, _, rfl, rfl, LwA_of_Aok Aok_R338, by
    simpa [R351, R344, R341] using SegA_z1c 0⟩

theorem Aok_R351 : Aok R351 := (BaseOk_RunA 0).aok _ _ R351_RunA0

theorem R351_row1 : ∀ j, 0 < j → j < R351.length → 1 ≤ entry R351 1 j := by
  intro j hj0 hjl
  simp only [R351, R344, R341, R338, List.length_append, List.length_cons,
    List.length_nil] at hjl
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp [R351, R344, R341, R338, entry]

/-- ★★★★★ シート行352 `R351 (1,1,0) = psi(W_w*W+W_w+W)`。 -/
theorem R352_mem : R351 ++ [((1, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  snocd_gen (by omega) Aok_R351 (Ancd_of_row1 R351_row1 1)
    (fun B hB => by simpa [bump] using Bok.append Aok_R351 hB)

/-- ★★★★★ シート行353 `R351 (1,1,0)(2,2,1)(3,1,0) = psi(W_w*W+W_w+psi_1(W_w*W))`。 -/
theorem R353_mem : R351 ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := (SegA_unit11_1 0).reapp P0 BaseOk_zero 0 R351 (LwB_of_base ⟨Aok_R351, rfl⟩)
  simpa using h

/-- ★★★★★ シート行354 `R353 (2,2,1) = psi(W_w*W+W_w+psi_1(W_w*W+W_w))`。 -/
theorem R354_mem : R351 ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := (SegA_z1c 0).reapp P0 BaseOk_zero 0 R351 (LwB_of_base ⟨Aok_R351, rfl⟩)
  simpa using h

/-- ★★★★★ シート行355 `R351 (2,1,0) = psi(W_w*W+W_w+psi_1(W_w*W+W_w)*W)`。 -/
theorem R355_mem : R351 ++ [((2, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hR : RunA 0 2 (R351 ++ [((2, 1, 0) : ℕ × ℕ × ℕ)]) :=
    ⟨1, R351, _, rfl, rfl, RunA0_LwA R351_RunA0, by simpa using SegA_one 1⟩
  exact ((BaseOk_RunA 0).aok _ _ hR).mem

/-- ★★★★★ シート行356 `R351 (2,2,0) = psi(W_w*W+W_w+W_2)`。 -/
theorem R356_mem : R351 ++ [((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  RunG_snoc2 Iface_RunA0 0 1 R351 R351_RunA0

#print axioms R356_mem


/-! ### junk の語「z の列と 1 の列」`Zw` と、行 357〜360 -/

/-- 記録 `(a,b,0)` の右の junk の字: `true` = z の列、`false` = 1 の列。 -/
def zcol (a b : ℕ) : Bool → ℕ × ℕ × ℕ
  | true => (a + 1, b + 1, 1)
  | false => (a + 2, 1, 0)

def Zw (w : List Bool) (a b : ℕ) : TrioSeq := w.map (zcol a b)

theorem Zw_nil (a b : ℕ) : Zw [] a b = [] := rfl

theorem Zw_snoc (w : List Bool) (t : Bool) (a b : ℕ) :
    Zw (w ++ [t]) a b = Zw w a b ++ [zcol a b t] := by simp [Zw]

theorem zcol_shift (a b s : ℕ) (t : Bool) :
    shiftr01 s 0 [zcol a b t] = [zcol (a + s) b t] := by
  cases t <;> simp [zcol, shiftr01] <;> omega

theorem Zw_shift (w : List Bool) (a b s : ℕ) : shiftr01 s 0 (Zw w a b) = Zw w (a + s) b := by
  induction w with
  | nil => simp [Zw, shiftr01]
  | cons t w ih =>
      rw [Zw, Zw, List.map_cons, List.map_cons,
        show (zcol a b t :: w.map (zcol a b)) = [zcol a b t] ++ w.map (zcol a b) from rfl,
        shiftr01_append0, zcol_shift]
      simpa [Zw] using congrArg (fun x => [zcol (a + s) b t] ++ x) ih

theorem Zw_ge {w : List Bool} {a b : ℕ} : ∀ x ∈ Zw w a b, a + 1 ≤ x.1 := by
  intro x hx
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
  cases t <;> simp [zcol]

theorem Zw_mono {w : List Bool} {a b : ℕ} : Mono (Zw w a b) := by
  intro x hx
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
  cases t <;> simp [zcol]

theorem MidD_Jw (a v : ℕ) (ha : 1 ≤ a) (hv : 1 ≤ v) (w : List Bool) :
    MidD (a + 1) (((a, v, 0) : ℕ × ℕ × ℕ) :: Zw w a v) := by
  have h := MidD_append (MidD_col a v ha hv) (N := Zw w a v) Zw_ge Zw_mono
  simpa using h

theorem entry_Jw {w : List Bool} {a b : ℕ} {r i : ℕ} (hi : i < w.length) :
    entry (Zw w a b) r i = entry [zcol a b (w[i]'hi)] r 0 := by
  rw [Zw, entry_map_lt (zcol a b) w hi r]

open Classical in
/-- junk の語の上の z の列の展開は、記録と junk の対角の塔。 -/
theorem oper_z1_Jw (Y0 : TrioSeq) (a b : ℕ) (hb : 1 ≤ b) (w : List Bool) (n : ℕ) :
    (Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: Zw w a b ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]))⟦n⟧
      = Y0 ++ Dzf (Zw w) a b n := by
  set C : TrioSeq := Zw w a b with hC
  set T : TrioSeq := ((a, b, 0) : ℕ × ℕ × ℕ) :: C ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] with hT
  set M : TrioSeq := Y0 ++ T with hM
  set p := Y0.length with hp
  set L := w.length with hL
  have hCL : C.length = L := by simp [hC, Zw, hL]
  have hlen : M.length = p + L + 2 := by simp [hM, hT, hC, Zw, hp, hL]; omega
  have eT : ∀ i q, entry M i (p + q) = entry T i q := fun i q => entry_append_right Y0 T i q
  have e0p : entry M 0 p = a ∧ entry M 1 p = b ∧ entry M 2 p = 0 := by
    refine ⟨?_, ?_, ?_⟩ <;> · rw [show p = p + 0 from rfl, eT]; simp [hT, entry]
  have eC : ∀ r i (hi : i < L), entry M r (p + 1 + i) = entry [zcol a b (w[i]'(by omega))] r 0 := by
    intro r i hi
    rw [show p + 1 + i = p + (i + 1) from by omega, eT]
    have : entry T r (i + 1) = entry C r i := by
      simp only [hT, entry, List.cons_append, List.getD_cons_succ]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega)]
    rw [this, hC, entry_Jw hi]
  have ege : ∀ i, i < L → a + 1 ≤ entry M 0 (p + 1 + i) := by
    intro i hi
    rw [eC 0 i hi]
    cases w[i] <;> simp [zcol, entry] <;> omega
  have ege' : ∀ j, p < j → j < p + 1 + L → a + 1 ≤ entry M 0 j := by
    intro j hj1 hj2
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < L ∧ j = p + 1 + i := ⟨j - (p + 1), by omega, by omega⟩
    exact ege i hi
  -- z の位置は行 1 の子
  have hl1 : ∀ i (hi : i < L), w[i] = true → le1 M p (p + 1 + i) := by
    intro i hi ht
    have e0 : entry M 0 (p + 1 + i) = a + 1 := by rw [eC 0 i hi, ht]; simp [zcol, entry]
    have e1 : entry M 1 (p + 1 + i) = b + 1 := by rw [eC 1 i hi, ht]; simp [zcol, entry]
    have hl0 : le0 M p (p + 1 + i) := by
      refine ⟨by omega, by omega, Relation.ReflTransGen.single ?_⟩
      refine ⟨by omega, by omega, by omega, by rw [e0p.1, e0]; omega, ?_⟩
      intro j hj
      rw [e0]
      exact ege' j hj.1 (by omega)
    refine ⟨by omega, by omega, Relation.ReflTransGen.single ?_⟩
    refine ⟨by omega, by omega, by omega, by rw [e0p.2.1, e1]; omega, hl0, ?_⟩
    intro j hj
    have := le0_eq_of_min (M := M) (p := p) (a := a) hj.1 hj.2 e0
      (fun j'' h1 h2 => ege' j'' h1 (by omega))
    subst this
    rw [e1]
  -- 1 の列は行 1 の子ではない
  have hnl1 : ∀ i (hi : i < L), w[i] = false → ¬ le1 M p (p + 1 + i) := by
    intro i hi hf hc
    have e1 : entry M 1 (p + 1 + i) = 1 := by rw [eC 1 i hi, hf]; simp [zcol, entry]
    have := le1_row1_lt hc (by omega)
    rw [e0p.2.1, e1] at this
    omega
  have hbody : ∀ k i (hi : i < L),
      ((entry C 0 i + k, entry C 1 i + (if le1 M p (p + 1 + i) then k else 0),
        entry C 2 i) : ℕ × ℕ × ℕ) = zcol (a + k) (b + k) (w[i]'(by omega)) := by
    intro k i hi
    have hiw : i < w.length := by omega
    rw [hC, entry_Jw hiw, entry_Jw hiw, entry_Jw hiw]
    cases hw : w[i]'hiw with
    | true =>
        rw [if_pos (hl1 i hi hw)]
        simp [hw, zcol, entry]
        omega
    | false =>
        rw [if_neg (hnl1 i hi hw)]
        simp [hw, zcol, entry]
        omega
  rw [oper_z1_mask Y0 a b C (fun x hx => Zw_ge x hx) n]
  congr 1
  apply List.flatMap_congr
  intro k _
  congr 1
  rw [hCL]
  apply List.ext_getElem
  · simp [Zw, hL]
  · intro i h1 h2
    have hi : i < L := by simpa [hL, Zw] using h2
    simp only [List.getElem_map, List.getElem_range]
    rw [hbody k i hi]
    simp [Zw]

/-- 空の junk。 -/
theorem GoodFb_nil : GoodFb (Zw []) where
  ge := fun a b => Zw_ge
  mono := fun a b => Zw_mono
  shift := fun a b s => Zw_shift [] a b s
  pu := fun y c hy => by simpa [Zw_nil] using JkU_nil' hy c
  pk := fun c => by simpa [Zw_nil] using JkGU_nil c
  seg := fun h => by simpa [Zw_nil] using SegA_one h

theorem Zw_z1c : Zw [true, false] = Jz1c := by
  funext a b
  simp [Zw, Jz1c, zcol]

theorem GoodFb_z1c : GoodFb (Zw [true, false]) := by
  rw [Zw_z1c]; exact GoodF_z1c.toGoodFb

/-- ★ 語の最後に z の列を足しても普遍。 -/
theorem GoodFb_snocz {w : List Bool} (hG : GoodFb (Zw w)) : GoodFb (Zw (w ++ [true])) where
  ge := fun a b => Zw_ge
  mono := fun a b => Zw_mono
  shift := fun a b s => Zw_shift (w ++ [true]) a b s
  pu := by
    intro y c hy
    refine ⟨fun x hx => by have := Zw_ge (w := w ++ [true]) (a := c + 1) (b := y + 1) x hx; omega,
      Zw_mono, ?_⟩
    intro E hE t Z hZ
    rw [Zw_shift, Zw_snoc]
    refine A1_intro (Or.inr (Or.inl ?_))
    intro n _
    have e : Z ++ ([((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)] ++
        (Zw w (c + 1 + t) (y + 1) ++ [zcol (c + 1 + t) (y + 1) true]))
        = Z ++ (((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ) :: Zw w (c + 1 + t) (y + 1) ++
          [((c + 1 + t + 1, y + 1 + 1, 1) : ℕ × ℕ × ℕ)]) := by
      simp [zcol, List.append_assoc]
    rw [e, oper_z1_Jw Z (c + 1 + t) (y + 1) (by omega) w n]
    have h := Dzf_W hG hy hE (c := c + t) hZ n
    simpa [show c + t + 1 = c + 1 + t from by omega] using h
  pk := by
    intro c E hI
    refine ⟨fun x hx => by have := Zw_ge (w := w ++ [true]) (a := c + 1) (b := 2) x hx; omega,
      Zw_mono, ?_⟩
    intro j t X hX
    rw [Zw_shift, Zw_snoc]
    refine A1_intro (Or.inr (Or.inl ?_))
    intro n _
    have e : X ++ ([((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ)] ++
        (Zw w (c + 1 + t) 2 ++ [zcol (c + 1 + t) 2 true]))
        = X ++ (((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ) :: Zw w (c + 1 + t) 2 ++
          [((c + 1 + t + 1, 2 + 1, 1) : ℕ × ℕ × ℕ)]) := by
      simp [zcol, List.append_assoc]
    rw [e, oper_z1_Jw X (c + 1 + t) 2 (by omega) w n]
    have h := Dzf_W_RunG hG hI (c := c + t) hX n
    simpa [show c + t + 1 = c + 1 + t from by omega] using h
  seg := by
    intro h
    refine ⟨by simpa [show h + 1 + 1 = h + 2 from by omega] using
        MidD_Jw (h + 1) 1 (by omega) (by omega) (w ++ [true]), by simp [entry], ?_⟩
    intro P hP s A' hA'
    have e : shiftr01 s 0 (((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: Zw (w ++ [true]) (h + 1) 1)
        = ((h + s + 1, 1, 0) : ℕ × ℕ × ℕ) :: Zw w (h + s + 1) 1 ++
          [((h + s + 1 + 1, 1 + 1, 1) : ℕ × ℕ × ℕ)] := by
      rw [show ((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: Zw (w ++ [true]) (h + 1) 1
          = [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ Zw (w ++ [true]) (h + 1) 1 from rfl,
        shiftr01_append0, shift_col, Zw_shift, Zw_snoc]
      simp [zcol, show h + 1 + s = h + s + 1 from by omega, List.append_assoc]
    rw [e]
    refine A1_intro (Or.inr (Or.inl ?_))
    intro n _
    rw [oper_z1_Jw A' (h + s + 1) 1 (by omega) w n]
    exact Dzf_W_LwA hG (h := h + s) ⟨P, hP, hA'⟩ n

theorem GoodFb_z1c_rep : ∀ m : ℕ, GoodFb (Zw ([true, false] ++ List.replicate m true))
  | 0 => by simpa using GoodFb_z1c
  | (m + 1) => by
      have h := GoodFb_snocz (GoodFb_z1c_rep m)
      have e : [true, false] ++ List.replicate m true ++ [true]
          = [true, false] ++ List.replicate (m + 1) true := by
        rw [List.append_assoc, ← List.replicate_succ']
      rwa [e] at h

/-- ★★★★★ シート行357 `R351 (2,2,0)(3,3,1)(4,1,0)(3,3,1) = psi(W_w*W+W_w+psi_2(W_w*W+W_w))`。 -/
theorem R357_PkGA : PkGA 2 (R351 ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++ Zw [true, false, true] 2 2)) :=
  ⟨RunA 0, Iface_RunA0, 0, 1, R351, Zw [true, false, true] 2 2, rfl, R351_RunA0, rfl,
    (GoodFb_z1c_rep 1).pk 1⟩

theorem R357_mem : R351 ++ [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ),
    ((4, 1, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := (PkGA_Aok R357_PkGA).mem
  simpa [Zw, zcol] using h

/-- ★★★★★ シート行358 `R357 (3,3,0) = psi(W_w*W+W_w+W_3)`。 -/
theorem R358_mem : R351 ++ [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ),
    ((4, 1, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ), ((3, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hPU : PU 2 3 ((R351 ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++ Zw [true, false, true] 2 2)) ++
      ([((3, 3, 0) : ℕ × ℕ × ℕ)] ++ [])) :=
    ⟨PkGA, 2, _, [], Ifc3_toIfcV Ifc3_PkGA, rfl, R357_PkGA, rfl, JkU_nil' (le_refl 2) 2⟩
  have h := ((BaseOk_PU 2).aok _ _ hPU).mem
  simpa [Zw, zcol, List.append_assoc] using h

/-- ★★★★★ シート行359 `R351 (2,2,1) = psi(W_w*W+W_w*2)`。 -/
theorem R359_mem : R351 ++ [((2, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := ((GoodFb_z1c_rep 2).seg 0).reapp P0 BaseOk_zero 0 R338
    (LwB_of_base ⟨Aok_R338, rfl⟩)
  simpa [Zw, zcol, R351, R344, R341, List.append_assoc] using h

/-- ★★★★★ シート行360 `R359 (2,2,1) = psi(W_w*W+W_w*3)`。 -/
theorem R360_mem : R351 ++ [((2, 2, 1) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := ((GoodFb_z1c_rep 3).seg 0).reapp P0 BaseOk_zero 0 R338
    (LwB_of_base ⟨Aok_R338, rfl⟩)
  simpa [Zw, zcol, R351, R344, R341, List.append_assoc] using h

#print axioms R360_mem


/-! ### 行 361 -/

theorem R344_z_rep (n : ℕ) :
    R344 ++ (List.range n).flatMap (fun _ => [((2, 2, 1) : ℕ × ℕ × ℕ)])
      = R338 ++ (((0 + 1, 1, 0) : ℕ × ℕ × ℕ) :: Zw ([true, false] ++ List.replicate n true) 1 1) := by
  rw [flatMap_const_singleton]
  simp [R344, R341, Zw, zcol, List.append_assoc, List.map_append, List.map_replicate]

theorem R344_z_rep_mem (n : ℕ) :
    R344 ++ (List.range n).flatMap (fun _ => [((2, 2, 1) : ℕ × ℕ × ℕ)]) ∈ W 0 := by
  rw [R344_z_rep n]
  have h := ((GoodFb_z1c_rep n).seg 0).reapp P0 BaseOk_zero 0 R338 (LwB_of_base ⟨Aok_R338, rfl⟩)
  simpa using h

/-- ★★★★★ シート行361 `R344 (2,2,1)(3,0,0) = psi(W_w*W+W_w*w)`。 -/
theorem R361_mem : R344 ++ [((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := flat_mem'' (Y0 := R344) (M := [((2, 2, 1) : ℕ × ℕ × ℕ)]) (d := 3)
    (by simp) (by simp [entry]) (by intro r hr1 hrl; simp at hrl; omega)
    R344_z_rep_mem
  simpa using h

#print axioms R361_mem


/-! ### 複合字の語: 1 つの字 = z の列 + 1 の列 `k` 本 + 荷 `Y`（高さ `a+2`） -/

/-- 複合字。`p.1` = 1 の列の本数、`p.2` = 荷。 -/
def colC (a b : ℕ) (p : ℕ × TrioSeq) : TrioSeq :=
  ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ) ::
    (List.replicate p.1 ((a + 2, 1, 0) : ℕ × ℕ × ℕ) ++ shiftr01 (a + 2) 0 p.2)

def wordC (a b : ℕ) (ws : List (ℕ × TrioSeq)) : TrioSeq := ws.flatMap (colC a b)

/-- 荷はすべて `Bok`。 -/
def WplC (ws : List (ℕ × TrioSeq)) : Prop := ∀ p ∈ ws, Bok p.2

theorem WplC_nil : WplC [] := fun _ h => by simp at h

theorem WplC_append {ws1 ws2 : List (ℕ × TrioSeq)} (h1 : WplC ws1) (h2 : WplC ws2) :
    WplC (ws1 ++ ws2) := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact h1 p h
  · exact h2 p h

theorem WplC_of_append_left {ws1 ws2 : List (ℕ × TrioSeq)} (h : WplC (ws1 ++ ws2)) : WplC ws1 :=
  fun p hp => h p (List.mem_append_left _ hp)

theorem WplC_singleton {k : ℕ} {Y : TrioSeq} (hY : Bok Y) : WplC [(k, Y)] := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst hp; exact hY

theorem wordC_nil (a b : ℕ) : wordC a b [] = [] := rfl

theorem wordC_append (a b : ℕ) (ws1 ws2 : List (ℕ × TrioSeq)) :
    wordC a b (ws1 ++ ws2) = wordC a b ws1 ++ wordC a b ws2 := by simp [wordC]

theorem wordC_singleton (a b : ℕ) (p : ℕ × TrioSeq) : wordC a b [p] = colC a b p := by
  simp [wordC]

theorem wordC_cons (a b : ℕ) (p : ℕ × TrioSeq) (ws : List (ℕ × TrioSeq)) :
    wordC a b (p :: ws) = colC a b p ++ wordC a b ws := by simp [wordC]

theorem colC_shift (a b s : ℕ) (p : ℕ × TrioSeq) :
    shiftr01 s 0 (colC a b p) = colC (a + s) b p := by
  rw [colC, show ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ) ::
      (List.replicate p.1 ((a + 2, 1, 0) : ℕ × ℕ × ℕ) ++ shiftr01 (a + 2) 0 p.2)
      = [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] ++
        (List.replicate p.1 ((a + 2, 1, 0) : ℕ × ℕ × ℕ) ++ shiftr01 (a + 2) 0 p.2) from rfl,
    shiftr01_append0, shiftr01_append0, shift_zcol, shiftr01_add0,
    show a + 2 + s = a + s + 2 from by omega, show a + 1 + s = a + s + 1 from by omega]
  have hr : shiftr01 s 0 (List.replicate p.1 ((a + 2, 1, 0) : ℕ × ℕ × ℕ))
      = List.replicate p.1 ((a + s + 2, 1, 0) : ℕ × ℕ × ℕ) := by
    simp [shiftr01, List.map_replicate]
    omega
  rw [hr]
  rfl

theorem wordC_shift (a b s : ℕ) (ws : List (ℕ × TrioSeq)) :
    shiftr01 s 0 (wordC a b ws) = wordC (a + s) b ws := by
  induction ws with
  | nil => simp [wordC, shiftr01]
  | cons p ws ih => rw [wordC_cons, wordC_cons, shiftr01_append0, colC_shift, ih]

theorem colC_ge (a b : ℕ) (p : ℕ × TrioSeq) : ∀ x ∈ colC a b p, a + 1 ≤ x.1 := by
  intro x hx
  simp only [colC, List.mem_cons, List.mem_append, List.mem_replicate, shiftr01,
    List.mem_map] at hx
  rcases hx with rfl | ⟨-, rfl⟩ | ⟨q, -, rfl⟩
  · exact le_refl _
  · show a + 1 ≤ a + 2; omega
  · show a + 1 ≤ q.1 + (a + 2); omega

theorem wordC_ge (a b : ℕ) (ws : List (ℕ × TrioSeq)) : ∀ x ∈ wordC a b ws, a + 1 ≤ x.1 := by
  intro x hx
  simp only [wordC, List.mem_flatMap] at hx
  obtain ⟨p, -, hx⟩ := hx
  exact colC_ge a b p x hx

theorem colC_mono {a b : ℕ} {p : ℕ × TrioSeq} (hp : Mono p.2) : Mono (colC a b p) := by
  intro x hx
  simp only [colC, List.mem_cons, List.mem_append, List.mem_replicate, shiftr01,
    List.mem_map] at hx
  rcases hx with rfl | ⟨-, rfl⟩ | ⟨q, hq, rfl⟩
  · show 1 ≤ b + 1; omega
  · show (0 : ℕ) ≤ 1; omega
  · simpa using hp q hq

theorem wordC_mono {a b : ℕ} {ws : List (ℕ × TrioSeq)} (hw : WplC ws) : Mono (wordC a b ws) := by
  intro x hx
  simp only [wordC, List.mem_flatMap] at hx
  obtain ⟨p, hp, hx⟩ := hx
  exact colC_mono (hw p hp).mono x hx

theorem MidD_wordC (a v : ℕ) (ha : 1 ≤ a) (hv : 1 ≤ v) {ws : List (ℕ × TrioSeq)}
    (hw : WplC ws) : MidD (a + 1) (((a, v, 0) : ℕ × ℕ × ℕ) :: wordC a v ws) := by
  have h := MidD_append (MidD_col a v ha hv) (N := wordC a v ws) (wordC_ge a v ws) (wordC_mono hw)
  simpa using h

theorem colC_length (a b : ℕ) (p : ℕ × TrioSeq) : (colC a b p).length = p.1 + p.2.length + 1 := by
  simp [colC, shiftr01]

theorem colC_ne (a b : ℕ) (p : ℕ × TrioSeq) : colC a b p ≠ [] := by simp [colC]

#print axioms wordC_shift


/-! ### 複合字の語の上の z の列の展開 -/

def MzC (Y0 : TrioSeq) (a b : ℕ) (ws : List (ℕ × TrioSeq)) : TrioSeq :=
  Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordC a b ws ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)])

theorem entry_colC_zero (a b : ℕ) (p : ℕ × TrioSeq) (r : ℕ) :
    entry (colC a b p) r 0 = entry [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] r 0 := by
  simp [colC, entry]

theorem entry_colC_one (a b : ℕ) (p : ℕ × TrioSeq) (r t : ℕ) (ht : t < p.1) :
    entry (colC a b p) r (t + 1) = entry [((a + 2, 1, 0) : ℕ × ℕ × ℕ)] r 0 := by
  simp only [colC, entry, List.getD_cons_succ]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simpa using ht), List.getElem?_replicate]
  simp [ht]

theorem entry_colC_pay (a b : ℕ) (p : ℕ × TrioSeq) (r t : ℕ) (ht : t < p.2.length) :
    entry (colC a b p) r (p.1 + t + 1) = entry (shiftr01 (a + 2) 0 p.2) r t := by
  simp only [colC, entry, List.getD_cons_succ]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp), List.length_replicate]
  simp

theorem entry_MzC_p (Y0 : TrioSeq) (a b : ℕ) (ws : List (ℕ × TrioSeq)) (r : ℕ) :
    entry (MzC Y0 a b ws) r Y0.length = entry [((a, b, 0) : ℕ × ℕ × ℕ)] r 0 := by
  rw [MzC, show Y0.length = Y0.length + 0 from rfl, entry_append_right]
  simp [entry]

theorem entry_MzC_word (Y0 : TrioSeq) (a b : ℕ) (ws : List (ℕ × TrioSeq)) (r i : ℕ)
    (hi : i < (wordC a b ws).length) :
    entry (MzC Y0 a b ws) r (Y0.length + 1 + i) = entry (wordC a b ws) r i := by
  have e : MzC Y0 a b ws = (Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)]) ++
      (wordC a b ws ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]) := by
    simp [MzC]
  rw [e, show Y0.length + 1 + i = (Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)]).length + i from by
      simp only [List.length_append, List.length_singleton],
    entry_append_right, entry_append_left hi]

theorem entry_wordC_pos (Y0 : TrioSeq) (a b : ℕ) (ws1 ws3 : List (ℕ × TrioSeq))
    (p : ℕ × TrioSeq) (r t : ℕ) (ht : t < (colC a b p).length) :
    entry (MzC Y0 a b (ws1 ++ p :: ws3)) r (Y0.length + 1 + (wordC a b ws1).length + t)
      = entry (colC a b p) r t := by
  have e : MzC Y0 a b (ws1 ++ p :: ws3)
      = (Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)] ++ wordC a b ws1) ++
        (colC a b p ++ (wordC a b ws3 ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)])) := by
    simp [MzC, wordC_append, wordC_cons, List.append_assoc]
  rw [e, show Y0.length + 1 + (wordC a b ws1).length + t
      = (Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)] ++ wordC a b ws1).length + t from by
        simp only [List.length_append, List.length_singleton],
    entry_append_right, entry_append_left ht]

theorem entry_wordC_ge (a b : ℕ) (ws : List (ℕ × TrioSeq)) {i : ℕ}
    (hi : i < (wordC a b ws).length) : a + 1 ≤ entry (wordC a b ws) 0 i := by
  have := wordC_ge a b ws _ (List.getElem_mem hi)
  have he : entry (wordC a b ws) 0 i = ((wordC a b ws)[i]).1 := by
    simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  omega

/-- 字の先頭（z の列）は記録の行 1 の子。 -/
theorem le1_zposC (Y0 : TrioSeq) (a b : ℕ) (ws1 ws3 : List (ℕ × TrioSeq)) (p : ℕ × TrioSeq) :
    le1 (MzC Y0 a b (ws1 ++ p :: ws3)) Y0.length
      (Y0.length + 1 + (wordC a b ws1).length) := by
  set M := MzC Y0 a b (ws1 ++ p :: ws3) with hM
  set q := Y0.length + 1 + (wordC a b ws1).length with hq
  have hlenw : (wordC a b (ws1 ++ p :: ws3)).length
      = (wordC a b ws1).length + (colC a b p).length + (wordC a b ws3).length := by
    rw [wordC_append, wordC_cons, List.length_append, List.length_append]
    omega
  have hlen : M.length = Y0.length + 1 + (wordC a b (ws1 ++ p :: ws3)).length + 1 := by
    simp [hM, MzC]
    omega
  have hcl : 0 < (colC a b p).length := by rw [colC_length]; omega
  have hql : q < M.length := by omega
  have e0p : entry M 0 Y0.length = a := by rw [hM, entry_MzC_p]; simp [entry]
  have e1p : entry M 1 Y0.length = b := by rw [hM, entry_MzC_p]; simp [entry]
  have eq0 : entry M 0 q = a + 1 := by
    have h := entry_wordC_pos Y0 a b ws1 ws3 p 0 0 hcl
    rw [entry_colC_zero] at h
    simp only [Nat.add_zero] at h
    rw [hM, hq, h]; simp [entry]
  have eq1 : entry M 1 q = b + 1 := by
    have h := entry_wordC_pos Y0 a b ws1 ws3 p 1 0 hcl
    rw [entry_colC_zero] at h
    simp only [Nat.add_zero] at h
    rw [hM, hq, h]; simp [entry]
  have hge : ∀ j', Y0.length < j' → j' ≤ q → a + 1 ≤ entry M 0 j' := by
    intro j' h1 h2
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < (wordC a b (ws1 ++ p :: ws3)).length ∧ j' = Y0.length + 1 + i :=
      ⟨j' - (Y0.length + 1), by omega, by omega⟩
    rw [hM, entry_MzC_word Y0 a b _ 0 i hi]
    exact entry_wordC_ge a b _ hi
  have hl0 : le0 M Y0.length q := le0_of_between e0p q (by omega) hql hge
  refine ⟨by omega, hql, Relation.ReflTransGen.single ?_⟩
  refine ⟨by omega, hql, by omega, by rw [e1p, eq1]; omega, hl0, ?_⟩
  intro j hj
  have := le0_eq_of_min hj.1 hj.2 eq0 (fun j'' h1 h2 => hge j'' h1 (by omega))
  subst this; exact le_rfl

/-- 1 の列は行 1 が 1 なので、記録（行 1 = b ≥ 1）の行 1 の子孫ではない。 -/
theorem not_le1_oneC (Y0 : TrioSeq) (a b : ℕ) (hb : 1 ≤ b) (ws1 ws3 : List (ℕ × TrioSeq))
    (p : ℕ × TrioSeq) (t : ℕ) (ht : t < p.1) :
    ¬ le1 (MzC Y0 a b (ws1 ++ p :: ws3)) Y0.length
      (Y0.length + 1 + (wordC a b ws1).length + (t + 1)) := by
  intro hc
  set M := MzC Y0 a b (ws1 ++ p :: ws3) with hM
  have e1p : entry M 1 Y0.length = b := by rw [hM, entry_MzC_p]; simp [entry]
  have e1 : entry M 1 (Y0.length + 1 + (wordC a b ws1).length + (t + 1)) = 1 := by
    have h := entry_wordC_pos Y0 a b ws1 ws3 p 1 (t + 1) (by rw [colC_length]; omega)
    rw [entry_colC_one a b p 1 t ht] at h
    rw [hM, h]; simp [entry]
  have := le1_row1_lt hc (by omega)
  rw [e1p, e1] at this
  omega

/-- 荷の列は記録の行 1 の子孫ではない（荷の根は行 1 が 0）。 -/
theorem not_le1_payC (Y0 : TrioSeq) (a b : ℕ) (ws1 ws3 : List (ℕ × TrioSeq))
    {p : ℕ × TrioSeq} (hp : Bok p.2) (t : ℕ) (ht : t < p.2.length) :
    ¬ le1 (MzC Y0 a b (ws1 ++ p :: ws3)) Y0.length
      (Y0.length + 1 + (wordC a b ws1).length + (p.1 + t + 1)) := by
  set M := MzC Y0 a b (ws1 ++ p :: ws3) with hM
  set q := Y0.length + 1 + (wordC a b ws1).length with hq
  have hlenw : (wordC a b (ws1 ++ p :: ws3)).length
      = (wordC a b ws1).length + (colC a b p).length + (wordC a b ws3).length := by
    rw [wordC_append, wordC_cons, List.length_append, List.length_append]
    omega
  have hlen : M.length = Y0.length + 1 + (wordC a b (ws1 ++ p :: ws3)).length + 1 := by
    simp [hM, MzC]
    omega
  have hcl : (colC a b p).length = p.1 + p.2.length + 1 := colC_length a b p
  have hY0 : 0 < p.2.length := by omega
  -- 荷のブロックは [q + p.1 + 1, q + p.1 + 1 + |Y|)
  have eblk : ∀ r u, u < p.2.length →
      entry M r (q + p.1 + 1 + u) = entry (shiftr01 (a + 2) 0 p.2) r u := by
    intro r u hu
    have h := entry_wordC_pos Y0 a b ws1 ws3 p r (p.1 + u + 1) (by omega)
    rw [entry_colC_pay a b p r u hu] at h
    rw [hM, hq, show Y0.length + 1 + (wordC a b ws1).length + p.1 + 1 + u
      = Y0.length + 1 + (wordC a b ws1).length + (p.1 + u + 1) from by omega]
    exact h
  have hroot := block_root (M := M) (s := q + p.1 + 1) (e := q + p.1 + 1 + p.2.length)
    (d := a + 2) (by omega)
    (by rw [show q + p.1 + 1 = q + p.1 + 1 + 0 from rfl, eblk 0 0 hY0, entry0_shiftr01 hY0,
        hp.root]; omega)
    (by intro j hj1 hj2
        obtain ⟨u, hu, rfl⟩ : ∃ u, u < p.2.length ∧ j = q + p.1 + 1 + u :=
          ⟨j - (q + p.1 + 1), by omega, by omega⟩
        rw [eblk 0 u hu, entry0_shiftr01 hu]; omega)
    (by intro j hj1 hj2 hd
        obtain ⟨u, hu, rfl⟩ : ∃ u, u < p.2.length ∧ j = q + p.1 + 1 + u :=
          ⟨j - (q + p.1 + 1), by omega, by omega⟩
        rw [eblk 0 u hu, entry0_shiftr01 hu] at hd
        rw [eblk 1 u hu, entry1_shiftr01]
        exact (Zroot_entry hp.zroot (by omega)).1)
  intro hle
  have hx := le1_lower_bound hroot Y0.length (q + p.1 + 1 + t) (by
    have : q + (p.1 + t + 1) = q + p.1 + 1 + t := by omega
    rwa [this] at hle) (by omega) (by omega)
  omega

#print axioms not_le1_payC


/-! ### 複合字の語の上昇と展開 -/

theorem getElem?_colC_zero (a b : ℕ) (p : ℕ × TrioSeq) :
    (colC a b p)[0]? = some ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ) := by simp [colC]

theorem getElem?_colC_one (a b : ℕ) (p : ℕ × TrioSeq) (u : ℕ) (hu : u < p.1) :
    (colC a b p)[u + 1]? = some ((a + 2, 1, 0) : ℕ × ℕ × ℕ) := by
  simp [colC, List.getElem?_append_left, List.getElem?_replicate, hu]

theorem getElem?_colC_pay (a b : ℕ) (p : ℕ × TrioSeq) (u : ℕ) (hu : u < p.2.length) :
    (colC a b p)[p.1 + u + 1]? = some ((((p.2[u]'hu).1 + (a + 2), (p.2[u]'hu).2.1,
      (p.2[u]'hu).2.2)) : ℕ × ℕ × ℕ) := by
  simp [colC, List.getElem?_append_right, shiftr01, List.getElem?_map,
    List.getElem?_eq_getElem hu]

theorem rise_colC (a b k : ℕ) (p : ℕ × TrioSeq) (P : ℕ → Prop) [DecidablePred P]
    (hP0 : P 0) (hP : ∀ t, 1 ≤ t → t < (colC a b p).length → ¬ P t) :
    (List.range (colC a b p).length).map (fun t =>
      ((entry (colC a b p) 0 t + k, entry (colC a b p) 1 t + (if P t then k else 0),
        entry (colC a b p) 2 t) : ℕ × ℕ × ℕ)) = colC (a + k) (b + k) p := by
  have hlenk : (colC (a + k) (b + k) p).length = (colC a b p).length := by
    rw [colC_length, colC_length]
  have hlen := colC_length a b p
  apply List.ext_getElem?
  intro i
  rcases Nat.lt_or_ge i (colC a b p).length with hi | hi
  · rw [List.getElem?_map, List.getElem?_range hi]
    simp only [Option.map_some]
    match i, hi with
    | 0, _ =>
        rw [getElem?_colC_zero, entry_colC_zero, entry_colC_zero, entry_colC_zero, if_pos hP0]
        simp [entry]
        omega
    | (u + 1), hu =>
        rw [if_neg (hP (u + 1) (by omega) hu)]
        rcases Nat.lt_or_ge u p.1 with hlt | hge
        · rw [entry_colC_one a b p 0 u hlt, entry_colC_one a b p 1 u hlt,
            entry_colC_one a b p 2 u hlt, getElem?_colC_one (a + k) (b + k) p u hlt]
          simp [entry]
          omega
        · obtain ⟨u', rfl⟩ : ∃ u', u = p.1 + u' := ⟨u - p.1, by omega⟩
          have hu' : u' < p.2.length := by omega
          rw [show p.1 + u' + 1 = p.1 + u' + 1 from rfl,
            entry_colC_pay a b p 0 u' hu', entry_colC_pay a b p 1 u' hu',
            entry_colC_pay a b p 2 u' hu', getElem?_colC_pay (a + k) (b + k) p u' hu']
          simp [shiftr01, entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu']
          omega
  · rw [List.getElem?_eq_none (by simpa using hi), List.getElem?_eq_none (by omega)]

open Classical in
theorem rise_wordC (Y0 : TrioSeq) (a b k : ℕ) (hb : 1 ≤ b) {ws : List (ℕ × TrioSeq)}
    (hw : WplC ws) :
    ∀ (ws2 ws1 ws3 : List (ℕ × TrioSeq)), ws = ws1 ++ ws2 ++ ws3 →
      (List.range (wordC a b ws2).length).map (fun i =>
        ((entry (wordC a b ws2) 0 i + k, entry (wordC a b ws2) 1 i +
          (if le1 (MzC Y0 a b ws) Y0.length (Y0.length + 1 + (wordC a b ws1).length + i)
            then k else 0), entry (wordC a b ws2) 2 i) : ℕ × ℕ × ℕ))
      = wordC (a + k) (b + k) ws2
  | [], _, _, _ => by simp [wordC]
  | (p :: ws2), ws1, ws3, hws => by
      have hws' : ws = (ws1 ++ [p]) ++ ws2 ++ ws3 := by rw [hws]; simp
      have hws'' : ws = ws1 ++ p :: (ws2 ++ ws3) := by rw [hws]; simp
      have hp : Bok p.2 := hw p (by rw [hws]; simp)
      have ih := rise_wordC Y0 a b k hb hw ws2 (ws1 ++ [p]) ws3 hws'
      rw [wordC_cons, wordC_cons, List.length_append, List.range_add, List.map_append,
        List.map_map]
      congr 1
      · rw [← rise_colC a b k p (fun t => le1 (MzC Y0 a b ws) Y0.length
            (Y0.length + 1 + (wordC a b ws1).length + t))
            (by rw [hws'']; simpa using le1_zposC Y0 a b ws1 (ws2 ++ ws3) p)
            (by intro t ht1 ht
                rcases Nat.lt_or_ge (t - 1) p.1 with hlt | hge
                · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
                  rw [hws'']
                  exact not_le1_oneC Y0 a b hb ws1 (ws2 ++ ws3) p u (by omega)
                · obtain ⟨u, rfl⟩ : ∃ u, t = p.1 + u + 1 := ⟨t - 1 - p.1, by omega⟩
                  rw [hws'']
                  refine not_le1_payC Y0 a b ws1 (ws2 ++ ws3) hp u ?_
                  rw [colC_length] at ht; omega)]
        apply List.map_congr_left
        intro t ht
        rw [List.mem_range] at ht
        rw [entry_append_left ht, entry_append_left ht, entry_append_left ht]
      · rw [← ih]
        apply List.map_congr_left
        intro i hi
        simp only [Function.comp]
        rw [entry_append_right, entry_append_right, entry_append_right, wordC_append,
          wordC_singleton, List.length_append,
          show Y0.length + 1 + (wordC a b ws1).length + ((colC a b p).length + i)
            = Y0.length + 1 + ((wordC a b ws1).length + (colC a b p).length) + i from by omega]

open Classical in
/-- ★ 複合字の語の上の z の列の展開: 記録と語の対角の塔。 -/
theorem oper_z1wC (Y0 : TrioSeq) (a b : ℕ) (hb : 1 ≤ b) {ws : List (ℕ × TrioSeq)}
    (hw : WplC ws) (n : ℕ) :
    (Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordC a b ws ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]))⟦n⟧
      = Y0 ++ Dzf (fun a b => wordC a b ws) a b n := by
  rw [oper_z1_mask Y0 a b (wordC a b ws) (wordC_ge a b ws) n]
  congr 1
  apply List.flatMap_congr
  intro k _
  congr 1
  have := rise_wordC Y0 a b k hb hw ws [] [] (by simp)
  simpa [wordC, MzC] using this

theorem z1wC_mem {Y0 : TrioSeq} {a b : ℕ} (hb : 1 ≤ b) {ws : List (ℕ × TrioSeq)}
    (hw : WplC ws) (htw : ∀ n, Y0 ++ Dzf (fun a b => wordC a b ws) a b n ∈ W 0) :
    Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordC a b ws ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]) ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_z1wC Y0 a b hb hw]
  exact htw n

#print axioms z1wC_mem


/-! ### 複合字の語の普遍性の骨組み -/

theorem GoodFb_of_keyC {ws : List (ℕ × TrioSeq)} (hw : WplC ws)
    {new : ℕ → List (ℕ × TrioSeq)}
    (hnew : ∀ n, 1 ≤ n → GoodFb (fun a b => wordC a b (new n)))
    (key : ∀ (Z : TrioSeq) (a b : ℕ), 1 ≤ b →
      (∀ n, 1 ≤ n → Z ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordC a b (new n)) ∈ W 0) →
      Z ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordC a b ws) ∈ W 0) :
    GoodFb (fun a b => wordC a b ws) where
  ge := fun a b => wordC_ge a b ws
  mono := fun a b => wordC_mono hw
  shift := fun a b s => wordC_shift a b s ws
  pu := by
    intro y c hy
    refine ⟨fun x hx => by have := wordC_ge (c + 1) (y + 1) ws x hx; omega, wordC_mono hw, ?_⟩
    intro E hE t Z hZ
    rw [wordC_shift]
    have h := key Z (c + 1 + t) (y + 1) (by omega) (fun n hn => by
      have hP : PU y (c + 1 + t) (Z ++ ([((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)] ++
          wordC (c + 1 + t) (y + 1) (new n))) :=
        ⟨E, c + t, Z, _, hE, by omega, hZ, by rw [show c + t + 1 = c + 1 + t from by omega],
          (hnew n hn).pu y (c + t) hy⟩
      simpa using ((BaseOk_PU y).aok _ _ hP).mem)
    simpa using h
  pk := by
    intro c E hI
    refine ⟨fun x hx => by have := wordC_ge (c + 1) 2 ws x hx; omega, wordC_mono hw, ?_⟩
    intro j t X hX
    rw [wordC_shift]
    have h := key X (c + 1 + t) 2 (by omega) (fun n hn => by
      have hP : PkGA (c + 1 + t) (X ++ ([((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ)] ++
          wordC (c + 1 + t) 2 (new n))) :=
        ⟨E, hI, j, c + t, X, _, by omega, hX, by rw [show c + t + 1 = c + 1 + t from by omega],
          (hnew n hn).pk (c + t)⟩
      simpa using (PkGA_Aok hP).mem)
    simpa using h
  seg := by
    intro h
    have hmid : MidD (h + 2) (((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordC (h + 1) 1 ws) := by
      have h1 := MidD_wordC (h + 1) 1 (by omega) (by omega) hw
      simpa [show h + 1 + 1 = h + 2 from by omega] using h1
    refine ⟨hmid, by simp [entry], ?_⟩
    intro P hP s A' hA'
    rw [show ((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordC (h + 1) 1 ws
        = [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ wordC (h + 1) 1 ws from rfl,
      shiftr01_append0, shift_col, wordC_shift]
    have hk := key A' (h + 1 + s) 1 (by omega) (fun n hn => by
      have hR : RunA 0 (h + s + 1) (A' ++ (((h + s + 1, 1, 0) : ℕ × ℕ × ℕ) ::
          wordC (h + s + 1) 1 (new n))) :=
        ⟨h + s, A', _, rfl, rfl, ⟨P, hP, hA'⟩, (hnew n hn).seg (h + s)⟩
      have := ((BaseOk_RunA 0).aok _ _ hR).mem
      simpa [show h + s + 1 = h + 1 + s from by omega] using this)
    simpa using hk

/-- 語の列は「z の列」「1 の列」「高さ `a+2` 以上」のどれか。 -/
theorem wordC_kind (a b : ℕ) (ws : List (ℕ × TrioSeq)) :
    ∀ x ∈ wordC a b ws, x = ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ) ∨
      x = ((a + 2, 1, 0) : ℕ × ℕ × ℕ) ∨ a + 2 ≤ x.1 := by
  intro x hx
  simp only [wordC, List.mem_flatMap] at hx
  obtain ⟨p, -, hxp⟩ := hx
  simp only [colC, List.mem_cons, List.mem_append, List.mem_replicate, shiftr01,
    List.mem_map] at hxp
  rcases hxp with h1 | ⟨-, h1⟩ | ⟨q, -, h1⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · refine Or.inr (Or.inr ?_)
    rw [← h1]
    simp

/-- 台座と記録と語の祖先条件。 -/
theorem Ancd_recword {a b : ℕ} (hb : 1 ≤ b) {Z : TrioSeq} (hZ : Ancd a Z)
    {ws : List (ℕ × TrioSeq)} (hw : WplC ws) :
    Ancd (a + 2) (Z ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordC a b ws)) := by
  set N : TrioSeq := ((a, b, 0) : ℕ × ℕ × ℕ) :: wordC a b ws with hN
  intro j hj0 hjl hlt hvis
  rcases Nat.lt_or_ge j Z.length with hjZ | hjZ
  · have e0 : entry (Z ++ N) 0 j = entry Z 0 j := entry_append_left hjZ
    have e1 : entry (Z ++ N) 1 j = entry Z 1 j := entry_append_left hjZ
    have hNl : Z.length < (Z ++ N).length := by simp [hN]
    have hlt1 : entry Z 0 j < a := by
      have h1 := hvis Z.length hjZ hNl
      have h2 : entry (Z ++ N) 0 Z.length = a := by
        rw [show Z.length = Z.length + 0 from rfl, entry_append_right]
        simp [hN, entry]
      rw [e0] at h1
      omega
    rw [e1]
    refine hZ j hj0 hjZ hlt1 ?_
    intro i hi hil
    have := hvis i hi (by simp [hN]; omega)
    rwa [e0, entry_append_left hil] at this
  · obtain ⟨u, hu, rfl⟩ : ∃ u, u < N.length ∧ j = Z.length + u :=
      ⟨j - Z.length, by simp [hN] at hjl ⊢; omega, by omega⟩
    rw [entry_append_right]
    match u, hu with
    | 0, _ => simpa [hN, entry] using hb
    | (i + 1), hi =>
        have hil : i < (wordC a b ws).length := by simp [hN] at hi; omega
        have he : entry N 0 (i + 1) = entry (wordC a b ws) 0 i := by simp [hN, entry]
        have he1 : entry N 1 (i + 1) = entry (wordC a b ws) 1 i := by simp [hN, entry]
        have hlt' : entry (wordC a b ws) 0 i < a + 2 := by
          have h := hlt
          rw [entry_append_right, he] at h
          exact h
        have he0v : entry (wordC a b ws) 0 i = ((wordC a b ws)[i]'hil).1 := by
          simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil]
        have he1v : entry (wordC a b ws) 1 i = ((wordC a b ws)[i]'hil).2.1 := by
          simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil]
        rw [he0v] at hlt'
        rcases wordC_kind a b ws _ (List.getElem_mem hil) with h1 | h1 | h1
        · rw [he1, he1v, h1]; simp
        · rw [he1, he1v, h1]
        · exact absurd hlt' (by omega)

#print axioms Ancd_recword


/-! ### 字を 1 つ継ぐ: 裸の z（場合 iv）と 1 の列（場合 iii） -/

theorem colC_z (a b : ℕ) : colC a b (0, []) = [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] := by
  simp [colC, shiftr01]

theorem colC_one_succ (a b k : ℕ) :
    colC a b (k + 1, []) = colC a b (k, []) ++ [((a + 2, 1, 0) : ℕ × ℕ × ℕ)] := by
  simp [colC, shiftr01, List.replicate_succ']

theorem colC_pay (a b k : ℕ) (B : TrioSeq) :
    colC a b (k, B) = colC a b (k, []) ++ shiftr01 (a + 2) 0 B := by
  simp [colC, shiftr01, List.append_assoc]

theorem colC_snoc_zero (a b k : ℕ) (Y : TrioSeq) :
    colC a b (k, Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])
      = colC a b (k, Y) ++ [((a + 2, 0, 0) : ℕ × ℕ × ℕ)] := by
  simp [colC, shiftr01, List.append_assoc]

theorem wordC_replicate (a b : ℕ) (p : ℕ × TrioSeq) : ∀ n : ℕ,
    wordC a b (List.replicate n p) = (List.range n).flatMap fun _ => colC a b p
  | 0 => by simp [wordC]
  | (n + 1) => by
      rw [List.replicate_succ, wordC_cons, wordC_replicate a b p n,
        List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]

/-- 場合 (iv): 裸の z を継ぐ。 -/
theorem GoodFb_snoczC {ws : List (ℕ × TrioSeq)} (hw : WplC ws)
    (hG : GoodFb (fun a b => wordC a b ws)) :
    GoodFb (fun a b => wordC a b (ws ++ [(0, [])])) where
  ge := fun a b => wordC_ge a b _
  mono := fun a b => wordC_mono (WplC_append hw (WplC_singleton Bok_nil))
  shift := fun a b s => wordC_shift a b s _
  pu := by
    intro y c hy
    refine ⟨fun x hx => by have := wordC_ge (c + 1) (y + 1) _ x hx; omega,
      wordC_mono (WplC_append hw (WplC_singleton Bok_nil)), ?_⟩
    intro E hE t Z hZ
    rw [wordC_shift, wordC_append, wordC_singleton, colC_z]
    have h := z1wC_mem (Y0 := Z) (a := c + 1 + t) (b := y + 1) (by omega) hw
      (fun n => by
        have := Dzf_W hG hy hE (c := c + t) (by simpa using hZ) n
        simpa [show c + t + 1 = c + 1 + t from by omega] using this)
    simpa [List.append_assoc] using h
  pk := by
    intro c E hI
    refine ⟨fun x hx => by have := wordC_ge (c + 1) 2 _ x hx; omega,
      wordC_mono (WplC_append hw (WplC_singleton Bok_nil)), ?_⟩
    intro j t X hX
    rw [wordC_shift, wordC_append, wordC_singleton, colC_z]
    have h := z1wC_mem (Y0 := X) (a := c + 1 + t) (b := 2) (by omega) hw
      (fun n => by
        have := Dzf_W_RunG hG hI (c := c + t) hX n
        simpa [show c + t + 1 = c + 1 + t from by omega] using this)
    simpa [List.append_assoc] using h
  seg := by
    intro h
    have hmid : MidD (h + 2) (((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordC (h + 1) 1 (ws ++ [(0, [])])) := by
      have h1 := MidD_wordC (h + 1) 1 (by omega) (by omega)
        (ws := ws ++ [((0 : ℕ), ([] : TrioSeq))])
        (WplC_append hw (WplC_singleton (k := 0) Bok_nil))
      simpa [show h + 1 + 1 = h + 2 from by omega] using h1
    refine ⟨hmid, by simp [entry], ?_⟩
    intro P hP s A' hA'
    rw [show ((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordC (h + 1) 1 (ws ++ [(0, [])])
        = [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ wordC (h + 1) 1 (ws ++ [(0, [])]) from rfl,
      shiftr01_append0, shift_col, wordC_shift, wordC_append, wordC_singleton, colC_z]
    have hz := z1wC_mem (Y0 := A') (a := h + 1 + s) (b := 1) (by omega) hw
      (fun n => by
        have := Dzf_W_LwA hG (h := h + s) ⟨P, hP, hA'⟩ n
        simpa [show h + s + 1 = h + 1 + s from by omega] using this)
    simpa [List.append_assoc] using hz

#print axioms GoodFb_snoczC


/-! ### 場合 (iii): 1 の列を継ぐ（snocd_gen、hang は荷つきの字） -/

theorem wordC_snoc_one (a b : ℕ) (ws : List (ℕ × TrioSeq)) (k : ℕ) :
    wordC a b (ws ++ [(k + 1, [])])
      = wordC a b (ws ++ [(k, [])]) ++ [((a + 2, 1, 0) : ℕ × ℕ × ℕ)] := by
  rw [wordC_append, wordC_append, wordC_singleton, wordC_singleton, colC_one_succ,
    List.append_assoc]

theorem wordC_snoc_pay (a b : ℕ) (ws : List (ℕ × TrioSeq)) (k : ℕ) (B : TrioSeq) :
    wordC a b (ws ++ [(k, B)])
      = wordC a b (ws ++ [(k, [])]) ++ shiftr01 (a + 2) 0 B := by
  rw [wordC_append, wordC_append, wordC_singleton, wordC_singleton, colC_pay,
    List.append_assoc]

/-- 場合 (iii): `1` の列を継ぐ。 -/
theorem GoodFb_snoc_oneC {ws : List (ℕ × TrioSeq)} (hw : WplC ws) (k : ℕ)
    (hprev : ∀ B : TrioSeq, Bok B → GoodFb (fun a b => wordC a b (ws ++ [(k, B)]))) :
    GoodFb (fun a b => wordC a b (ws ++ [(k + 1, [])])) where
  ge := fun a b => wordC_ge a b _
  mono := fun a b => wordC_mono (WplC_append hw (WplC_singleton (k := k + 1) Bok_nil))
  shift := fun a b s => wordC_shift a b s _
  pu := by
    intro y c hy
    refine ⟨fun x hx => by have := wordC_ge (c + 1) (y + 1) _ x hx; omega,
      wordC_mono (WplC_append hw (WplC_singleton (k := k + 1) Bok_nil)), ?_⟩
    intro E hE t Z hZ
    rw [wordC_shift, wordC_snoc_one]
    set a := c + 1 + t with ha
    have hbase : PU y a (Z ++ ([((a, y + 1, 0) : ℕ × ℕ × ℕ)] ++
        wordC a (y + 1) (ws ++ [(k, [])]))) :=
      ⟨E, c + t, Z, _, hE, by omega, hZ, by rw [ha, show c + t + 1 = c + 1 + t from by omega],
        (hprev [] Bok_nil).pu y (c + t) hy⟩
    have hAok := (BaseOk_PU y).aok _ _ hbase
    have hancZ : Ancd a Z := by
      have := (IfcV_iface (y + 1) hE).bok.ancd (c + t) Z hZ
      rwa [show c + t + 1 = a from by omega] at this
    have hanc : Ancd (a + 2) (Z ++ (((a, y + 1, 0) : ℕ × ℕ × ℕ) ::
        wordC a (y + 1) (ws ++ [(k, [])]))) :=
      Ancd_recword (by omega) hancZ (WplC_append hw (WplC_singleton (k := k) Bok_nil))
    have h := snocd_gen (Y := Z ++ (((a, y + 1, 0) : ℕ × ℕ × ℕ) ::
        wordC a (y + 1) (ws ++ [(k, [])]))) (d := a + 2) (by omega)
      (by simpa using hAok) hanc ?_
    · simpa [List.append_assoc] using h
    · intro B hB
      have h2 := (hprev B hB).pu y c hy
      have h3 := h2.2.2 E hE t Z hZ
      rw [wordC_shift, wordC_snoc_pay] at h3
      simpa [ha, List.append_assoc] using h3
  pk := by
    intro c E hI
    refine ⟨fun x hx => by have := wordC_ge (c + 1) 2 _ x hx; omega,
      wordC_mono (WplC_append hw (WplC_singleton (k := k + 1) Bok_nil)), ?_⟩
    intro j t X hX
    rw [wordC_shift, wordC_snoc_one]
    set a := c + 1 + t with ha
    have hbase : PkGA a (X ++ ([((a, 2, 0) : ℕ × ℕ × ℕ)] ++ wordC a 2 (ws ++ [(k, [])]))) :=
      ⟨E, hI, j, c + t, X, _, by omega, hX,
        by rw [ha, show c + t + 1 = c + 1 + t from by omega],
        (hprev [] Bok_nil).pk (c + t)⟩
    have hAok := PkGA_Aok hbase
    have hancX : Ancd a X := by
      have := (BaseOk_RunG hI.bok j).ancd (c + t) X hX
      rwa [show c + t + 1 = a from by omega] at this
    have hanc : Ancd (a + 2) (X ++ (((a, 2, 0) : ℕ × ℕ × ℕ) :: wordC a 2 (ws ++ [(k, [])]))) :=
      Ancd_recword (by omega) hancX (WplC_append hw (WplC_singleton (k := k) Bok_nil))
    have h := snocd_gen (Y := X ++ (((a, 2, 0) : ℕ × ℕ × ℕ) :: wordC a 2 (ws ++ [(k, [])])))
      (d := a + 2) (by omega) (by simpa using hAok) hanc ?_
    · simpa [List.append_assoc] using h
    · intro B hB
      have h2 := (hprev B hB).pk c E hI
      have h3 := h2.2.2 j t X hX
      rw [wordC_shift, wordC_snoc_pay] at h3
      simpa [ha, List.append_assoc] using h3
  seg := by
    intro h
    have hmid : MidD (h + 2) (((h + 1, 1, 0) : ℕ × ℕ × ℕ) ::
        wordC (h + 1) 1 (ws ++ [(k + 1, [])])) := by
      have h1 := MidD_wordC (h + 1) 1 (by omega) (by omega)
        (ws := ws ++ [((k + 1 : ℕ), ([] : TrioSeq))])
        (WplC_append hw (WplC_singleton (k := k + 1) Bok_nil))
      simpa [show h + 1 + 1 = h + 2 from by omega] using h1
    refine ⟨hmid, by simp [entry], ?_⟩
    intro P hP s A' hA'
    rw [show ((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordC (h + 1) 1 (ws ++ [(k + 1, [])])
        = [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ wordC (h + 1) 1 (ws ++ [(k + 1, [])]) from rfl,
      shiftr01_append0, shift_col, wordC_shift, wordC_snoc_one]
    set a := h + 1 + s with ha
    have hLw : LwA (h + s) A' := ⟨P, hP, hA'⟩
    have hbase : RunA 0 a (A' ++ (((a, 1, 0) : ℕ × ℕ × ℕ) :: wordC a 1 (ws ++ [(k, [])]))) :=
      ⟨h + s, A', _, by omega, rfl, hLw, by
        have := (hprev [] Bok_nil).seg (h + s)
        simpa [ha, show h + s + 1 = h + 1 + s from by omega] using this⟩
    have hAok := (BaseOk_RunA 0).aok _ _ hbase
    have hancA : Ancd a A' := by
      have := LwB_Ancd hP hA'
      rwa [show h + s + 1 = a from by omega] at this
    have hanc : Ancd (a + 2) (A' ++ (((a, 1, 0) : ℕ × ℕ × ℕ) :: wordC a 1 (ws ++ [(k, [])]))) :=
      Ancd_recword (by omega) hancA (WplC_append hw (WplC_singleton (k := k) Bok_nil))
    have hh := snocd_gen (Y := A' ++ (((a, 1, 0) : ℕ × ℕ × ℕ) :: wordC a 1 (ws ++ [(k, [])])))
      (d := a + 2) (by omega) hAok hanc ?_
    · simpa [List.append_assoc] using hh
    · intro B hB
      have h2 := ((hprev B hB).seg (h + s)).reapp P hP 0 A' (by simpa using hA')
      rw [show ((h + s + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordC (h + s + 1) 1 (ws ++ [(k, B)])
          = [((h + s + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ wordC (h + s + 1) 1 (ws ++ [(k, B)]) from rfl]
        at h2
      rw [wordC_snoc_pay] at h2
      simpa [ha, show h + s + 1 = h + 1 + s from by omega, List.append_assoc] using h2

#print axioms GoodFb_snoc_oneC


/-! ### 場合 (i)(ii): 荷の内部展開と、荷の複製 -/

/-- 場合 (i): 荷の末尾が非零なら、荷だけが展開される。 -/
theorem GoodFb_snoc_innerC {ws : List (ℕ × TrioSeq)} (hw : WplC ws) (k : ℕ) {Y : TrioSeq}
    (hY : Bok Y) (hlen : 2 ≤ Y.length)
    (hp : hasParent Y (srow Y (Y.length - 1)) (Y.length - 1))
    (hIH : ∀ n, 1 ≤ n → GoodFb (fun a b => wordC a b (ws ++ [(k, Y⟦n⟧)]))) :
    GoodFb (fun a b => wordC a b (ws ++ [(k, Y)])) := by
  refine GoodFb_of_keyC (WplC_append hw (WplC_singleton hY)) hIH ?_
  intro Z a b hb hn
  have e : ∀ B : TrioSeq, Z ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordC a b (ws ++ [(k, B)]))
      = (Z ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordC a b (ws ++ [(k, [])]))) ++ shiftr01 (a + 2) 0 B := by
    intro B
    rw [wordC_snoc_pay]
    simp [List.append_assoc]
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n hn'
  rw [e Y, oper_shift _ Y (a + 2) n hlen hp, ← e (Y⟦n⟧)]
  exact hn n hn'

/-- 場合 (ii): 荷の末尾が `(0,0,0)` なら、字が `n` 個に複製される。 -/
theorem GoodFb_snoc_dupC {ws : List (ℕ × TrioSeq)} (hw : WplC ws) (k : ℕ) {Y : TrioSeq}
    (hY : Bok (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])) (hY' : Bok Y)
    (hIH : ∀ n, 1 ≤ n → GoodFb (fun a b => wordC a b (ws ++ List.replicate n (k, Y)))) :
    GoodFb (fun a b => wordC a b (ws ++ [(k, Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])])) := by
  refine GoodFb_of_keyC (WplC_append hw (WplC_singleton hY)) hIH ?_
  intro Z a b hb hn
  have hhead : entry (colC a b (k, Y)) 0 0 < a + 2 := by
    rw [entry_colC_zero]; simp [entry]
  have htail : ∀ r, 1 ≤ r → r < (colC a b (k, Y)).length → a + 2 ≤ entry (colC a b (k, Y)) 0 r := by
    intro r hr1 hrl
    obtain ⟨u, rfl⟩ : ∃ u, r = u + 1 := ⟨r - 1, by omega⟩
    rw [colC_length] at hrl
    rcases Nat.lt_or_ge u k with hlt | hge
    · rw [entry_colC_one a b (k, Y) 0 u hlt]; simp [entry]
    · obtain ⟨u', rfl⟩ : ∃ u', u = k + u' := ⟨u - k, by omega⟩
      have hu' : u' < Y.length := by simp at hrl; omega
      rw [show k + u' + 1 = k + u' + 1 from rfl, entry_colC_pay a b (k, Y) 0 u' hu',
        entry0_shiftr01 hu']
      omega
  have h := flat_mem'' (Y0 := Z ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordC a b ws))
    (M := colC a b (k, Y)) (d := a + 2) (colC_ne a b (k, Y)) hhead htail
    (fun n => by
      match n with
      | 0 =>
          have h1 := hn 1 (le_refl 1)
          rw [wordC_append, wordC_replicate] at h1
          simp only [List.range_one, List.flatMap_cons, List.flatMap_nil,
            List.append_nil] at h1
          have h2 := W_take (by
            rw [show Z ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: (wordC a b ws ++ colC a b (k, Y)))
                = (Z ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordC a b ws)) ++ colC a b (k, Y) from by
                  simp [List.append_assoc]] at h1
            exact h1) (Z ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordC a b ws)).length
          rw [List.take_left] at h2
          simpa using h2
      | (n + 1) =>
          have h1 := hn (n + 1) (by omega)
          rw [wordC_append, wordC_replicate] at h1
          simpa [List.append_assoc] using h1)
  rw [wordC_append, wordC_singleton, colC_snoc_zero]
  simpa [List.append_assoc] using h

#print axioms GoodFb_snoc_dupC


/-! ### 主帰納法: 字を 1 つ継いでも普遍（`k` の強帰納法 ＋ 荷の W 帰納法） -/

theorem GoodFb_rep {ws : List (ℕ × TrioSeq)} (hw : WplC ws)
    {p : ℕ × TrioSeq} (hp : Bok p.2)
    (hstep : ∀ ws' : List (ℕ × TrioSeq), WplC ws' → GoodFb (fun a b => wordC a b ws') →
      GoodFb (fun a b => wordC a b (ws' ++ [p])))
    (hG : GoodFb (fun a b => wordC a b ws)) :
    ∀ n : ℕ, GoodFb (fun a b => wordC a b (ws ++ List.replicate n p))
  | 0 => by simpa using hG
  | (n + 1) => by
      have hwn : WplC (ws ++ List.replicate n p) := by
        refine WplC_append hw ?_
        intro q hq
        rw [List.eq_of_mem_replicate hq]
        exact hp
      have h := hstep (ws ++ List.replicate n p) hwn (GoodFb_rep hw hp hstep hG n)
      have e : ws ++ List.replicate n p ++ [p] = ws ++ List.replicate (n + 1) p := by
        rw [List.append_assoc, ← List.replicate_succ']
      rwa [e] at h

/-- ★★★★★ 複合字を 1 つ継いでも普遍。 -/
theorem GoodFb_snocC : ∀ (k : ℕ) (Y : TrioSeq), Bok Y → ∀ ws : List (ℕ × TrioSeq), WplC ws →
    GoodFb (fun a b => wordC a b ws) → GoodFb (fun a b => wordC a b (ws ++ [(k, Y)])) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
    -- まず荷が空の場合
    have hnil : ∀ ws : List (ℕ × TrioSeq), WplC ws → GoodFb (fun a b => wordC a b ws) →
        GoodFb (fun a b => wordC a b (ws ++ [(k, [])])) := by
      match k with
      | 0 => intro ws hw hG; exact GoodFb_snoczC hw hG
      | (k' + 1) =>
          intro ws hw hG
          refine GoodFb_snoc_oneC hw k' ?_
          intro B hB
          exact ihk k' (by omega) B hB ws hw hG
    -- 荷の W 帰納法
    have key : W 0 ⊆ {Y : TrioSeq | Bok Y → ∀ ws : List (ℕ × TrioSeq), WplC ws →
        GoodFb (fun a b => wordC a b ws) → GoodFb (fun a b => wordC a b (ws ++ [(k, Y)]))} := by
      refine A2' ?_
      intro Y hY
      simp only [Set.mem_setOf_eq]
      intro hYb ws hw hG
      by_cases hshort : Y.length ≤ 1
      · rcases (by omega : Y.length = 0 ∨ Y.length = 1) with h0 | h1
        · have hnil0 : Y = [] := List.length_eq_zero_iff.mp h0
          subst hnil0
          exact hnil ws hw hG
        · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
          have hc0 : c.1 = 0 := hYb.root
          obtain ⟨hc1, hc2⟩ := hYb.zroot c (by simp) hc0
          have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1 hc2)
          subst hcz
          have e : ([((0, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq)
              = ([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by simp
          rw [e]
          refine GoodFb_snoc_dupC hw k (by simpa using hYb) Bok_nil ?_
          intro n hn
          exact GoodFb_rep hw (p := (k, ([] : TrioSeq))) Bok_nil
            (fun ws' hw' hG' => hnil ws' hw' hG') hG n
      have hlen2 : 2 ≤ Y.length := by omega
      have hYne : Y ≠ [] := by intro hc; rw [hc] at hlen2; simp at hlen2
      rcases hY with ⟨hl, -⟩ | hnat | ⟨m, hm, -, -⟩
      · exact absurd hl hshort
      · by_cases hlast : entry Y 0 (Y.length - 1) = 0
        · -- 場合 (ii): 荷の末尾は (0,0,0)
          obtain ⟨he1, he2⟩ := Zroot_entry hYb.zroot hlast
          have hcol : Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) = ((0, 0, 0) : ℕ × ℕ × ℕ) :=
            Prod.ext hlast (Prod.ext he1 he2)
          have hgl : Y.getLast hYne = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
            have h1 : Y.getLast hYne = Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
              rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
                List.getElem?_eq_getElem (show Y.length - 1 < Y.length by omega)]
              rfl
            rw [h1, hcol]
          have hsplit : Y = Y.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
            rw [← hgl]; exact (List.dropLast_append_getLast hYne).symm
          have hop : Y⟦1⟧ = Y.dropLast := by
            rw [oper_eq_pred_of_zero 1 (by omega) ⟨hlast, he1, he2⟩]
            unfold Pred
            rw [if_neg (by omega)]
          have hdl := hnat 1 le_rfl
          rw [hop] at hdl
          simp only [Set.mem_setOf_eq] at hdl
          have hdb : Bok Y.dropLast := Bok_dropLast hYb
          rw [hsplit]
          refine GoodFb_snoc_dupC hw k (by rw [← hsplit]; exact hYb) hdb ?_
          intro n hn
          exact GoodFb_rep hw (p := (k, Y.dropLast)) hdb
            (fun ws' hw' hG' => hdl hdb ws' hw' hG') hG n
        · -- 場合 (i): 荷の末尾は非零
          have hnz : ¬ (entry Y 0 (Y.length - 1) = 0 ∧ entry Y 1 (Y.length - 1) = 0 ∧
              entry Y 2 (Y.length - 1) = 0) := fun h => hlast h.1
          have hp := hasParent_of_ZrootMono hYb.zroot hYb.mono hYb.root hlen2 hnz
          refine GoodFb_snoc_innerC hw k hYb hlen2 hp ?_
          intro n hn
          have := hnat n hn
          simp only [Set.mem_setOf_eq] at this
          exact this (Bok_oper hYb hn) ws hw hG
      · exact absurd hm (Nat.not_lt_zero m)
    intro Y hYb ws hw hG
    exact key hYb.mem hYb ws hw hG

/-- ★★★★★ 荷が `Bok` の複合字の語はすべて普遍。 -/
theorem GoodFb_wordC : ∀ ws : List (ℕ × TrioSeq), WplC ws → GoodFb (fun a b => wordC a b ws) := by
  intro ws
  induction ws using List.reverseRecOn with
  | nil =>
      intro _
      exact ⟨fun a b => by simp [wordC_nil], fun a b => by simp [wordC_nil, Mono],
        fun a b s => by simp [wordC_nil, shiftr01],
        fun y c hy => by simpa [wordC_nil] using JkU_nil' hy c,
        fun c => by simpa [wordC_nil] using JkGU_nil c,
        fun h => by simpa [wordC_nil] using SegA_one h⟩
  | append_singleton ws p ih =>
      intro hw
      have hw' : WplC ws := WplC_of_append_left hw
      have hp : Bok p.2 := hw p (by simp)
      have := GoodFb_snocC p.1 p.2 hp ws hw' (ih hw')
      simpa using this

#print axioms GoodFb_wordC


/-! ### シート行 362〜369（`R338` の上の複合字の語） -/

theorem rowC_mem (ws : List (ℕ × TrioSeq)) (hw : WplC ws) :
    R338 ++ (((1, 1, 0) : ℕ × ℕ × ℕ) :: wordC 1 1 ws) ∈ W 0 := by
  have h := ((GoodFb_wordC ws hw).seg 0).reapp P0 BaseOk_zero 0 R338
    (LwB_of_base ⟨Aok_R338, rfl⟩)
  simpa using h

theorem WplC_ex (ws : List (ℕ × TrioSeq)) (h : ∀ p ∈ ws, Bok p.2) : WplC ws := h

/-- 行344 の確認: `R344 = R338 ++ (1,1,0) :: wordC 1 1 [(1,[])]`。 -/
theorem R344_eq_wordC : R344 = R338 ++ (((1, 1, 0) : ℕ × ℕ × ℕ) :: wordC 1 1 [(1, [])]) := by
  simp [R344, R341, wordC, colC, shiftr01]

/-- ★★★★★ シート行362 `R344 (2,2,1)(3,0,0)(4,1,1) = psi(W_w*W+W_w*psi(W_w))`。 -/
theorem R362_mem : R344 ++ [((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 0, 0) : ℕ × ℕ × ℕ),
    ((4, 1, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := rowC_mem [(1, []), (0, Q)] (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact Bok_nil
    · exact Bok_Q)
  simpa [R344, R341, wordC, colC, shiftr01, Q, List.append_assoc] using h

/-- ★★★★★ シート行363 `R344 (2,2,1)(3,1,0) = psi(W_w*W2)`。 -/
theorem R363_mem : R344 ++ [((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := rowC_mem [(1, []), (1, [])] (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact Bok_nil)
  simpa [R344, R341, wordC, colC, shiftr01, List.append_assoc] using h

/-- ★★★★★ シート行364 `R363 (2,2,1) = psi(W_w*W2+W_w)`。 -/
theorem R364_mem : R344 ++ [((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := rowC_mem [(1, []), (1, []), (0, [])] (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact Bok_nil)
  simpa [R344, R341, wordC, colC, shiftr01, List.append_assoc] using h

/-- ★★★★★ シート行365 `R364 (3,1,0) = psi(W_w*W3)`。 -/
theorem R365_mem : R344 ++ [((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 1, 0) : ℕ × ℕ × ℕ),
    ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := rowC_mem [(1, []), (1, []), (1, [])] (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact Bok_nil)
  simpa [R344, R341, wordC, colC, shiftr01, List.append_assoc] using h

/-- ★★★★★ シート行366 `R344 (3,0,0) = psi(W_w*W*w)`。 -/
theorem R366_mem : R344 ++ [((3, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := rowC_mem [(1, [((0, 0, 0) : ℕ × ℕ × ℕ)])] (by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact Bok_zero)
  simpa [R344, R341, wordC, colC, shiftr01, List.append_assoc] using h

/-- ★★★★★ シート行367 `R344 (3,0,0)(4,1,1) = psi(W_w*W*psi(W_w))`。 -/
theorem R367_mem : R344 ++ [((3, 0, 0) : ℕ × ℕ × ℕ), ((4, 1, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := rowC_mem [(1, Q)] (by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact Bok_Q)
  simpa [R344, R341, wordC, colC, shiftr01, Q, List.append_assoc] using h

/-- ★★★★★ シート行368 `R344 (3,1,0) = psi(W_w*W^2)`。 -/
theorem R368_mem : R344 ++ [((3, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := rowC_mem [(2, [])] (by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact Bok_nil)
  simpa [R344, R341, wordC, colC, shiftr01, List.append_assoc] using h

/-- ★★★★★ シート行369 `R368 (3,1,0) = psi(W_w*W^3)`。 -/
theorem R369_mem : R344 ++ [((3, 1, 0) : ℕ × ℕ × ℕ), ((3, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := rowC_mem [(3, [])] (by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact Bok_nil)
  simpa [R344, R341, wordC, colC, shiftr01, List.append_assoc] using h

#print axioms R369_mem


/-! ### 行 370 -/

theorem R341_one_rep (n : ℕ) :
    R341 ++ (List.range n).flatMap (fun _ => [((3, 1, 0) : ℕ × ℕ × ℕ)])
      = R338 ++ (((1, 1, 0) : ℕ × ℕ × ℕ) :: wordC 1 1 [(n, [])]) := by
  rw [flatMap_const_singleton]
  simp [R341, wordC, colC, shiftr01, List.append_assoc]

/-- ★★★★★ シート行370 `R344 (4,0,0) = psi(W_w*W^w)`。 -/
theorem R370_mem : R344 ++ [((4, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := flat_mem'' (Y0 := R341) (M := [((3, 1, 0) : ℕ × ℕ × ℕ)]) (d := 4)
    (by simp) (by simp [entry]) (by intro r hr1 hrl; simp at hrl; omega)
    (fun n => by
      rw [R341_one_rep n]
      exact rowC_mem [(n, [])] (by
        intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        exact Bok_nil))
  simpa [R344, R341, List.append_assoc] using h

#print axioms R370_mem


/-! ### junk の木 `JT`: 記録 `(l, v, 0)` の右の junk の一般形

各項は高さ `l+1` に置かれ、自分の junk を持つ:
- `z sub rest`  : `(l+1, v+1, 1)` と、その junk `sub`（レベル `(l+1, v+1)`）、続き `rest`
- `rec w sub rest` : `(l+1, w, 0)` と、その junk `sub`（レベル `(l+1, w)`）、続き `rest`
- `blk Y rest`  : 荷 `Y↑(l+1)`、続き `rest`
-/

inductive JT : Type where
  | nil : JT
  | z : JT → JT → JT
  | rc : ℕ → JT → JT → JT
  | blk : TrioSeq → JT → JT

/-- 木の解釈。 -/
def jkT (l v : ℕ) : JT → TrioSeq
  | JT.nil => []
  | JT.z sub rest => ((l + 1, v + 1, 1) : ℕ × ℕ × ℕ) :: (jkT (l + 1) (v + 1) sub ++ jkT l v rest)
  | JT.rc w sub rest => ((l + 1, w, 0) : ℕ × ℕ × ℕ) :: (jkT (l + 1) w sub ++ jkT l v rest)
  | JT.blk Y rest => shiftr01 (l + 1) 0 Y ++ jkT l v rest

/-- 木が妥当: 荷はすべて `Bok`、記録の行 1 は `1 ≤ w ≤ v+1`。 -/
def JTOk (v : ℕ) : JT → Prop
  | JT.nil => True
  | JT.z sub rest => JTOk (v + 1) sub ∧ JTOk v rest
  | JT.rc w sub rest => 1 ≤ w ∧ w ≤ v + 1 ∧ JTOk w sub ∧ JTOk v rest
  | JT.blk Y rest => Bok Y ∧ JTOk v rest

theorem jkT_ge : ∀ (J : JT) (l v : ℕ), ∀ x ∈ jkT l v J, l + 1 ≤ x.1
  | JT.nil, l, v => by simp [jkT]
  | JT.z sub rest, l, v => by
      intro x hx
      simp only [jkT, List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | h | h
      · exact le_refl _
      · have := jkT_ge sub (l + 1) (v + 1) x h; omega
      · exact jkT_ge rest l v x h
  | JT.rc w sub rest, l, v => by
      intro x hx
      simp only [jkT, List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | h | h
      · exact le_refl _
      · have := jkT_ge sub (l + 1) w x h; omega
      · exact jkT_ge rest l v x h
  | JT.blk Y rest, l, v => by
      intro x hx
      simp only [jkT, List.mem_append, shiftr01, List.mem_map] at hx
      rcases hx with ⟨q, -, rfl⟩ | h
      · show l + 1 ≤ q.1 + (l + 1); omega
      · exact jkT_ge rest l v x h

theorem jkT_mono : ∀ (J : JT) (v : ℕ), JTOk v J → ∀ l : ℕ, Mono (jkT l v J)
  | JT.nil, v, _, l => by simp [jkT, Mono]
  | JT.z sub rest, v, hJ, l => by
      intro x hx
      simp only [jkT, List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | h | h
      · show 1 ≤ v + 1; omega
      · exact jkT_mono sub (v + 1) hJ.1 (l + 1) x h
      · exact jkT_mono rest v hJ.2 l x h
  | JT.rc w sub rest, v, hJ, l => by
      intro x hx
      simp only [jkT, List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | h | h
      · show (0 : ℕ) ≤ w; omega
      · exact jkT_mono sub w hJ.2.2.1 (l + 1) x h
      · exact jkT_mono rest v hJ.2.2.2 l x h
  | JT.blk Y rest, v, hJ, l => by
      intro x hx
      simp only [jkT, List.mem_append, shiftr01, List.mem_map] at hx
      rcases hx with ⟨q, hq, rfl⟩ | h
      · simpa using hJ.1.mono q hq
      · exact jkT_mono rest v hJ.2 l x h

theorem jkT_shift : ∀ (J : JT) (l v s : ℕ), shiftr01 s 0 (jkT l v J) = jkT (l + s) v J
  | JT.nil, l, v, s => by simp [jkT, shiftr01]
  | JT.z sub rest, l, v, s => by
      rw [jkT, show ((l + 1, v + 1, 1) : ℕ × ℕ × ℕ) :: (jkT (l + 1) (v + 1) sub ++ jkT l v rest)
          = [((l + 1, v + 1, 1) : ℕ × ℕ × ℕ)] ++ (jkT (l + 1) (v + 1) sub ++ jkT l v rest) from rfl,
        shiftr01_append0, shiftr01_append0, shift_zcol, jkT_shift sub (l + 1) (v + 1) s,
        jkT_shift rest l v s, show l + 1 + s = l + s + 1 from by omega]
      rfl
  | JT.rc w sub rest, l, v, s => by
      rw [jkT, show ((l + 1, w, 0) : ℕ × ℕ × ℕ) :: (jkT (l + 1) w sub ++ jkT l v rest)
          = [((l + 1, w, 0) : ℕ × ℕ × ℕ)] ++ (jkT (l + 1) w sub ++ jkT l v rest) from rfl,
        shiftr01_append0, shiftr01_append0, shift_col, jkT_shift sub (l + 1) w s,
        jkT_shift rest l v s, show l + 1 + s = l + s + 1 from by omega]
      rfl
  | JT.blk Y rest, l, v, s => by
      rw [jkT, shiftr01_append0, shiftr01_add0, jkT_shift rest l v s,
        show l + 1 + s = l + s + 1 from by omega]
      rfl

theorem MidD_jkT (l v : ℕ) (hl : 1 ≤ l) (hv : 1 ≤ v) {J : JT} (hJ : JTOk v J) :
    MidD (l + 1) (((l, v, 0) : ℕ × ℕ × ℕ) :: jkT l v J) := by
  have h := MidD_append (MidD_col l v hl hv) (N := jkT l v J) (jkT_ge J l v) (jkT_mono J v hJ l)
  simpa using h

#print axioms MidD_jkT


/-! ### z を含まない junk の木（1 の列と荷だけ）は、どの `BaseOk` 台座の上でも通る -/

/-- 木が「z を含まず、記録は 1 の列、荷は `Bok`」。 -/
def RT1 : JT → Prop
  | JT.nil => True
  | JT.z _ _ => False
  | JT.rc w sub rest => w = 1 ∧ RT1 sub ∧ RT1 rest
  | JT.blk Y rest => Bok Y ∧ RT1 rest

theorem RT1_JTOk : ∀ (J : JT), RT1 J → ∀ v : ℕ, JTOk v J
  | JT.nil, _, v => trivial
  | JT.z _ _, h, _ => absurd h (by simp [RT1])
  | JT.blk Y rest, hJ, v => ⟨hJ.1, RT1_JTOk rest hJ.2 v⟩
  | JT.rc w sub rest, hJ, v => by
      obtain ⟨rfl, hsub, hrest⟩ := hJ
      exact ⟨le_refl 1, by omega, RT1_JTOk sub hsub 1, RT1_JTOk rest hrest v⟩

/-- ★★★ `BaseOk` 台座の元に、z を含まない木の junk を継いでも台座の元のまま。 -/
theorem RT1_close : ∀ (J : JT), RT1 J → ∀ (P : ℕ → TrioSeq → Prop), BaseOk P →
    ∀ (l v : ℕ) (Y0 : TrioSeq), P l Y0 → P l (Y0 ++ jkT l v J)
  | JT.nil, _, P, hP, l, v, Y0, hY0 => by simpa [jkT] using hY0
  | JT.z _ _, h, _, _, _, _, _, _ => absurd h (by simp [RT1])
  | JT.blk Y rest, hJ, P, hP, l, v, Y0, hY0 => by
      have hY : Bok Y := hJ.1
      -- 荷を吸収
      have hstep : P l (Y0 ++ shiftr01 (l + 1) 0 Y) := by
        refine hP.close l Y0 _ hY0 ?_ ?_ ?_
        · intro x hx
          simp only [shiftr01, List.mem_map] at hx
          obtain ⟨q, -, rfl⟩ := hx
          show l + 1 ≤ q.1 + (l + 1); omega
        · intro x hx
          simp only [shiftr01, List.mem_map] at hx
          obtain ⟨q, hq, rfl⟩ := hx
          simpa using hY.mono q hq
        · intro t A' hA'
          rw [shiftr01_add0]
          have := hP.hang (l + t) A' hA' Y hY
          rwa [show l + t + 1 = l + 1 + t from by omega] at this
      have h2 := RT1_close rest hJ.2 P hP l v _ hstep
      rw [jkT]
      simpa [List.append_assoc] using h2
  | JT.rc w sub rest, hJ, P, hP, l, v, Y0, hY0 => by
      obtain ⟨rfl, hsub, hrest⟩ := hJ
      -- 1 の列とその junk をまとめて吸収
      have hstep : P l (Y0 ++ ([((l + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ jkT (l + 1) 1 sub)) := by
        refine hP.close l Y0 _ hY0 ?_ ?_ ?_
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · simp only [List.mem_singleton] at h; subst h; simp
          · have := jkT_ge sub (l + 1) 1 x h; omega
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · simp only [List.mem_singleton] at h; subst h; simp
          · exact jkT_mono sub 1 (RT1_JTOk sub hsub 1) (l + 1) x h
        · intro t A' hA'
          rw [shiftr01_append0, shift_col, jkT_shift]
          have hAok : Aok A' := hP.aok (l + t) A' hA'
          have hLw : LwA (l + t) A' := ⟨P, hP, LwB_of_base hA'⟩
          have hR : RunA 0 (l + t + 1) (A' ++ [((l + t + 1, 1, 0) : ℕ × ℕ × ℕ)]) :=
            ⟨l + t, A', _, rfl, rfl, hLw, by simpa using SegA_one (l + t)⟩
          have h1 := RT1_close sub hsub (RunA 0) (BaseOk_RunA 0) (l + t + 1) 1 _ hR
          have h2 := ((BaseOk_RunA 0).aok _ _ h1).mem
          rw [show l + 1 + t = l + t + 1 from by omega]
          simpa [List.append_assoc] using h2
      have h2 := RT1_close rest hrest P hP l v _ hstep
      rw [jkT]
      simpa [List.append_assoc] using h2


/-! ## 木の字（`Jk1`）: z の列の junk を「1 の列 + その junk」「荷」の木にする

`jk1 l N` はレベル `l`（＝親の高さ `l`、列は高さ `l+1` 以上）に展開した列。
- `Jk1.pay N Y`: 木 `N` の右に荷 `Y`（高さ `l+1` から）
- `Jk1.one N M`: 木 `N` の右に 1 の列 `(l+1,1,0)` と、その junk `M`（レベル `l+1`）

`wordC` の複合字 `colC a b (k,Y)` は「1 の列が全部兄弟」の特別な場合。 -/

inductive Jk1 : Type
  | nil : Jk1
  | pay : Jk1 → TrioSeq → Jk1
  | one : Jk1 → Jk1 → Jk1
  | two : Jk1 → Jk1 → Jk1

/-- 木をレベル `l` で列に展開する。 -/
def jk1 : ℕ → Jk1 → TrioSeq
  | _, Jk1.nil => []
  | l, Jk1.pay N Y => jk1 l N ++ shiftr01 (l + 1) 0 Y
  | l, Jk1.one N M => jk1 l N ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) M)
  | l, Jk1.two N M => jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) M)

/-- 木の先頭段が 2 の記録でない（2 の記録の直上に置ける形）。 -/
def TopOk : Jk1 → Prop
  | Jk1.nil => True
  | Jk1.pay N _ => TopOk N
  | Jk1.one N _ => TopOk N
  | Jk1.two _ _ => False

/-- 木が荷だけでできている（`one` も 2 の記録も含まない）。 -/
def PayOnly : Jk1 → Prop
  | Jk1.nil => True
  | Jk1.pay N Y => PayOnly N ∧ Bok Y
  | Jk1.one _ _ => False
  | Jk1.two _ _ => False

/-- junk のレベル（1 の列の上）で妥当。荷はすべて `Bok`。2 の記録を置ける。 -/
def JkJ : Jk1 → Prop
  | Jk1.nil => True
  | Jk1.pay N Y => JkJ N ∧ Bok Y
  | Jk1.one N M => JkJ N ∧ JkJ M
  | Jk1.two N M => JkJ N ∧ PayOnly M

/-- 質量計算のための一般版（2 の記録に制限を付けない）。 -/
def JkA : Jk1 → Prop
  | Jk1.nil => True
  | Jk1.pay N Y => JkA N ∧ Bok Y
  | Jk1.one N M => JkA N ∧ JkA M
  | Jk1.two N M => JkA N ∧ JkA M

/-- 字の先頭段で妥当。2 の記録は置けない（字の z の直上になり、上がってしまう）。 -/
def JkOk : Jk1 → Prop
  | Jk1.nil => True
  | Jk1.pay N Y => JkOk N ∧ Bok Y
  | Jk1.one N M => JkOk N ∧ JkJ M
  | Jk1.two _ _ => False

theorem JkJ_of_JkOk : ∀ N : Jk1, JkOk N → JkJ N
  | Jk1.nil, _ => trivial
  | Jk1.pay N Y, h => ⟨JkJ_of_JkOk N h.1, h.2⟩
  | Jk1.one N M, h => ⟨JkJ_of_JkOk N h.1, h.2⟩
  | Jk1.two _ _, h => absurd h (by simp [JkOk])

theorem JkA_of_PayOnly : ∀ W : Jk1, PayOnly W → JkA W
  | Jk1.nil, _ => trivial
  | Jk1.pay N Y, h => ⟨JkA_of_PayOnly N h.1, h.2⟩
  | Jk1.one _ _, h => absurd h (by simp [PayOnly])
  | Jk1.two _ _, h => absurd h (by simp [PayOnly])

theorem JkA_of_JkJ : ∀ N : Jk1, JkJ N → JkA N
  | Jk1.nil, _ => trivial
  | Jk1.pay N Y, h => ⟨JkA_of_JkJ N h.1, h.2⟩
  | Jk1.one N M, h => ⟨JkA_of_JkJ N h.1, JkA_of_JkJ M h.2⟩
  | Jk1.two N M, h => ⟨JkA_of_JkJ N h.1, JkA_of_PayOnly M h.2⟩

theorem JkOk_nil : JkOk Jk1.nil := trivial

theorem JkJ_nil : JkJ Jk1.nil := trivial

theorem jk1_nil (l : ℕ) : jk1 l Jk1.nil = [] := rfl

theorem jk1_pay_nil (l : ℕ) (N : Jk1) : jk1 l (Jk1.pay N []) = jk1 l N := by
  simp [jk1, shiftr01]

/-- 木の列はすべて高さ `l+1` 以上。 -/
theorem jk1_ge : ∀ (N : Jk1) (l : ℕ), ∀ x ∈ jk1 l N, l + 1 ≤ x.1
  | Jk1.nil, l => by simp [jk1]
  | Jk1.pay N Y, l => by
      intro x hx
      simp only [jk1, List.mem_append, shiftr01, List.mem_map] at hx
      rcases hx with h | ⟨q, -, rfl⟩
      · exact jk1_ge N l x h
      · show l + 1 ≤ q.1 + (l + 1); omega
  | Jk1.one N M, l => by
      intro x hx
      simp only [jk1, List.mem_append, List.mem_cons] at hx
      rcases hx with h | rfl | h
      · exact jk1_ge N l x h
      · exact le_refl _
      · have := jk1_ge M (l + 1) x h; omega
  | Jk1.two N M, l => by
      intro x hx
      simp only [jk1, List.mem_append, List.mem_cons] at hx
      rcases hx with h | rfl | h
      · exact jk1_ge N l x h
      · exact le_refl _
      · have := jk1_ge M (l + 1) x h; omega

theorem jk1_mono : ∀ (N : Jk1), JkA N → ∀ l : ℕ, Mono (jk1 l N)
  | Jk1.nil, _, l => by simp [jk1, Mono]
  | Jk1.pay N Y, hN, l => by
      intro x hx
      simp only [jk1, List.mem_append, shiftr01, List.mem_map] at hx
      rcases hx with h | ⟨q, hq, rfl⟩
      · exact jk1_mono N hN.1 l x h
      · simpa using hN.2.mono q hq
  | Jk1.one N M, hN, l => by
      intro x hx
      simp only [jk1, List.mem_append, List.mem_cons] at hx
      rcases hx with h | rfl | h
      · exact jk1_mono N hN.1 l x h
      · show (0 : ℕ) ≤ 1; omega
      · exact jk1_mono M hN.2 (l + 1) x h
  | Jk1.two N M, hN, l => by
      intro x hx
      simp only [jk1, List.mem_append, List.mem_cons] at hx
      rcases hx with h | rfl | h
      · exact jk1_mono N hN.1 l x h
      · show (0 : ℕ) ≤ 2; omega
      · exact jk1_mono M hN.2 (l + 1) x h

theorem jk1_shift : ∀ (N : Jk1) (l s : ℕ), shiftr01 s 0 (jk1 l N) = jk1 (l + s) N
  | Jk1.nil, l, s => by simp [jk1, shiftr01]
  | Jk1.pay N Y, l, s => by
      rw [jk1, shiftr01_append0, jk1_shift N l s, shiftr01_add0,
        show l + 1 + s = l + s + 1 from by omega]
      rfl
  | Jk1.one N M, l, s => by
      rw [jk1, show ((l + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) M
          = [((l + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ jk1 (l + 1) M from rfl,
        shiftr01_append0, shiftr01_append0, shift_col, jk1_shift N l s,
        jk1_shift M (l + 1) s, show l + 1 + s = l + s + 1 from by omega]
      rfl
  | Jk1.two N M, l, s => by
      rw [jk1, show ((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) M
          = [((l + 1, 2, 0) : ℕ × ℕ × ℕ)] ++ jk1 (l + 1) M from rfl,
        shiftr01_append0, shiftr01_append0, shift_col, jk1_shift N l s,
        jk1_shift M (l + 1) s, show l + 1 + s = l + s + 1 from by omega]
      rfl

#print axioms jk1_shift


/-! ### `Ancd` を組み立てる補助補題 -/

theorem entry0_of_ge {N : TrioSeq} {d : ℕ} (hN : ∀ x ∈ N, d ≤ x.1) :
    ∀ u, u < N.length → d ≤ entry N 0 u := by
  intro u hu
  have h := hN (N[u]'hu) (List.getElem_mem hu)
  have he : entry N 0 u = (N[u]'hu).1 := by
    simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu]
  omega

/-- 高さ `d` 以上の塊を継いでも祖先条件は保たれる。 -/
theorem Ancd_append_ge {d : ℕ} {X N : TrioSeq} (hX : Ancd d X) (hN : ∀ x ∈ N, d ≤ x.1) :
    Ancd d (X ++ N) := by
  intro j hj0 hjl hlt hvis
  rcases Nat.lt_or_ge j X.length with hjX | hjX
  · rw [entry_append_left hjX]
    refine hX j hj0 hjX (by rwa [entry_append_left hjX] at hlt) ?_
    intro i hi hil
    have := hvis i hi (by simp; omega)
    rwa [entry_append_left hjX, entry_append_left hil] at this
  · exfalso
    obtain ⟨u, hu, rfl⟩ : ∃ u, u < N.length ∧ j = X.length + u :=
      ⟨j - X.length, by simp at hjl; omega, by omega⟩
    rw [entry_append_right] at hlt
    have := entry0_of_ge hN u hu
    omega

/-- 行 1 が 1 以上の列を 1 本継いでも祖先条件は保たれる。 -/
theorem Ancd_snoc_one1 {d : ℕ} {X : TrioSeq} (hX : Ancd d X) {c : ℕ × ℕ × ℕ}
    (hc : 1 ≤ c.2.1) : Ancd d (X ++ [c]) := by
  intro j hj0 hjl hlt hvis
  rcases Nat.lt_or_ge j X.length with hjX | hjX
  · rw [entry_append_left hjX]
    refine hX j hj0 hjX (by rwa [entry_append_left hjX] at hlt) ?_
    intro i hi hil
    have := hvis i hi (by simp; omega)
    rwa [entry_append_left hjX, entry_append_left hil] at this
  · obtain ⟨u, hu, rfl⟩ : ∃ u, u < 1 ∧ j = X.length + u :=
      ⟨j - X.length, by simp at hjl; omega, by omega⟩
    have hu0 : u = 0 := by omega
    subst hu0
    rw [entry_append_right]
    simpa [entry] using hc

/-- 高さ `a` の「軸」の列を継ぐと、祖先条件はどんな `d` でも成り立つ。 -/
theorem Ancd_snoc_pivot {a d : ℕ} {Z : TrioSeq} (hZ : Ancd a Z) {c : ℕ × ℕ × ℕ}
    (hc0 : c.1 = a) (hc1 : 1 ≤ c.2.1) : Ancd d (Z ++ [c]) := by
  intro j hj0 hjl hlt hvis
  rcases Nat.lt_or_ge j Z.length with hjZ | hjZ
  · have hZl : Z.length < (Z ++ [c]).length := by simp
    have hcz : entry (Z ++ [c]) 0 Z.length = a := by
      rw [show Z.length = Z.length + 0 from rfl, entry_append_right]
      simpa [entry] using hc0
    have hlt1 : entry Z 0 j < a := by
      have h1 := hvis Z.length hjZ hZl
      rw [entry_append_left hjZ, hcz] at h1
      exact h1
    rw [entry_append_left hjZ]
    refine hZ j hj0 hjZ hlt1 ?_
    intro i hi hil
    have := hvis i hi (by simp; omega)
    rwa [entry_append_left hjZ, entry_append_left hil] at this
  · obtain ⟨u, hu, rfl⟩ : ∃ u, u < 1 ∧ j = Z.length + u :=
      ⟨j - Z.length, by simp at hjl; omega, by omega⟩
    have hu0 : u = 0 := by omega
    subst hu0
    rw [entry_append_right]
    simpa [entry] using hc1

/-- 高さ `l+1` 以上の塊 `B` の直後に高さ `l+1` 以下の列を置くと、`B` の列は不可視。 -/
theorem Ancd_append_low {d l : ℕ} {X B : TrioSeq} (hX : Ancd d X)
    (hB : ∀ x ∈ B, l + 1 ≤ x.1) {c : ℕ × ℕ × ℕ} (hc0 : c.1 ≤ l + 1) (hc1 : 1 ≤ c.2.1) :
    Ancd d ((X ++ B) ++ [c]) := by
  have hcpos : ((X ++ B) ++ [c]).length = X.length + B.length + 1 := by simp; omega
  have hclast : entry ((X ++ B) ++ [c]) 0 (X.length + B.length) = c.1 := by
    rw [show X.length + B.length = (X ++ B).length + 0 from by simp, entry_append_right]
    simp [entry]
  intro j hj0 hjl hlt hvis
  rcases Nat.lt_or_ge j X.length with hjX | hjX
  · have hjXB : j < (X ++ B).length := by simp; omega
    rw [entry_append_left hjXB, entry_append_left hjX]
    refine hX j hj0 hjX (by rwa [entry_append_left hjXB, entry_append_left hjX] at hlt) ?_
    intro i hi hil
    have hiXB : i < (X ++ B).length := by simp; omega
    have := hvis i hi (by omega)
    rwa [entry_append_left hjXB, entry_append_left hjX, entry_append_left hiXB,
      entry_append_left hil] at this
  rcases Nat.lt_or_ge j (X.length + B.length) with hjB | hjB
  · exfalso
    obtain ⟨u, hu, rfl⟩ : ∃ u, u < B.length ∧ j = X.length + u :=
      ⟨j - X.length, by omega, by omega⟩
    have hjXB : X.length + u < (X ++ B).length := by simp; omega
    have he : entry ((X ++ B) ++ [c]) 0 (X.length + u) = entry B 0 u := by
      rw [entry_append_left hjXB, entry_append_right]
    have h1 := hvis (X.length + B.length) (by omega) (by omega)
    rw [he, hclast] at h1
    have := entry0_of_ge hB u hu
    omega
  · obtain ⟨u, hu, rfl⟩ : ∃ u, u < 1 ∧ j = (X ++ B).length + u :=
      ⟨j - (X.length + B.length), by omega, by simp; omega⟩
    have hu0 : u = 0 := by omega
    subst hu0
    rw [entry_append_right]
    simpa [entry] using hc1

#print axioms Ancd_append_low


/-! ### 木の字と語 -/

/-- 木の字: z の列 `(a+1,b+1,1)` とその junk（レベル `a+1`）。 -/
def colJ (a b : ℕ) (N : Jk1) : TrioSeq := ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ) :: jk1 (a + 1) N

/-- 木の字の語。 -/
def wordJ (a b : ℕ) (ws : List Jk1) : TrioSeq := ws.flatMap (colJ a b)

/-- 語の各字の荷はすべて `Bok`。 -/
def WOk (ws : List Jk1) : Prop := ∀ N ∈ ws, JkOk N

theorem WOk_nil : WOk [] := fun _ h => by simp at h

theorem WOk_append {ws1 ws2 : List Jk1} (h1 : WOk ws1) (h2 : WOk ws2) : WOk (ws1 ++ ws2) := by
  intro N hN
  rcases List.mem_append.mp hN with h | h
  · exact h1 N h
  · exact h2 N h

theorem WOk_of_append_left {ws1 ws2 : List Jk1} (h : WOk (ws1 ++ ws2)) : WOk ws1 :=
  fun N hN => h N (List.mem_append_left _ hN)

theorem WOk_singleton {N : Jk1} (hN : JkOk N) : WOk [N] := by
  intro M hM
  simp only [List.mem_singleton] at hM
  subst hM; exact hN

theorem WOk_replicate {N : Jk1} (hN : JkOk N) (n : ℕ) : WOk (List.replicate n N) := by
  intro M hM
  rw [List.eq_of_mem_replicate hM]; exact hN

/-- 背骨のフレーム。`fone U` は「左兄弟 `U` + 1 の列」、
`fotw U` は「左兄弟 `U` + 1 の列 + 2 の記録」。 -/
inductive Frm : Type
  | fone : Jk1 → Frm
  | fotw : Jk1 → Frm

/-- 背骨の文脈: 外側から内側へ並べたフレームの列。 -/
def plug : List Frm → Jk1 → Jk1
  | [], T => T
  | (Frm.fone N :: rest), T => Jk1.one N (plug rest T)
  | (Frm.fotw N :: rest), T => Jk1.one N (Jk1.two Jk1.nil (plug rest T))

/-- フレーム列が稼ぐ高さ。 -/
def dep : List Frm → ℕ
  | [] => 0
  | (Frm.fone _ :: rest) => dep rest + 1
  | (Frm.fotw _ :: rest) => dep rest + 2

def frmT : Frm → Jk1
  | Frm.fone N => N
  | Frm.fotw N => N

theorem plug_nil (T : Jk1) : plug [] T = T := rfl

theorem plug_snoc : ∀ (ctx : List Frm) (X T : Jk1),
    plug (ctx ++ [Frm.fone X]) T = plug ctx (Jk1.one X T)
  | [], _, _ => rfl
  | (Frm.fone N :: rest), X, T => by
      show Jk1.one N (plug (rest ++ [Frm.fone X]) T) = Jk1.one N (plug rest (Jk1.one X T))
      rw [plug_snoc rest X T]
  | (Frm.fotw N :: rest), X, T => by
      show Jk1.one N (Jk1.two Jk1.nil (plug (rest ++ [Frm.fone X]) T))
        = Jk1.one N (Jk1.two Jk1.nil (plug rest (Jk1.one X T)))
      rw [plug_snoc rest X T]

theorem plug_snoc2 : ∀ (ctx : List Frm) (X T : Jk1),
    plug (ctx ++ [Frm.fotw X]) T = plug ctx (Jk1.one X (Jk1.two Jk1.nil T))
  | [], _, _ => rfl
  | (Frm.fone N :: rest), X, T => by
      show Jk1.one N (plug (rest ++ [Frm.fotw X]) T)
        = Jk1.one N (plug rest (Jk1.one X (Jk1.two Jk1.nil T)))
      rw [plug_snoc2 rest X T]
  | (Frm.fotw N :: rest), X, T => by
      show Jk1.one N (Jk1.two Jk1.nil (plug (rest ++ [Frm.fotw X]) T))
        = Jk1.one N (Jk1.two Jk1.nil (plug rest (Jk1.one X (Jk1.two Jk1.nil T))))
      rw [plug_snoc2 rest X T]

theorem dep_snoc : ∀ (ctx : List Frm) (X : Jk1), dep (ctx ++ [Frm.fone X]) = dep ctx + 1
  | [], _ => rfl
  | (Frm.fone _ :: rest), X => by
      show dep (rest ++ [Frm.fone X]) + 1 = dep rest + 1 + 1
      rw [dep_snoc rest X]
  | (Frm.fotw _ :: rest), X => by
      show dep (rest ++ [Frm.fone X]) + 2 = dep rest + 2 + 1
      rw [dep_snoc rest X]

theorem dep_snoc2 : ∀ (ctx : List Frm) (X : Jk1), dep (ctx ++ [Frm.fotw X]) = dep ctx + 2
  | [], _ => rfl
  | (Frm.fone _ :: rest), X => by
      show dep (rest ++ [Frm.fotw X]) + 1 = dep rest + 1 + 2
      rw [dep_snoc2 rest X]
  | (Frm.fotw _ :: rest), X => by
      show dep (rest ++ [Frm.fotw X]) + 2 = dep rest + 2 + 2
      rw [dep_snoc2 rest X]

/-- 文脈の先頭フレームの木が `TopOk`。 -/
def HdT : List Frm → Prop
  | [] => True
  | (Frm.fone N :: _) => TopOk N
  | (Frm.fotw N :: _) => TopOk N

/-- 文脈がすべて junk レベルで妥当。 -/
def CtxJ : List Frm → Prop
  | [] => True
  | (Frm.fone N :: rest) => JkJ N ∧ CtxJ rest
  | (Frm.fotw _ :: _) => False

/-- 文脈の一番外は字レベル、残りは junk レベル。 -/
def CtxOk : List Frm → Prop
  | [] => True
  | (Frm.fone N :: rest) => JkOk N ∧ CtxJ rest
  | (Frm.fotw _ :: _) => False

/-- 文脈の一番内側に置く木に要る条件（junk レベル）。
一番内のフレームが 2 の記録なら、木の先頭段は 2 の記録ではいけない。 -/
def CtxXJ : List Frm → Jk1 → Prop
  | [], X => JkJ X
  | [Frm.fotw _], X => JkJ X ∧ TopOk X
  | (_ :: rest), X => CtxXJ rest X

/-- 文脈の一番内側に置く木に要る条件。空文脈なら字レベル。 -/
def CtxX : List Frm → Jk1 → Prop
  | [], X => JkOk X
  | (f :: rest), X => CtxXJ (f :: rest) X

theorem CtxXJ_cons (f g : Frm) (rest : List Frm) (X : Jk1) :
    CtxXJ (f :: g :: rest) X = CtxXJ (g :: rest) X := by
  cases f <;> cases g <;> rfl

theorem TopOk_plug_cons : ∀ (f : Frm) (rest : List Frm) (T : Jk1), HdT (f :: rest) →
    TopOk (plug (f :: rest) T)
  | Frm.fone _, _, _, h => h
  | Frm.fotw _, _, _, h => h

theorem CtxXJ_snoc1 : ∀ (ctx : List Frm) (U W : Jk1), JkJ W → CtxXJ (ctx ++ [Frm.fone U]) W
  | [], _, _, h => h
  | (f :: rest), U, W, h => by
      have e : CtxXJ ((f :: rest) ++ [Frm.fone U]) W = CtxXJ (rest ++ [Frm.fone U]) W := by
        cases rest with
        | nil => cases f <;> rfl
        | cons g gs => cases f <;> cases g <;> rfl
      rw [e]
      exact CtxXJ_snoc1 rest U W h

theorem CtxXJ_snoc2 : ∀ (ctx : List Frm) (U W : Jk1), JkJ W → TopOk W →
    CtxXJ (ctx ++ [Frm.fotw U]) W
  | [], _, _, h, h2 => ⟨h, h2⟩
  | (f :: rest), U, W, h, h2 => by
      have e : CtxXJ ((f :: rest) ++ [Frm.fotw U]) W = CtxXJ (rest ++ [Frm.fotw U]) W := by
        cases rest with
        | nil => cases f <;> rfl
        | cons g gs => cases f <;> cases g <;> rfl
      rw [e]
      exact CtxXJ_snoc2 rest U W h h2

theorem CtxXJ_snoc1_of : ∀ (ctx : List Frm) (U W : Jk1), CtxXJ (ctx ++ [Frm.fone U]) W → JkJ W
  | [], _, _, h => h
  | (f :: rest), U, W, h => by
      have e : CtxXJ ((f :: rest) ++ [Frm.fone U]) W = CtxXJ (rest ++ [Frm.fone U]) W := by
        cases rest with
        | nil => cases f <;> rfl
        | cons g gs => cases f <;> cases g <;> rfl
      rw [e] at h
      exact CtxXJ_snoc1_of rest U W h

theorem CtxXJ_snoc2_of : ∀ (ctx : List Frm) (U W : Jk1), CtxXJ (ctx ++ [Frm.fotw U]) W →
    JkJ W ∧ TopOk W
  | [], _, _, h => h
  | (f :: rest), U, W, h => by
      have e : CtxXJ ((f :: rest) ++ [Frm.fotw U]) W = CtxXJ (rest ++ [Frm.fotw U]) W := by
        cases rest with
        | nil => cases f <;> rfl
        | cons g gs => cases f <;> cases g <;> rfl
      rw [e] at h
      exact CtxXJ_snoc2_of rest U W h

theorem CtxX_snoc1 (ctx : List Frm) (U W : Jk1) : CtxX (ctx ++ [Frm.fone U]) W ↔ JkJ W := by
  have hne : ctx ++ [Frm.fone U] ≠ [] := by simp
  cases h : ctx ++ [Frm.fone U] with
  | nil => exact absurd h hne
  | cons f rest =>
      constructor
      · intro hx
        exact CtxXJ_snoc1_of ctx U W (by rw [h]; exact hx)
      · intro hx
        show CtxXJ (f :: rest) W
        rw [← h]
        exact CtxXJ_snoc1 ctx U W hx

theorem CtxX_snoc2 (ctx : List Frm) (U W : Jk1) :
    CtxX (ctx ++ [Frm.fotw U]) W ↔ JkJ W ∧ TopOk W := by
  have hne : ctx ++ [Frm.fotw U] ≠ [] := by simp
  cases h : ctx ++ [Frm.fotw U] with
  | nil => exact absurd h hne
  | cons f rest =>
      constructor
      · intro hx
        exact CtxXJ_snoc2_of ctx U W (by rw [h]; exact hx)
      · intro hx
        show CtxXJ (f :: rest) W
        rw [← h]
        exact CtxXJ_snoc2 ctx U W hx.1 hx.2

theorem CtxXJ_of_JkJhd : ∀ (ctx : List Frm) (X : Jk1), JkJ X → TopOk X → CtxXJ ctx X
  | [], _, h, _ => h
  | [Frm.fone _], _, h, _ => h
  | [Frm.fotw _], _, h, h2 => ⟨h, h2⟩
  | (_ :: g :: rest), X, h, h2 => by
      rw [CtxXJ_cons]
      exact CtxXJ_of_JkJhd (g :: rest) X h h2

theorem JkJ_of_CtxXJ : ∀ (ctx : List Frm) (X : Jk1), CtxXJ ctx X → JkJ X
  | [], _, h => h
  | [Frm.fone _], _, h => h
  | [Frm.fotw _], _, h => h.1
  | (_ :: g :: rest), X, h => by
      rw [CtxXJ_cons] at h
      exact JkJ_of_CtxXJ (g :: rest) X h

theorem CtxX_of_JkOk : ∀ (ctx : List Frm) (X : Jk1), JkOk X → TopOk X → CtxX ctx X
  | [], _, h, _ => h
  | (f :: rest), X, h, h2 => CtxXJ_of_JkJhd (f :: rest) X (JkJ_of_JkOk X h) h2

theorem CtxX_of_JkJ : ∀ (ctx : List Frm), ctx ≠ [] → ∀ X : Jk1, JkJ X → TopOk X → CtxX ctx X
  | [], h, _, _, _ => absurd rfl h
  | (f :: rest), _, X, h, h2 => CtxXJ_of_JkJhd (f :: rest) X h h2

theorem JkJ_of_CtxX : ∀ (ctx : List Frm) (X : Jk1), CtxX ctx X → JkJ X
  | [], X, h => JkJ_of_JkOk X h
  | (f :: rest), X, h => JkJ_of_CtxXJ (f :: rest) X h

theorem CtxX_nil (ctx : List Frm) : CtxX ctx Jk1.nil :=
  CtxX_of_JkOk ctx Jk1.nil JkOk_nil trivial

theorem CtxX_one : ∀ (ctx : List Frm) (X T : Jk1), CtxX ctx X → JkJ T → CtxX ctx (Jk1.one X T)
  | [], X, T, hX, hT => ⟨hX, hT⟩
  | (f :: rest), X, T, hX, hT => by
      show CtxXJ (f :: rest) (Jk1.one X T)
      cases rest with
      | nil =>
          cases f with
          | fone _ => exact ⟨JkJ_of_CtxXJ _ X hX, hT⟩
          | fotw _ => exact ⟨⟨hX.1, hT⟩, hX.2⟩
      | cons g gs =>
          have hX' : CtxXJ (f :: g :: gs) X := hX
          rw [CtxXJ_cons] at hX'
          rw [CtxXJ_cons]
          exact CtxX_one (g :: gs) X T hX' hT

theorem JkJ_plug : ∀ (ctx : List Frm), CtxJ ctx → ∀ T : Jk1, CtxXJ ctx T → JkJ (plug ctx T)
  | [], _, _, hT => hT
  | (Frm.fone N :: rest), hc, T, hT => by
      refine ⟨hc.1, JkJ_plug rest hc.2 T ?_⟩
      cases rest with
      | nil => exact JkJ_of_CtxXJ _ T hT
      | cons g gs => rwa [CtxXJ_cons] at hT
  | (Frm.fotw N :: rest), hc, T, hT => absurd hc (by simp [CtxJ])

theorem JkOk_plug : ∀ (ctx : List Frm), CtxOk ctx → ∀ T : Jk1, CtxX ctx T → JkOk (plug ctx T)
  | [], _, _, hT => hT
  | (Frm.fone N :: rest), hc, T, hT => by
      have hT' : CtxXJ (Frm.fone N :: rest) T := hT
      have h2 := JkJ_plug (Frm.fone N :: rest) ⟨JkJ_of_JkOk N hc.1, hc.2⟩ T hT'
      exact ⟨hc.1, h2.2⟩
  | (Frm.fotw N :: rest), hc, T, hT => absurd hc (by simp [CtxOk])

theorem CtxJ_snoc : ∀ (ctx : List Frm) (X : Jk1), CtxJ ctx → CtxXJ ctx X →
    CtxJ (ctx ++ [Frm.fone X])
  | [], X, _, hf => ⟨hf, trivial⟩
  | (Frm.fone N :: rest), X, hc, hf => by
      refine ⟨hc.1, CtxJ_snoc rest X hc.2 ?_⟩
      cases rest with
      | nil => exact JkJ_of_CtxXJ _ _ hf
      | cons g gs => rwa [CtxXJ_cons] at hf
  | (Frm.fotw N :: rest), X, hc, hf => absurd hc (by simp [CtxJ])

theorem CtxOk_snoc : ∀ (ctx : List Frm) (X : Jk1), CtxOk ctx → CtxX ctx X →
    CtxOk (ctx ++ [Frm.fone X])
  | [], X, _, hf => ⟨hf, trivial⟩
  | (Frm.fone N :: rest), X, hc, hf => by
      have hf' : CtxXJ (Frm.fone N :: rest) X := hf
      refine ⟨hc.1, CtxJ_snoc rest X hc.2 ?_⟩
      cases rest with
      | nil => exact JkJ_of_CtxXJ _ _ hf'
      | cons g gs => rwa [CtxXJ_cons] at hf'
  | (Frm.fotw N :: rest), X, hc, hf => absurd hc (by simp [CtxOk])

/-! ### 字と語の基本補題 -/

theorem colJ_shift (a b s : ℕ) (N : Jk1) : shiftr01 s 0 (colJ a b N) = colJ (a + s) b N := by
  rw [colJ, show ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ) :: jk1 (a + 1) N
      = [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] ++ jk1 (a + 1) N from rfl,
    shiftr01_append0, shift_zcol, jk1_shift N (a + 1) s,
    show a + 1 + s = a + s + 1 from by omega]
  rfl

theorem wordJ_shift (a b s : ℕ) (ws : List Jk1) :
    shiftr01 s 0 (wordJ a b ws) = wordJ (a + s) b ws := by
  induction ws with
  | nil => simp [wordJ, shiftr01]
  | cons N ws ih =>
      simp only [wordJ, List.flatMap_cons] at *
      rw [shiftr01_append0, colJ_shift, ih]

theorem colJ_ge (a b : ℕ) (N : Jk1) : ∀ x ∈ colJ a b N, a + 1 ≤ x.1 := by
  intro x hx
  simp only [colJ, List.mem_cons] at hx
  rcases hx with rfl | h
  · exact le_refl _
  · have := jk1_ge N (a + 1) x h; omega

theorem wordJ_ge (a b : ℕ) (ws : List Jk1) : ∀ x ∈ wordJ a b ws, a + 1 ≤ x.1 := by
  intro x hx
  simp only [wordJ, List.mem_flatMap] at hx
  obtain ⟨N, -, hx⟩ := hx
  exact colJ_ge a b N x hx

theorem colJ_mono {a b : ℕ} {N : Jk1} (hN : JkJ N) : Mono (colJ a b N) := by
  intro x hx
  simp only [colJ, List.mem_cons] at hx
  rcases hx with rfl | h
  · show 1 ≤ b + 1; omega
  · exact jk1_mono N (JkA_of_JkJ N hN) (a + 1) x h

theorem wordJ_mono {a b : ℕ} {ws : List Jk1} (hw : WOk ws) : Mono (wordJ a b ws) := by
  intro x hx
  simp only [wordJ, List.mem_flatMap] at hx
  obtain ⟨N, hN, hx⟩ := hx
  exact colJ_mono (JkJ_of_JkOk N (hw N hN)) x hx

theorem wordJ_nil (a b : ℕ) : wordJ a b [] = [] := rfl

theorem wordJ_append (a b : ℕ) (ws1 ws2 : List Jk1) :
    wordJ a b (ws1 ++ ws2) = wordJ a b ws1 ++ wordJ a b ws2 := by simp [wordJ]

theorem wordJ_singleton (a b : ℕ) (N : Jk1) : wordJ a b [N] = colJ a b N := by simp [wordJ]

theorem wordJ_cons (a b : ℕ) (N : Jk1) (ws : List Jk1) :
    wordJ a b (N :: ws) = colJ a b N ++ wordJ a b ws := by simp [wordJ]

theorem colJ_ne (a b : ℕ) (N : Jk1) : colJ a b N ≠ [] := by simp [colJ]

theorem MidD_wordJ (a v : ℕ) (ha : 1 ≤ a) (hv : 1 ≤ v) {ws : List Jk1} (hw : WOk ws) :
    MidD (a + 1) (((a, v, 0) : ℕ × ℕ × ℕ) :: wordJ a v ws) := by
  have h := MidD_append (MidD_col a v ha hv) (N := wordJ a v ws) (wordJ_ge a v ws) (wordJ_mono hw)
  simpa using h

#print axioms MidD_wordJ


/-! ### 木の junk には行 1 の鎖が入れない -/

theorem entry_cons_succ (c : ℕ × ℕ × ℕ) (L : TrioSeq) (r u : ℕ) :
    entry (c :: L) r (u + 1) = entry L r u := by
  simp [entry, List.getD_cons_succ]

theorem entry_append_at (A T : TrioSeq) (i : ℕ) : entry (A ++ T) i A.length = entry T i 0 := by
  simpa using entry_append_right A T i 0

theorem jk1_length_pay (l : ℕ) (N : Jk1) (Y : TrioSeq) :
    (jk1 l (Jk1.pay N Y)).length = (jk1 l N).length + Y.length := by
  simp [jk1, shiftr01]

theorem jk1_length_one (l : ℕ) (N M : Jk1) :
    (jk1 l (Jk1.one N M)).length = (jk1 l N).length + 1 + (jk1 (l + 1) M).length := by
  simp [jk1]; omega

/-- `p` と `q0` の間に、高さ `l` の 1 の列 `r` があり、その右は `q0` まで高さ ≥ `l+1`。 -/
def Grd (M : TrioSeq) (p q0 l : ℕ) : Prop :=
  ∃ r v, p < r ∧ r < q0 ∧ entry M 1 r = 1 ∧ entry M 0 r = v ∧ v ≤ l ∧
    (∀ j, r < j → j < q0 → v + 1 ≤ entry M 0 j)

/-- 1 の列（高さ `l`）の右にある 2 の記録は、行 1 が 1 以上の列の子孫にならない。
`nextrel1` の最小性に 1 の列を入れると `2 ≤ 1` になる。 -/
theorem not_le1_two {M : TrioSeq} {p r q l : ℕ}
    (hp1 : 1 ≤ entry M 1 p) (hpr : p < r) (hr1 : entry M 1 r = 1) (hr0 : entry M 0 r = l)
    (hrq : r < q) (hq1 : entry M 1 q = 2)
    (hge : ∀ j, r < j → j ≤ q → l + 1 ≤ entry M 0 j) : ¬ le1 M p q := by
  rintro ⟨hpl, hql, hch⟩
  rcases Relation.ReflTransGen.cases_tail hch with h1 | ⟨c, hc1, hc2⟩
  · omega
  · rcases eq_or_ne c p with rfl | hne
    · have hle0r : le0 M r q := le0_of_between hr0 q hrq hql hge
      have h5 := hc2.2.2.2.2.2 r ⟨hpr, hle0r⟩
      omega
    · have hlepc : le1 M p c := ⟨hpl, hc2.1, hc1⟩
      have h3 := le1_row1_lt hlepc (Ne.symm hne)
      have h4 := hc2.2.2.2.1
      omega

#print axioms not_le1_two

/-- ★ 記録（行 1 が 1 以上）から、木の junk の列へは行 1 の鎖が届かない。
2 の記録を含む木では、その左に高さ `l` の 1 の列があること（`Grd`）が要る。 -/
theorem not_le1_jk1 : ∀ (N : Jk1) (M : TrioSeq) (p q0 l : ℕ),
    (JkOk N ∨ (JkA N ∧ Grd M p q0 l)) →
    1 ≤ entry M 1 p → p < q0 → q0 + (jk1 l N).length ≤ M.length →
    (∀ (r t : ℕ), t < (jk1 l N).length → entry M r (q0 + t) = entry (jk1 l N) r t) →
    ∀ t, t < (jk1 l N).length → ¬ le1 M p (q0 + t)
  | Jk1.nil, M, p, q0, l, _, _, _, _, _ => by simp [jk1]
  | Jk1.pay N Y, M, p, q0, l, hN, hp1, hpq, hlen, hent => by
      have hY : Bok Y := by rcases hN with h | ⟨h, -⟩ <;> exact h.2
      have hNs : JkOk N ∨ (JkA N ∧ Grd M p q0 l) := by
        rcases hN with h | ⟨h, hg⟩
        · exact Or.inl h.1
        · exact Or.inr ⟨h.1, hg⟩
      have hlenp : (jk1 l (Jk1.pay N Y)).length = (jk1 l N).length + Y.length :=
        jk1_length_pay l N Y
      have hsplit : jk1 l (Jk1.pay N Y) = jk1 l N ++ shiftr01 (l + 1) 0 Y := rfl
      intro t ht
      rcases Nat.lt_or_ge t (jk1 l N).length with htL | htL
      · refine not_le1_jk1 N M p q0 l hNs hp1 hpq (by omega) ?_ t htL
        intro r u hu
        have h := hent r u (by omega)
        rwa [hsplit, entry_append_left (by omega)] at h
      · obtain ⟨u, hu, rfl⟩ : ∃ u, u < Y.length ∧ t = (jk1 l N).length + u :=
          ⟨t - (jk1 l N).length, by omega, by omega⟩
        have eblk : ∀ r u', u' < Y.length →
            entry M r (q0 + ((jk1 l N).length + u'))
              = entry (shiftr01 (l + 1) 0 Y) r u' := by
          intro r u' hu'
          have h := hent r ((jk1 l N).length + u') (by omega)
          rwa [hsplit, entry_append_right] at h
        have eblk' : ∀ r u', u' < Y.length →
            entry M r (q0 + (jk1 l N).length + u')
              = entry (shiftr01 (l + 1) 0 Y) r u' := by
          intro r u' hu'
          rw [show q0 + (jk1 l N).length + u' = q0 + ((jk1 l N).length + u') from by omega]
          exact eblk r u' hu'
        have hroot := block_root (M := M) (s := q0 + (jk1 l N).length)
          (e := q0 + (jk1 l N).length + Y.length) (d := l + 1) (by omega)
          (by have h := eblk' 0 0 (by omega)
              rw [Nat.add_zero] at h
              rw [h, entry0_shiftr01 (by omega : 0 < Y.length), hY.root]
              omega)
          (by intro j hj1 hj2
              obtain ⟨u', hu', rfl⟩ : ∃ u', u' < Y.length ∧ j = q0 + (jk1 l N).length + u' :=
                ⟨j - (q0 + (jk1 l N).length), by omega, by omega⟩
              rw [eblk' 0 u' hu', entry0_shiftr01 hu']; omega)
          (by intro j hj1 hj2 hd
              obtain ⟨u', hu', rfl⟩ : ∃ u', u' < Y.length ∧ j = q0 + (jk1 l N).length + u' :=
                ⟨j - (q0 + (jk1 l N).length), by omega, by omega⟩
              rw [eblk' 0 u' hu', entry0_shiftr01 hu'] at hd
              rw [eblk' 1 u' hu', entry1_shiftr01]
              exact (Zroot_entry hY.zroot (by omega)).1)
        intro hle
        have hle' : le1 M p (q0 + (jk1 l N).length + u) := by
          rwa [show q0 + (jk1 l N).length + u = q0 + ((jk1 l N).length + u) from by omega]
        have := le1_lower_bound hroot p (q0 + (jk1 l N).length + u) hle' (by omega) (by omega)
        omega
  | Jk1.one N M', M, p, q0, l, hN, hp1, hpq, hlen, hent => by
      have hNs : JkOk N ∨ (JkA N ∧ Grd M p q0 l) := by
        rcases hN with h | ⟨h, hg⟩
        · exact Or.inl h.1
        · exact Or.inr ⟨h.1, hg⟩
      have hJM' : JkA M' := by
        rcases hN with h | ⟨h, -⟩
        · exact JkA_of_JkJ M' h.2
        · exact h.2
      have hlenp : (jk1 l (Jk1.one N M')).length
          = (jk1 l N).length + 1 + (jk1 (l + 1) M').length := jk1_length_one l N M'
      have hsplit : jk1 l (Jk1.one N M')
          = jk1 l N ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) M') := rfl
      have e1 : entry M 1 (q0 + (jk1 l N).length) = 1 := by
        have h := hent 1 (jk1 l N).length (by omega)
        rw [hsplit, entry_append_at] at h
        rw [h]; simp [entry]
      have e0 : entry M 0 (q0 + (jk1 l N).length) = l + 1 := by
        have h := hent 0 (jk1 l N).length (by omega)
        rw [hsplit, entry_append_at] at h
        rw [h]; simp [entry]
      intro t ht
      rcases Nat.lt_or_ge t (jk1 l N).length with htL | htL
      · refine not_le1_jk1 N M p q0 l hNs hp1 hpq (by omega) ?_ t htL
        intro r u hu
        have h := hent r u (by omega)
        rwa [hsplit, entry_append_left (by omega)] at h
      rcases Nat.lt_or_ge t ((jk1 l N).length + 1) with htL1 | htL1
      · have ht0 : t = (jk1 l N).length := by omega
        subst ht0
        intro hle
        have := le1_row1_lt hle (by omega)
        rw [e1] at this
        omega
      · obtain ⟨u, hu, rfl⟩ : ∃ u, u < (jk1 (l + 1) M').length ∧ t = (jk1 l N).length + 1 + u :=
          ⟨t - ((jk1 l N).length + 1), by omega, by omega⟩
        have hsub : ∀ (r u' : ℕ), u' < (jk1 (l + 1) M').length →
            entry M r (q0 + (jk1 l N).length + 1 + u') = entry (jk1 (l + 1) M') r u' := by
          intro r u' hu'
          have h := hent r ((jk1 l N).length + (u' + 1)) (by omega)
          rw [hsplit, entry_append_right, entry_cons_succ] at h
          rw [show q0 + (jk1 l N).length + 1 + u' = q0 + ((jk1 l N).length + (u' + 1)) from
            by omega]
          exact h
        have hgrd : Grd M p (q0 + (jk1 l N).length + 1) (l + 1) :=
          ⟨q0 + (jk1 l N).length, l + 1, by omega, by omega, e1, e0, le_refl _,
            by intro j hj1 hj2; omega⟩
        have hres := not_le1_jk1 M' M p (q0 + (jk1 l N).length + 1) (l + 1)
          (Or.inr ⟨hJM', hgrd⟩) hp1 (by omega) (by omega) hsub u hu
        rwa [show q0 + ((jk1 l N).length + 1 + u) = q0 + (jk1 l N).length + 1 + u from by omega]
  | Jk1.two N M', M, p, q0, l, hN, hp1, hpq, hlen, hent => by
      obtain ⟨⟨hJN, hJM⟩, r, v, hpr, hrq0, hr1, hr0, hvl, hrge⟩ :
          (JkA N ∧ JkA M') ∧ Grd M p q0 l := by
        rcases hN with h | ⟨h, hg⟩
        · exact absurd h (by simp [JkOk])
        · exact ⟨h, hg⟩
      have hsplit : jk1 l (Jk1.two N M')
          = jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) M') := rfl
      have hlenp : (jk1 l (Jk1.two N M')).length
          = (jk1 l N).length + 1 + (jk1 (l + 1) M').length := by
        rw [hsplit]; simp; omega
      have hge : ∀ j, q0 ≤ j → j < q0 + (jk1 l (Jk1.two N M')).length →
          l + 1 ≤ entry M 0 j := by
        intro j hj1 hj2
        obtain ⟨u, hu, rfl⟩ : ∃ u, u < (jk1 l (Jk1.two N M')).length ∧ j = q0 + u :=
          ⟨j - q0, by omega, by omega⟩
        rw [hent 0 u hu]
        exact entry0_of_ge (jk1_ge (Jk1.two N M') l) u hu
      intro t ht
      rcases Nat.lt_or_ge t (jk1 l N).length with htL | htL
      · refine not_le1_jk1 N M p q0 l
          (Or.inr ⟨hJN, ⟨r, v, hpr, hrq0, hr1, hr0, hvl, hrge⟩⟩)
          hp1 hpq (by omega) ?_ t htL
        intro i u hu
        have h := hent i u (by omega)
        rwa [hsplit, entry_append_left (by omega)] at h
      rcases Nat.lt_or_ge t ((jk1 l N).length + 1) with htL1 | htL1
      · have ht0 : t = (jk1 l N).length := by omega
        subst ht0
        have hq1 : entry M 1 (q0 + (jk1 l N).length) = 2 := by
          have h := hent 1 (jk1 l N).length (by omega)
          rw [hsplit, entry_append_at] at h
          rw [h]; simp [entry]
        refine not_le1_two hp1 hpr hr1 hr0 (by omega) hq1 ?_
        intro j hj1 hj2
        rcases Nat.lt_or_ge j q0 with hjq | hjq
        · exact hrge j hj1 hjq
        · have := hge j hjq (by omega)
          omega
      · obtain ⟨u, hu, rfl⟩ : ∃ u, u < (jk1 (l + 1) M').length ∧
            t = (jk1 l N).length + 1 + u :=
          ⟨t - ((jk1 l N).length + 1), by omega, by omega⟩
        have hsub : ∀ (i u' : ℕ), u' < (jk1 (l + 1) M').length →
            entry M i (q0 + (jk1 l N).length + 1 + u') = entry (jk1 (l + 1) M') i u' := by
          intro i u' hu'
          have h := hent i ((jk1 l N).length + (u' + 1)) (by omega)
          rw [hsplit, entry_append_right, entry_cons_succ] at h
          rw [show q0 + (jk1 l N).length + 1 + u' = q0 + ((jk1 l N).length + (u' + 1)) from
            by omega]
          exact h
        have hgrd : Grd M p (q0 + (jk1 l N).length + 1) (l + 1) := by
          refine ⟨r, v, hpr, by omega, hr1, hr0, by omega, ?_⟩
          intro j hj1 hj2
          rcases Nat.lt_or_ge j q0 with hjq | hjq
          · exact hrge j hj1 hjq
          · have := hge j hjq (by omega)
            omega
        have hres := not_le1_jk1 M' M p (q0 + (jk1 l N).length + 1) (l + 1)
          (Or.inr ⟨hJM, hgrd⟩) hp1 (by omega) (by omega) hsub u hu
        rwa [show q0 + ((jk1 l N).length + 1 + u) = q0 + (jk1 l N).length + 1 + u from by omega]

#print axioms not_le1_jk1


/-! ### 木の字の語の上の z の列の展開 -/

def MzJ (Y0 : TrioSeq) (a b : ℕ) (ws : List Jk1) : TrioSeq :=
  Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordJ a b ws ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)])

theorem colJ_length (a b : ℕ) (N : Jk1) : (colJ a b N).length = (jk1 (a + 1) N).length + 1 := by
  simp [colJ]

theorem entry_MzJ_p (Y0 : TrioSeq) (a b : ℕ) (ws : List Jk1) (r : ℕ) :
    entry (MzJ Y0 a b ws) r Y0.length = entry [((a, b, 0) : ℕ × ℕ × ℕ)] r 0 := by
  rw [MzJ, entry_append_at]
  simp [entry]

theorem entry_MzJ_word (Y0 : TrioSeq) (a b : ℕ) (ws : List Jk1) (r i : ℕ)
    (hi : i < (wordJ a b ws).length) :
    entry (MzJ Y0 a b ws) r (Y0.length + 1 + i) = entry (wordJ a b ws) r i := by
  have e : MzJ Y0 a b ws = (Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)]) ++
      (wordJ a b ws ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]) := by
    simp [MzJ]
  rw [e, show Y0.length + 1 + i = (Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)]).length + i from by
      simp only [List.length_append, List.length_singleton],
    entry_append_right, entry_append_left hi]

theorem entry_wordJ_pos (Y0 : TrioSeq) (a b : ℕ) (ws1 ws3 : List Jk1) (N : Jk1) (r t : ℕ)
    (ht : t < (colJ a b N).length) :
    entry (MzJ Y0 a b (ws1 ++ N :: ws3)) r (Y0.length + 1 + (wordJ a b ws1).length + t)
      = entry (colJ a b N) r t := by
  have e : MzJ Y0 a b (ws1 ++ N :: ws3)
      = (Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)] ++ wordJ a b ws1) ++
        (colJ a b N ++ (wordJ a b ws3 ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)])) := by
    simp [MzJ, wordJ_append, wordJ_cons, List.append_assoc]
  rw [e, show Y0.length + 1 + (wordJ a b ws1).length + t
      = (Y0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)] ++ wordJ a b ws1).length + t from by
        simp only [List.length_append, List.length_singleton],
    entry_append_right, entry_append_left ht]

theorem entry_wordJ_ge (a b : ℕ) (ws : List Jk1) {i : ℕ}
    (hi : i < (wordJ a b ws).length) : a + 1 ≤ entry (wordJ a b ws) 0 i := by
  have := wordJ_ge a b ws _ (List.getElem_mem hi)
  have he : entry (wordJ a b ws) 0 i = ((wordJ a b ws)[i]).1 := by
    simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  omega

theorem MzJ_length (Y0 : TrioSeq) (a b : ℕ) (ws : List Jk1) :
    (MzJ Y0 a b ws).length = Y0.length + 1 + (wordJ a b ws).length + 1 := by
  simp [MzJ]; omega

/-- 字の先頭（z の列）は記録の行 1 の子。 -/
theorem le1_zposJ (Y0 : TrioSeq) (a b : ℕ) (ws1 ws3 : List Jk1) (N : Jk1) :
    le1 (MzJ Y0 a b (ws1 ++ N :: ws3)) Y0.length
      (Y0.length + 1 + (wordJ a b ws1).length) := by
  set M := MzJ Y0 a b (ws1 ++ N :: ws3) with hM
  set q := Y0.length + 1 + (wordJ a b ws1).length with hq
  have hlenw : (wordJ a b (ws1 ++ N :: ws3)).length
      = (wordJ a b ws1).length + (colJ a b N).length + (wordJ a b ws3).length := by
    rw [wordJ_append, wordJ_cons, List.length_append, List.length_append]
    omega
  have hlen : M.length = Y0.length + 1 + (wordJ a b (ws1 ++ N :: ws3)).length + 1 := by
    rw [hM, MzJ_length]
  have hcl : 0 < (colJ a b N).length := by rw [colJ_length]; omega
  have hql : q < M.length := by omega
  have e0p : entry M 0 Y0.length = a := by rw [hM, entry_MzJ_p]; simp [entry]
  have e1p : entry M 1 Y0.length = b := by rw [hM, entry_MzJ_p]; simp [entry]
  have eq0 : entry M 0 q = a + 1 := by
    have h := entry_wordJ_pos Y0 a b ws1 ws3 N 0 0 hcl
    rw [hM, hq, Nat.add_zero] at *
    rw [h]; simp [colJ, entry]
  have eq1 : entry M 1 q = b + 1 := by
    have h := entry_wordJ_pos Y0 a b ws1 ws3 N 1 0 hcl
    rw [hM, hq, Nat.add_zero] at *
    rw [h]; simp [colJ, entry]
  have hge : ∀ j', Y0.length < j' → j' ≤ q → a + 1 ≤ entry M 0 j' := by
    intro j' h1 h2
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < (wordJ a b (ws1 ++ N :: ws3)).length ∧ j' = Y0.length + 1 + i :=
      ⟨j' - (Y0.length + 1), by omega, by omega⟩
    rw [hM, entry_MzJ_word Y0 a b _ 0 i hi]
    exact entry_wordJ_ge a b _ hi
  have hl0 : le0 M Y0.length q := le0_of_between e0p q (by omega) hql hge
  refine ⟨by omega, hql, Relation.ReflTransGen.single ?_⟩
  refine ⟨by omega, hql, by omega, by rw [e1p, eq1]; omega, hl0, ?_⟩
  intro j hj
  have := le0_eq_of_min hj.1 hj.2 eq0 (fun j'' h1 h2 => hge j'' h1 (by omega))
  subst this; exact le_rfl

/-- 字の junk（木）の列は記録の行 1 の子孫ではない。 -/
theorem not_le1_treeJ (Y0 : TrioSeq) (a b : ℕ) (hb : 1 ≤ b) (ws1 ws3 : List Jk1)
    {N : Jk1} (hN : JkOk N) (t : ℕ) (ht : t < (jk1 (a + 1) N).length) :
    ¬ le1 (MzJ Y0 a b (ws1 ++ N :: ws3)) Y0.length
      (Y0.length + 1 + (wordJ a b ws1).length + (t + 1)) := by
  set M := MzJ Y0 a b (ws1 ++ N :: ws3) with hM
  set q0 := Y0.length + 1 + (wordJ a b ws1).length + 1 with hq0
  have hlenw : (wordJ a b (ws1 ++ N :: ws3)).length
      = (wordJ a b ws1).length + (colJ a b N).length + (wordJ a b ws3).length := by
    rw [wordJ_append, wordJ_cons, List.length_append, List.length_append]
    omega
  have hlen : M.length = Y0.length + 1 + (wordJ a b (ws1 ++ N :: ws3)).length + 1 := by
    rw [hM, MzJ_length]
  have hcl : (colJ a b N).length = (jk1 (a + 1) N).length + 1 := colJ_length a b N
  have hp1 : 1 ≤ entry M 1 Y0.length := by
    rw [hM, entry_MzJ_p]; simpa [entry] using hb
  have hent : ∀ (r u : ℕ), u < (jk1 (a + 1) N).length →
      entry M r (q0 + u) = entry (jk1 (a + 1) N) r u := by
    intro r u hu
    have h := entry_wordJ_pos Y0 a b ws1 ws3 N r (u + 1) (by omega)
    rw [colJ, entry_cons_succ] at h
    rw [hM, hq0, show Y0.length + 1 + (wordJ a b ws1).length + 1 + u
      = Y0.length + 1 + (wordJ a b ws1).length + (u + 1) from by omega]
    exact h
  have := not_le1_jk1 N M Y0.length q0 (a + 1) (Or.inl hN) hp1 (by omega) (by omega) hent t ht
  rwa [hq0, show Y0.length + 1 + (wordJ a b ws1).length + 1 + t
    = Y0.length + 1 + (wordJ a b ws1).length + (t + 1) from by omega] at this

#print axioms not_le1_treeJ


/-! ### 木の字の上昇 -/

theorem jk1_length_shift (N : Jk1) (l s : ℕ) :
    (jk1 (l + s) N).length = (jk1 l N).length := by
  rw [← jk1_shift N l s]; simp [shiftr01]

theorem rise_colJ (a b k : ℕ) (N : Jk1) (P : ℕ → Prop) [DecidablePred P]
    (hP0 : P 0) (hP : ∀ t, 1 ≤ t → t < (colJ a b N).length → ¬ P t) :
    (List.range (colJ a b N).length).map (fun t =>
      ((entry (colJ a b N) 0 t + k, entry (colJ a b N) 1 t + (if P t then k else 0),
        entry (colJ a b N) 2 t) : ℕ × ℕ × ℕ)) = colJ (a + k) (b + k) N := by
  have hJ : jk1 (a + k + 1) N = shiftr01 k 0 (jk1 (a + 1) N) := by
    rw [jk1_shift N (a + 1) k, show a + 1 + k = a + k + 1 from by omega]
  have hlen : (colJ (a + k) (b + k) N).length = (colJ a b N).length := by
    rw [colJ_length, colJ_length, hJ]; simp [shiftr01]
  apply List.ext_getElem?
  intro i
  rcases Nat.lt_or_ge i (colJ a b N).length with hi | hi
  · rw [List.getElem?_map, List.getElem?_range hi]
    simp only [Option.map_some]
    match i, hi with
    | 0, _ =>
        rw [if_pos hP0]
        simp [colJ, entry]
        omega
    | (u + 1), hu =>
        have hu' : u < (jk1 (a + 1) N).length := by rw [colJ_length] at hu; omega
        rw [if_neg (hP (u + 1) (by omega) hu), Nat.add_zero]
        show some ((entry (colJ a b N) 0 (u + 1) + k, entry (colJ a b N) 1 (u + 1),
          entry (colJ a b N) 2 (u + 1)) : ℕ × ℕ × ℕ) = _
        rw [show colJ a b N = ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ) :: jk1 (a + 1) N from rfl,
          entry_cons_succ, entry_cons_succ, entry_cons_succ,
          show colJ (a + k) (b + k) N
            = ((a + k + 1, b + k + 1, 1) : ℕ × ℕ × ℕ) :: jk1 (a + k + 1) N from rfl,
          List.getElem?_cons_succ, hJ, shiftr01, List.getElem?_map,
          List.getElem?_eq_getElem hu']
        simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu']
  · rw [List.getElem?_eq_none (by simpa using hi), List.getElem?_eq_none (by omega)]

open Classical in
theorem rise_wordJ (Y0 : TrioSeq) (a b k : ℕ) (hb : 1 ≤ b) {ws : List Jk1} (hw : WOk ws) :
    ∀ (ws2 ws1 ws3 : List Jk1), ws = ws1 ++ ws2 ++ ws3 →
      (List.range (wordJ a b ws2).length).map (fun i =>
        ((entry (wordJ a b ws2) 0 i + k, entry (wordJ a b ws2) 1 i +
          (if le1 (MzJ Y0 a b ws) Y0.length (Y0.length + 1 + (wordJ a b ws1).length + i)
            then k else 0), entry (wordJ a b ws2) 2 i) : ℕ × ℕ × ℕ))
      = wordJ (a + k) (b + k) ws2
  | [], _, _, _ => by simp [wordJ]
  | (N :: ws2), ws1, ws3, hws => by
      have hws' : ws = (ws1 ++ [N]) ++ ws2 ++ ws3 := by rw [hws]; simp
      have hws'' : ws = ws1 ++ N :: (ws2 ++ ws3) := by rw [hws]; simp
      have hN : JkOk N := hw N (by rw [hws]; simp)
      have ih := rise_wordJ Y0 a b k hb hw ws2 (ws1 ++ [N]) ws3 hws'
      rw [wordJ_cons, wordJ_cons, List.length_append, List.range_add, List.map_append,
        List.map_map]
      congr 1
      · rw [← rise_colJ a b k N (fun t => le1 (MzJ Y0 a b ws) Y0.length
            (Y0.length + 1 + (wordJ a b ws1).length + t))
            (by rw [hws'']; simpa using le1_zposJ Y0 a b ws1 (ws2 ++ ws3) N)
            (by intro t ht1 ht
                obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
                rw [hws'']
                refine not_le1_treeJ Y0 a b hb ws1 (ws2 ++ ws3) hN u ?_
                rw [colJ_length] at ht; omega)]
        apply List.map_congr_left
        intro t ht
        rw [List.mem_range] at ht
        rw [entry_append_left ht, entry_append_left ht, entry_append_left ht]
      · rw [← ih]
        apply List.map_congr_left
        intro i hi
        simp only [Function.comp]
        rw [entry_append_right, entry_append_right, entry_append_right, wordJ_append,
          wordJ_singleton, List.length_append,
          show Y0.length + 1 + (wordJ a b ws1).length + ((colJ a b N).length + i)
            = Y0.length + 1 + ((wordJ a b ws1).length + (colJ a b N).length) + i from by omega]

open Classical in
/-- ★ 木の字の語の上の z の列の展開: 記録と語の対角の塔。 -/
theorem oper_z1wJ (Y0 : TrioSeq) (a b : ℕ) (hb : 1 ≤ b) {ws : List Jk1}
    (hw : WOk ws) (n : ℕ) :
    (Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordJ a b ws ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]))⟦n⟧
      = Y0 ++ Dzf (fun a b => wordJ a b ws) a b n := by
  rw [oper_z1_mask Y0 a b (wordJ a b ws) (wordJ_ge a b ws) n]
  congr 1
  apply List.flatMap_congr
  intro k _
  congr 1
  have := rise_wordJ Y0 a b k hb hw ws [] [] (by simp)
  simpa [wordJ, MzJ] using this

theorem z1wJ_mem {Y0 : TrioSeq} {a b : ℕ} (hb : 1 ≤ b) {ws : List Jk1} (hw : WOk ws)
    (htw : ∀ n, Y0 ++ Dzf (fun a b => wordJ a b ws) a b n ∈ W 0) :
    Y0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordJ a b ws ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)])
      ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  rw [oper_z1wJ Y0 a b hb hw]
  exact htw n

#print axioms z1wJ_mem


/-! ### 木の字の語の普遍性の骨組み -/

theorem colJ_nil (a b : ℕ) : colJ a b Jk1.nil = [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)] := rfl

theorem GoodFb_of_keyJ {ws : List Jk1} (hw : WOk ws)
    {new : ℕ → List Jk1}
    (hnew : ∀ n, 1 ≤ n → GoodFb (fun a b => wordJ a b (new n)))
    (key : ∀ (Z : TrioSeq) (a b : ℕ), 1 ≤ b →
      (∀ n, 1 ≤ n → Z ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordJ a b (new n)) ∈ W 0) →
      Z ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordJ a b ws) ∈ W 0) :
    GoodFb (fun a b => wordJ a b ws) where
  ge := fun a b => wordJ_ge a b ws
  mono := fun a b => wordJ_mono hw
  shift := fun a b s => wordJ_shift a b s ws
  pu := by
    intro y c hy
    refine ⟨fun x hx => by have := wordJ_ge (c + 1) (y + 1) ws x hx; omega, wordJ_mono hw, ?_⟩
    intro E hE t Z hZ
    rw [wordJ_shift]
    have h := key Z (c + 1 + t) (y + 1) (by omega) (fun n hn => by
      have hP : PU y (c + 1 + t) (Z ++ ([((c + 1 + t, y + 1, 0) : ℕ × ℕ × ℕ)] ++
          wordJ (c + 1 + t) (y + 1) (new n))) :=
        ⟨E, c + t, Z, _, hE, by omega, hZ, by rw [show c + t + 1 = c + 1 + t from by omega],
          (hnew n hn).pu y (c + t) hy⟩
      simpa using ((BaseOk_PU y).aok _ _ hP).mem)
    simpa using h
  pk := by
    intro c E hI
    refine ⟨fun x hx => by have := wordJ_ge (c + 1) 2 ws x hx; omega, wordJ_mono hw, ?_⟩
    intro j t X hX
    rw [wordJ_shift]
    have h := key X (c + 1 + t) 2 (by omega) (fun n hn => by
      have hP : PkGA (c + 1 + t) (X ++ ([((c + 1 + t, 2, 0) : ℕ × ℕ × ℕ)] ++
          wordJ (c + 1 + t) 2 (new n))) :=
        ⟨E, hI, j, c + t, X, _, by omega, hX, by rw [show c + t + 1 = c + 1 + t from by omega],
          (hnew n hn).pk (c + t)⟩
      simpa using (PkGA_Aok hP).mem)
    simpa using h
  seg := by
    intro h
    have hmid : MidD (h + 2) (((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordJ (h + 1) 1 ws) := by
      have h1 := MidD_wordJ (h + 1) 1 (by omega) (by omega) hw
      simpa [show h + 1 + 1 = h + 2 from by omega] using h1
    refine ⟨hmid, by simp [entry], ?_⟩
    intro P hP s A' hA'
    rw [show ((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordJ (h + 1) 1 ws
        = [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ wordJ (h + 1) 1 ws from rfl,
      shiftr01_append0, shift_col, wordJ_shift]
    have hk := key A' (h + 1 + s) 1 (by omega) (fun n hn => by
      have hR : RunA 0 (h + s + 1) (A' ++ (((h + s + 1, 1, 0) : ℕ × ℕ × ℕ) ::
          wordJ (h + s + 1) 1 (new n))) :=
        ⟨h + s, A', _, rfl, rfl, ⟨P, hP, hA'⟩, (hnew n hn).seg (h + s)⟩
      have := ((BaseOk_RunA 0).aok _ _ hR).mem
      simpa [show h + s + 1 = h + 1 + s from by omega] using this)
    simpa using hk

/-- 木の字の語はすべて空なら junk も空。 -/
theorem GoodFb_wordJ_nil : GoodFb (fun a b => wordJ a b []) :=
  ⟨fun a b => by simp [wordJ_nil], fun a b => by simp [wordJ_nil, Mono],
    fun a b s => by simp [wordJ_nil, shiftr01],
    fun y c hy => by simpa [wordJ_nil] using JkU_nil' hy c,
    fun c => by simpa [wordJ_nil] using JkGU_nil c,
    fun h => by simpa [wordJ_nil] using SegA_one h⟩

/-- 場合 (iv): 語の最後に裸の z を継ぐ。 -/
theorem GoodFb_snoczJ {ws : List Jk1} (hw : WOk ws)
    (hG : GoodFb (fun a b => wordJ a b ws)) :
    GoodFb (fun a b => wordJ a b (ws ++ [Jk1.nil])) where
  ge := fun a b => wordJ_ge a b _
  mono := fun a b => wordJ_mono (WOk_append hw (WOk_singleton JkOk_nil))
  shift := fun a b s => wordJ_shift a b s _
  pu := by
    intro y c hy
    refine ⟨fun x hx => by have := wordJ_ge (c + 1) (y + 1) _ x hx; omega,
      wordJ_mono (WOk_append hw (WOk_singleton JkOk_nil)), ?_⟩
    intro E hE t Z hZ
    rw [wordJ_shift, wordJ_append, wordJ_singleton, colJ_nil]
    have h := z1wJ_mem (Y0 := Z) (a := c + 1 + t) (b := y + 1) (by omega) hw
      (fun n => by
        have := Dzf_W hG hy hE (c := c + t) (by simpa using hZ) n
        simpa [show c + t + 1 = c + 1 + t from by omega] using this)
    simpa [List.append_assoc] using h
  pk := by
    intro c E hI
    refine ⟨fun x hx => by have := wordJ_ge (c + 1) 2 _ x hx; omega,
      wordJ_mono (WOk_append hw (WOk_singleton JkOk_nil)), ?_⟩
    intro j t X hX
    rw [wordJ_shift, wordJ_append, wordJ_singleton, colJ_nil]
    have h := z1wJ_mem (Y0 := X) (a := c + 1 + t) (b := 2) (by omega) hw
      (fun n => by
        have := Dzf_W_RunG hG hI (c := c + t) hX n
        simpa [show c + t + 1 = c + 1 + t from by omega] using this)
    simpa [List.append_assoc] using h
  seg := by
    intro h
    have hmid : MidD (h + 2) (((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordJ (h + 1) 1 (ws ++ [Jk1.nil])) := by
      have h1 := MidD_wordJ (h + 1) 1 (by omega) (by omega)
        (ws := ws ++ [Jk1.nil]) (WOk_append hw (WOk_singleton JkOk_nil))
      simpa [show h + 1 + 1 = h + 2 from by omega] using h1
    refine ⟨hmid, by simp [entry], ?_⟩
    intro P hP s A' hA'
    rw [show ((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordJ (h + 1) 1 (ws ++ [Jk1.nil])
        = [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ wordJ (h + 1) 1 (ws ++ [Jk1.nil]) from rfl,
      shiftr01_append0, shift_col, wordJ_shift, wordJ_append, wordJ_singleton, colJ_nil]
    have hz := z1wJ_mem (Y0 := A') (a := h + 1 + s) (b := 1) (by omega) hw
      (fun n => by
        have := Dzf_W_LwA hG (h := h + s) ⟨P, hP, hA'⟩ n
        simpa [show h + s + 1 = h + 1 + s from by omega] using this)
    simpa [List.append_assoc] using hz

#print axioms GoodFb_snoczJ


/-! ### 木の字を語に継げる: `GOK` -/

/-- 木 `T` は、どの良い語の右にも字として継げる。 -/
def GOK (T : Jk1) : Prop :=
  ∀ ws : List Jk1, WOk ws → GoodFb (fun a b => wordJ a b ws) →
    GoodFb (fun a b => wordJ a b (ws ++ [T]))

theorem colJ_pay (a b : ℕ) (Z : Jk1) (B : TrioSeq) :
    colJ a b (Jk1.pay Z B) = colJ a b Z ++ shiftr01 (a + 2) 0 B := rfl

theorem colJ_pay_nil (a b : ℕ) (Z : Jk1) : colJ a b (Jk1.pay Z []) = colJ a b Z := by
  simp [colJ_pay, shiftr01]

theorem colJ_snoc_zero (a b : ℕ) (Z : Jk1) (Y : TrioSeq) :
    colJ a b (Jk1.pay Z (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]))
      = colJ a b (Jk1.pay Z Y) ++ [((a + 2, 0, 0) : ℕ × ℕ × ℕ)] := by
  rw [colJ_pay, colJ_pay, shiftr01_append0, ← List.append_assoc]
  simp [shiftr01]

theorem entry_colJ_ge (a b : ℕ) (N : Jk1) : ∀ r, 1 ≤ r → r < (colJ a b N).length →
    a + 2 ≤ entry (colJ a b N) 0 r := by
  intro r hr1 hrl
  obtain ⟨u, rfl⟩ : ∃ u, r = u + 1 := ⟨r - 1, by omega⟩
  rw [colJ_length] at hrl
  rw [show colJ a b N = ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ) :: jk1 (a + 1) N from rfl,
    entry_cons_succ]
  have := entry0_of_ge (jk1_ge N (a + 1)) u (by omega)
  omega

theorem wordJ_replicate (a b : ℕ) (N : Jk1) : ∀ n : ℕ,
    wordJ a b (List.replicate n N) = (List.range n).flatMap fun _ => colJ a b N
  | 0 => by simp [wordJ]
  | (n + 1) => by
      rw [List.replicate_succ, wordJ_cons, wordJ_replicate a b N n, List.range_succ_eq_map,
        List.flatMap_cons]
      simp [List.flatMap_map]

/-- 語の右に同じ字を `n` 個継ぐ。 -/
theorem GoodFb_repJ {ws : List Jk1} (hw : WOk ws) {N : Jk1} (hN : JkOk N)
    (hstep : ∀ ws' : List Jk1, WOk ws' → GoodFb (fun a b => wordJ a b ws') →
      GoodFb (fun a b => wordJ a b (ws' ++ [N])))
    (hG : GoodFb (fun a b => wordJ a b ws)) :
    ∀ n : ℕ, GoodFb (fun a b => wordJ a b (ws ++ List.replicate n N))
  | 0 => by simpa using hG
  | (n + 1) => by
      have hwn : WOk (ws ++ List.replicate n N) := WOk_append hw (WOk_replicate hN n)
      have h := hstep (ws ++ List.replicate n N) hwn (GoodFb_repJ hw hN hstep hG n)
      have e : ws ++ List.replicate n N ++ [N] = ws ++ List.replicate (n + 1) N := by
        rw [List.append_assoc, ← List.replicate_succ']
      rwa [e] at h

/-- 場合 (i): 荷の末尾が非零。 -/
theorem GoodFb_snoc_innerJ {ws : List Jk1} (hw : WOk ws) {Z : Jk1} (hZ : JkOk Z) {Y : TrioSeq}
    (hY : Bok Y) (hlen : 2 ≤ Y.length)
    (hp : hasParent Y (srow Y (Y.length - 1)) (Y.length - 1))
    (hIH : ∀ n, 1 ≤ n → GoodFb (fun a b => wordJ a b (ws ++ [Jk1.pay Z (Y⟦n⟧)]))) :
    GoodFb (fun a b => wordJ a b (ws ++ [Jk1.pay Z Y])) := by
  refine GoodFb_of_keyJ (WOk_append hw (WOk_singleton ⟨hZ, hY⟩)) hIH ?_
  intro Z0 a b hb hn
  have e : ∀ B : TrioSeq, Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordJ a b (ws ++ [Jk1.pay Z B]))
      = (Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordJ a b (ws ++ [Z]))) ++ shiftr01 (a + 2) 0 B := by
    intro B
    rw [wordJ_append, wordJ_singleton, colJ_pay, wordJ_append, wordJ_singleton]
    simp [List.append_assoc]
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n hn'
  rw [e Y, oper_shift _ Y (a + 2) n hlen hp, ← e (Y⟦n⟧)]
  exact hn n hn'

/-- 場合 (ii): 荷の末尾が `(0,0,0)` なら、字が `n` 個に複製される。 -/
theorem GoodFb_snoc_dupJ {ws : List Jk1} (hw : WOk ws) {Z : Jk1} (hZ : JkOk Z) {Y : TrioSeq}
    (hY : Bok (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])) (hY' : Bok Y)
    (hIH : ∀ n, 1 ≤ n →
      GoodFb (fun a b => wordJ a b (ws ++ List.replicate n (Jk1.pay Z Y)))) :
    GoodFb (fun a b => wordJ a b (ws ++ [Jk1.pay Z (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])])) := by
  refine GoodFb_of_keyJ (WOk_append hw (WOk_singleton ⟨hZ, hY⟩)) hIH ?_
  intro Z0 a b hb hn
  have hhead : entry (colJ a b (Jk1.pay Z Y)) 0 0 < a + 2 := by
    show entry (((a + 1, b + 1, 1) : ℕ × ℕ × ℕ) :: _) 0 0 < a + 2
    simp [entry]
  have h := flat_mem'' (Y0 := Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordJ a b ws))
    (M := colJ a b (Jk1.pay Z Y)) (d := a + 2) (colJ_ne a b _) hhead
    (entry_colJ_ge a b (Jk1.pay Z Y))
    (fun n => by
      match n with
      | 0 =>
          have h1 := hn 1 (le_refl 1)
          rw [wordJ_append, wordJ_replicate] at h1
          simp only [List.range_one, List.flatMap_cons, List.flatMap_nil,
            List.append_nil] at h1
          have h2 := W_take (by
            rw [show Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: (wordJ a b ws ++ colJ a b (Jk1.pay Z Y)))
                = (Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordJ a b ws)) ++ colJ a b (Jk1.pay Z Y) from by
                  simp [List.append_assoc]] at h1
            exact h1) (Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordJ a b ws)).length
          rw [List.take_left] at h2
          simpa using h2
      | (n + 1) =>
          have h1 := hn (n + 1) (by omega)
          rw [wordJ_append, wordJ_replicate] at h1
          simpa [List.append_assoc] using h1)
  rw [wordJ_append, wordJ_singleton, colJ_snoc_zero]
  simpa [List.append_assoc] using h

#print axioms GoodFb_snoc_dupJ


theorem GOK_pay_nil {Z : Jk1} (h : GOK Z) : GOK (Jk1.pay Z []) := by
  intro ws hw hG
  have efun : (fun a b => wordJ a b (ws ++ [Jk1.pay Z []]))
      = (fun a b => wordJ a b (ws ++ [Z])) := by
    funext a b
    rw [wordJ_append, wordJ_append, wordJ_singleton, wordJ_singleton, colJ_pay_nil]
  rw [efun]
  exact h ws hw hG

/-- ★★★ 深さ 0（字の直下）に荷を継いでも良い。 -/
theorem AY0 : ∀ (Y : TrioSeq), Bok Y → ∀ (Z : Jk1), JkOk Z → GOK Z → GOK (Jk1.pay Z Y) := by
  have key : W 0 ⊆ {Y : TrioSeq | Bok Y → ∀ (Z : Jk1), JkOk Z → GOK Z → GOK (Jk1.pay Z Y)} := by
    refine A2' ?_
    intro Y hY
    simp only [Set.mem_setOf_eq]
    intro hYb Z hZ hGZ ws hw hG
    by_cases hshort : Y.length ≤ 1
    · rcases (by omega : Y.length = 0 ∨ Y.length = 1) with h0 | h1
      · have hnil0 : Y = [] := List.length_eq_zero_iff.mp h0
        subst hnil0
        exact GOK_pay_nil hGZ ws hw hG
      · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
        have hc0 : c.1 = 0 := hYb.root
        obtain ⟨hc1, hc2⟩ := hYb.zroot c (by simp) hc0
        have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1 hc2)
        subst hcz
        have e : ([((0, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq)
            = ([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by simp
        rw [e]
        refine GoodFb_snoc_dupJ hw hZ (by simpa using hYb) Bok_nil ?_
        intro n hn
        exact GoodFb_repJ hw (N := Jk1.pay Z ([] : TrioSeq)) ⟨hZ, Bok_nil⟩
          (fun ws' hw' hG' => GOK_pay_nil hGZ ws' hw' hG') hG n
    have hlen2 : 2 ≤ Y.length := by omega
    have hYne : Y ≠ [] := by intro hc; rw [hc] at hlen2; simp at hlen2
    rcases hY with ⟨hl, -⟩ | hnat | ⟨m, hm, -, -⟩
    · exact absurd hl hshort
    · by_cases hlast : entry Y 0 (Y.length - 1) = 0
      · obtain ⟨he1, he2⟩ := Zroot_entry hYb.zroot hlast
        have hcol : Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) = ((0, 0, 0) : ℕ × ℕ × ℕ) :=
          Prod.ext hlast (Prod.ext he1 he2)
        have hgl : Y.getLast hYne = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
          have h1 : Y.getLast hYne = Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
            rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show Y.length - 1 < Y.length by omega)]
            rfl
          rw [h1, hcol]
        have hsplit : Y = Y.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
          rw [← hgl]; exact (List.dropLast_append_getLast hYne).symm
        have hop : Y⟦1⟧ = Y.dropLast := by
          rw [oper_eq_pred_of_zero 1 (by omega) ⟨hlast, he1, he2⟩]
          unfold Pred
          rw [if_neg (by omega)]
        have hdl := hnat 1 le_rfl
        rw [hop] at hdl
        simp only [Set.mem_setOf_eq] at hdl
        have hdb : Bok Y.dropLast := Bok_dropLast hYb
        rw [hsplit]
        refine GoodFb_snoc_dupJ hw hZ (by rw [← hsplit]; exact hYb) hdb ?_
        intro n hn
        exact GoodFb_repJ hw (N := Jk1.pay Z Y.dropLast) ⟨hZ, hdb⟩
          (fun ws' hw' hG' => hdl hdb Z hZ hGZ ws' hw' hG') hG n
      · have hnz : ¬ (entry Y 0 (Y.length - 1) = 0 ∧ entry Y 1 (Y.length - 1) = 0 ∧
            entry Y 2 (Y.length - 1) = 0) := fun h => hlast h.1
        have hp := hasParent_of_ZrootMono hYb.zroot hYb.mono hYb.root hlen2 hnz
        refine GoodFb_snoc_innerJ hw hZ hYb hlen2 hp ?_
        intro n hn
        have := hnat n hn
        simp only [Set.mem_setOf_eq] at this
        exact this (Bok_oper hYb hn) Z hZ hGZ ws hw hG
    · exact absurd hm (Nat.not_lt_zero m)
  intro Y hYb Z hZ hGZ
  exact key hYb.mem hYb Z hZ hGZ

#print axioms AY0


/-! ### 背骨の文脈と木の分解 -/

theorem jk1_plug_one : ∀ (ctx : List Frm) (X T : Jk1) (l : ℕ),
    jk1 l (plug ctx (Jk1.one X T))
      = jk1 l (plug ctx X) ++
        (((l + dep ctx + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + dep ctx + 1) T)
  | [], X, T, l => by simp [plug, jk1, dep]
  | (Frm.fone N :: rest), X, T, l => by
      show jk1 l (Jk1.one N (plug rest (Jk1.one X T)))
        = jk1 l (Jk1.one N (plug rest X)) ++ _
      rw [jk1, jk1, jk1_plug_one rest X T (l + 1)]
      simp only [dep, List.cons_append, List.append_assoc]
      rw [show l + 1 + dep rest + 1 = l + (dep rest + 1) + 1 from by omega]
  | (Frm.fotw N :: rest), X, T, l => by
      show jk1 l N ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) ::
          (jk1 (l + 1) Jk1.nil ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ) ::
            jk1 (l + 2) (plug rest (Jk1.one X T))))) = _
      rw [jk1_plug_one rest X T (l + 2)]
      show _ = jk1 l N ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) ::
          (jk1 (l + 1) Jk1.nil ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ) ::
            jk1 (l + 2) (plug rest X)))) ++ _
      simp only [dep, jk1, List.nil_append, List.cons_append, List.append_assoc]
      rw [show l + 2 + dep rest + 1 = l + (dep rest + 2) + 1 from by omega]

theorem jk1_plug_congr : ∀ (ctx : List Frm) {T1 T2 : Jk1}, (∀ l, jk1 l T1 = jk1 l T2) →
    ∀ l, jk1 l (plug ctx T1) = jk1 l (plug ctx T2)
  | [], _, _, h, l => h l
  | (Frm.fone N :: rest), T1, T2, h, l => by
      show jk1 l (Jk1.one N (plug rest T1)) = jk1 l (Jk1.one N (plug rest T2))
      rw [jk1, jk1, jk1_plug_congr rest h (l + 1)]
  | (Frm.fotw N :: rest), T1, T2, h, l => by
      show jk1 l N ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) ::
          (jk1 (l + 1) Jk1.nil ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ) ::
            jk1 (l + 2) (plug rest T1)))) = _
      rw [jk1_plug_congr rest h (l + 2)]
      rfl

theorem GOK_congr {T1 T2 : Jk1} (h : ∀ l, jk1 l T1 = jk1 l T2) (hT : GOK T1) : GOK T2 := by
  intro ws hw hG
  have efun : (fun a b => wordJ a b (ws ++ [T2])) = (fun a b => wordJ a b (ws ++ [T1])) := by
    funext a b
    rw [wordJ_append, wordJ_append, wordJ_singleton, wordJ_singleton, colJ, colJ, h]
  rw [efun]
  exact hT ws hw hG

theorem JkOk_pay_nil (Z : Jk1) : ∀ l, jk1 l (Jk1.pay Z []) = jk1 l Z := fun l => jk1_pay_nil l Z

/-- 木 `X` の右に「1 の列 + junk `T`」を `n` 個継ぐ。 -/
def itJ (T : Jk1) : ℕ → Jk1 → Jk1
  | 0, X => X
  | (n + 1), X => Jk1.one (itJ T n X) T

theorem JkJ_itJ {T : Jk1} (hT : JkJ T) : ∀ (n : ℕ) {X : Jk1}, JkJ X → JkJ (itJ T n X)
  | 0, _, hX => hX
  | (n + 1), _, hX => ⟨JkJ_itJ hT n hX, hT⟩

theorem CtxX_itJ {ctx : List Frm} {T : Jk1} (hT : JkJ T) : ∀ (n : ℕ) {X : Jk1},
    CtxX ctx X → CtxX ctx (itJ T n X)
  | 0, _, hX => hX
  | (n + 1), _, hX => CtxX_one ctx _ T (CtxX_itJ hT n hX) hT

#print axioms jk1_plug_one


theorem jk1_plug_pay (ctx : List Frm) (X Z : Jk1) (Y : TrioSeq) (l : ℕ) :
    jk1 l (plug ctx (Jk1.one X (Jk1.pay Z Y)))
      = jk1 l (plug ctx (Jk1.one X Z)) ++ shiftr01 (l + dep ctx + 2) 0 Y := by
  rw [jk1_plug_one ctx X (Jk1.pay Z Y) l, jk1_plug_one ctx X Z l, jk1,
    show l + dep ctx + 1 + 1 = l + dep ctx + 2 from by omega]
  simp [List.append_assoc]

theorem jk1_plug_itJ (ctx : List Frm) (X T : Jk1) (l : ℕ) : ∀ n : ℕ,
    jk1 l (plug ctx (itJ T n X))
      = jk1 l (plug ctx X) ++ (List.range n).flatMap
        (fun _ => ((l + dep ctx + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + dep ctx + 1) T)
  | 0 => by simp [itJ]
  | (n + 1) => by
      show jk1 l (plug ctx (Jk1.one (itJ T n X) T)) = _
      rw [jk1_plug_one ctx (itJ T n X) T l, jk1_plug_itJ ctx X T l n, List.range_succ,
        List.flatMap_append]
      simp [List.append_assoc]

/-- 深さ ≥ 1 の位置に荷を継ぐときの、字の分解。 -/
theorem colJ_plug_pay (a b : ℕ) (ctx : List Frm) (X Z : Jk1) (Y : TrioSeq) :
    colJ a b (plug ctx (Jk1.one X (Jk1.pay Z Y)))
      = colJ a b (plug ctx (Jk1.one X Z)) ++ shiftr01 (a + dep ctx + 3) 0 Y := by
  rw [colJ, colJ, jk1_plug_pay ctx X Z Y (a + 1),
    show a + 1 + dep ctx + 2 = a + dep ctx + 3 from by omega]
  rfl

theorem colJ_plug_one (a b : ℕ) (ctx : List Frm) (X T : Jk1) :
    colJ a b (plug ctx (Jk1.one X T))
      = colJ a b (plug ctx X) ++
        (((a + dep ctx + 2, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (a + dep ctx + 2) T) := by
  rw [colJ, colJ, jk1_plug_one ctx X T (a + 1),
    show a + 1 + dep ctx + 1 = a + dep ctx + 2 from by omega]
  rfl

theorem colJ_plug_itJ (a b : ℕ) (ctx : List Frm) (X T : Jk1) (n : ℕ) :
    colJ a b (plug ctx (itJ T n X))
      = colJ a b (plug ctx X) ++ (List.range n).flatMap
        (fun _ => ((a + dep ctx + 2, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (a + dep ctx + 2) T) := by
  rw [colJ, colJ, jk1_plug_itJ ctx X T (a + 1) n,
    show a + 1 + dep ctx + 1 = a + dep ctx + 2 from by omega]
  rfl

#print axioms colJ_plug_itJ


/-! ### 深さ ≥ 1 の位置に荷を継ぐ: 場合 (i)(ii) -/

theorem GoodFb_snoc_innerJs {ws : List Jk1} (hw : WOk ws) {ctx : List Frm} (hc : CtxOk ctx)
    {X Z : Jk1} (hX : CtxX ctx X) (hZ : JkJ Z) {Y : TrioSeq}
    (hY : Bok Y) (hlen : 2 ≤ Y.length)
    (hp : hasParent Y (srow Y (Y.length - 1)) (Y.length - 1))
    (hIH : ∀ n, 1 ≤ n →
      GoodFb (fun a b => wordJ a b (ws ++ [plug ctx (Jk1.one X (Jk1.pay Z (Y⟦n⟧)))]))) :
    GoodFb (fun a b => wordJ a b (ws ++ [plug ctx (Jk1.one X (Jk1.pay Z Y))])) := by
  refine GoodFb_of_keyJ (WOk_append hw (WOk_singleton
    (JkOk_plug ctx hc _ (CtxX_one ctx X _ hX ⟨hZ, hY⟩)))) hIH ?_
  intro Z0 a b hb hn
  have e : ∀ B : TrioSeq,
      Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) ::
        wordJ a b (ws ++ [plug ctx (Jk1.one X (Jk1.pay Z B))]))
      = (Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordJ a b (ws ++ [plug ctx (Jk1.one X Z)])))
        ++ shiftr01 (a + dep ctx + 3) 0 B := by
    intro B
    rw [wordJ_append, wordJ_singleton, colJ_plug_pay, wordJ_append, wordJ_singleton]
    simp [List.append_assoc]
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n hn'
  rw [e Y, oper_shift _ Y (a + dep ctx + 3) n hlen hp, ← e (Y⟦n⟧)]
  exact hn n hn'

theorem GoodFb_snoc_dupJs {ws : List Jk1} (hw : WOk ws) {ctx : List Frm} (hc : CtxOk ctx)
    {X Z : Jk1} (hX : CtxX ctx X) (hZ : JkJ Z) {Y : TrioSeq}
    (hY0 : Bok (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])) (hY : Bok Y)
    (hIH : ∀ n, 1 ≤ n →
      GoodFb (fun a b => wordJ a b (ws ++ [plug ctx (itJ (Jk1.pay Z Y) n X)]))) :
    GoodFb (fun a b => wordJ a b
      (ws ++ [plug ctx (Jk1.one X (Jk1.pay Z (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])))])) := by
  refine GoodFb_of_keyJ (WOk_append hw (WOk_singleton
    (JkOk_plug ctx hc _ (CtxX_one ctx X _ hX ⟨hZ, hY0⟩)))) hIH ?_
  intro Z0 a b hb hn
  set p := dep ctx with hp
  set M : TrioSeq := ((a + p + 2, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (a + p + 2) (Jk1.pay Z Y) with hM
  set Y0 : TrioSeq := Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) ::
    (wordJ a b ws ++ colJ a b (plug ctx X))) with hY0d
  have hhead : entry M 0 0 < a + p + 3 := by rw [hM]; simp [entry]
  have htail : ∀ r, 1 ≤ r → r < M.length → a + p + 3 ≤ entry M 0 r := by
    intro r hr1 hrl
    obtain ⟨u, rfl⟩ : ∃ u, r = u + 1 := ⟨r - 1, by omega⟩
    rw [hM, entry_cons_succ]
    have hu : u < (jk1 (a + p + 2) (Jk1.pay Z Y)).length := by
      rw [hM] at hrl; simp at hrl; omega
    have := entry0_of_ge (jk1_ge (Jk1.pay Z Y) (a + p + 2)) u hu
    omega
  have hcolsplit : ∀ n : ℕ, colJ a b (plug ctx (itJ (Jk1.pay Z Y) n X))
      = colJ a b (plug ctx X) ++ (List.range n).flatMap (fun _ => M) := by
    intro n
    rw [colJ_plug_itJ a b ctx X (Jk1.pay Z Y) n, hM, hp]
  have htw : ∀ n : ℕ, Y0 ++ (List.range n).flatMap (fun _ => M) ∈ W 0 := by
    intro n
    match n with
    | 0 =>
        have h1 := hn 1 (le_refl 1)
        rw [wordJ_append, wordJ_singleton, hcolsplit 1] at h1
        have h2 := W_take (by
          rw [show Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: (wordJ a b ws ++
              (colJ a b (plug ctx X) ++ (List.range 1).flatMap (fun _ => M))))
              = Y0 ++ (List.range 1).flatMap (fun _ => M) from by
                rw [hY0d]; simp [List.append_assoc]] at h1
          exact h1) Y0.length
        rw [List.take_left] at h2
        simpa using h2
    | (n + 1) =>
        have h1 := hn (n + 1) (by omega)
        rw [wordJ_append, wordJ_singleton, hcolsplit (n + 1)] at h1
        rw [show Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: (wordJ a b ws ++
            (colJ a b (plug ctx X) ++ (List.range (n + 1)).flatMap (fun _ => M))))
            = Y0 ++ (List.range (n + 1)).flatMap (fun _ => M) from by
              rw [hY0d]; simp [List.append_assoc]] at h1
        exact h1
  have h := flat_mem'' (Y0 := Y0) (M := M) (d := a + p + 3) (by rw [hM]; simp)
    hhead htail htw
  rw [wordJ_append, wordJ_singleton, colJ_plug_one a b ctx X (Jk1.pay Z (Y ++ [((0,0,0) : ℕ × ℕ × ℕ)]))]
  have esplit : jk1 (a + p + 2) (Jk1.pay Z (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]))
      = jk1 (a + p + 2) (Jk1.pay Z Y) ++ [((a + p + 3, 0, 0) : ℕ × ℕ × ℕ)] := by
    show jk1 (a + p + 2) Z ++ shiftr01 (a + p + 3) 0 (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])
      = (jk1 (a + p + 2) Z ++ shiftr01 (a + p + 3) 0 Y) ++ _
    rw [shiftr01_append0, ← List.append_assoc]
    simp [shiftr01]
  rw [← hp, esplit]
  rw [hY0d] at h
  simpa [hM, List.append_assoc] using h

#print axioms GoodFb_snoc_dupJs


theorem GOK_chainJ {ctx : List Frm} {X T : Jk1} (hXok : CtxX ctx X) (hTok : JkJ T)
    (hX : GOK (plug ctx X))
    (hstep : ∀ V : Jk1, CtxX ctx V → GOK (plug ctx V) → GOK (plug ctx (Jk1.one V T))) :
    ∀ n, GOK (plug ctx (itJ T n X))
  | 0 => hX
  | (n + 1) => hstep (itJ T n X) (CtxX_itJ hTok n hXok) (GOK_chainJ hXok hTok hX hstep n)

theorem jk1_one_pay_nil (X Z : Jk1) : ∀ l,
    jk1 l (Jk1.one X (Jk1.pay Z [])) = jk1 l (Jk1.one X Z) := by
  intro l
  show jk1 l X ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) (Jk1.pay Z []))
    = jk1 l X ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) Z)
  rw [jk1_pay_nil]

/-- ★★★ 深さ ≥ 1 の位置に荷を継いでも良い。 -/
theorem AYs : ∀ (Y : TrioSeq), Bok Y → ∀ (ctx : List Frm), CtxOk ctx → ∀ (X Z : Jk1),
    CtxX ctx X → JkJ Z →
    (∀ V : Jk1, CtxX ctx V → GOK (plug ctx V) → GOK (plug ctx (Jk1.one V Z))) →
    GOK (plug ctx X) →
    GOK (plug ctx (Jk1.one X (Jk1.pay Z Y))) := by
  have key : W 0 ⊆ {Y : TrioSeq | Bok Y → ∀ (ctx : List Frm), CtxOk ctx → ∀ (X Z : Jk1),
      CtxX ctx X → JkJ Z →
      (∀ V : Jk1, CtxX ctx V → GOK (plug ctx V) → GOK (plug ctx (Jk1.one V Z))) →
      GOK (plug ctx X) → GOK (plug ctx (Jk1.one X (Jk1.pay Z Y)))} := by
    refine A2' ?_
    intro Y hY
    simp only [Set.mem_setOf_eq]
    intro hYb ctx hc X Z hX hZ hAP hGX
    by_cases hshort : Y.length ≤ 1
    · rcases (by omega : Y.length = 0 ∨ Y.length = 1) with h0 | h1
      · have hnil0 : Y = [] := List.length_eq_zero_iff.mp h0
        subst hnil0
        exact GOK_congr (fun l => (jk1_plug_congr ctx (jk1_one_pay_nil X Z) l).symm)
          (hAP X hX hGX)
      · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
        have hc0 : c.1 = 0 := hYb.root
        obtain ⟨hc1, hc2⟩ := hYb.zroot c (by simp) hc0
        have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1 hc2)
        subst hcz
        have e : ([((0, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq)
            = ([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by simp
        rw [e]
        have hstep : ∀ V : Jk1, CtxX ctx V → GOK (plug ctx V) →
            GOK (plug ctx (Jk1.one V (Jk1.pay Z ([] : TrioSeq)))) := by
          intro V hV hGV
          exact GOK_congr (fun l => (jk1_plug_congr ctx (jk1_one_pay_nil V Z) l).symm)
            (hAP V hV hGV)
        intro ws hw hG
        refine GoodFb_snoc_dupJs hw hc hX hZ (by simpa using hYb) Bok_nil ?_
        intro n hn
        exact GOK_chainJ (T := Jk1.pay Z ([] : TrioSeq)) hX ⟨hZ, Bok_nil⟩ hGX hstep n ws hw hG
    have hlen2 : 2 ≤ Y.length := by omega
    have hYne : Y ≠ [] := by intro hcc; rw [hcc] at hlen2; simp at hlen2
    rcases hY with ⟨hl, -⟩ | hnat | ⟨m, hm, -, -⟩
    · exact absurd hl hshort
    · by_cases hlast : entry Y 0 (Y.length - 1) = 0
      · obtain ⟨he1, he2⟩ := Zroot_entry hYb.zroot hlast
        have hcol : Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) = ((0, 0, 0) : ℕ × ℕ × ℕ) :=
          Prod.ext hlast (Prod.ext he1 he2)
        have hgl : Y.getLast hYne = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
          have h1 : Y.getLast hYne = Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
            rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show Y.length - 1 < Y.length by omega)]
            rfl
          rw [h1, hcol]
        have hsplit : Y = Y.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
          rw [← hgl]; exact (List.dropLast_append_getLast hYne).symm
        have hop : Y⟦1⟧ = Y.dropLast := by
          rw [oper_eq_pred_of_zero 1 (by omega) ⟨hlast, he1, he2⟩]
          unfold Pred
          rw [if_neg (by omega)]
        have hdl := hnat 1 le_rfl
        rw [hop] at hdl
        simp only [Set.mem_setOf_eq] at hdl
        have hdb : Bok Y.dropLast := Bok_dropLast hYb
        rw [hsplit]
        have hstep : ∀ V : Jk1, CtxX ctx V → GOK (plug ctx V) →
            GOK (plug ctx (Jk1.one V (Jk1.pay Z Y.dropLast))) :=
          fun V hV hGV => hdl hdb ctx hc V Z hV hZ hAP hGV
        intro ws hw hG
        refine GoodFb_snoc_dupJs hw hc hX hZ (by rw [← hsplit]; exact hYb) hdb ?_
        intro n hn
        exact GOK_chainJ (T := Jk1.pay Z Y.dropLast) hX ⟨hZ, hdb⟩ hGX hstep n ws hw hG
      · have hnz : ¬ (entry Y 0 (Y.length - 1) = 0 ∧ entry Y 1 (Y.length - 1) = 0 ∧
            entry Y 2 (Y.length - 1) = 0) := fun h => hlast h.1
        have hp := hasParent_of_ZrootMono hYb.zroot hYb.mono hYb.root hlen2 hnz
        intro ws hw hG
        refine GoodFb_snoc_innerJs hw hc hX hZ hYb hlen2 hp ?_
        intro n hn
        have := hnat n hn
        simp only [Set.mem_setOf_eq] at this
        exact this (Bok_oper hYb hn) ctx hc X Z hX hZ hAP hGX ws hw hG
    · exact absurd hm (Nat.not_lt_zero m)
  intro Y hYb ctx hc X Z hX hZ hAP hGX
  exact key hYb.mem hYb ctx hc X Z hX hZ hAP hGX

#print axioms AYs


/-! ### 木の字の語の祖先条件と、1 の列を継ぐ（深さ 0） -/

theorem wordJ_kind (a b : ℕ) (ws : List Jk1) :
    ∀ x ∈ wordJ a b ws, x = ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ) ∨ a + 2 ≤ x.1 := by
  intro x hx
  simp only [wordJ, List.mem_flatMap] at hx
  obtain ⟨N, -, hxp⟩ := hx
  simp only [colJ, List.mem_cons] at hxp
  rcases hxp with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (jk1_ge N (a + 1) x h1)

theorem Ancd_recwordJ {a b : ℕ} (hb : 1 ≤ b) {Z : TrioSeq} (hZ : Ancd a Z) (ws : List Jk1) :
    Ancd (a + 2) (Z ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordJ a b ws)) := by
  set N : TrioSeq := ((a, b, 0) : ℕ × ℕ × ℕ) :: wordJ a b ws with hN
  intro j hj0 hjl hlt hvis
  rcases Nat.lt_or_ge j Z.length with hjZ | hjZ
  · have e0 : entry (Z ++ N) 0 j = entry Z 0 j := entry_append_left hjZ
    have e1 : entry (Z ++ N) 1 j = entry Z 1 j := entry_append_left hjZ
    have hNl : Z.length < (Z ++ N).length := by simp [hN]
    have hlt1 : entry Z 0 j < a := by
      have h1 := hvis Z.length hjZ hNl
      have h2 : entry (Z ++ N) 0 Z.length = a := by
        rw [show Z.length = Z.length + 0 from rfl, entry_append_right]
        simp [hN, entry]
      rw [e0] at h1
      omega
    rw [e1]
    refine hZ j hj0 hjZ hlt1 ?_
    intro i hi hil
    have := hvis i hi (by simp [hN]; omega)
    rwa [e0, entry_append_left hil] at this
  · obtain ⟨u, hu, rfl⟩ : ∃ u, u < N.length ∧ j = Z.length + u :=
      ⟨j - Z.length, by simp [hN] at hjl ⊢; omega, by omega⟩
    rw [entry_append_right]
    match u, hu with
    | 0, _ => simpa [hN, entry] using hb
    | (i + 1), hi =>
        have hil : i < (wordJ a b ws).length := by simp [hN] at hi; omega
        have he : entry N 0 (i + 1) = entry (wordJ a b ws) 0 i := by simp [hN, entry]
        have he1 : entry N 1 (i + 1) = entry (wordJ a b ws) 1 i := by simp [hN, entry]
        have hlt' : entry (wordJ a b ws) 0 i < a + 2 := by
          have h := hlt
          rw [entry_append_right, he] at h
          exact h
        have he0v : entry (wordJ a b ws) 0 i = ((wordJ a b ws)[i]'hil).1 := by
          simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil]
        have he1v : entry (wordJ a b ws) 1 i = ((wordJ a b ws)[i]'hil).2.1 := by
          simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil]
        rw [he0v] at hlt'
        rcases wordJ_kind a b ws _ (List.getElem_mem hil) with h1 | h1
        · rw [he1, he1v, h1]; simp
        · exact absurd hlt' (by omega)

theorem GOK_nil : GOK Jk1.nil := fun ws hw hG => GoodFb_snoczJ hw hG

theorem colJ_one_nil (a b : ℕ) (V : Jk1) :
    colJ a b (Jk1.one V Jk1.nil) = colJ a b V ++ [((a + 2, 1, 0) : ℕ × ℕ × ℕ)] := by
  show ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ) :: (jk1 (a + 1) V ++ (((a + 2, 1, 0) : ℕ × ℕ × ℕ) :: []))
    = (((a + 1, b + 1, 1) : ℕ × ℕ × ℕ) :: jk1 (a + 1) V) ++ [((a + 2, 1, 0) : ℕ × ℕ × ℕ)]
  simp

theorem wordJ_snoc_one (a b : ℕ) (ws : List Jk1) (V : Jk1) :
    wordJ a b (ws ++ [Jk1.one V Jk1.nil])
      = wordJ a b (ws ++ [V]) ++ [((a + 2, 1, 0) : ℕ × ℕ × ℕ)] := by
  rw [wordJ_append, wordJ_append, wordJ_singleton, wordJ_singleton, colJ_one_nil,
    List.append_assoc]

theorem wordJ_snoc_pay (a b : ℕ) (ws : List Jk1) (V : Jk1) (B : TrioSeq) :
    wordJ a b (ws ++ [Jk1.pay V B])
      = wordJ a b (ws ++ [V]) ++ shiftr01 (a + 2) 0 B := by
  rw [wordJ_append, wordJ_append, wordJ_singleton, wordJ_singleton, colJ_pay,
    List.append_assoc]

/-- ★★★ 深さ 0 に「junk のない 1 の列」を継いでも良い。 -/
theorem AP0nil (V : Jk1) (hV : JkOk V) (hGV : GOK V) : GOK (Jk1.one V Jk1.nil) := by
  intro ws hw hG
  have hwO : WOk (ws ++ [Jk1.one V Jk1.nil]) := WOk_append hw (WOk_singleton ⟨hV, JkOk_nil⟩)
  have hprev : ∀ B : TrioSeq, Bok B → GoodFb (fun a b => wordJ a b (ws ++ [Jk1.pay V B])) :=
    fun B hB => AY0 B hB V hV hGV ws hw hG
  have hbaseV : GoodFb (fun a b => wordJ a b (ws ++ [V])) := hGV ws hw hG
  refine ⟨fun a b => wordJ_ge a b _, fun a b => wordJ_mono hwO,
    fun a b s => wordJ_shift a b s _, ?_, ?_, ?_⟩
  · intro y c hy
    refine ⟨fun x hx => by have := wordJ_ge (c + 1) (y + 1) _ x hx; omega, wordJ_mono hwO, ?_⟩
    intro E hE t Z hZ
    rw [wordJ_shift, wordJ_snoc_one]
    set a := c + 1 + t with ha
    have hbase : PU y a (Z ++ ([((a, y + 1, 0) : ℕ × ℕ × ℕ)] ++ wordJ a (y + 1) (ws ++ [V]))) :=
      ⟨E, c + t, Z, _, hE, by omega, hZ, by rw [ha, show c + t + 1 = c + 1 + t from by omega],
        hbaseV.pu y (c + t) hy⟩
    have hAok := (BaseOk_PU y).aok _ _ hbase
    have hancZ : Ancd a Z := by
      have := (IfcV_iface (y + 1) hE).bok.ancd (c + t) Z hZ
      rwa [show c + t + 1 = a from by omega] at this
    have hanc : Ancd (a + 2)
        (Z ++ (((a, y + 1, 0) : ℕ × ℕ × ℕ) :: wordJ a (y + 1) (ws ++ [V]))) :=
      Ancd_recwordJ (by omega) hancZ _
    have h := snocd_gen (Y := Z ++ (((a, y + 1, 0) : ℕ × ℕ × ℕ) :: wordJ a (y + 1) (ws ++ [V])))
      (d := a + 2) (by omega) (by simpa using hAok) hanc ?_
    · simpa [List.append_assoc] using h
    · intro B hB
      have h2 := (hprev B hB).pu y c hy
      have h3 := h2.2.2 E hE t Z hZ
      rw [wordJ_shift, wordJ_snoc_pay] at h3
      simpa [ha, List.append_assoc] using h3
  · intro c E hI
    refine ⟨fun x hx => by have := wordJ_ge (c + 1) 2 _ x hx; omega, wordJ_mono hwO, ?_⟩
    intro j t X hX
    rw [wordJ_shift, wordJ_snoc_one]
    set a := c + 1 + t with ha
    have hbase : PkGA a (X ++ ([((a, 2, 0) : ℕ × ℕ × ℕ)] ++ wordJ a 2 (ws ++ [V]))) :=
      ⟨E, hI, j, c + t, X, _, by omega, hX,
        by rw [ha, show c + t + 1 = c + 1 + t from by omega], hbaseV.pk (c + t)⟩
    have hAok := PkGA_Aok hbase
    have hancX : Ancd a X := by
      have := (BaseOk_RunG hI.bok j).ancd (c + t) X hX
      rwa [show c + t + 1 = a from by omega] at this
    have hanc : Ancd (a + 2) (X ++ (((a, 2, 0) : ℕ × ℕ × ℕ) :: wordJ a 2 (ws ++ [V]))) :=
      Ancd_recwordJ (by omega) hancX _
    have h := snocd_gen (Y := X ++ (((a, 2, 0) : ℕ × ℕ × ℕ) :: wordJ a 2 (ws ++ [V])))
      (d := a + 2) (by omega) (by simpa using hAok) hanc ?_
    · simpa [List.append_assoc] using h
    · intro B hB
      have h2 := (hprev B hB).pk c E hI
      have h3 := h2.2.2 j t X hX
      rw [wordJ_shift, wordJ_snoc_pay] at h3
      simpa [ha, List.append_assoc] using h3
  · intro h
    have hmid : MidD (h + 2) (((h + 1, 1, 0) : ℕ × ℕ × ℕ) ::
        wordJ (h + 1) 1 (ws ++ [Jk1.one V Jk1.nil])) := by
      have h1 := MidD_wordJ (h + 1) 1 (by omega) (by omega) hwO
      simpa [show h + 1 + 1 = h + 2 from by omega] using h1
    refine ⟨hmid, by simp [entry], ?_⟩
    intro P hP s A' hA'
    rw [show ((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordJ (h + 1) 1 (ws ++ [Jk1.one V Jk1.nil])
        = [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ wordJ (h + 1) 1 (ws ++ [Jk1.one V Jk1.nil]) from rfl,
      shiftr01_append0, shift_col, wordJ_shift, wordJ_snoc_one]
    set a := h + 1 + s with ha
    have hLw : LwA (h + s) A' := ⟨P, hP, hA'⟩
    have hbase : RunA 0 a (A' ++ (((a, 1, 0) : ℕ × ℕ × ℕ) :: wordJ a 1 (ws ++ [V]))) :=
      ⟨h + s, A', _, by omega, rfl, hLw, by
        have := hbaseV.seg (h + s)
        simpa [ha, show h + s + 1 = h + 1 + s from by omega] using this⟩
    have hAok := (BaseOk_RunA 0).aok _ _ hbase
    have hancA : Ancd a A' := by
      have := LwB_Ancd hP hA'
      rwa [show h + s + 1 = a from by omega] at this
    have hanc : Ancd (a + 2) (A' ++ (((a, 1, 0) : ℕ × ℕ × ℕ) :: wordJ a 1 (ws ++ [V]))) :=
      Ancd_recwordJ (by omega) hancA _
    have hh := snocd_gen (Y := A' ++ (((a, 1, 0) : ℕ × ℕ × ℕ) :: wordJ a 1 (ws ++ [V])))
      (d := a + 2) (by omega) hAok hanc ?_
    · simpa [List.append_assoc] using hh
    · intro B hB
      have h2 := ((hprev B hB).seg (h + s)).reapp P hP 0 A' (by simpa using hA')
      rw [show ((h + s + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordJ (h + s + 1) 1 (ws ++ [Jk1.pay V B])
          = [((h + s + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ wordJ (h + s + 1) 1 (ws ++ [Jk1.pay V B])
          from rfl] at h2
      rw [wordJ_snoc_pay] at h2
      simpa [ha, show h + s + 1 = h + 1 + s from by omega, List.append_assoc] using h2

#print axioms AP0nil


/-! ### 深さ 1 の荷（1 の列の上の荷）と、シート行 371 -/

theorem APpayJ (Z : Jk1) (Y : TrioSeq) (hZ : JkJ Z) (hY : Bok Y)
    (hAP : ∀ V : Jk1, JkOk V → GOK V → GOK (Jk1.one V Z)) :
    ∀ V : Jk1, JkOk V → GOK V → GOK (Jk1.one V (Jk1.pay Z Y)) := by
  intro V hV hGV
  exact AYs Y hY [] trivial V Z hV hZ (fun W hW hGW => hAP W hW hGW) hGV

/-- 1 の列の上に任意の `Bok` の荷を吊るした字。 -/
theorem GOK_oneB {B : TrioSeq} (hB : Bok B) :
    GOK (Jk1.one Jk1.nil (Jk1.pay Jk1.nil B)) :=
  APpayJ Jk1.nil B JkJ_nil hB (fun V hV hGV => AP0nil V hV hGV) Jk1.nil JkOk_nil GOK_nil

/-- ★★★★★ 単位の上の 1 の列の、さらに上に高さ `h+4` で任意の `Bok` を吊るす。 -/
theorem hangU11one {h : ℕ} {A : TrioSeq} (hA : LwA h A) {B : TrioSeq} (hB : Bok B) :
    A ++ ([((h + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 1) : ℕ × ℕ × ℕ),
      ((h + 3, 1, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 (h + 4) 0 B) ∈ W 0 := by
  obtain ⟨P, hP, hL⟩ := hA
  have hG := GOK_oneB hB [] WOk_nil GoodFb_wordJ_nil
  have h1 := (hG.seg h).reapp P hP 0 A (by simpa using hL)
  simpa [wordJ, colJ, jk1, shiftr01_zero, List.append_assoc,
    show h + 1 + 1 = h + 2 from by omega, show h + 1 + 1 + 1 = h + 3 from by omega,
    show h + 1 + 1 + 1 + 1 = h + 4 from by omega] using h1

theorem R344_row1 : ∀ j, 0 < j → j < R344.length → 1 ≤ entry R344 1 j := by
  intro j hj0 hjl
  simp only [R344, R341, R338, List.length_append, List.length_cons, List.length_nil] at hjl
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl <;> simp [R344, R341, R338, entry]

/-- ★★★★★ シート行371 `R344 (4,1,0) = psi(W_w*W^W)`。 -/
theorem R371_mem : R344 ++ [((4, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine snocd_gen (Y := R344) (d := 4) (by omega) Aok_R344 (Ancd_of_row1 R344_row1 4) ?_
  intro B hB
  have h := hangU11one (h := 0) (LwA_of_Aok Aok_R338) hB
  simpa [R344, R341, List.append_assoc] using h

#print axioms R371_mem


/-! ### 深さ一般の祖先条件 -/

theorem jk1_plug_pay0 : ∀ (ctx : List Frm) (W : Jk1) (C : TrioSeq) (l : ℕ),
    jk1 l (plug ctx (Jk1.pay W C))
      = jk1 l (plug ctx W) ++ shiftr01 (l + dep ctx + 1) 0 C
  | [], W, C, l => by simp [plug, jk1, dep]
  | (Frm.fone N :: rest), W, C, l => by
      show jk1 l (Jk1.one N (plug rest (Jk1.pay W C))) = jk1 l (Jk1.one N (plug rest W)) ++ _
      rw [jk1, jk1, jk1_plug_pay0 rest W C (l + 1)]
      simp only [dep, List.cons_append, List.append_assoc]
      rw [show l + 1 + dep rest + 1 = l + (dep rest + 1) + 1 from by omega]
  | (Frm.fotw N :: rest), W, C, l => by
      show jk1 l N ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) ::
          (jk1 (l + 1) Jk1.nil ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ) ::
            jk1 (l + 2) (plug rest (Jk1.pay W C))))) = _
      rw [jk1_plug_pay0 rest W C (l + 2)]
      show _ = jk1 l N ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) ::
          (jk1 (l + 1) Jk1.nil ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ) ::
            jk1 (l + 2) (plug rest W)))) ++ _
      simp only [dep, jk1, List.nil_append, List.cons_append, List.append_assoc]
      rw [show l + 2 + dep rest + 1 = l + (dep rest + 2) + 1 from by omega]

theorem colJ_plug_pay0 (a b : ℕ) (ctx : List Frm) (W : Jk1) (C : TrioSeq) :
    colJ a b (plug ctx (Jk1.pay W C))
      = colJ a b (plug ctx W) ++ shiftr01 (a + dep ctx + 2) 0 C := by
  rw [colJ, colJ, jk1_plug_pay0 ctx W C (a + 1),
    show a + 1 + dep ctx + 1 = a + dep ctx + 2 from by omega]
  rfl

theorem colJ_plug_one_nil (a b : ℕ) (ctx : List Frm) (W : Jk1) :
    colJ a b (plug ctx (Jk1.one W Jk1.nil))
      = colJ a b (plug ctx W) ++ [((a + dep ctx + 2, 1, 0) : ℕ × ℕ × ℕ)] := by
  rw [colJ_plug_one a b ctx W Jk1.nil]
  rfl

/-- 文脈に沿った木の junk は、祖先条件を壊さない（深さの分だけ `d` を許す）。 -/
theorem Ancd_plug_jk1 : ∀ (ctx : List Frm) (W : Jk1) (l d : ℕ) (P : TrioSeq),
    d ≤ l + dep ctx + 1 → Ancd d P → Ancd d (P ++ jk1 l (plug ctx W))
  | [], W, l, d, P, hd, hP => by
      refine Ancd_append_ge hP ?_
      intro x hx
      have := jk1_ge W l x (by simpa [plug] using hx)
      simp only [dep] at hd
      omega
  | (Frm.fone N :: rest), W, l, d, P, hd, hP => by
      have e : jk1 l (plug (Frm.fone N :: rest) W)
          = jk1 l N ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) (plug rest W)) := rfl
      have h1 : Ancd d ((P ++ jk1 l N) ++ [((l + 1, 1, 0) : ℕ × ℕ × ℕ)]) :=
        Ancd_append_low hP (jk1_ge N l) (by simp) (by simp)
      have h2 := Ancd_plug_jk1 rest W (l + 1) d _
        (by simp only [dep] at hd; omega) h1
      rw [e]
      simpa [List.append_assoc] using h2
  | (Frm.fotw N :: rest), W, l, d, P, hd, hP => by
      have e : jk1 l (plug (Frm.fotw N :: rest) W)
          = ((jk1 l N ++ [((l + 1, 1, 0) : ℕ × ℕ × ℕ)]) ++ [((l + 2, 2, 0) : ℕ × ℕ × ℕ)]) ++
            jk1 (l + 2) (plug rest W) := by
        show jk1 l N ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) ::
          (jk1 (l + 1) Jk1.nil ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ) ::
            jk1 (l + 2) (plug rest W)))) = _
        simp [jk1, List.append_assoc]
      have h1 : Ancd d ((P ++ jk1 l N) ++ [((l + 1, 1, 0) : ℕ × ℕ × ℕ)]) :=
        Ancd_append_low hP (jk1_ge N l) (by simp) (by simp)
      have h1' : Ancd d (((P ++ jk1 l N) ++ [((l + 1, 1, 0) : ℕ × ℕ × ℕ)]) ++
          [((l + 2, 2, 0) : ℕ × ℕ × ℕ)]) := by
        have := Ancd_append_low (X := (P ++ jk1 l N) ++ [((l + 1, 1, 0) : ℕ × ℕ × ℕ)])
          (B := ([] : TrioSeq)) (l := l + 1) h1 (by simp)
          (c := ((l + 2, 2, 0) : ℕ × ℕ × ℕ)) (by simp) (by simp)
        simpa using this
      have h2 := Ancd_plug_jk1 rest W (l + 2) d _
        (by simp only [dep] at hd; omega) h1'
      rw [e]
      simpa [List.append_assoc] using h2

/-- 語の後ろに低い列を置くと、語の junk は不可視。 -/
theorem Ancd_wordJ_pre : ∀ (ws : List Jk1) (a b d : ℕ) (P : TrioSeq) (c : ℕ × ℕ × ℕ),
    1 ≤ b → c.1 ≤ a + 2 → 1 ≤ c.2.1 → Ancd d P → Ancd d ((P ++ wordJ a b ws) ++ [c]) := by
  intro ws
  induction ws using List.reverseRecOn with
  | nil =>
      intro a b d P c hb hc0 hc1 hP
      simpa [wordJ_nil] using Ancd_snoc_one1 hP hc1
  | append_singleton ws' N ih =>
      intro a b d P c hb hc0 hc1 hP
      have hprev := ih a b d P ((a + 1, b + 1, 1) : ℕ × ℕ × ℕ) hb (by show a + 1 ≤ a + 2; omega) (by show 1 ≤ b + 1; omega) hP
      have h2 : Ancd d ((((P ++ wordJ a b ws') ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)])
          ++ jk1 (a + 1) N) ++ [c]) :=
        Ancd_append_low hprev (jk1_ge N (a + 1)) (by omega) hc1
      have e : (((P ++ wordJ a b ws') ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]) ++ jk1 (a + 1) N)
          = P ++ wordJ a b (ws' ++ [N]) := by
        rw [wordJ_append, wordJ_singleton, colJ]
        simp [List.append_assoc]
      rwa [e] at h2

/-- 記録 + 語 + 文脈つきの木 の祖先条件。 -/
theorem Ancd_recwordJ_plug {a b : ℕ} (hb : 1 ≤ b) {Z0 : TrioSeq} (hZ : Ancd a Z0)
    (ws : List Jk1) (ctx : List Frm) (W : Jk1) :
    Ancd (a + dep ctx + 2)
      (Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: (wordJ a b ws ++ colJ a b (plug ctx W)))) := by
  set d := a + dep ctx + 2 with hd
  have h1 : Ancd d (Z0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)]) :=
    Ancd_snoc_pivot hZ rfl (by simpa using hb)
  have h2 : Ancd d (((Z0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)]) ++ wordJ a b ws)
      ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]) :=
    Ancd_wordJ_pre ws a b d _ _ hb (by show a + 1 ≤ a + 2; omega) (by show 1 ≤ b + 1; omega) h1
  have h3 := Ancd_plug_jk1 ctx W (a + 1) d _ (by omega) h2
  have e : (((Z0 ++ [((a, b, 0) : ℕ × ℕ × ℕ)]) ++ wordJ a b ws)
      ++ [((a + 1, b + 1, 1) : ℕ × ℕ × ℕ)]) ++ jk1 (a + 1) (plug ctx W)
      = Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: (wordJ a b ws ++ colJ a b (plug ctx W))) := by
    rw [colJ]
    simp [List.append_assoc]
  rwa [e] at h3

#print axioms Ancd_recwordJ_plug


theorem wordJ_snoc_plug_one (a b : ℕ) (ws : List Jk1) (ctx : List Frm) (V : Jk1) :
    wordJ a b (ws ++ [plug ctx (Jk1.one V Jk1.nil)])
      = wordJ a b (ws ++ [plug ctx V]) ++ [((a + dep ctx + 2, 1, 0) : ℕ × ℕ × ℕ)] := by
  rw [wordJ_append, wordJ_append, wordJ_singleton, wordJ_singleton, colJ_plug_one_nil,
    List.append_assoc]

theorem wordJ_snoc_plug_pay (a b : ℕ) (ws : List Jk1) (ctx : List Frm) (V : Jk1) (C : TrioSeq) :
    wordJ a b (ws ++ [plug ctx (Jk1.pay V C)])
      = wordJ a b (ws ++ [plug ctx V]) ++ shiftr01 (a + dep ctx + 2) 0 C := by
  rw [wordJ_append, wordJ_append, wordJ_singleton, wordJ_singleton, colJ_plug_pay0,
    List.append_assoc]

/-- ★★★ 深さ `|ctx|` に「junk のない 1 の列」を継いでも良い（吊るしを仮定として受け取る）。 -/
theorem APnil_gen (ctx : List Frm) (hc : CtxOk ctx) (V : Jk1) (hV : CtxX ctx V)
    (hGV : GOK (plug ctx V))
    (hang : ∀ C : TrioSeq, Bok C → GOK (plug ctx (Jk1.pay V C))) :
    GOK (plug ctx (Jk1.one V Jk1.nil)) := by
  intro ws hw hG
  set p := dep ctx with hp
  have hwO : WOk (ws ++ [plug ctx (Jk1.one V Jk1.nil)]) :=
    WOk_append hw (WOk_singleton (JkOk_plug ctx hc _ (CtxX_one ctx V Jk1.nil hV JkJ_nil)))
  have hbaseV : GoodFb (fun a b => wordJ a b (ws ++ [plug ctx V])) := hGV ws hw hG
  have hprev : ∀ C : TrioSeq, Bok C →
      GoodFb (fun a b => wordJ a b (ws ++ [plug ctx (Jk1.pay V C)])) :=
    fun C hC => hang C hC ws hw hG
  refine ⟨fun a b => wordJ_ge a b _, fun a b => wordJ_mono hwO,
    fun a b s => wordJ_shift a b s _, ?_, ?_, ?_⟩
  · intro y c hy
    refine ⟨fun x hx => by have := wordJ_ge (c + 1) (y + 1) _ x hx; omega, wordJ_mono hwO, ?_⟩
    intro E hE t Z hZ
    rw [wordJ_shift, wordJ_snoc_plug_one]
    set a := c + 1 + t with ha
    have hbase : PU y a (Z ++ ([((a, y + 1, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a (y + 1) (ws ++ [plug ctx V]))) :=
      ⟨E, c + t, Z, _, hE, by omega, hZ, by rw [ha, show c + t + 1 = c + 1 + t from by omega],
        hbaseV.pu y (c + t) hy⟩
    have hAok := (BaseOk_PU y).aok _ _ hbase
    have hancZ : Ancd a Z := by
      have := (IfcV_iface (y + 1) hE).bok.ancd (c + t) Z hZ
      rwa [show c + t + 1 = a from by omega] at this
    have hanc : Ancd (a + p + 2)
        (Z ++ (((a, y + 1, 0) : ℕ × ℕ × ℕ) :: wordJ a (y + 1) (ws ++ [plug ctx V]))) := by
      have h1 := Ancd_recwordJ_plug (a := a) (b := y + 1) (by omega) hancZ ws ctx V
      rw [wordJ_append, wordJ_singleton]
      rwa [← hp] at h1
    have h := snocd_gen (Y := Z ++ (((a, y + 1, 0) : ℕ × ℕ × ℕ) ::
        wordJ a (y + 1) (ws ++ [plug ctx V]))) (d := a + p + 2) (by omega)
      (by simpa using hAok) hanc ?_
    · simpa [List.append_assoc] using h
    · intro B hB
      have h2 := (hprev B hB).pu y c hy
      have h3 := h2.2.2 E hE t Z hZ
      rw [wordJ_shift, wordJ_snoc_plug_pay] at h3
      simpa [ha, ← hp, List.append_assoc] using h3
  · intro c E hI
    refine ⟨fun x hx => by have := wordJ_ge (c + 1) 2 _ x hx; omega, wordJ_mono hwO, ?_⟩
    intro j t X hX
    rw [wordJ_shift, wordJ_snoc_plug_one]
    set a := c + 1 + t with ha
    have hbase : PkGA a (X ++ ([((a, 2, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a 2 (ws ++ [plug ctx V]))) :=
      ⟨E, hI, j, c + t, X, _, by omega, hX,
        by rw [ha, show c + t + 1 = c + 1 + t from by omega], hbaseV.pk (c + t)⟩
    have hAok := PkGA_Aok hbase
    have hancX : Ancd a X := by
      have := (BaseOk_RunG hI.bok j).ancd (c + t) X hX
      rwa [show c + t + 1 = a from by omega] at this
    have hanc : Ancd (a + p + 2)
        (X ++ (((a, 2, 0) : ℕ × ℕ × ℕ) :: wordJ a 2 (ws ++ [plug ctx V]))) := by
      have h1 := Ancd_recwordJ_plug (a := a) (b := 2) (by omega) hancX ws ctx V
      rw [wordJ_append, wordJ_singleton]
      rwa [← hp] at h1
    have h := snocd_gen (Y := X ++ (((a, 2, 0) : ℕ × ℕ × ℕ) ::
        wordJ a 2 (ws ++ [plug ctx V]))) (d := a + p + 2) (by omega)
      (by simpa using hAok) hanc ?_
    · simpa [List.append_assoc] using h
    · intro B hB
      have h2 := (hprev B hB).pk c E hI
      have h3 := h2.2.2 j t X hX
      rw [wordJ_shift, wordJ_snoc_plug_pay] at h3
      simpa [ha, ← hp, List.append_assoc] using h3
  · intro h
    have hmid : MidD (h + 2) (((h + 1, 1, 0) : ℕ × ℕ × ℕ) ::
        wordJ (h + 1) 1 (ws ++ [plug ctx (Jk1.one V Jk1.nil)])) := by
      have h1 := MidD_wordJ (h + 1) 1 (by omega) (by omega) hwO
      simpa [show h + 1 + 1 = h + 2 from by omega] using h1
    refine ⟨hmid, by simp [entry], ?_⟩
    intro P hP s A' hA'
    rw [show ((h + 1, 1, 0) : ℕ × ℕ × ℕ) ::
          wordJ (h + 1) 1 (ws ++ [plug ctx (Jk1.one V Jk1.nil)])
        = [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ++
          wordJ (h + 1) 1 (ws ++ [plug ctx (Jk1.one V Jk1.nil)]) from rfl,
      shiftr01_append0, shift_col, wordJ_shift, wordJ_snoc_plug_one]
    set a := h + 1 + s with ha
    have hLw : LwA (h + s) A' := ⟨P, hP, hA'⟩
    have hbase : RunA 0 a (A' ++ (((a, 1, 0) : ℕ × ℕ × ℕ) ::
        wordJ a 1 (ws ++ [plug ctx V]))) :=
      ⟨h + s, A', _, by omega, rfl, hLw, by
        have := hbaseV.seg (h + s)
        simpa [ha, show h + s + 1 = h + 1 + s from by omega] using this⟩
    have hAok := (BaseOk_RunA 0).aok _ _ hbase
    have hancA : Ancd a A' := by
      have := LwB_Ancd hP hA'
      rwa [show h + s + 1 = a from by omega] at this
    have hanc : Ancd (a + p + 2)
        (A' ++ (((a, 1, 0) : ℕ × ℕ × ℕ) :: wordJ a 1 (ws ++ [plug ctx V]))) := by
      have h1 := Ancd_recwordJ_plug (a := a) (b := 1) (by omega) hancA ws ctx V
      rw [wordJ_append, wordJ_singleton]
      rwa [← hp] at h1
    have hh := snocd_gen (Y := A' ++ (((a, 1, 0) : ℕ × ℕ × ℕ) ::
        wordJ a 1 (ws ++ [plug ctx V]))) (d := a + p + 2) (by omega) hAok hanc ?_
    · simpa [List.append_assoc] using hh
    · intro B hB
      have h2 := ((hprev B hB).seg (h + s)).reapp P hP 0 A' (by simpa using hA')
      rw [show ((h + s + 1, 1, 0) : ℕ × ℕ × ℕ) ::
            wordJ (h + s + 1) 1 (ws ++ [plug ctx (Jk1.pay V B)])
          = [((h + s + 1, 1, 0) : ℕ × ℕ × ℕ)] ++
            wordJ (h + s + 1) 1 (ws ++ [plug ctx (Jk1.pay V B)]) from rfl] at h2
      rw [wordJ_snoc_plug_pay] at h2
      simpa [ha, ← hp, show h + s + 1 = h + 1 + s from by omega, List.append_assoc] using h2

#print axioms APnil_gen


/-! ### 深さ 0 の「項として継げる」木 `APz` と、その 1 段上 -/

/-- 木 `V` は、どの良い木の右にも「1 の列 + junk `V`」として継げる。 -/
def APz (V : Jk1) : Prop := ∀ U : Jk1, JkOk U → GOK U → GOK (Jk1.one U V)

theorem APz_nil : APz Jk1.nil := fun U hU hGU => AP0nil U hU hGU

theorem GOK_onePay {T V : Jk1} (hT : JkOk T) (hV : JkJ V) (hGT : GOK T) (hA : APz V)
    {C : TrioSeq} (hC : Bok C) : GOK (Jk1.one T (Jk1.pay V C)) :=
  AYs C hC [] trivial T V hT hV (fun U hU hGU => hA U hU hGU) hGT

/-- `APz` は荷の追加で閉じている。 -/
theorem APz_pay {V : Jk1} (hV : JkJ V) (hA : APz V) {C : TrioSeq} (hC : Bok C) :
    APz (Jk1.pay V C) := fun U hU hGU => GOK_onePay hU hV hGU hA hC

/-- ★★★ `APz V` なら、`one V nil`（junk のない 1 の列）を項として継げる。 -/
theorem GOK_oneOneNil {T V : Jk1} (hT : JkOk T) (hV : JkJ V) (hGT : GOK T) (hA : APz V) :
    GOK (Jk1.one T (Jk1.one V Jk1.nil)) := by
  refine APnil_gen [Frm.fone T] ⟨hT, trivial⟩ V hV ?_ ?_
  · exact hA T hT hGT
  · intro C hC
    exact GOK_onePay hT hV hGT hA hC

/-- 行 371 の字の木は完全に普遍（GoodFb 3 段すべて）。 -/
theorem GOK_T371 : GOK (Jk1.one Jk1.nil (Jk1.one Jk1.nil Jk1.nil)) :=
  GOK_oneOneNil JkOk_nil JkOk_nil GOK_nil APz_nil

theorem JkOk_T371 : JkOk (Jk1.one Jk1.nil (Jk1.one Jk1.nil Jk1.nil)) :=
  ⟨trivial, trivial, trivial⟩

/-- 行 371 を「字の普遍性」から出し直す（`GoodFb` の 3 段すべてが付く）。 -/
theorem R371_mem' : R344 ++ [((4, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hG := GOK_T371 [] WOk_nil GoodFb_wordJ_nil
  have h := (hG.seg 0).reapp P0 BaseOk_zero 0 R338 (LwB_of_base ⟨Aok_R338, rfl⟩)
  simpa [wordJ, colJ, jk1, shiftr01_zero, R344, R341, List.append_assoc] using h

#print axioms R371_mem'


/-! ### `APz` を連鎖に沿って持ち回る版の荷追加 -/

theorem APz_congr {V1 V2 : Jk1} (h : ∀ l, jk1 l V1 = jk1 l V2) (hA : APz V1) : APz V2 := by
  intro U hU hGU
  refine GOK_congr (fun l => ?_) (hA U hU hGU)
  show jk1 l U ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) V1)
    = jk1 l U ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) V2)
  rw [h]

theorem GOK_chainJz {ctx : List Frm} {X T : Jk1} (hXok : CtxX ctx X) (hXz : APz X)
    (hTok : JkJ T) (hX : GOK (plug ctx X))
    (hstep : ∀ V : Jk1, CtxX ctx V → APz V → GOK (plug ctx V) → GOK (plug ctx (Jk1.one V T)))
    (hpres : ∀ V : Jk1, JkJ V → APz V → APz (Jk1.one V T)) :
    ∀ n, GOK (plug ctx (itJ T n X)) ∧ APz (itJ T n X)
  | 0 => ⟨hX, hXz⟩
  | (n + 1) => by
      obtain ⟨h1, h2⟩ := GOK_chainJz hXok hXz hTok hX hstep hpres n
      have hok := CtxX_itJ hTok n hXok
      exact ⟨hstep (itJ T n X) hok h2 h1, hpres (itJ T n X) (JkJ_of_CtxX ctx _ hok) h2⟩

/-- ★★★ `APz` を仮定に持ち回る荷追加。連鎖の木も `APz` のまま。 -/
theorem AYz : ∀ (Y : TrioSeq), Bok Y → ∀ (Z : Jk1), JkJ Z →
    (∀ V : Jk1, JkJ V → APz V → APz (Jk1.one V Z)) →
    ∀ (X : Jk1), JkJ X → APz X → APz (Jk1.one X (Jk1.pay Z Y)) := by
  have key : W 0 ⊆ {Y : TrioSeq | Bok Y → ∀ (Z : Jk1), JkJ Z →
      (∀ V : Jk1, JkJ V → APz V → APz (Jk1.one V Z)) →
      ∀ (X : Jk1), JkJ X → APz X → APz (Jk1.one X (Jk1.pay Z Y))} := by
    refine A2' ?_
    intro Y hY
    simp only [Set.mem_setOf_eq]
    intro hYb Z hZ hR X hX hXz
    by_cases hshort : Y.length ≤ 1
    · rcases (by omega : Y.length = 0 ∨ Y.length = 1) with h0 | h1
      · have hnil0 : Y = [] := List.length_eq_zero_iff.mp h0
        subst hnil0
        exact APz_congr (fun l => (jk1_one_pay_nil X Z l).symm) (hR X hX hXz)
      · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
        have hc0 : c.1 = 0 := hYb.root
        obtain ⟨hc1, hc2⟩ := hYb.zroot c (by simp) hc0
        have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1 hc2)
        subst hcz
        have hpres : ∀ V : Jk1, JkJ V → APz V → APz (Jk1.one V (Jk1.pay Z ([] : TrioSeq))) :=
          fun V hV hVz => APz_congr (fun l => (jk1_one_pay_nil V Z l).symm) (hR V hV hVz)
        intro U hU hGU
        have e : ([((0, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq)
            = ([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by simp
        rw [e]
        intro ws hw hG
        refine GoodFb_snoc_dupJs hw (ctx := [Frm.fone U]) ⟨hU, trivial⟩ hX hZ
          (by simpa using hYb) Bok_nil ?_
        intro n hn
        refine (GOK_chainJz (ctx := [Frm.fone U]) (T := Jk1.pay Z ([] : TrioSeq)) hX hXz
          ⟨hZ, Bok_nil⟩ (hXz U hU hGU) ?_ hpres n).1 ws hw hG
        intro V hV hVz hGV
        exact hpres V hV hVz U hU hGU
    have hlen2 : 2 ≤ Y.length := by omega
    have hYne : Y ≠ [] := by intro hcc; rw [hcc] at hlen2; simp at hlen2
    rcases hY with ⟨hl, -⟩ | hnat | ⟨m, hm, -, -⟩
    · exact absurd hl hshort
    · by_cases hlast : entry Y 0 (Y.length - 1) = 0
      · obtain ⟨he1, he2⟩ := Zroot_entry hYb.zroot hlast
        have hcol : Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) = ((0, 0, 0) : ℕ × ℕ × ℕ) :=
          Prod.ext hlast (Prod.ext he1 he2)
        have hgl : Y.getLast hYne = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
          have h1 : Y.getLast hYne = Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
            rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show Y.length - 1 < Y.length by omega)]
            rfl
          rw [h1, hcol]
        have hsplit : Y = Y.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
          rw [← hgl]; exact (List.dropLast_append_getLast hYne).symm
        have hop : Y⟦1⟧ = Y.dropLast := by
          rw [oper_eq_pred_of_zero 1 (by omega) ⟨hlast, he1, he2⟩]
          unfold Pred
          rw [if_neg (by omega)]
        have hdl := hnat 1 le_rfl
        rw [hop] at hdl
        simp only [Set.mem_setOf_eq] at hdl
        have hdb : Bok Y.dropLast := Bok_dropLast hYb
        have hpres : ∀ V : Jk1, JkJ V → APz V → APz (Jk1.one V (Jk1.pay Z Y.dropLast)) :=
          fun V hV hVz => hdl hdb Z hZ hR V hV hVz
        intro U hU hGU
        rw [hsplit]
        intro ws hw hG
        refine GoodFb_snoc_dupJs hw (ctx := [Frm.fone U]) ⟨hU, trivial⟩ hX hZ
          (by rw [← hsplit]; exact hYb) hdb ?_
        intro n hn
        refine (GOK_chainJz (ctx := [Frm.fone U]) (T := Jk1.pay Z Y.dropLast) hX hXz
          ⟨hZ, hdb⟩ (hXz U hU hGU) ?_ hpres n).1 ws hw hG
        intro V hV hVz hGV
        exact hpres V hV hVz U hU hGU
      · have hnz : ¬ (entry Y 0 (Y.length - 1) = 0 ∧ entry Y 1 (Y.length - 1) = 0 ∧
            entry Y 2 (Y.length - 1) = 0) := fun h => hlast h.1
        have hp := hasParent_of_ZrootMono hYb.zroot hYb.mono hYb.root hlen2 hnz
        intro U hU hGU
        intro ws hw hG
        refine GoodFb_snoc_innerJs hw (ctx := [Frm.fone U]) ⟨hU, trivial⟩ hX hZ hYb hlen2 hp ?_
        intro n hn
        have := hnat n hn
        simp only [Set.mem_setOf_eq] at this
        exact this (Bok_oper hYb hn) Z hZ hR X hX hXz U hU hGU ws hw hG
    · exact absurd hm (Nat.not_lt_zero m)
  intro Y hYb Z hZ hR X hX hXz
  exact key hYb.mem hYb Z hZ hR X hX hXz

#print axioms AYz


/-! ### `APz` の閉包を「1 の列 + 荷だけの junk」まで広げる -/

theorem PayOnly_JkJ : ∀ W : Jk1, PayOnly W → JkJ W
  | Jk1.nil, _ => trivial
  | Jk1.pay N Y, h => ⟨PayOnly_JkJ N h.1, h.2⟩
  | Jk1.one _ _, h => absurd h (by simp [PayOnly])
  | Jk1.two _ _, h => absurd h (by simp [PayOnly])

/-- ★★★ `APz V` かつ `W` が荷だけなら、項 `one V W` を継げる。 -/
theorem APz_onePayOnly : ∀ W : Jk1, PayOnly W → ∀ V : Jk1, JkJ V → APz V →
    APz (Jk1.one V W)
  | Jk1.nil, _, V, hV, hVz => by
      intro U hU hGU
      exact GOK_oneOneNil hU hV hGU hVz
  | Jk1.pay W₀ C, h, V, hV, hVz =>
      AYz C h.2 W₀ (PayOnly_JkJ W₀ h.1) (APz_onePayOnly W₀ h.1) V hV hVz
  | Jk1.one _ _, h, _, _, _ => absurd h (by simp [PayOnly])
  | Jk1.two _ _, h, _, _, _ => absurd h (by simp [PayOnly])

/-! ### シート行 372 -/

def T372 (B : TrioSeq) : Jk1 := Jk1.one Jk1.nil (Jk1.one Jk1.nil (Jk1.pay Jk1.nil B))

theorem JkOk_T372 {B : TrioSeq} (hB : Bok B) : JkOk (T372 B) :=
  ⟨trivial, trivial, trivial, hB⟩

theorem GOK_T372 {B : TrioSeq} (hB : Bok B) : GOK (T372 B) := by
  have hAPz : APz (Jk1.one Jk1.nil (Jk1.pay Jk1.nil B)) :=
    APz_onePayOnly (Jk1.pay Jk1.nil B) ⟨trivial, hB⟩ Jk1.nil JkJ_nil APz_nil
  exact hAPz Jk1.nil JkOk_nil GOK_nil

def R371 : TrioSeq := R344 ++ [((4, 1, 0) : ℕ × ℕ × ℕ)]

theorem R371_eq : R371 = R338 ++ (((1, 1, 0) : ℕ × ℕ × ℕ) ::
    wordJ 1 1 [Jk1.one Jk1.nil (Jk1.one Jk1.nil Jk1.nil)]) := by
  simp [R371, R344, R341, wordJ, colJ, jk1, shiftr01]

theorem Aok_R371 : Aok R371 := by
  have hR : RunA 0 1 (R338 ++ (((1, 1, 0) : ℕ × ℕ × ℕ) ::
      wordJ 1 1 [Jk1.one Jk1.nil (Jk1.one Jk1.nil Jk1.nil)])) :=
    ⟨0, R338, _, rfl, rfl, LwA_of_Aok Aok_R338,
      (GOK_T371 [] WOk_nil GoodFb_wordJ_nil).seg 0⟩
  rw [R371_eq]
  exact (BaseOk_RunA 0).aok _ _ hR

theorem R371_row1 : ∀ j, 0 < j → j < R371.length → 1 ≤ entry R371 1 j := by
  intro j hj0 hjl
  simp only [R371, R344, R341, R338, List.length_append, List.length_cons,
    List.length_nil] at hjl
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp [R371, R344, R341, R338, entry]

/-- ★★★★★ 高さ `h+5` で任意の `Bok` を吊るす（1 の列 2 段の上）。 -/
theorem hangU11two {h : ℕ} {A : TrioSeq} (hA : LwA h A) {B : TrioSeq} (hB : Bok B) :
    A ++ ([((h + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 1) : ℕ × ℕ × ℕ),
      ((h + 3, 1, 0) : ℕ × ℕ × ℕ), ((h + 4, 1, 0) : ℕ × ℕ × ℕ)] ++
      shiftr01 (h + 5) 0 B) ∈ W 0 := by
  obtain ⟨P, hP, hL⟩ := hA
  have hG := GOK_T372 hB [] WOk_nil GoodFb_wordJ_nil
  have h1 := (hG.seg h).reapp P hP 0 A (by simpa using hL)
  simpa [wordJ, colJ, jk1, T372, shiftr01_zero, List.append_assoc,
    show h + 1 + 1 = h + 2 from by omega, show h + 1 + 1 + 1 = h + 3 from by omega,
    show h + 1 + 1 + 1 + 1 = h + 4 from by omega,
    show h + 1 + 1 + 1 + 1 + 1 = h + 5 from by omega] using h1

/-- ★★★★★ シート行372 `R344 (4,1,0)(5,1,0) = psi(W_w*W^W^W)`。 -/
theorem R372_mem : R371 ++ [((5, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine snocd_gen (Y := R371) (d := 5) (by omega) Aok_R371 (Ancd_of_row1 R371_row1 5) ?_
  intro B hB
  have h := hangU11two (h := 0) (LwA_of_Aok Aok_R338) hB
  simpa [R371, R344, R341, List.append_assoc] using h

#print axioms R372_mem


/-! ### 任意の深さ: `APd k`（深さ `k` で項として継げる）と文脈への言い換え -/

/-- 深さ `k` で「1 の列 + junk `V`」として継げる。`APd 0 = APz`。 -/
def APd : ℕ → Jk1 → Prop
  | 0, V => ∀ U : Jk1, JkOk U → GOK U → GOK (Jk1.one U V)
  | (k + 1), V => ∀ U : Jk1, JkJ U → APd k U → APd k (Jk1.one U V)

theorem APd_zero (V : Jk1) : APd 0 V ↔ APz V := Iff.rfl

/-- 深さ `k` の良い文脈。 -/
def GCtx : ℕ → List Frm → Prop
  | 0, ctx => ∃ U : Jk1, ctx = [Frm.fone U] ∧ JkOk U ∧ GOK U
  | (k + 1), ctx => ∃ (ctx' : List Frm) (U : Jk1), ctx = ctx' ++ [Frm.fone U] ∧ GCtx k ctx' ∧
      JkJ U ∧ APd k U

theorem GCtx_ne : ∀ (k : ℕ) (ctx : List Frm), GCtx k ctx → ctx ≠ []
  | 0, ctx, h => by
      obtain ⟨U, rfl, -, -⟩ := h
      simp
  | (k + 1), ctx, h => by
      obtain ⟨ctx', U, rfl, -, -, -⟩ := h
      simp

theorem GCtx_CtxX_one : ∀ (k : ℕ) (ctx : List Frm), GCtx k ctx → ∀ X : Jk1, JkJ X → CtxX ctx X
  | 0, ctx, h, X, hX => by
      obtain ⟨U, rfl, -, -⟩ := h
      exact (CtxX_snoc1 [] U X).mpr hX
  | (k + 1), ctx, h, X, hX => by
      obtain ⟨ctx', U, rfl, -, -, -⟩ := h
      exact (CtxX_snoc1 ctx' U X).mpr hX

theorem GCtx_CtxOk : ∀ (k : ℕ) (ctx : List Frm), GCtx k ctx → CtxOk ctx
  | 0, ctx, h => by
      obtain ⟨U, rfl, hU, -⟩ := h
      exact ⟨hU, trivial⟩
  | (k + 1), ctx, h => by
      obtain ⟨ctx', U, rfl, hc', hU, -⟩ := h
      exact CtxOk_snoc ctx' U (GCtx_CtxOk k ctx' hc')
        (GCtx_CtxX_one k ctx' hc' U hU)

/-- `APd k V` は「深さ `k` のどの良い文脈でも `plug ctx V` が良い」と同値。 -/
theorem APd_iff : ∀ (k : ℕ) (V : Jk1), APd k V ↔ ∀ ctx : List Frm, GCtx k ctx → GOK (plug ctx V)
  | 0, V => by
      constructor
      · rintro h ctx ⟨U, rfl, hU, hGU⟩
        exact h U hU hGU
      · intro h U hU hGU
        exact h [Frm.fone U] ⟨U, rfl, hU, hGU⟩
  | (k + 1), V => by
      constructor
      · rintro h ctx ⟨ctx', U, rfl, hc', hU, hUk⟩
        rw [plug_snoc]
        exact (APd_iff k (Jk1.one U V)).mp (h U hU hUk) ctx' hc'
      · intro h U hU hUk
        refine (APd_iff k (Jk1.one U V)).mpr ?_
        intro ctx' hc'
        rw [← plug_snoc]
        exact h (ctx' ++ [Frm.fone U]) ⟨ctx', U, rfl, hc', hU, hUk⟩

#print axioms APd_iff


theorem APd_congr : ∀ (k : ℕ) {V1 V2 : Jk1}, (∀ l, jk1 l V1 = jk1 l V2) → APd k V1 → APd k V2 := by
  intro k V1 V2 h hA
  rw [APd_iff] at hA ⊢
  intro ctx hc
  exact GOK_congr (jk1_plug_congr ctx h) (hA ctx hc)

theorem GOK_chainJd {k : ℕ} {ctx : List Frm} (hc : GCtx k ctx) {X T : Jk1}
    (hXok : JkJ X) (hXk : APd k X) (hTok : JkJ T)
    (hstep : ∀ V : Jk1, JkJ V → APd k V → APd k (Jk1.one V T)) :
    ∀ n, GOK (plug ctx (itJ T n X)) ∧ APd k (itJ T n X)
  | 0 => ⟨(APd_iff k X).mp hXk ctx hc, hXk⟩
  | (n + 1) => by
      obtain ⟨h1, h2⟩ := GOK_chainJd hc hXok hXk hTok hstep n
      have hok := JkJ_itJ hTok n hXok
      have h3 := hstep (itJ T n X) hok h2
      exact ⟨(APd_iff k _).mp h3 ctx hc, h3⟩

/-- ★★★ 任意の深さでの荷追加。`APd (k+1) Z` を仮定に持ち回る。 -/
theorem AYd : ∀ (Y : TrioSeq), Bok Y → ∀ (k : ℕ) (Z : Jk1), JkJ Z → APd (k + 1) Z →
    ∀ (X : Jk1), JkJ X → APd k X → APd k (Jk1.one X (Jk1.pay Z Y)) := by
  have key : W 0 ⊆ {Y : TrioSeq | Bok Y → ∀ (k : ℕ) (Z : Jk1), JkJ Z → APd (k + 1) Z →
      ∀ (X : Jk1), JkJ X → APd k X → APd k (Jk1.one X (Jk1.pay Z Y))} := by
    refine A2' ?_
    intro Y hY
    simp only [Set.mem_setOf_eq]
    intro hYb k Z hZ hRZ X hX hXk
    by_cases hshort : Y.length ≤ 1
    · rcases (by omega : Y.length = 0 ∨ Y.length = 1) with h0 | h1
      · have hnil0 : Y = [] := List.length_eq_zero_iff.mp h0
        subst hnil0
        exact APd_congr k (fun l => (jk1_one_pay_nil X Z l).symm) (hRZ X hX hXk)
      · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
        have hc0 : c.1 = 0 := hYb.root
        obtain ⟨hc1, hc2⟩ := hYb.zroot c (by simp) hc0
        have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1 hc2)
        subst hcz
        have hpres : ∀ V : Jk1, JkJ V → APd k V → APd k (Jk1.one V (Jk1.pay Z ([] : TrioSeq))) :=
          fun V hV hVk => APd_congr k (fun l => (jk1_one_pay_nil V Z l).symm) (hRZ V hV hVk)
        have e : ([((0, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq)
            = ([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by simp
        rw [e, APd_iff]
        intro ctx hc ws hw hG
        refine GoodFb_snoc_dupJs hw (GCtx_CtxOk k ctx hc)
          (GCtx_CtxX_one k ctx hc X hX) hZ
          (by simpa using hYb) Bok_nil ?_
        intro n hn
        exact (GOK_chainJd (T := Jk1.pay Z ([] : TrioSeq)) hc hX hXk ⟨hZ, Bok_nil⟩ hpres n).1 ws hw hG
    have hlen2 : 2 ≤ Y.length := by omega
    have hYne : Y ≠ [] := by intro hcc; rw [hcc] at hlen2; simp at hlen2
    rcases hY with ⟨hl, -⟩ | hnat | ⟨m, hm, -, -⟩
    · exact absurd hl hshort
    · by_cases hlast : entry Y 0 (Y.length - 1) = 0
      · obtain ⟨he1, he2⟩ := Zroot_entry hYb.zroot hlast
        have hcol : Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) = ((0, 0, 0) : ℕ × ℕ × ℕ) :=
          Prod.ext hlast (Prod.ext he1 he2)
        have hgl : Y.getLast hYne = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
          have h1 : Y.getLast hYne = Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
            rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show Y.length - 1 < Y.length by omega)]
            rfl
          rw [h1, hcol]
        have hsplit : Y = Y.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
          rw [← hgl]; exact (List.dropLast_append_getLast hYne).symm
        have hop : Y⟦1⟧ = Y.dropLast := by
          rw [oper_eq_pred_of_zero 1 (by omega) ⟨hlast, he1, he2⟩]
          unfold Pred
          rw [if_neg (by omega)]
        have hdl := hnat 1 le_rfl
        rw [hop] at hdl
        simp only [Set.mem_setOf_eq] at hdl
        have hdb : Bok Y.dropLast := Bok_dropLast hYb
        have hpres : ∀ V : Jk1, JkJ V → APd k V → APd k (Jk1.one V (Jk1.pay Z Y.dropLast)) :=
          fun V hV hVk => hdl hdb k Z hZ hRZ V hV hVk
        rw [hsplit, APd_iff]
        intro ctx hc ws hw hG
        refine GoodFb_snoc_dupJs hw (GCtx_CtxOk k ctx hc)
          (GCtx_CtxX_one k ctx hc X hX) hZ
          (by rw [← hsplit]; exact hYb) hdb ?_
        intro n hn
        exact (GOK_chainJd (T := Jk1.pay Z Y.dropLast) hc hX hXk ⟨hZ, hdb⟩ hpres n).1 ws hw hG
      · have hnz : ¬ (entry Y 0 (Y.length - 1) = 0 ∧ entry Y 1 (Y.length - 1) = 0 ∧
            entry Y 2 (Y.length - 1) = 0) := fun h => hlast h.1
        have hp := hasParent_of_ZrootMono hYb.zroot hYb.mono hYb.root hlen2 hnz
        rw [APd_iff]
        intro ctx hc ws hw hG
        refine GoodFb_snoc_innerJs hw (GCtx_CtxOk k ctx hc)
          (GCtx_CtxX_one k ctx hc X hX) hZ hYb hlen2 hp ?_
        intro n hn
        have hh := hnat n hn
        simp only [Set.mem_setOf_eq] at hh
        exact (APd_iff k _).mp (hh (Bok_oper hYb hn) k Z hZ hRZ X hX hXk) ctx hc ws hw hG
    · exact absurd hm (Nat.not_lt_zero m)
  intro Y hYb k Z hZ hRZ X hX hXk
  exact key hYb.mem hYb k Z hZ hRZ X hX hXk

#print axioms AYd



/-! ### `APd` の閉包 → すべての木が普遍 -/

theorem APd_pay : ∀ (k : ℕ) (V : Jk1), JkJ V → APd k V → ∀ C : TrioSeq, Bok C →
    APd k (Jk1.pay V C)
  | 0, V, hV, hVk, C, hC => APz_pay hV hVk hC
  | (k + 1), V, hV, hVk, C, hC => fun U hU hUk => AYd C hC k V hV hVk U hU hUk

theorem APd_oneNil (k : ℕ) (V : Jk1) (hV : JkJ V) (hVk : APd k V) :
    APd k (Jk1.one V Jk1.nil) := by
  rw [APd_iff]
  intro ctx hc
  refine APnil_gen ctx (GCtx_CtxOk k ctx hc) V
    (GCtx_CtxX_one k ctx hc V hV) ((APd_iff k V).mp hVk ctx hc) ?_
  intro C hC
  exact (APd_iff k _).mp (APd_pay k V hV hVk C hC) ctx hc

theorem APd_nil : ∀ k : ℕ, APd k Jk1.nil
  | 0 => APz_nil
  | (k + 1) => fun U hU hUk => APd_oneNil k U hU hUk

theorem APd_one (k : ℕ) {V W : Jk1} (hV : JkJ V) (hVk : APd k V) (hW : APd (k + 1) W) :
    APd k (Jk1.one V W) := hW V hV hVk


/-! ### 木の連結と、1 の列の塔の木 -/

/-- 木の連結。`jk1 l (appJ N1 N2) = jk1 l N1 ++ jk1 l N2`。 -/
def appJ : Jk1 → Jk1 → Jk1
  | N1, Jk1.nil => N1
  | N1, Jk1.pay N2 Y => Jk1.pay (appJ N1 N2) Y
  | N1, Jk1.one N2 M => Jk1.one (appJ N1 N2) M
  | _, Jk1.two N2 M => Jk1.two N2 M

theorem jk1_appJ : ∀ (N2 N1 : Jk1) (l : ℕ), TopOk N2 →
    jk1 l (appJ N1 N2) = jk1 l N1 ++ jk1 l N2
  | Jk1.nil, N1, l, _ => by simp [appJ, jk1]
  | Jk1.pay N2 Y, N1, l, h => by
      show jk1 l (appJ N1 N2) ++ shiftr01 (l + 1) 0 Y = _
      rw [jk1_appJ N2 N1 l h]
      show _ = jk1 l N1 ++ (jk1 l N2 ++ shiftr01 (l + 1) 0 Y)
      rw [List.append_assoc]
  | Jk1.one N2 M, N1, l, h => by
      show jk1 l (appJ N1 N2) ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) M) = _
      rw [jk1_appJ N2 N1 l h]
      show _ = jk1 l N1 ++ (jk1 l N2 ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) M))
      rw [List.append_assoc]
  | Jk1.two _ _, _, _, h => absurd h (by simp [TopOk])

/-- 「1 の列 + junk `M'`」を入れ子に `n` 回繰り返した木。 -/
def twr (M' : Jk1) : ℕ → Jk1
  | 0 => Jk1.nil
  | (n + 1) => Jk1.one Jk1.nil (appJ M' (twr M' n))

theorem JkJ_twr_app {M' : Jk1} (hM' : JkJ M') : ∀ n : ℕ, JkJ (appJ M' (twr M' n))
  | 0 => hM'
  | (n + 1) => ⟨hM', JkJ_twr_app hM' n⟩

theorem TopOk_twr (M' : Jk1) : ∀ n : ℕ, TopOk (twr M' n)
  | 0 => trivial
  | (n + 1) => trivial

theorem JkOk_twr {M' : Jk1} (hM' : JkJ M') : ∀ n : ℕ, JkOk (twr M' n)
  | 0 => trivial
  | (n + 1) => ⟨trivial, JkJ_twr_app hM' n⟩

theorem jk1_twr : ∀ (M' : Jk1) (n l : ℕ),
    jk1 l (twr M' n) = (List.range n).flatMap
      (fun k => shiftr01 k 0 (((l + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) M'))
  | M', 0, l => by simp [twr, jk1]
  | M', (n + 1), l => by
      show jk1 l Jk1.nil ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) ::
        jk1 (l + 1) (appJ M' (twr M' n))) = _
      rw [jk1_appJ (twr M' n) M' (l + 1) (TopOk_twr M' n), jk1_twr M' n (l + 1),
        List.range_succ_eq_map,
        List.flatMap_cons]
      simp only [jk1, List.nil_append, shiftr01_zero, List.flatMap_map, Function.comp_def]
      congr 1
      congr 1
      apply List.flatMap_congr
      intro k _
      rw [show ((l + 1 + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1 + 1) M'
          = shiftr01 1 0 (((l + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) M') from by
        show _ = shiftr01 1 0 [((l + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 1 0 (jk1 (l + 1) M')
        rw [shift_col, jk1_shift M' (l + 1) 1]
        rfl, shiftr01_add0]
      congr 1
      omega

#print axioms jk1_twr

/-! ### 階段の木と、2 の記録を項として継ぐ -/

/-- 階段の木: 1 の列が `n` 段。 -/
def stairJ : ℕ → Jk1
  | 0 => Jk1.nil
  | (n + 1) => Jk1.one Jk1.nil (stairJ n)

theorem JkJ_stairJ : ∀ n : ℕ, JkJ (stairJ n)
  | 0 => trivial
  | (n + 1) => ⟨trivial, JkJ_stairJ n⟩

theorem JkOk_stairJ : ∀ n : ℕ, JkOk (stairJ n)
  | 0 => trivial
  | (n + 1) => ⟨trivial, JkJ_stairJ n⟩

theorem jk1_stairJ_succ (n l : ℕ) :
    jk1 l (stairJ (n + 1)) = ((l + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) (stairJ n) := by
  show jk1 l Jk1.nil ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) (stairJ n)) = _
  simp [jk1]

theorem jk1_stairJ : ∀ (n l : ℕ),
    jk1 l (stairJ n) = (List.range n).map (fun k => ((l + 1 + k, 1, 0) : ℕ × ℕ × ℕ))
  | 0, l => by simp [stairJ, jk1]
  | (n + 1), l => by
      rw [jk1_stairJ_succ n l, jk1_stairJ n (l + 1), List.range_succ_eq_map, List.map_cons,
        List.map_map]
      congr 1
      apply List.map_congr_left
      intro k _
      show ((l + 1 + 1 + k, 1, 0) : ℕ × ℕ × ℕ) = ((l + 1 + (k + 1), 1, 0) : ℕ × ℕ × ℕ)
      congr 1
      omega

theorem flatMap_sing {α β : Type} (l : List α) (f : α → β) :
    l.flatMap (fun x => [f x]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem APd_stair : ∀ (m k : ℕ), APd k (stairJ m)
  | 0, k => APd_nil k
  | (m + 1), k => APd_one k JkJ_nil (APd_nil k) (APd_stair m (k + 1))

/-- 1 の列の塔は階段の木そのもの。 -/
theorem Mtw_stair (Y0 : TrioSeq) (l n : ℕ) :
    Mtw Y0 [((l + 1, 1, 0) : ℕ × ℕ × ℕ)] n = Y0 ++ jk1 l (stairJ n) := by
  rw [Mtw, jk1_stairJ n l, ← flatMap_sing]
  congr 1
  all_goals (apply List.flatMap_congr; intro k _; rw [shift_col])

theorem colJ_plug_stair (a b : ℕ) (ctx : List Frm) (V : Jk1) (l : ℕ)
    (hl : l = a + dep ctx + 1) (m : ℕ) :
    colJ a b (plug (ctx ++ [Frm.fone V]) (stairJ m))
      = colJ a b (plug ctx V) ++ jk1 l (stairJ (m + 1)) := by
  subst hl
  rw [plug_snoc, colJ_plug_one a b ctx V (stairJ m),
    jk1_stairJ_succ m (a + dep ctx + 1),
    show a + dep ctx + 1 + 1 = a + dep ctx + 2 from by omega]

theorem colJ_plug_twostair (a b : ℕ) (ctx : List Frm) (V : Jk1) (l : ℕ)
    (hl : l = a + dep ctx + 1) :
    colJ a b (plug (ctx ++ [Frm.fone V]) (Jk1.two Jk1.nil Jk1.nil))
      = (colJ a b (plug ctx V) ++ [((l + 1, 1, 0) : ℕ × ℕ × ℕ)])
        ++ [((l + 1 + 1, 2, 0) : ℕ × ℕ × ℕ)] := by
  subst hl
  rw [plug_snoc, colJ_plug_one a b ctx V (Jk1.two Jk1.nil Jk1.nil),
    show a + dep ctx + 1 + 1 = a + dep ctx + 2 from by omega]
  have e : jk1 (a + dep ctx + 2) (Jk1.two Jk1.nil Jk1.nil)
      = [((a + dep ctx + 2 + 1, 2, 0) : ℕ × ℕ × ℕ)] := by simp [jk1]
  rw [e]
  simp [List.append_assoc]

theorem wordJ_snoc_plug_stair (a b : ℕ) (ws : List Jk1) (ctx : List Frm) (V : Jk1) (l : ℕ)
    (hl : l = a + dep ctx + 1) (m : ℕ) :
    wordJ a b (ws ++ [plug (ctx ++ [Frm.fone V]) (stairJ m)])
      = wordJ a b (ws ++ [plug ctx V]) ++ jk1 l (stairJ (m + 1)) := by
  rw [wordJ_append, wordJ_singleton, colJ_plug_stair a b ctx V l hl m, wordJ_append,
    wordJ_singleton, List.append_assoc]

theorem wordJ_snoc_twostair (a b : ℕ) (ws : List Jk1) (ctx : List Frm) (V : Jk1) (l : ℕ)
    (hl : l = a + dep ctx + 1) :
    wordJ a b (ws ++ [plug (ctx ++ [Frm.fone V]) (Jk1.two Jk1.nil Jk1.nil)])
      = (wordJ a b (ws ++ [plug ctx V]) ++ [((l + 1, 1, 0) : ℕ × ℕ × ℕ)])
        ++ [((l + 1 + 1, 2, 0) : ℕ × ℕ × ℕ)] := by
  rw [wordJ_append, wordJ_singleton, colJ_plug_twostair a b ctx V l hl, wordJ_append,
    wordJ_singleton]
  simp [List.append_assoc]

/-- 良い文脈は「外側の文脈 + 最内の木」に割れて、外側だけでも良い。 -/
theorem GCtx_split : ∀ (k : ℕ) (ctx : List Frm), GCtx k ctx →
    ∃ (ctx0 : List Frm) (V : Jk1), ctx = ctx0 ++ [Frm.fone V] ∧ GOK (plug ctx0 V)
  | 0, ctx, h => by
      obtain ⟨U, rfl, -, hGU⟩ := h
      exact ⟨[], U, rfl, hGU⟩
  | (k + 1), ctx, h => by
      obtain ⟨ctx0, U, rfl, hc0, -, hUk⟩ := h
      exact ⟨ctx0, U, rfl, (APd_iff k U).mp hUk ctx0 (by exact hc0)⟩

/-- ★★★★★ 2 の記録は、どの深さでも項として継げる（1 の列の直上になるので上がらない）。 -/
theorem APd_twoNil (k : ℕ) : APd k (Jk1.two Jk1.nil Jk1.nil) := by
  rw [APd_iff]
  intro ctx hc
  obtain ⟨ctx0, V, rfl, hGV⟩ := GCtx_split k ctx hc
  have hcO : CtxOk (ctx0 ++ [Frm.fone V]) := GCtx_CtxOk k _ hc
  have hstair : ∀ m : ℕ, GOK (plug (ctx0 ++ [Frm.fone V]) (stairJ m)) :=
    fun m => (APd_iff k (stairJ m)).mp (APd_stair m k) _ hc
  intro ws hw hG
  have hwO : WOk (ws ++ [plug (ctx0 ++ [Frm.fone V]) (Jk1.two Jk1.nil Jk1.nil)]) :=
    WOk_append hw (WOk_singleton (JkOk_plug _ hcO _
      ((CtxX_snoc1 ctx0 V _).mpr ⟨trivial, trivial⟩)))
  have hbaseV : GoodFb (fun a b => wordJ a b (ws ++ [plug ctx0 V])) := hGV ws hw hG
  have hstG : ∀ m : ℕ,
      GoodFb (fun a b => wordJ a b (ws ++ [plug (ctx0 ++ [Frm.fone V]) (stairJ m)])) :=
    fun m => hstair m ws hw hG
  refine ⟨fun a b => wordJ_ge a b _, fun a b => wordJ_mono hwO,
    fun a b s => wordJ_shift a b s _, ?_, ?_, ?_⟩
  · intro y c hy
    refine ⟨fun x hx => by have := wordJ_ge (c + 1) (y + 1) _ x hx; omega, wordJ_mono hwO, ?_⟩
    intro E hE t Z hZ
    rw [wordJ_shift, wordJ_snoc_twostair (c + 1 + t) (y + 1) ws ctx0 V
      (c + 1 + t + dep ctx0 + 1) rfl]
    set a := c + 1 + t with ha
    have hbase0 : Z ++ ([((a, y + 1, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a (y + 1) (ws ++ [plug ctx0 V])) ∈ W 0 := by
      have h0 := (hbaseV.pu y c hy).2.2 E hE t Z hZ
      rw [wordJ_shift] at h0
      simpa [ha] using h0
    have htw : ∀ n, Mtw (Z ++ ([((a, y + 1, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a (y + 1) (ws ++ [plug ctx0 V])))
        [((a + dep ctx0 + 1 + 1, 1, 0) : ℕ × ℕ × ℕ)] n ∈ W 0 := by
      intro n
      rw [Mtw_stair]
      cases n with
      | zero => simpa [stairJ, jk1] using hbase0
      | succ m =>
          have h1 := ((hstG m).pu y c hy).2.2 E hE t Z hZ
          rw [wordJ_shift, wordJ_snoc_plug_stair (c + 1 + t) (y + 1) ws ctx0 V
            (c + 1 + t + dep ctx0 + 1) rfl m] at h1
          simpa [ha, List.append_assoc] using h1
    have h := snocY_mem (Y0 := Z ++ ([((a, y + 1, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a (y + 1) (ws ++ [plug ctx0 V])))
      (M := [((a + dep ctx0 + 1 + 1, 1, 0) : ℕ × ℕ × ℕ)])
      (L := a + dep ctx0 + 1 + 1) (y := 2)
      (by simp) (MidD_col (a + dep ctx0 + 1 + 1) 1 (by omega) (by omega))
      (by simp [entry]) (by omega) htw
    simpa [List.append_assoc] using h
  · intro c E hI
    refine ⟨fun x hx => by have := wordJ_ge (c + 1) 2 _ x hx; omega, wordJ_mono hwO, ?_⟩
    intro j t Z hZ
    rw [wordJ_shift, wordJ_snoc_twostair (c + 1 + t) 2 ws ctx0 V
      (c + 1 + t + dep ctx0 + 1) rfl]
    set a := c + 1 + t with ha
    have hbase0 : Z ++ ([((a, 2, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a 2 (ws ++ [plug ctx0 V])) ∈ W 0 := by
      have h0 := (hbaseV.pk c E hI).2.2 j t Z hZ
      rw [wordJ_shift] at h0
      simpa [ha] using h0
    have htw : ∀ n, Mtw (Z ++ ([((a, 2, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a 2 (ws ++ [plug ctx0 V])))
        [((a + dep ctx0 + 1 + 1, 1, 0) : ℕ × ℕ × ℕ)] n ∈ W 0 := by
      intro n
      rw [Mtw_stair]
      cases n with
      | zero => simpa [stairJ, jk1] using hbase0
      | succ m =>
          have h1 := ((hstG m).pk c E hI).2.2 j t Z hZ
          rw [wordJ_shift, wordJ_snoc_plug_stair (c + 1 + t) 2 ws ctx0 V
            (c + 1 + t + dep ctx0 + 1) rfl m] at h1
          simpa [ha, List.append_assoc] using h1
    have h := snocY_mem (Y0 := Z ++ ([((a, 2, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a 2 (ws ++ [plug ctx0 V])))
      (M := [((a + dep ctx0 + 1 + 1, 1, 0) : ℕ × ℕ × ℕ)])
      (L := a + dep ctx0 + 1 + 1) (y := 2)
      (by simp) (MidD_col (a + dep ctx0 + 1 + 1) 1 (by omega) (by omega))
      (by simp [entry]) (by omega) htw
    simpa [List.append_assoc] using h
  · intro h
    have hmid : MidD (h + 2) (((h + 1, 1, 0) : ℕ × ℕ × ℕ) ::
        wordJ (h + 1) 1 (ws ++ [plug (ctx0 ++ [Frm.fone V]) (Jk1.two Jk1.nil Jk1.nil)])) := by
      have h1 := MidD_wordJ (h + 1) 1 (by omega) (by omega) hwO
      simpa [show h + 1 + 1 = h + 2 from by omega] using h1
    refine ⟨hmid, by simp [entry], ?_⟩
    intro P hP s A' hA'
    rw [show ((h + 1, 1, 0) : ℕ × ℕ × ℕ) ::
          wordJ (h + 1) 1 (ws ++ [plug (ctx0 ++ [Frm.fone V]) (Jk1.two Jk1.nil Jk1.nil)])
        = [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ++
          wordJ (h + 1) 1 (ws ++ [plug (ctx0 ++ [Frm.fone V]) (Jk1.two Jk1.nil Jk1.nil)]) from rfl,
      shiftr01_append0, shift_col, wordJ_shift,
      wordJ_snoc_twostair (h + 1 + s) 1 ws ctx0 V (h + 1 + s + dep ctx0 + 1) rfl]
    set a := h + 1 + s with ha
    have hbase0 : A' ++ ([((a, 1, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a 1 (ws ++ [plug ctx0 V])) ∈ W 0 := by
      have h0 := (hbaseV.seg (h + s)).reapp P hP 0 A' (by simpa using hA')
      rw [show ((h + s + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordJ (h + s + 1) 1 (ws ++ [plug ctx0 V])
          = [((h + s + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ wordJ (h + s + 1) 1 (ws ++ [plug ctx0 V])
          from rfl] at h0
      simpa [ha, show h + s + 1 = h + 1 + s from by omega] using h0
    have htw : ∀ n, Mtw (A' ++ ([((a, 1, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a 1 (ws ++ [plug ctx0 V])))
        [((a + dep ctx0 + 1 + 1, 1, 0) : ℕ × ℕ × ℕ)] n ∈ W 0 := by
      intro n
      rw [Mtw_stair]
      cases n with
      | zero => simpa [stairJ, jk1] using hbase0
      | succ m =>
          have h1 := ((hstG m).seg (h + s)).reapp P hP 0 A' (by simpa using hA')
          rw [show ((h + s + 1, 1, 0) : ℕ × ℕ × ℕ) ::
                wordJ (h + s + 1) 1 (ws ++ [plug (ctx0 ++ [Frm.fone V]) (stairJ m)])
              = [((h + s + 1, 1, 0) : ℕ × ℕ × ℕ)] ++
                wordJ (h + s + 1) 1 (ws ++ [plug (ctx0 ++ [Frm.fone V]) (stairJ m)]) from rfl] at h1
          rw [wordJ_snoc_plug_stair (h + s + 1) 1 ws ctx0 V (h + s + 1 + dep ctx0 + 1) rfl m]
            at h1
          simpa [ha, show h + s + 1 = h + 1 + s from by omega, List.append_assoc] using h1
    have hh := snocY_mem (Y0 := A' ++ ([((a, 1, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a 1 (ws ++ [plug ctx0 V])))
      (M := [((a + dep ctx0 + 1 + 1, 1, 0) : ℕ × ℕ × ℕ)])
      (L := a + dep ctx0 + 1 + 1) (y := 2)
      (by simp) (MidD_col (a + dep ctx0 + 1 + 1) 1 (by omega) (by omega))
      (by simp [entry]) (by omega) htw
    simpa [List.append_assoc] using hh

#print axioms APd_twoNil

/-! ### 一般の左兄弟つき 2 の記録（`two N nil`） -/

theorem appJ_twr : ∀ (N : Jk1) (m : ℕ), appJ N (twr N m) = plug (List.replicate m (Frm.fone N)) N
  | _, 0 => rfl
  | N, (m + 1) => by
      show Jk1.one (appJ N Jk1.nil) (appJ N (twr N m)) = _
      rw [appJ_twr N m]
      rfl

theorem plug_append : ∀ (c1 c2 : List Frm) (T : Jk1), plug (c1 ++ c2) T = plug c1 (plug c2 T)
  | [], _, _ => rfl
  | (Frm.fone N :: rest), c2, T => by
      show Jk1.one N (plug (rest ++ c2) T) = Jk1.one N (plug rest (plug c2 T))
      rw [plug_append rest c2 T]
  | (Frm.fotw N :: rest), c2, T => by
      show Jk1.one N (Jk1.two Jk1.nil (plug (rest ++ c2) T))
        = Jk1.one N (Jk1.two Jk1.nil (plug rest (plug c2 T)))
      rw [plug_append rest c2 T]

theorem GCtx_rep {N : Jk1} (hJN : JkJ N) (hNall : ∀ k, APd k N) :
    ∀ (m k : ℕ) (ctx : List Frm), GCtx k ctx → GCtx (k + m) (ctx ++ List.replicate m (Frm.fone N))
  | 0, k, ctx, hc => by simpa using hc
  | (m + 1), k, ctx, hc => by
      have h1 := GCtx_rep hJN hNall m k ctx hc
      have e : ctx ++ List.replicate (m + 1) (Frm.fone N)
          = (ctx ++ List.replicate m (Frm.fone N)) ++ [Frm.fone N] := by
        rw [List.replicate_succ']
        simp
      rw [e, show k + (m + 1) = (k + m) + 1 from by omega]
      exact ⟨ctx ++ List.replicate m (Frm.fone N), N, rfl, h1, hJN, hNall (k + m)⟩

theorem APd_plug_rep (N : Jk1) (hJN : JkJ N) (hNall : ∀ k, APd k N) (m k : ℕ) :
    APd k (plug (List.replicate m (Frm.fone N)) N) := by
  rw [APd_iff]
  intro ctx hc
  rw [← plug_append]
  exact (APd_iff (k + m) N).mp (hNall (k + m)) _ (GCtx_rep hJN hNall m k ctx hc)

theorem Mtw_twr (Y0 : TrioSeq) {N : Jk1} (l n : ℕ) :
    Mtw Y0 (((l + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) N) n = Y0 ++ jk1 l (twr N n) := by
  rw [Mtw, jk1_twr N n l]

theorem MidD_colN (d : ℕ) (N : Jk1) (hd : 1 ≤ d) (hJN : JkJ N) :
    MidD (d + 1) (((d, 1, 0) : ℕ × ℕ × ℕ) :: jk1 d N) := by
  have h1 := MidD_append (MidD_col d 1 hd (by omega)) (N := jk1 d N)
    (fun x hx => by have := jk1_ge N d x hx; omega) (jk1_mono N (JkA_of_JkJ N hJN) d)
  simpa using h1

theorem colJ_plug_twoN (a b : ℕ) (ctx : List Frm) (V : Jk1) {N : Jk1} (l : ℕ)
    (hl : l = a + dep ctx + 1) :
    colJ a b (plug (ctx ++ [Frm.fone V]) (Jk1.two N Jk1.nil))
      = (colJ a b (plug ctx V) ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) N))
        ++ [((l + 1 + 1, 2, 0) : ℕ × ℕ × ℕ)] := by
  subst hl
  rw [plug_snoc, colJ_plug_one a b ctx V (Jk1.two N Jk1.nil),
    show a + dep ctx + 1 + 1 = a + dep ctx + 2 from by omega]
  have e : jk1 (a + dep ctx + 2) (Jk1.two N Jk1.nil)
      = jk1 (a + dep ctx + 2) N ++ [((a + dep ctx + 2 + 1, 2, 0) : ℕ × ℕ × ℕ)] := by
    show jk1 (a + dep ctx + 2) N ++
      (((a + dep ctx + 2 + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (a + dep ctx + 2 + 1) Jk1.nil) = _
    simp [jk1]
  rw [e]
  simp [List.append_assoc]

theorem wordJ_snoc_twoN (a b : ℕ) (ws : List Jk1) (ctx : List Frm) (V : Jk1) {N : Jk1} (l : ℕ)
    (hl : l = a + dep ctx + 1) :
    wordJ a b (ws ++ [plug (ctx ++ [Frm.fone V]) (Jk1.two N Jk1.nil)])
      = (wordJ a b (ws ++ [plug ctx V]) ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) N))
        ++ [((l + 1 + 1, 2, 0) : ℕ × ℕ × ℕ)] := by
  rw [wordJ_append, wordJ_singleton, colJ_plug_twoN a b ctx V l hl, wordJ_append,
    wordJ_singleton]
  simp [List.append_assoc]

theorem colJ_plug_twr (a b : ℕ) (ctx : List Frm) (V : Jk1) {N : Jk1} (l : ℕ)
    (hl : l = a + dep ctx + 1) (m : ℕ) :
    colJ a b (plug (ctx ++ [Frm.fone V]) (plug (List.replicate m (Frm.fone N)) N))
      = colJ a b (plug ctx V) ++ jk1 l (twr N (m + 1)) := by
  subst hl
  rw [plug_snoc, colJ_plug_one a b ctx V (plug (List.replicate m (Frm.fone N)) N),
    show a + dep ctx + 1 + 1 = a + dep ctx + 2 from by omega]
  have e : jk1 (a + dep ctx + 1) (twr N (m + 1))
      = ((a + dep ctx + 2, 1, 0) : ℕ × ℕ × ℕ) ::
        jk1 (a + dep ctx + 2) (plug (List.replicate m (Frm.fone N)) N) := by
    show jk1 (a + dep ctx + 1) Jk1.nil ++
      (((a + dep ctx + 1 + 1, 1, 0) : ℕ × ℕ × ℕ) ::
        jk1 (a + dep ctx + 1 + 1) (appJ N (twr N m))) = _
    rw [appJ_twr N m, show a + dep ctx + 1 + 1 = a + dep ctx + 2 from by omega]
    simp [jk1]
  rw [e]

theorem wordJ_snoc_plug_twr (a b : ℕ) (ws : List Jk1) (ctx : List Frm) (V : Jk1) {N : Jk1} (l : ℕ)
    (hl : l = a + dep ctx + 1) (m : ℕ) :
    wordJ a b (ws ++ [plug (ctx ++ [Frm.fone V]) (plug (List.replicate m (Frm.fone N)) N)])
      = wordJ a b (ws ++ [plug ctx V]) ++ jk1 l (twr N (m + 1)) := by
  rw [wordJ_append, wordJ_singleton, colJ_plug_twr a b ctx V l hl m, wordJ_append,
    wordJ_singleton, List.append_assoc]

theorem APd_twoNilGen (N : Jk1) (hJN : JkJ N) (hNall : ∀ k, APd k N) (k : ℕ) :
    APd k (Jk1.two N Jk1.nil) := by
  rw [APd_iff]
  intro ctx hc
  obtain ⟨ctx0, V, rfl, hGV⟩ := GCtx_split k ctx hc
  have hcO : CtxOk (ctx0 ++ [Frm.fone V]) := GCtx_CtxOk k _ hc
  have hstair : ∀ m : ℕ, GOK (plug (ctx0 ++ [Frm.fone V]) (plug (List.replicate m (Frm.fone N)) N)) :=
    fun m => (APd_iff k _).mp (APd_plug_rep N hJN hNall m k) _ hc
  intro ws hw hG
  have hwO : WOk (ws ++ [plug (ctx0 ++ [Frm.fone V]) (Jk1.two N Jk1.nil)]) :=
    WOk_append hw (WOk_singleton (JkOk_plug _ hcO _
      ((CtxX_snoc1 ctx0 V _).mpr ⟨hJN, trivial⟩)))
  have hbaseV : GoodFb (fun a b => wordJ a b (ws ++ [plug ctx0 V])) := hGV ws hw hG
  have hstG : ∀ m : ℕ,
      GoodFb (fun a b => wordJ a b (ws ++ [plug (ctx0 ++ [Frm.fone V]) (plug (List.replicate m (Frm.fone N)) N)])) :=
    fun m => hstair m ws hw hG
  refine ⟨fun a b => wordJ_ge a b _, fun a b => wordJ_mono hwO,
    fun a b s => wordJ_shift a b s _, ?_, ?_, ?_⟩
  · intro y c hy
    refine ⟨fun x hx => by have := wordJ_ge (c + 1) (y + 1) _ x hx; omega, wordJ_mono hwO, ?_⟩
    intro E hE t Z hZ
    rw [wordJ_shift, wordJ_snoc_twoN (c + 1 + t) (y + 1) ws ctx0 V
      (c + 1 + t + dep ctx0 + 1) rfl]
    set a := c + 1 + t with ha
    have hbase0 : Z ++ ([((a, y + 1, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a (y + 1) (ws ++ [plug ctx0 V])) ∈ W 0 := by
      have h0 := (hbaseV.pu y c hy).2.2 E hE t Z hZ
      rw [wordJ_shift] at h0
      simpa [ha] using h0
    have htw : ∀ n, Mtw (Z ++ ([((a, y + 1, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a (y + 1) (ws ++ [plug ctx0 V])))
        (((a + dep ctx0 + 1 + 1, 1, 0) : ℕ × ℕ × ℕ) ::
          jk1 (a + dep ctx0 + 1 + 1) N) n ∈ W 0 := by
      intro n
      rw [Mtw_twr]
      cases n with
      | zero => simpa [twr, jk1] using hbase0
      | succ m =>
          have h1 := ((hstG m).pu y c hy).2.2 E hE t Z hZ
          rw [wordJ_shift, wordJ_snoc_plug_twr (c + 1 + t) (y + 1) ws ctx0 V
            (c + 1 + t + dep ctx0 + 1) rfl m] at h1
          simpa [ha, List.append_assoc] using h1
    have h := snocY_mem (Y0 := Z ++ ([((a, y + 1, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a (y + 1) (ws ++ [plug ctx0 V])))
      (M := ((a + dep ctx0 + 1 + 1, 1, 0) : ℕ × ℕ × ℕ) ::
        jk1 (a + dep ctx0 + 1 + 1) N)
      (L := a + dep ctx0 + 1 + 1) (y := 2)
      (by simp) (MidD_colN (a + dep ctx0 + 1 + 1) N (by omega) hJN)
      (by simp [entry]) (by omega) htw
    simpa [List.append_assoc] using h
  · intro c E hI
    refine ⟨fun x hx => by have := wordJ_ge (c + 1) 2 _ x hx; omega, wordJ_mono hwO, ?_⟩
    intro j t Z hZ
    rw [wordJ_shift, wordJ_snoc_twoN (c + 1 + t) 2 ws ctx0 V
      (c + 1 + t + dep ctx0 + 1) rfl]
    set a := c + 1 + t with ha
    have hbase0 : Z ++ ([((a, 2, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a 2 (ws ++ [plug ctx0 V])) ∈ W 0 := by
      have h0 := (hbaseV.pk c E hI).2.2 j t Z hZ
      rw [wordJ_shift] at h0
      simpa [ha] using h0
    have htw : ∀ n, Mtw (Z ++ ([((a, 2, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a 2 (ws ++ [plug ctx0 V])))
        (((a + dep ctx0 + 1 + 1, 1, 0) : ℕ × ℕ × ℕ) ::
          jk1 (a + dep ctx0 + 1 + 1) N) n ∈ W 0 := by
      intro n
      rw [Mtw_twr]
      cases n with
      | zero => simpa [twr, jk1] using hbase0
      | succ m =>
          have h1 := ((hstG m).pk c E hI).2.2 j t Z hZ
          rw [wordJ_shift, wordJ_snoc_plug_twr (c + 1 + t) 2 ws ctx0 V
            (c + 1 + t + dep ctx0 + 1) rfl m] at h1
          simpa [ha, List.append_assoc] using h1
    have h := snocY_mem (Y0 := Z ++ ([((a, 2, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a 2 (ws ++ [plug ctx0 V])))
      (M := ((a + dep ctx0 + 1 + 1, 1, 0) : ℕ × ℕ × ℕ) ::
        jk1 (a + dep ctx0 + 1 + 1) N)
      (L := a + dep ctx0 + 1 + 1) (y := 2)
      (by simp) (MidD_colN (a + dep ctx0 + 1 + 1) N (by omega) hJN)
      (by simp [entry]) (by omega) htw
    simpa [List.append_assoc] using h
  · intro h
    have hmid : MidD (h + 2) (((h + 1, 1, 0) : ℕ × ℕ × ℕ) ::
        wordJ (h + 1) 1 (ws ++ [plug (ctx0 ++ [Frm.fone V]) (Jk1.two N Jk1.nil)])) := by
      have h1 := MidD_wordJ (h + 1) 1 (by omega) (by omega) hwO
      simpa [show h + 1 + 1 = h + 2 from by omega] using h1
    refine ⟨hmid, by simp [entry], ?_⟩
    intro P hP s A' hA'
    rw [show ((h + 1, 1, 0) : ℕ × ℕ × ℕ) ::
          wordJ (h + 1) 1 (ws ++ [plug (ctx0 ++ [Frm.fone V]) (Jk1.two N Jk1.nil)])
        = [((h + 1, 1, 0) : ℕ × ℕ × ℕ)] ++
          wordJ (h + 1) 1 (ws ++ [plug (ctx0 ++ [Frm.fone V]) (Jk1.two N Jk1.nil)]) from rfl,
      shiftr01_append0, shift_col, wordJ_shift,
      wordJ_snoc_twoN (h + 1 + s) 1 ws ctx0 V (h + 1 + s + dep ctx0 + 1) rfl]
    set a := h + 1 + s with ha
    have hbase0 : A' ++ ([((a, 1, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a 1 (ws ++ [plug ctx0 V])) ∈ W 0 := by
      have h0 := (hbaseV.seg (h + s)).reapp P hP 0 A' (by simpa using hA')
      rw [show ((h + s + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordJ (h + s + 1) 1 (ws ++ [plug ctx0 V])
          = [((h + s + 1, 1, 0) : ℕ × ℕ × ℕ)] ++ wordJ (h + s + 1) 1 (ws ++ [plug ctx0 V])
          from rfl] at h0
      simpa [ha, show h + s + 1 = h + 1 + s from by omega] using h0
    have htw : ∀ n, Mtw (A' ++ ([((a, 1, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a 1 (ws ++ [plug ctx0 V])))
        (((a + dep ctx0 + 1 + 1, 1, 0) : ℕ × ℕ × ℕ) ::
          jk1 (a + dep ctx0 + 1 + 1) N) n ∈ W 0 := by
      intro n
      rw [Mtw_twr]
      cases n with
      | zero => simpa [twr, jk1] using hbase0
      | succ m =>
          have h1 := ((hstG m).seg (h + s)).reapp P hP 0 A' (by simpa using hA')
          rw [show ((h + s + 1, 1, 0) : ℕ × ℕ × ℕ) ::
                wordJ (h + s + 1) 1 (ws ++ [plug (ctx0 ++ [Frm.fone V]) (plug (List.replicate m (Frm.fone N)) N)])
              = [((h + s + 1, 1, 0) : ℕ × ℕ × ℕ)] ++
                wordJ (h + s + 1) 1 (ws ++ [plug (ctx0 ++ [Frm.fone V]) (plug (List.replicate m (Frm.fone N)) N)]) from rfl] at h1
          rw [wordJ_snoc_plug_twr (h + s + 1) 1 ws ctx0 V (h + s + 1 + dep ctx0 + 1) rfl m]
            at h1
          simpa [ha, show h + s + 1 = h + 1 + s from by omega, List.append_assoc] using h1
    have hh := snocY_mem (Y0 := A' ++ ([((a, 1, 0) : ℕ × ℕ × ℕ)] ++
        wordJ a 1 (ws ++ [plug ctx0 V])))
      (M := ((a + dep ctx0 + 1 + 1, 1, 0) : ℕ × ℕ × ℕ) ::
        jk1 (a + dep ctx0 + 1 + 1) N)
      (L := a + dep ctx0 + 1 + 1) (y := 2)
      (by simp) (MidD_colN (a + dep ctx0 + 1 + 1) N (by omega) hJN)
      (by simp [entry]) (by omega) htw
    simpa [List.append_assoc] using hh


#print axioms APd_twoNilGen

/-! ### 2 の記録の上に荷を吊るす（`two N (pay Z Y)`） -/

theorem jk1_plug_two : ∀ (ctx : List Frm) (N M : Jk1) (l : ℕ),
    jk1 l (plug ctx (Jk1.two N M))
      = jk1 l (plug ctx N) ++
        (((l + dep ctx + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + dep ctx + 1) M)
  | [], N, M, l => by
      show jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) M) = _
      simp [plug, dep]
  | (Frm.fone X :: rest), N, M, l => by
      show jk1 l X ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) (plug rest (Jk1.two N M)))
        = (jk1 l X ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) (plug rest N))) ++ _
      rw [jk1_plug_two rest N M (l + 1)]
      simp only [dep, List.cons_append, List.append_assoc]
      rw [show l + 1 + dep rest + 1 = l + (dep rest + 1) + 1 from by omega]
  | (Frm.fotw X :: rest), N, M, l => by
      show jk1 l X ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) ::
          (jk1 (l + 1) Jk1.nil ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ) ::
            jk1 (l + 2) (plug rest (Jk1.two N M))))) = _
      rw [jk1_plug_two rest N M (l + 2)]
      show _ = (jk1 l X ++ (((l + 1, 1, 0) : ℕ × ℕ × ℕ) ::
          (jk1 (l + 1) Jk1.nil ++ (((l + 2, 2, 0) : ℕ × ℕ × ℕ) ::
            jk1 (l + 2) (plug rest N))))) ++ _
      simp only [dep, jk1, List.nil_append, List.cons_append, List.append_assoc]
      rw [show l + 2 + dep rest + 1 = l + (dep rest + 2) + 1 from by omega]

theorem colJ_plug_two (a b : ℕ) (ctx : List Frm) (N M : Jk1) :
    colJ a b (plug ctx (Jk1.two N M))
      = colJ a b (plug ctx N) ++
        (((a + dep ctx + 2, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (a + dep ctx + 2) M) := by
  rw [colJ, colJ, jk1_plug_two ctx N M (a + 1),
    show a + 1 + dep ctx + 1 = a + dep ctx + 2 from by omega]
  rfl

theorem jk1_two_pay_nil (N Z : Jk1) : ∀ l,
    jk1 l (Jk1.two N (Jk1.pay Z [])) = jk1 l (Jk1.two N Z) := by
  intro l
  show jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) (Jk1.pay Z []))
    = jk1 l N ++ (((l + 1, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (l + 1) Z)
  rw [jk1_pay_nil]

theorem colJ_plug_twoPay (a b : ℕ) (ctx : List Frm) (N Z : Jk1) (Y : TrioSeq) :
    colJ a b (plug ctx (Jk1.two N (Jk1.pay Z Y)))
      = colJ a b (plug ctx (Jk1.two N Z)) ++ shiftr01 (a + dep ctx + 3) 0 Y := by
  rw [colJ_plug_two a b ctx N (Jk1.pay Z Y), colJ_plug_two a b ctx N Z, jk1,
    show a + dep ctx + 2 + 1 = a + dep ctx + 3 from by omega]
  simp [List.append_assoc]

/-- 「2 の記録 + junk `T`」を同じ高さに `n` 個並べた木。 -/
def twoIt (N T : Jk1) : ℕ → Jk1
  | 0 => N
  | (n + 1) => Jk1.two (twoIt N T n) T

theorem colJ_plug_twoIt (a b : ℕ) (ctx : List Frm) (N T : Jk1) : ∀ n : ℕ,
    colJ a b (plug ctx (twoIt N T n))
      = colJ a b (plug ctx N) ++ (List.range n).flatMap
        (fun _ => ((a + dep ctx + 2, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (a + dep ctx + 2) T)
  | 0 => by simp [twoIt]
  | (n + 1) => by
      show colJ a b (plug ctx (Jk1.two (twoIt N T n) T)) = _
      rw [colJ_plug_two a b ctx (twoIt N T n) T, colJ_plug_twoIt a b ctx N T n,
        List.range_succ, List.flatMap_append]
      simp [List.append_assoc]

theorem GoodFb_snoc_innerJt {ws : List Jk1} (hw : WOk ws) {ctx : List Frm} (hc : CtxOk ctx)
    {N Z : Jk1} (hN : JkJ N) (hZ : PayOnly Z) {Y : TrioSeq}
    (hcx : CtxX ctx (Jk1.two N (Jk1.pay Z Y)))
    (hY : Bok Y) (hlen : 2 ≤ Y.length)
    (hp : hasParent Y (srow Y (Y.length - 1)) (Y.length - 1))
    (hIH : ∀ n, 1 ≤ n →
      GoodFb (fun a b => wordJ a b (ws ++ [plug ctx (Jk1.two N (Jk1.pay Z (Y⟦n⟧)))]))) :
    GoodFb (fun a b => wordJ a b (ws ++ [plug ctx (Jk1.two N (Jk1.pay Z Y))])) := by
  refine GoodFb_of_keyJ (WOk_append hw (WOk_singleton
    (JkOk_plug ctx hc _ (hcx)))) hIH ?_
  intro Z0 a b hb hn
  have e : ∀ B : TrioSeq,
      Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) ::
        wordJ a b (ws ++ [plug ctx (Jk1.two N (Jk1.pay Z B))]))
      = (Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: wordJ a b (ws ++ [plug ctx (Jk1.two N Z)])))
        ++ shiftr01 (a + dep ctx + 3) 0 B := by
    intro B
    rw [wordJ_append, wordJ_singleton, colJ_plug_twoPay, wordJ_append, wordJ_singleton]
    simp [List.append_assoc]
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n hn'
  rw [e Y, oper_shift _ Y (a + dep ctx + 3) n hlen hp, ← e (Y⟦n⟧)]
  exact hn n hn'

theorem GoodFb_snoc_dupJt {ws : List Jk1} (hw : WOk ws) {ctx : List Frm} (hc : CtxOk ctx)
    {N Z : Jk1} (hN : JkJ N) (hZ : PayOnly Z) {Y : TrioSeq}
    (hcx : CtxX ctx (Jk1.two N (Jk1.pay Z (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]))))
    (hY0 : Bok (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])) (hY : Bok Y)
    (hIH : ∀ n, 1 ≤ n →
      GoodFb (fun a b => wordJ a b (ws ++ [plug ctx (twoIt N (Jk1.pay Z Y) n)]))) :
    GoodFb (fun a b => wordJ a b
      (ws ++ [plug ctx (Jk1.two N (Jk1.pay Z (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])))])) := by
  refine GoodFb_of_keyJ (WOk_append hw (WOk_singleton
    (JkOk_plug ctx hc _ (hcx)))) hIH ?_
  intro Z0 a b hb hn
  set p := dep ctx with hp
  set M : TrioSeq := ((a + p + 2, 2, 0) : ℕ × ℕ × ℕ) :: jk1 (a + p + 2) (Jk1.pay Z Y) with hM
  set Y0 : TrioSeq := Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) ::
    (wordJ a b ws ++ colJ a b (plug ctx N))) with hY0d
  have hhead : entry M 0 0 < a + p + 3 := by rw [hM]; simp [entry]
  have htail : ∀ r, 1 ≤ r → r < M.length → a + p + 3 ≤ entry M 0 r := by
    intro r hr1 hrl
    obtain ⟨u, rfl⟩ : ∃ u, r = u + 1 := ⟨r - 1, by omega⟩
    rw [hM, entry_cons_succ]
    have hu : u < (jk1 (a + p + 2) (Jk1.pay Z Y)).length := by
      rw [hM] at hrl; simp at hrl; omega
    have := entry0_of_ge (jk1_ge (Jk1.pay Z Y) (a + p + 2)) u hu
    omega
  have hcolsplit : ∀ n : ℕ, colJ a b (plug ctx (twoIt N (Jk1.pay Z Y) n))
      = colJ a b (plug ctx N) ++ (List.range n).flatMap (fun _ => M) := by
    intro n
    rw [colJ_plug_twoIt a b ctx N (Jk1.pay Z Y) n, hM, hp]
  have htw : ∀ n : ℕ, Y0 ++ (List.range n).flatMap (fun _ => M) ∈ W 0 := by
    intro n
    match n with
    | 0 =>
        have h1 := hn 1 (le_refl 1)
        rw [wordJ_append, wordJ_singleton, hcolsplit 1] at h1
        have h2 := W_take (by
          rw [show Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: (wordJ a b ws ++
              (colJ a b (plug ctx N) ++ (List.range 1).flatMap (fun _ => M))))
              = Y0 ++ (List.range 1).flatMap (fun _ => M) from by
                rw [hY0d]; simp [List.append_assoc]] at h1
          exact h1) Y0.length
        rw [List.take_left] at h2
        simpa using h2
    | (n + 1) =>
        have h1 := hn (n + 1) (by omega)
        rw [wordJ_append, wordJ_singleton, hcolsplit (n + 1)] at h1
        rw [show Z0 ++ (((a, b, 0) : ℕ × ℕ × ℕ) :: (wordJ a b ws ++
            (colJ a b (plug ctx N) ++ (List.range (n + 1)).flatMap (fun _ => M))))
            = Y0 ++ (List.range (n + 1)).flatMap (fun _ => M) from by
              rw [hY0d]; simp [List.append_assoc]] at h1
        exact h1
  have h := flat_mem'' (Y0 := Y0) (M := M) (d := a + p + 3) (by rw [hM]; simp)
    hhead htail htw
  rw [wordJ_append, wordJ_singleton,
    colJ_plug_two a b ctx N (Jk1.pay Z (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]))]
  have esplit : jk1 (a + p + 2) (Jk1.pay Z (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]))
      = jk1 (a + p + 2) (Jk1.pay Z Y) ++ [((a + p + 3, 0, 0) : ℕ × ℕ × ℕ)] := by
    show jk1 (a + p + 2) Z ++ shiftr01 (a + p + 3) 0 (Y ++ [((0, 0, 0) : ℕ × ℕ × ℕ)])
      = (jk1 (a + p + 2) Z ++ shiftr01 (a + p + 3) 0 Y) ++ _
    rw [shiftr01_append0, ← List.append_assoc]
    simp [shiftr01]
  rw [← hp, esplit]
  rw [hY0d] at h
  simpa [hM, List.append_assoc] using h

theorem APd_chainT {k : ℕ} {ctx : List Frm} (hc : GCtx k ctx) {N T : Jk1}
    (hN : JkJ N) (hNall : ∀ j, APd j N) (hT : PayOnly T)
    (hstep : ∀ N' : Jk1, JkJ N' → (∀ j, APd j N') → ∀ j, APd j (Jk1.two N' T)) :
    ∀ n, GOK (plug ctx (twoIt N T n)) ∧ JkJ (twoIt N T n) ∧ (∀ j, APd j (twoIt N T n))
  | 0 => ⟨(APd_iff k N).mp (hNall k) ctx hc, hN, hNall⟩
  | (n + 1) => by
      obtain ⟨-, h2, h3⟩ := APd_chainT hc hN hNall hT hstep n
      have h4 := hstep (twoIt N T n) h2 h3
      exact ⟨(APd_iff k _).mp (h4 k) ctx hc, ⟨h2, hT⟩, h4⟩

/-- ★★★ 2 の記録の上に `Bok` の荷を吊るす。 -/
theorem APd_twoPay : ∀ (Y : TrioSeq), Bok Y → ∀ (Z : Jk1), PayOnly Z →
    (∀ (N : Jk1), JkJ N → (∀ j, APd j N) → ∀ k, APd k (Jk1.two N Z)) →
    ∀ (N : Jk1), JkJ N → (∀ j, APd j N) → ∀ k, APd k (Jk1.two N (Jk1.pay Z Y)) := by
  have key : W 0 ⊆ {Y : TrioSeq | Bok Y → ∀ (Z : Jk1), PayOnly Z →
      (∀ (N : Jk1), JkJ N → (∀ j, APd j N) → ∀ k, APd k (Jk1.two N Z)) →
      ∀ (N : Jk1), JkJ N → (∀ j, APd j N) → ∀ k, APd k (Jk1.two N (Jk1.pay Z Y))} := by
    refine A2' ?_
    intro Y hY
    simp only [Set.mem_setOf_eq]
    intro hYb Z hZ hRZ N hN hNall
    by_cases hshort : Y.length ≤ 1
    · rcases (by omega : Y.length = 0 ∨ Y.length = 1) with h0 | h1
      · have hnil0 : Y = [] := List.length_eq_zero_iff.mp h0
        subst hnil0
        intro k
        exact APd_congr k (fun l => (jk1_two_pay_nil N Z l).symm) (hRZ N hN hNall k)
      · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
        have hc0 : c.1 = 0 := hYb.root
        obtain ⟨hc1, hc2⟩ := hYb.zroot c (by simp) hc0
        have hcz : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext hc0 (Prod.ext hc1 hc2)
        subst hcz
        have hpres : ∀ N' : Jk1, JkJ N' → (∀ j, APd j N') →
            ∀ j, APd j (Jk1.two N' (Jk1.pay Z ([] : TrioSeq))) :=
          fun N' hN' hN'all j =>
            APd_congr j (fun l => (jk1_two_pay_nil N' Z l).symm) (hRZ N' hN' hN'all j)
        have e : ([((0, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq)
            = ([] : TrioSeq) ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by simp
        intro k
        rw [e, APd_iff]
        intro ctx hc ws hw hG
        refine GoodFb_snoc_dupJt hw (GCtx_CtxOk k ctx hc) hN hZ
          (GCtx_CtxX_one k ctx hc _ ⟨hN, hZ, by simpa using hYb⟩)
          (by simpa using hYb) Bok_nil ?_
        intro n hn
        exact (APd_chainT (T := Jk1.pay Z ([] : TrioSeq)) hc hN hNall ⟨hZ, Bok_nil⟩ hpres n).1 ws hw hG
    have hlen2 : 2 ≤ Y.length := by omega
    have hYne : Y ≠ [] := by intro hcc; rw [hcc] at hlen2; simp at hlen2
    rcases hY with ⟨hl, -⟩ | hnat | ⟨m, hm, -, -⟩
    · exact absurd hl hshort
    · by_cases hlast : entry Y 0 (Y.length - 1) = 0
      · obtain ⟨he1, he2⟩ := Zroot_entry hYb.zroot hlast
        have hcol : Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) = ((0, 0, 0) : ℕ × ℕ × ℕ) :=
          Prod.ext hlast (Prod.ext he1 he2)
        have hgl : Y.getLast hYne = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
          have h1 : Y.getLast hYne = Y.getD (Y.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
            rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show Y.length - 1 < Y.length by omega)]
            rfl
          rw [h1, hcol]
        have hsplit : Y = Y.dropLast ++ [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
          rw [← hgl]; exact (List.dropLast_append_getLast hYne).symm
        have hop : Y⟦1⟧ = Y.dropLast := by
          rw [oper_eq_pred_of_zero 1 (by omega) ⟨hlast, he1, he2⟩]
          unfold Pred
          rw [if_neg (by omega)]
        have hdl := hnat 1 le_rfl
        rw [hop] at hdl
        simp only [Set.mem_setOf_eq] at hdl
        have hdb : Bok Y.dropLast := Bok_dropLast hYb
        have hpres : ∀ N' : Jk1, JkJ N' → (∀ j, APd j N') →
            ∀ j, APd j (Jk1.two N' (Jk1.pay Z Y.dropLast)) :=
          fun N' hN' hN'all => hdl hdb Z hZ hRZ N' hN' hN'all
        intro k
        rw [hsplit, APd_iff]
        intro ctx hc ws hw hG
        refine GoodFb_snoc_dupJt hw (GCtx_CtxOk k ctx hc) hN hZ
          (GCtx_CtxX_one k ctx hc _ ⟨hN, hZ, by rw [← hsplit]; exact hYb⟩)
          (by rw [← hsplit]; exact hYb) hdb ?_
        intro n hn
        exact (APd_chainT (T := Jk1.pay Z Y.dropLast) hc hN hNall ⟨hZ, hdb⟩ hpres n).1 ws hw hG
      · have hnz : ¬ (entry Y 0 (Y.length - 1) = 0 ∧ entry Y 1 (Y.length - 1) = 0 ∧
            entry Y 2 (Y.length - 1) = 0) := fun h => hlast h.1
        have hp := hasParent_of_ZrootMono hYb.zroot hYb.mono hYb.root hlen2 hnz
        intro k
        rw [APd_iff]
        intro ctx hc ws hw hG
        refine GoodFb_snoc_innerJt hw (GCtx_CtxOk k ctx hc) hN hZ
          (GCtx_CtxX_one k ctx hc _ ⟨hN, hZ, hYb⟩) hYb hlen2 hp ?_
        intro n hn
        have hh := hnat n hn
        simp only [Set.mem_setOf_eq] at hh
        exact (APd_iff k _).mp (hh (Bok_oper hYb hn) Z hZ hRZ N hN hNall k) ctx hc ws hw hG
    · exact absurd hm (Nat.not_lt_zero m)
  intro Y hYb Z hZ hRZ N hN hNall
  exact key hYb.mem hYb Z hZ hRZ N hN hNall

#print axioms APd_twoPay

/-- ★★★★★ 荷だけの junk を持つ 2 の記録は、どの深さでも項として継げる。 -/
theorem APd_twoPayOnly : ∀ (M : Jk1), PayOnly M → ∀ (N : Jk1), JkJ N → (∀ j, APd j N) →
    ∀ k, APd k (Jk1.two N M)
  | Jk1.nil, _, N, hN, hNall => APd_twoNilGen N hN hNall
  | Jk1.pay Z C, h, N, hN, hNall =>
      APd_twoPay C h.2 Z h.1 (fun N' hN' hN'all => APd_twoPayOnly Z h.1 N' hN' hN'all) N hN hNall
  | Jk1.one _ _, h, _, _, _ => absurd h (by simp [PayOnly])
  | Jk1.two _ _, h, _, _, _ => absurd h (by simp [PayOnly])

#print axioms APd_twoPayOnly



/-- ★★★★★ どの妥当な木も、どの深さでも項として継げる。 -/
theorem APd_all : ∀ (T : Jk1), JkJ T → ∀ k : ℕ, APd k T
  | Jk1.nil, _, k => APd_nil k
  | Jk1.pay N Y, h, k => APd_pay k N h.1 (APd_all N h.1 k) Y h.2
  | Jk1.one N M, h, k => APd_one k h.1 (APd_all N h.1 k) (APd_all M h.2 (k + 1))
  | Jk1.two N M, h, k => APd_twoPayOnly M h.2 N h.1 (APd_all N h.1) k

/-- ★★★★★ どの妥当な木も、字として語の右に継げる（GoodFb 3 段すべて）。 -/
theorem GOK_all : ∀ (T : Jk1), JkOk T → GOK T
  | Jk1.nil, _ => GOK_nil
  | Jk1.pay N Y, h => AY0 Y h.2 N h.1 (GOK_all N h.1)
  | Jk1.one N M, h => APd_all M h.2 0 N h.1 (GOK_all N h.1)
  | Jk1.two _ _, h => absurd h (by simp [JkOk])

#print axioms GOK_all


/-! ### 語版と、階段の塔 -/

theorem GoodFb_wordJ : ∀ ws : List Jk1, WOk ws → GoodFb (fun a b => wordJ a b ws) := by
  intro ws
  induction ws using List.reverseRecOn with
  | nil => intro _; exact GoodFb_wordJ_nil
  | append_singleton ws N ih =>
      intro hw
      have hw' : WOk ws := WOk_of_append_left hw
      exact GOK_all N (hw N (by simp)) ws hw' (ih hw')

/-- ★★★★★ `R338` の上に、木の字の語をどれでも継げる。 -/
theorem rowJ_mem (ws : List Jk1) (hw : WOk ws) :
    R338 ++ (((1, 1, 0) : ℕ × ℕ × ℕ) :: wordJ 1 1 ws) ∈ W 0 := by
  have h := ((GoodFb_wordJ ws hw).seg 0).reapp P0 BaseOk_zero 0 R338
    (LwB_of_base ⟨Aok_R338, rfl⟩)
  simpa using h

theorem stair_tower (n : ℕ) :
    R338 ++ (((1, 1, 0) : ℕ × ℕ × ℕ) :: wordJ 1 1 [stairJ n])
      = Mtw R341 [((3, 1, 0) : ℕ × ℕ × ℕ)] n := by
  have e : (List.range n).flatMap (fun k => shiftr01 k 0 [((3, 1, 0) : ℕ × ℕ × ℕ)])
      = (List.range n).map (fun k => ((3 + k, 1, 0) : ℕ × ℕ × ℕ)) := by
    rw [← flatMap_sing]
    apply List.flatMap_congr
    intro k _
    simp only [shiftr01, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq,
      and_true, and_self]
    try omega
  rw [wordJ_singleton, colJ, jk1_stairJ n 2, Mtw, e, R341, R338]
  simp

/-- 階段の塔はすべて `W 0`。 -/
theorem stair_tower_mem (n : ℕ) : Mtw R341 [((3, 1, 0) : ℕ × ℕ × ℕ)] n ∈ W 0 := by
  rw [← stair_tower n]
  exact rowJ_mem [stairJ n] (WOk_singleton (JkOk_stairJ n))

/-- ★★★★★ シート行373 `R344 (4,2,0) = psi(W_w*psi_1(W_2))`。 -/
theorem R373_mem : R344 ++ [((4, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hM : MidD 4 [((3, 1, 0) : ℕ × ℕ × ℕ)] := by
    have h := MidD_col 3 1 (by omega) (by omega)
    rwa [show 3 + 1 = 4 from rfl] at h
  have h := snocY_mem (Y0 := R341) (M := [((3, 1, 0) : ℕ × ℕ × ℕ)]) (L := 3) (y := 2)
    (by simp [R341, R338]) hM (by simp [entry]) (by omega) stair_tower_mem
  simpa [R344, R341, List.append_assoc] using h

#print axioms R373_mem






/-- ★★★★★ 「単位 + 1 の列 + 木の junk」の右に 2 の記録を継ぐ。 -/
theorem hang2rec {h : ℕ} {A : TrioSeq} (hA : LwA h A) {M' : Jk1} (hM' : JkJ M') :
    (A ++ ([((h + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 1) : ℕ × ℕ × ℕ)] ++
      (((h + 3, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (h + 3) M'))) ++ [((h + 4, 2, 0) : ℕ × ℕ × ℕ)]
      ∈ W 0 := by
  obtain ⟨P, hP, hL⟩ := hA
  have hAne : A ≠ [] := (LwA_Aok ⟨P, hP, hL⟩).ne
  set Y0 : TrioSeq := A ++ [((h + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 1) : ℕ × ℕ × ℕ)] with hY0
  set M : TrioSeq := ((h + 3, 1, 0) : ℕ × ℕ × ℕ) :: jk1 (h + 3) M' with hM0
  have hMid : MidD (h + 4) M := by
    have h1 := MidD_append (MidD_col (h + 3) 1 (by omega) (by omega)) (N := jk1 (h + 3) M')
      (fun x hx => by have := jk1_ge M' (h + 3) x hx; omega) (jk1_mono M' (JkA_of_JkJ M' hM') (h + 3))
    rw [hM0]
    simpa [show h + 3 + 1 = h + 4 from rfl] using h1
  have htw : ∀ n, Mtw Y0 M n ∈ W 0 := by
    intro n
    have hG := GOK_all (twr M' n) (JkOk_twr hM' n) [] WOk_nil GoodFb_wordJ_nil
    have h1 := (hG.seg h).reapp P hP 0 A (by simpa using hL)
    have e : A ++ (((h + 1, 1, 0) : ℕ × ℕ × ℕ) :: wordJ (h + 1) 1 [twr M' n])
        = Mtw Y0 M n := by
      rw [wordJ_singleton, colJ, jk1_twr M' n (h + 2), hY0, hM0, Mtw]
      simp [List.append_assoc]
    rw [← e]
    simpa using h1
  have h2 := snocY_mem (Y0 := Y0) (M := M) (L := h + 3) (y := 2)
    (by rw [hY0]; simp [hAne]) hMid (by rw [hM0]; simp [entry]) (by omega) htw
  rw [hY0, hM0] at h2
  simpa [List.append_assoc] using h2

/-- 行373 を `hang2rec` から出し直す。 -/
theorem R373_mem' : R344 ++ [((4, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := hang2rec (h := 0) (LwA_of_Aok Aok_R338) (M' := Jk1.nil) trivial
  simpa [R344, R341, jk1, List.append_assoc] using h

#print axioms hang2rec

/-- ★ `hangU11two` の 2 の記録版: `(h+4,2,0)` の**上に**荷を吊るす。
2 の記録の直上が荷（`Bok B`）なら今の `JkJ` で許されている。 -/
theorem hangU11rec {h : ℕ} {A : TrioSeq} (hA : LwA h A) {B : TrioSeq} (hB : Bok B) :
    A ++ ([((h + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 1) : ℕ × ℕ × ℕ),
      ((h + 3, 1, 0) : ℕ × ℕ × ℕ), ((h + 4, 2, 0) : ℕ × ℕ × ℕ)] ++
      shiftr01 (h + 5) 0 B) ∈ W 0 := by
  obtain ⟨P, hP, hL⟩ := hA
  have hT : JkOk (Jk1.one Jk1.nil (Jk1.two Jk1.nil (Jk1.pay Jk1.nil B))) :=
    ⟨trivial, trivial, trivial, hB⟩
  have hG := GOK_all _ hT [] WOk_nil GoodFb_wordJ_nil
  have h1 := (hG.seg h).reapp P hP 0 A (by simpa using hL)
  simpa [wordJ, colJ, jk1, shiftr01_zero, List.append_assoc,
    show h + 1 + 1 = h + 2 from by omega, show h + 1 + 1 + 1 = h + 3 from by omega,
    show h + 1 + 1 + 1 + 1 = h + 4 from by omega,
    show h + 1 + 1 + 1 + 1 + 1 = h + 5 from by omega] using h1

/-- ★★★★★ シート行374 `R344 (4,2,0)(4,2,0) = psi(W_w*psi_1(W_2*2))`。 -/
theorem R374_mem : R344 ++ [((4, 2, 0) : ℕ × ℕ × ℕ), ((4, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := hang2rec (h := 0) (LwA_of_Aok Aok_R338) (M' := Jk1.two Jk1.nil Jk1.nil) ⟨trivial, trivial⟩
  simpa [R344, R341, jk1, List.append_assoc] using h

#print axioms R374_mem

/-! ### 行374 と行375 の間: `R344 (4,2,0)(5,1,0)`
2 の記録 `(4,2,0)` の上に荷を吊るせる（`hangU11rec`）ので、
`snocd_gen (d = 5)` で 1 の列 `(5,1,0)` が 1 本だけ乗る。 -/

def R373 : TrioSeq := R344 ++ [((4, 2, 0) : ℕ × ℕ × ℕ)]

theorem MidD_col42 : MidD 5 [((4, 2, 0) : ℕ × ℕ × ℕ)] := MidD_col 4 2 (by omega) (by omega)

theorem Aok_R373 : Aok R373 :=
  Aok_append_Mid (d := 5) (by omega) Aok_R344 MidD_col42 R373_mem

theorem R373_row1 : ∀ j, 0 < j → j < R373.length → 1 ≤ entry R373 1 j := by
  intro j hj0 hjl
  simp only [R373, R344, R341, R338, List.length_append, List.length_cons,
    List.length_nil] at hjl
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp [R373, R344, R341, R338, entry]

/-- ★★★★ `R344 (4,2,0)(5,1,0)`（シート行374 と行375 の間）。 -/
theorem R373a_mem : R344 ++ [((4, 2, 0) : ℕ × ℕ × ℕ), ((5, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := snocd_gen (Y := R373) (d := 5) (by omega) Aok_R373 (Ancd_of_row1 R373_row1 5) ?_
  · simpa [R373, List.append_assoc] using h
  · intro B hB
    have h2 := hangU11rec (h := 0) (LwA_of_Aok Aok_R338) hB
    simpa [R373, R344, R341, List.append_assoc] using h2

#print axioms R373a_mem

/-! ### 行 1 の 1 を 2 に置き換える（`sub21`）

`(h,1,0)` を `(h,2,0)` に替えても、その列が「誰の行 1 の親でもない」なら
展開は変わらない（`tools/cmp_two_vs_one.py` で 40 例以上検証済み）。
ここではその置換の定義と、行 0 / 行 2 / 行 0 の祖先関係が不変であることを示す。 -/

/-- `S j` が真の列だけ、行 1 の値を 2 に置き換える。 -/
def sub21 (S : ℕ → Bool) (M : TrioSeq) : TrioSeq :=
  (List.range M.length).map fun j =>
    let c := M.getD j ((0, 0, 0) : ℕ × ℕ × ℕ)
    if S j then (c.1, 2, c.2.2) else c

@[simp] theorem sub21_length (S : ℕ → Bool) (M : TrioSeq) : (sub21 S M).length = M.length := by
  simp [sub21]

theorem sub21_getD (S : ℕ → Bool) (M : TrioSeq) {j : ℕ} (hj : j < M.length) :
    (sub21 S M).getD j ((0, 0, 0) : ℕ × ℕ × ℕ)
      = (if S j then ((M.getD j ((0, 0, 0) : ℕ × ℕ × ℕ)).1, 2,
            (M.getD j ((0, 0, 0) : ℕ × ℕ × ℕ)).2.2)
         else M.getD j ((0, 0, 0) : ℕ × ℕ × ℕ)) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hj)]
  simp [sub21, List.getElem_map, List.getElem_range]

theorem entry_sub21_0 (S : ℕ → Bool) (M : TrioSeq) (j : ℕ) :
    entry (sub21 S M) 0 j = entry M 0 j := by
  by_cases hj : j < M.length
  · rw [entry, entry, sub21_getD S M hj]
    by_cases hs : S j <;> simp [hs]
  · have h1 : (sub21 S M).getD j ((0, 0, 0) : ℕ × ℕ × ℕ) = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hj)]; rfl
    have h2 : M.getD j ((0, 0, 0) : ℕ × ℕ × ℕ) = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    simp only [entry]
    rw [h1, h2]

theorem entry_sub21_2 (S : ℕ → Bool) (M : TrioSeq) (j : ℕ) :
    entry (sub21 S M) 2 j = entry M 2 j := by
  by_cases hj : j < M.length
  · rw [entry, entry, sub21_getD S M hj]
    by_cases hs : S j <;> simp [hs]
  · have h1 : (sub21 S M).getD j ((0, 0, 0) : ℕ × ℕ × ℕ) = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hj)]; rfl
    have h2 : M.getD j ((0, 0, 0) : ℕ × ℕ × ℕ) = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    simp only [entry]
    rw [h1, h2]

theorem entry_sub21_1_of (S : ℕ → Bool) (M : TrioSeq) {j : ℕ} (hj : j < M.length)
    (hs : S j = true) : entry (sub21 S M) 1 j = 2 := by
  rw [entry, sub21_getD S M hj]
  simp [hs]

theorem entry_sub21_1_off (S : ℕ → Bool) (M : TrioSeq) {j : ℕ} (hs : S j = false) :
    entry (sub21 S M) 1 j = entry M 1 j := by
  by_cases hj : j < M.length
  · rw [entry, entry, sub21_getD S M hj]
    simp [hs]
  · have h1 : (sub21 S M).getD j ((0, 0, 0) : ℕ × ℕ × ℕ) = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hj)]; rfl
    have h2 : M.getD j ((0, 0, 0) : ℕ × ℕ × ℕ) = ((0, 0, 0) : ℕ × ℕ × ℕ) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    simp only [entry]
    rw [h1, h2]

/-- 行 0 は触らないので、行 0 の「次」関係は不変。 -/
theorem nextrel0_sub21 (S : ℕ → Bool) (M : TrioSeq) (j0 j1 : ℕ) :
    nextrel0 (sub21 S M) j0 j1 ↔ nextrel0 M j0 j1 := by
  simp only [nextrel0, sub21_length, entry_sub21_0]

/-- 行 0 の祖先関係も不変。 -/
theorem le0_sub21 (S : ℕ → Bool) (M : TrioSeq) (j0 j1 : ℕ) :
    le0 (sub21 S M) j0 j1 ↔ le0 M j0 j1 := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by simpa using h1, by simpa using h2, ?_⟩
    refine Relation.ReflTransGen.mono ?_ h3
    intro a b hab
    exact (nextrel0_sub21 S M a b).mp hab
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by simpa using h1, by simpa using h2, ?_⟩
    refine Relation.ReflTransGen.mono ?_ h3
    intro a b hab
    exact (nextrel0_sub21 S M a b).mpr hab

/-- 行 1 の値が 1 の列も 2 の列も `srow = 1`（行 2 が 0 なら）。 -/
theorem srow_sub21 (S : ℕ → Bool) (M : TrioSeq) (j : ℕ)
    (hz : ∀ i, S i = true → entry M 2 i = 0)
    (hone : ∀ i, S i = true → i < M.length → entry M 1 i = 1) :
    srow (sub21 S M) j = srow M j := by
  by_cases hj : j < M.length
  · by_cases hs : S j
    · have h2 : entry M 2 j = 0 := hz j hs
      have h1 : entry M 1 j = 1 := hone j hs hj
      simp [srow, entry_sub21_2, h2, entry_sub21_1_of S M hj hs, h1]
    · simp [srow, entry_sub21_2, entry_sub21_1_off S M (by simpa using hs)]
  · have hj2 : ¬ j < (sub21 S M).length := by simpa using hj
    have e1 : entry M 1 j = 0 := by
      rw [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have e2 : entry M 2 j = 0 := by
      rw [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have e3 : entry (sub21 S M) 1 j = 0 := by
      rw [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hj)]; rfl
    simp [srow, entry_sub21_2, e2, e1, e3]

end Small
end TRIO
