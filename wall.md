# 壁

シート行376 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,0)(5,3,0)` は
次のどれか 1 本で出る。すべて緑の還元。

## ★道3（族を使わない・いちばん弱い）

    HangB : ∀ js B, Bok B → BM js ++ shiftr01 (2 + hgtB js + 1) 0 B ∈ W 0
    R376_of_HangB : HangB → 行376

`BM js` はブロックの塔の行列（`BM [] = R341`、`BM (j::js) = BM js ++ blkM (2+hgtB js) j`）。
幅の多重集合の DM 帰納で `BM js ∈ W 0` は回っている（`BM_memAok`）。
`HangB` は「ブロックの塔の上に任意の標準行列を吊るす」。

## 道1（木の言葉・いちばん弱い形）

    FoneB : ∀ ws, GOK (plug (BCtx ws) (one nil nil))
          ⟺ ∀ js, GOK (bdA (js ++ [0]))
    R376_of_FoneB : FoneB → 行376

`bdA js` 側（幅 ≥ 1）は階段 `GOK_oneUV_RunSB` で無条件に落ちるので、
**幅 0 の入り目（裸の 1 の枠）だけが壁**。
`PayB`（荷）からは `APnil_gen0` で出る（`FoneB_of_PayB`）。

## 道2（族 `WFd`）

    WFd_nilT : ∀ k ks, WFd ((k,0) :: ks) nil
    R376_of_WFd_nilAll : (∀ ks, WFd ks nil) → 行376

幅 ≥ 1 の入り目の空木は階段 `WFd_nilF` で無条件（緑）。
幅 ≥ 1 の入り目の**荷**も `WFd_payAll` で通った（緑、追記280）。

残っているのは 1 点だけ:

    WFd ((k,0)::ks) nil = ∀ U, FrmF ks U → WFd ks U → WFd ks (one U nil)

を `APnil_gen0` で出すには `WFd ks (pay U C)` が要り、`WFd_payAll` に渡すには
`U` が「`ks` より DM で小さい形でも良い」ことが要る。いまの族は枠 `U` について
`WFd ks U` しか言っていない。

### 直し方（設計は確定、実装が残り）

枠の条件を兄弟の条件と同じ形に強める:

    FrCond ks U := WFd ks U ∧
      （ks = (k',w)::ks' のとき）∀ k₂ < k', ∀ p (予算 < k'), WFd ((k₂,w)::(p++ks')) U

- `WFd_bdA` の枠はすべて `nil` なので `∀s, WFd s nil` から出る。
- 階段 `WFd_nilF` の塔の枠 `C` は**兄弟の条件**から出る
  （`∀k₂ ≤ m+1, ∀q(予算 < m+1), WFd ((k₂,i)::(q++(r++ks))) C` の k₂ < m の部分）。
- `WFd_payAll` が要る `Z` の形は `k₂ = k'` が `WFd_ck_shift`、`k₂ < k'` が
  `FrCond` の第 2 項。鎖で形が伸びても閉じている。
- 測度（入り目 (予算,幅) の辞書式の DM）で `(k₂,w) <ₗ (k',w)`、`p` の予算 < k' なので
  停止する。

最後は次の 2 本立ての Acc（DM）帰納:

    motive s := WFd s nil ∧ ∀ C, Bok C → WFd s (pay nil C)

## 死んだ道

`WGd`（`Ins`/`InsT` で相対化した族）は空虚。`WGd_zero_bad` が示すとおり
予算 0 で相対化が消え、条件が満たせない。
