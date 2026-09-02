
### 2026-09-02 (続き22) 続き21 の修正: 「自分の接頭辞」だけでは足りない。界面 Iface と相対的な積み上げ
続き21 の穴: 段 k のクラス C_k を固定すると、3-塔の複製は C_k の元の**上**（rank が増える）に載るので、
複製の junk の再継ぎ条件が C_k の文脈では足りない（レベルは頂上、junk は真横、の矛盾は解消不能）。
rank ∀ を定義に入れると非構造的。→ 界面（一階の性質）で抽象化する。

定義の順序（循環なし）:
 1. 相対的な群 VU E（既にある: 頭 + 記録、条件は E ++ 途中群 の上）。頭は junk なし。
    StkC Q j := Q の元 ++ 相対群 j 個（レベル = 頂上の記録）。Iface を参照しない。
 2. Iface Q :=
    (I1) Q の元は W 0 / Aok / Ancd
    (I2) ∀ j, StkC Q j の元の頂上に Bok を吊るせる
    (I3) ∀ j, StkC Q j の元の頂上に (·,2,0) を置ける       （段 k では (·,k,0)）
    (I4) close: ∀ j で StkC Q j の上に再継ぎできる junk（stack-universal）は Q の頂上に吸収できる
 3. 抽象群 AbsG: 頭は junk なし。記録 N_i の条件:
      ∀ Q, Iface Q → ∀ Z ∈ StkC Q S (任意 S) ++ 自分の接頭辞（junk は「∀ S', StkC Q S' ++ 途中」で再継ぎ可）,
        Z ++ ... ++ N_i ∈ W 0
 4. K_{≤n} := LwA ++ SegA ++ 抽象群 ≤ n 個（junk は K_{≤n-1} に対して stack-universal）。
補題:
 (A) Iface_stack: Iface Q → Iface (StkC Q j)（StkC (StkC Q j) j' = StkC Q (j+j')）。
 (B) Iface (RunA 0): I2/I3 は j の帰納法。j = 0 は BaseOk_RunA / RunA_snoc2。
     j+1: 吊るしは blkD_memS（M = 最後の記録ブロック、不変量 = StkC Q j ++ 途中、hclose = VU_close）。
     r = 0（頭だけ）の吊るしは不変量 = ⋃_S StkC Q S、hbase = I3、hclose は前の群か Q.close(I4)。
     Snoc2 は再台座（I2）+ 複製 (M0 ++ S)。
 (C) 3-記録の抽象条件: Z ∈ Q, 接頭辞 p'（universal junk つき）→ 塔 Z ++ p'^k は StkC Q k の元（複製は相対群）。
 (D) 行295: T_n = D_1 ++ (2 3^n)。T_{n+1} = T_n ++ 3 は (C) を Q := RunA 0 で。K_{≤n} は D_4 には不要。
 (E) 行296 には段 k の一般化（Snoc_k、(k+1)-記録）と K_{≤n} の Iface が要る。
注意: blkD_memS の不変量 P は自由に選べる（∃ S を含めてよい）。ここが鍵。
