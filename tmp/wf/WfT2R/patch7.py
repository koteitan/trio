F='/home/koteitan/proofs/trio/Ytosk/lean/Ytosk/WfT2R7.lean'
t=open(F).read()
def rep(a,b,cnt=1):
    global t
    assert t.count(a)==cnt,(t.count(a),a[:90])
    t=t.replace(a,b)
# r2X_t2XR
rep("      TRIO.srow M (M.length - 1) = 2 → Res3T2 M ρ rk := by","      TRIO.srow M (M.length - 1) = 2 → Res3T2X M ρ rk := by")
rep("""        (∀ p, T2Seed M r L p → SeedL ρ σ p) ∧
        AbsWN M (TRIO.gexp""","""        (∀ p, T2Seed M r L p → SeedL ρ σ p) ∧
        WfAbsW.AbsWNx M (TRIO.gexp""")
rep("    exact ⟨fun p hp => (hBR.2.1 p hp).1, hBR.2.2.2⟩","    exact ⟨fun p hp => (hBR.2.1 p hp).1, hBR.2.2.2.1⟩")
rep("""  refine ⟨fun r L hlen hr n σ hn hCN _ => (hbig r L hlen hr n σ hn hCN).2,
    fun r L qp pq""","""  refine ⟨fun r L qp pq""")
# t2_dropsCX
rep("""    (I : Inv3C M ρ rk) (R : Res3D M ρ rk) (R2 : Res3T2 M ρ rk) (hX : SInvX M) (hJ : RowJ M)""",
"""    (I : Inv3C M ρ rk) (R : Res3D M ρ rk) (R2 : Res3T2X M ρ rk)
    (hD2 : ∀ n, 2 ≤ n → ∀ σ rkN, Cons (expand M n) σ → Rk (expand M n) rkN → Good3 (expand M n) σ →
      isOT (root (expand M n) σ) = true ∧ root (expand M n) σ < root M ρ)
    (hX : SInvX M) (hJ : RowJ M)""")
s=t.index('theorem t2_dropsCX'); a=t.index('    intro n hn σ rkN hCN hRN hGN\n',s); b=t.index('\n  intro n\n  rcases n with',a)
t=t[:a]+"""    intro n hn σ rkN hCN hRN hGN
    have h := hD2 n hn σ rkN (by rw [hexp n]; exact hCN) (by rw [hexp n]; exact hRN) (by rw [hexp n]; exact hGN)
    rw [hexp n] at h; exact h"""+t[b:]
# hT2_V2XR
rep("theorem hT2_V2XR (h2 : ExpT2V2) (hR2 : R2V2) (hCB","theorem hT2_V2XR (h2 : ExpT2V2) (hR2 : R2V2X) (hD2 : T2Drop2X) (hCB")
rep("  · apply t2_dropsCX (Inv3V2.toC C.S C.I) R (hCB M","  · apply t2_dropsC (Inv3V2.toC C.S C.I) R (hCB M")
rep("  · apply t2_dropsCX (Inv3V2.toC C.S C.I) R (hR2 M ρ rk ⟨C.toStepCtxB, hb⟩ hz hs) hX",
    "  · apply t2_dropsCX (Inv3V2.toC C.S C.I) R (hR2 M ρ rk ⟨C.toStepCtxB, hb⟩ hz hs)\n      (hD2 M ρ rk ⟨C.toStepCtxB, hb⟩ hz hs) hX")
# desc3
rep("(h2 : ExpT2V2) (hR2 : R2V2) (hCB : T2CBadOut) : Desc3 := by","(h2 : ExpT2V2) (hR2 : R2V2X) (hD2 : T2Drop2X) (hCB : T2CBadOut) : Desc3 := by")
rep("(hT2_V2XR h2 hR2 hCB hTB C R)","(hT2_V2XR h2 hR2 hD2 hCB hTB C R)")
# badOut
rep("(hTB : TakeBadV2) (h2 : ExpT2V2) (hR2 : R2V2)\n    (hCB : T2CBadOut) : BadOutT2B := by","(hTB : TakeBadV2) (h2 : ExpT2V2) (hR2 : R2V2X)\n    (hD2 : T2Drop2X) (hCB : T2CBadOut) : BadOutT2B := by")
s=t.index('theorem badOutT2B_ofXR'); a=t.index('  have key :',s); b=t.index('\nend Ytosk',a)
t=t[:a]+"""  by_cases hb : T2CBad M
  · have key := hCB M ρ rk CB hb hz h2t
    refine ⟨key.1 n hn, ?_⟩
    exact t2_drops_ge2 (Inv3W.ofV2 CB.S CB.I) CB.toW key.2 hX hJ hz h2t (fun m hm _ _ => by
      obtain ⟨ρN, rkN, IN⟩ := key.1 m hm
      exact ⟨ρN, rkN, IN.cons, IN.rank, IN.good⟩) n hn
  · obtain ⟨ρN, rkN, IN⟩ := h2 M ρ rk ⟨CB, hb⟩ hz h2t n hn
    refine ⟨⟨ρN, rkN, IN⟩, root (expand M n) ρN, ⟨ρN, rkN, IN.cons, IN.rank, rfl⟩, ?_⟩
    exact hD2 M ρ rk ⟨CB, hb⟩ hz h2t n hn ρN rkN IN.cons IN.rank IN.good
"""+t[b:]
t=t+open('/home/koteitan/proofs/trio/tmp/wf/WfT2R/tail7.lean').read()
open(F,'w').write(t)
