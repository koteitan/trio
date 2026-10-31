F='/home/koteitan/proofs/trio/Ytosk/lean/Ytosk/WfT2R8.lean'
t=open(F).read()
def rep(a,b,cnt=1):
    global t
    assert t.count(a)==cnt,(t.count(a),a[:90])
    t=t.replace(a,b)
rep("    (r2V2_ofXR hB) hCB)","    (r2V2_ofXR hB) (t2Drop2X_of hB) hCB)")
rep("(hDU : HDropU) (hTB2 : T2BadRes) (hStep","(hDU : HDropU) (hQD : T2QNDomBad2) (hRX : WfT2X.T2BelowRV2X) (hStep")
rep("(WfB2S.huacB2_of_ab hStep) hTB2.2)","(WfB2S.huacB2_of_ab hStep) hQD)")
i=t.index("  have hBX : WfT2X.T2BelowXResV2X := "); j=t.index("\n",i)
t=t[:i]+"  have hBX : WfT2X.T2BelowXResV2X := WfT2X.t2BelowXResV2X_of hRX hP (t2SeedOTV2_of hP (t2SeedOTRestV2_of_B hCl hP))"+t[j:]
rep("hE2 (r2V2_ofXR hBX) hCB","hE2 (r2V2_ofXR hBX) (t2Drop2X_of hBX) hCB")
t+='''
/-! The axioms of the new top theorem. -/
#print axioms Ytosk.trio_terminates_main_V2_curXR
'''
open(F,'w').write(t)
