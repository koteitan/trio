import subprocess, re
BMS = "/home/koteitan/code/yaBMS/c/bms"
def parse(s): return [tuple(int(x) for x in m.split(',')) for m in re.findall(r'\(([^)]*)\)', s)]
def run(mat, n):
    out = subprocess.run([BMS,"-d",f"{mat}[{n}]"],capture_output=True,text=True).stdout
    ls=[l for l in out.strip().split('\n') if l.strip()]
    return parse(ls[-1])
def std(mat): return subprocess.run([BMS,"-s",mat],capture_output=True,text=True).stdout.strip()

bases = {
  "R344": "(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)",
  "R341+": "(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)",
}
# base の直後に (h,1,0) or (h,2,0) を置き、その上に junk。h は base の次の高さ
cases = []
for bn, b in bases.items():
    h = 4 if bn=="R344" else 3
    junks = ["(J1,1,0)","(J1,0,0)","(J1,1,0)(J2,0,0)","(J1,1,0)(J1,1,0)",
             "(J1,1,0)(J2,2,0)","(J1,1,0)(J2,1,0)","(J1,1,0)(J2,2,0)(J3,1,0)",
             "(J1,1,0)(J2,2,0)(J3,1,0)(J4,2,0)","(J1,1,0)(J2,1,0)(J3,0,0)",
             "(J1,0,0)(J2,1,0)","(J1,1,0)(J2,0,0)(J3,1,0)","(J1,1,0)(J2,1,0)(J2,1,0)",
             "(J1,1,0)(J2,2,0)(J2,2,0)","(J1,1,0)(J2,2,0)(J3,1,0)(J3,1,0)",
             "(J1,1,0)(J2,1,0)(J3,2,0)","(J1,1,0)(J2,2,0)(J3,0,0)"]
    for J in junks:
        JJ = J
        for i in range(1,6): JJ = JJ.replace(f"J{i}", str(h+i))
        cases.append((bn, b, h, JJ))

bad=0
for bn,b,h,J in cases:
    A = b + f"({h},1,0)" + J
    B = b + f"({h},2,0)" + J
    sA,sB = std(A), std(B)
    ok=True; msg=""
    if sB != "1":
        print(f"{bn} J={J!r:34} stdB={sB}  (skip: B が非標準)"); continue
    for n in (1,2,3,4,5):
        a,b2 = run(A,n), run(B,n)
        if len(a)!=len(b2): ok=False; msg=f"n={n} len {len(a)}!={len(b2)}"; break
        if [c[0] for c in a]!=[c[0] for c in b2]: ok=False; msg=f"n={n} row0"; break
        if [c[2] for c in a]!=[c[2] for c in b2]: ok=False; msg=f"n={n} row2"; break
        d=[(i,a[i][1],b2[i][1]) for i in range(len(a)) if a[i][1]!=b2[i][1]]
        if any(x[1]!=1 or x[2]!=2 for x in d): ok=False; msg=f"n={n} row1 {d[:4]}"; break
    print(f"{bn} J={J!r:34} stdA={sA} stdB={sB} {'OK' if ok else 'NG '+msg}")
    if not ok: bad+=1
print("bad =", bad)
