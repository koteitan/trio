import subprocess, re
BMS="/home/koteitan/code/yaBMS/c/bms"
def parse(s): return [tuple(int(x) for x in m.split(',')) for m in re.findall(r'\(([^)]*)\)',s)]
def fmt(cs): return "".join(f"({a},{b},{c})" for a,b,c in cs)
def run(m,n):
    o=subprocess.run([BMS,"-d",f"{m}[{n}]"],capture_output=True,text=True).stdout
    ls=[l for l in o.strip().split('\n') if l.strip()]
    return parse(ls[-1])
def std(m): return subprocess.run([BMS,"-s",m],capture_output=True,text=True).stdout.strip()
R344="(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)"
def cmp(a,b):
    if len(a)!=len(b): return f"len {len(a)}!={len(b)}"
    if [c[0] for c in a]!=[c[0] for c in b]: return "row0"
    if [c[2] for c in a]!=[c[2] for c in b]: return "row2"
    d=[(i,a[i][1],b[i][1]) for i in range(len(a)) if a[i][1]!=b[i][1]]
    if any(x[1]!=1 or x[2]!=2 for x in d): return f"row1 {d[:4]}"
    return None
junks=["(5,1,0)","(5,0,0)","(5,1,0)(6,0,0)","(5,1,0)(5,1,0)","(5,1,0)(6,1,0)",
       "(5,1,0)(6,2,0)","(5,1,0)(6,1,0)(7,0,0)","(5,0,0)(6,1,0)",
       "(5,1,0)(6,2,0)(7,1,0)","(5,1,0)(6,0,0)(7,1,0)"]
bad=0
for J in junks:
    A=R344+"(4,1,0)"+J; B=R344+"(4,2,0)"+J
    msgs=[]
    for n1 in (1,2,3):
        a1,b1=run(A,n1),run(B,n1)
        e=cmp(a1,b1)
        if e: msgs.append(f"[{n1}]:{e}"); continue
        for n2 in (1,2,3):
            a2,b2=run(fmt(a1),n2),run(fmt(b1),n2)
            e2=cmp(a2,b2)
            if e2: msgs.append(f"[{n1}][{n2}]:{e2}")
            else:
                for n3 in (1,2):
                    a3,b3=run(fmt(a2),n3),run(fmt(b2),n3)
                    e3=cmp(a3,b3)
                    if e3: msgs.append(f"[{n1}][{n2}][{n3}]:{e3}")
    print(f"J={J!r:28} {'OK' if not msgs else 'NG '+';'.join(msgs[:3])}")
    if msgs: bad+=1
print("bad =",bad)
