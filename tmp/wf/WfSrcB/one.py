import sys,pickle,re
sys.path[:0]=['tmp/wf/WfSrcB','tmp/codex','tools','tmp/claude']
import probe_b2 as P
for s in sys.argv[1:]:
    M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
    cnt,ex=P.run([M])
    print(cnt);print(ex)
