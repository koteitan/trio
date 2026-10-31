import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfB2S')
import fr6,subprocess,re
def parse(s):return [tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
for s in sys.argv[1:]:
 M=parse(s);fr6.MODE='all'
 st=subprocess.run(['/home/koteitan/proofs/trio/bms','-s',s],capture_output=True,text=True).stdout.strip()
 print(st,fr6.run([M]))
