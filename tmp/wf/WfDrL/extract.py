"""WfDrL: copy Lean declarations with their active section context (variable/include lines).
usage: python3 extract.py FILE NAME...  -> prints, per name, a `section ... end` block with the decl."""
import re,sys
KW=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(theorem|lemma|def|structure|abbrev|instance|inductive)\s+([^\s({:]+)')
def blocks(path):
    L=open(path).read().split('\n')
    out=[];stack=[[]];i=0;pend=[]
    while i<len(L):
        l=L[i]
        if l.startswith('section') :stack.append([]);i+=1;continue
        if l.startswith('end') and not l.startswith('end Ytosk'):
            if len(stack)>1:stack.pop()
            i+=1;continue
        if l.startswith('variable') or l.startswith('include') or (l.startswith('omit') and not l.rstrip().endswith(' in')):
            j=i+1
            while j<len(L) and L[j].startswith('  '):j+=1
            stack[-1].append('\n'.join(L[i:j]));i=j;continue
        if l.startswith('/--') or (l.startswith('open') and l.rstrip().endswith(' in')) or l.startswith('omit') or l.startswith('@[') or l.startswith('set_option') and l.rstrip().endswith(' in'):
            if l.startswith('/--'):
                j=i
                while '-/' not in L[j]:j+=1
                pend.append('\n'.join(L[i:j+1]));i=j+1;continue
            pend.append(l);i+=1;continue
        m=KW.match(l)
        if m:
            j=i+1
            while j<len(L) and (L[j].startswith(' ') or L[j]=='' and j+1<len(L) and L[j+1].startswith(' ')):j+=1
            out.append((m.group(2),[x for s in stack for x in s],'\n'.join(pend+L[i:j])))
            pend=[];i=j;continue
        if l.strip()=='' :i+=1;continue
        pend=[];i+=1
    return out
if __name__=='__main__':
    B={n:(c,t) for n,c,t in blocks(sys.argv[1])}
    for n in sys.argv[2:]:
        c,t=B[n]
        print('section');print('\n'.join(c));print(t);print('end\n')
