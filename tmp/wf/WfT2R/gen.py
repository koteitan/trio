# generate X copies of the t = 2 consumers of T2BelowXResAt (WfT2R)
import re,sys,os
D='/home/koteitan/proofs/trio/Ytosk/lean/Ytosk/'
def chunks(f):
    txt=open(D+f).read()
    lines=txt.split('\n')
    # namespace tracking
    ns=[];out=[];cur=None
    i=0
    res={}
    starts=[]
    for k,l in enumerate(lines):
        m=re.match(r'(?:private )?(?:protected )?(?:noncomputable )?(theorem|lemma|def|abbrev|structure|inductive) ([^\s(:{]+)',l)
        if m: starts.append((k,m.group(2)))
    # compute namespace at each line
    nsl=[];stack=[]
    for l in lines:
        m=re.match(r'namespace (\S+)',l)
        if m: stack.append(m.group(1))
        m=re.match(r'end (\S+)',l)
        if m and stack and stack[-1]==m.group(1): stack.pop()
        nsl.append('.'.join(stack))
    for idx,(k,n) in enumerate(starts):
        # start back over doc comment / open .. in
        s=k
        while s>0 and (lines[s-1].startswith('open ') and lines[s-1].endswith(' in')):
            s-=1
        # doc comment
        if s>0 and lines[s-1].rstrip().endswith('-/'):
            t=s-1
            while not lines[t].startswith('/-'): t-=1
            if lines[t].startswith('/--'): s=t
        # end: next nonempty top-level line that is not continuation
        e=k+1
        while e<len(lines):
            l=lines[e]
            if l and not l[0].isspace() and not l.startswith('--') and not l.startswith('|'):
                break
            e+=1
        res[n]=(nsl[k],'\n'.join(lines[s:e]).rstrip()+'\n')
    return res
def gen(out, header, items, ren, opens):
    body=[header]
    for f,names in items:
        cs=chunks(f)
        for n in names:
            ns,t=cs[n]
            for a,b in ren:
                t=re.sub(r'(?<![\w])'+a+r'(?![\w\'])',b,t)
            body.append(f'namespace {ns}\nopen {opens.get(f,"T Classical")}\nset_option linter.unusedVariables false\nset_option linter.unusedSectionVars false\n\n{t}\nend {ns}\n')
    open(D+out,'w').write('\n'.join(body))
