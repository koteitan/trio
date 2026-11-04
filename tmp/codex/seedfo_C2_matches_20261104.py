"""G7. Exact value/frame matches inside N for the resolved G6 C2 frames.
Full terms and matrices are retained. n=2,3 only. No Lean changes.
Self matches are labelled explicitly; summary witnesses exclude the column
whose state/value is being matched. Template provenance is from gexp blocks,
not a claim of literal column equality after row shifts.
"""
from pathlib import Path
import argparse, collections, multiprocessing, sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'tmp/codex'))
import seedfo_C2_shapes_20261104 as G
import json
F,B,A=G.F,G.B,G.A
OUT=ROOT/'tmp/codex/seedfo_C2_matches_20261104'


def freeze(t):
    return tuple(freeze(x) for x in t)


def provenance(i,r,L,k):
    original=i if i<r else r+(i-r)%L
    return dict(column=i,template_column=original,copy_number=None if i<r else (i-r)//L,
                template_is_r=original==r,template_is_k=original==k,
                unchanged_prefix=i<r)


def value_index(C,get):
    out=collections.defaultdict(list)
    for i in range(len(C.M)):out[get(i)].append(i)
    return out


def changes(old,new):
    """Syntactic increment, since ordinal subtraction would not be unique."""
    out=dict(old=old,new=new,increases=B.lt(old,new),equal=old==new)
    if old and new:
        out.update(index_old=old[0],index_new=new[0],index_equal=old[0]==new[0],
                   argument_old=old[1],argument_new=new[1],argument_equal=old[1]==new[1],
                   tail_equal=old[2]==new[2],single_old=old[2]==B.Z,single_new=new[2]==B.Z,
                   only_index_changes=old[0]!=new[0] and old[1:]==new[1:],
                   only_argument_changes=old[0]==new[0] and old[1]!=new[1] and old[2]==new[2])
    xs,ys=B.summ(old),B.summ(new); j=0
    while j<min(len(xs),len(ys)) and xs[j]==ys[j]:j+=1
    out.update(common_leading_summands=xs[:j],old_remaining_summands=xs[j:],new_remaining_summands=ys[j:])
    # Shortest summand suffix which really satisfies old + suffix = new.
    # This is an addition certificate, NOT ordinal subtraction.
    out['additive_suffix']=None
    for length in range(len(ys)+1):
        suffix=B.sumN(ys[len(ys)-length:]) if length else B.Z
        if A.Y.add(old,suffix)==new:
            out['additive_suffix']=suffix;break
    return out


def measure(row):
    base={k:row[k] for k in ('set','index','matrix','x','r','L','q','upg_xminus1','n')}
    try:
        M=list(map(tuple,row['matrix']));r=row['r'];L=row['L'];x=row['x'];k=row['upg_xminus1'];n=row['n']
        C,T=A.ctx(M),A.ctx(M[:x]);N=list(map(tuple,B.trio.expand([list(c) for c in M],n)));CN=A.ctx(N)
        if not all(ctx.ok for ctx in (C,T,CN)):raise ValueError('canonical evaluation failed')
        indexes={}
        for label,ctx in [('M',C),('T',T),('N',CN)]:
            indexes[label]={field:value_index(ctx,getattr(ctx,field)) for field in ('o','v')}
        lc=CN.CL(r);grown=[]
        for d in lc:
            if d>=x or not B.lt(T.o(d),CN.o(d)):continue
            new=CN.o(d);nv=CN.v(d);entry=dict(column=d,provenance=provenance(d,r,L,k),
                o_change=changes(T.o(d),new),v_change=changes(T.v(d),nv),
                old_o_index_is_v=bool(T.o(d)) and T.o(d)[0]==T.v(d),
                new_o_index_is_v=bool(new) and new[0]==nv)
            for label in ('M','T','N'):
                entry['matches_'+label]={
                    term+'_'+field:[provenance(i,r,L,k) if label=='N' else dict(column=i)
                                   for i in indexes[label][field].get(value,[])]
                    for term,value in [('new_o',new),('new_v',nv)] for field in ('o','v')}
            entry['other_N_o_matches']=[z for z in entry['matches_N']['new_o_o'] if z['column']!=d]
            grown.append(entry)
        # Genuine frames have a next counted child; complete states are not
        # admitted as matches merely because Good3 proves o(i) is OT.
        target_states=collections.defaultdict(list)
        for i in range(len(N)):
            cli=CN.CL(i);a=CN.v(i)
            for j,c in enumerate(cli):
                state=(a,B.spa(a,B.sumN([CN.o(d) for d in cli[:j]])),B.Z)
                target_states[state].append(dict(provenance(i,r,L,k),position=j,
                    previous_children=cli[:j],current_child=c,remaining_children=cli[j+1:]))
        frames=[]
        for j,c in enumerate(lc):
            state=(CN.v(r),B.spa(CN.v(r),B.sumN([CN.o(d) for d in lc[:j]])),B.Z)
            matches=target_states.get(state,[])
            frames.append(dict(position=j,current_child=c,previous_children=lc[:j],state=state,
                               matches_N=matches,other_column_matches_N=[m for m in matches if m['column']!=r]))
        return dict(base,status='RESOLVED',CL_N_r=lc,CL_T_r=T.CL(r),grown=grown,frames=frames)
    except Exception as e:return dict(base,status='UNRESOLVED',error=repr(e))


def file_task(path):
    path=Path(path);dest=OUT/path.name
    if dest.exists():return json.loads(dest.read_text())['counts']
    source=json.loads(path.read_text());counts=collections.Counter();records=[]
    for row in source['records']:
        if row['status']!='RESOLVED':
            records.append(row);counts['upstream.UNRESOLVED']+=1;continue
        rec=measure(row);records.append(rec)
        if rec['status']!='RESOLVED':counts['UNRESOLVED']+=1;continue
        pre='n'+str(row['n']);counts[pre+'.frames']+=1
        counts[pre+'.grown_count.'+str(len(rec['grown']))]+=1
        for entry in rec['grown']:
            counts[pre+'.grown_children']+=1
            counts[pre+'.other_N_o_match.'+str(bool(entry['other_N_o_matches']))]+=1
            for key in ('index_equal','argument_equal','only_index_changes','only_argument_changes','increases'):
                counts[pre+'.o_change.'+key+'.'+str(entry['o_change'].get(key))]+=1
            for label in ('M','T','N'):
                for key,vals in entry['matches_'+label].items():counts[pre+'.matches_'+label+'.'+key+'.'+str(bool(vals))]+=1
        for frame in rec['frames']:
            counts[pre+'.seed_splits']+=1
            matches=frame['other_column_matches_N']
            counts[pre+'.split.other_column_match.'+str(bool(matches))]+=1
            counts[pre+'.split.other_r_copy_match.'+str(any(m['template_is_r'] for m in matches))]+=1
            counts[pre+'.split.k_copy_match.'+str(any(m['template_is_k'] for m in matches))]+=1
        counts[pre+'.all_splits_other_column_match.'+str(all(f['other_column_matches_N'] for f in rec['frames']))]+=1
    F.atomic(dest,dict(set=source['set'],shard=source['shard'],counts=counts,records=records))
    return counts


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--self-test',action='store_true');args=parser.parse_args()
    if args.self_test:
        M=[(0,0,0),(1,1,1),(2,1,1),(3,1,0),(1,1,1),(2,1,1),(3,1,0),
           (1,1,1),(2,1,0),(3,2,1),(4,2,1),(5,2,0),(3,2,1),(4,2,1),(5,1,0),(4,2,1)]
        _,fail=F.inspect(0,M);rows=G.one(fail[0])
        for row in rows:
            row['set']='self-test';rec=measure(row)
            assert rec['status']=='RESOLVED',rec
            assert len(rec['grown'])==2,rec
            assert all(any(m['column']==row['r'] and m['position']==f['position'] for m in f['matches_N']) for f in rec['frames'])
            assert all(any(m['column']==g['column'] for m in g['matches_N']['new_o_o']) for g in rec['grown'])
            print(json.dumps(dict(n=row['n'],grown=[dict(column=g['column'],only_index_changes=g['o_change']['only_index_changes'],other_N_o_matches=g['other_N_o_matches']) for g in rec['grown']],other_frame_matches=[f['other_column_matches_N'] for f in rec['frames']])))
        return
    OUT.mkdir(parents=True,exist_ok=True)
    summary=json.loads((G.OUT/'summary.json').read_text());assert summary['complete']
    paths=sorted(G.OUT.glob('set*-shard*.json'));counts=collections.Counter()
    with multiprocessing.get_context('fork').Pool(3) as pool:
        for c in pool.imap_unordered(file_task,map(str,paths),chunksize=1):counts.update(c)
    F.atomic(OUT/'summary.json',dict(complete=True,n_samples=[2,3],counts=counts,input=str(G.OUT),checkpoints=len(paths)))
    print(json.dumps(dict(counts)),flush=True)


if __name__=='__main__':main()
