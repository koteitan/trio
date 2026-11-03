"""G6(b). Classify changed C2 seed children and candidate QFO witnesses.
Uses G5 checkpoints, never silently drops their UNRESOLVED C2 sources.
n=2,3 only. No assertion about all n or a new Lean residual.
Lhd tests use lhd_exact.lhd at z only, never the suspect eta checker.
"""
from pathlib import Path
import argparse, collections, json, multiprocessing, os, sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'tmp/codex'))
import seedfo_C_facts_20261104 as F
B,A=F.B,F.A
from lhd_exact import lhd
OUT=ROOT/'tmp/codex/seedfo_C2_shapes_20261104'


def rel(new,old):
    if new==old:return 'equal'
    if lhd(new,old):return 'Lhd_z'
    if B.lt(new,old):return 'lt_only'
    return 'not_lt'


def ancestors(C,row,i):
    seen=set(); i=C.e.par(row,i)
    while i is not None and i not in seen:
        seen.add(i); i=C.e.par(row,i)
    return seen


def states(C):
    """All intermediate states, including empty and complete child lists."""
    out=collections.defaultdict(list)
    for i in range(len(C.M)):
        lc=C.CL(i); a=C.v(i)
        for j in range(len(lc)+1):
            t=(a,B.spa(a,B.sumN([C.o(d) for d in lc[:j]])),B.Z)
            out[t].append([i,j])
    return out


def one(rec):
    M=list(map(tuple,rec['matrix'])); x=rec['x']; r=rec['r']; q=rec['q']; k=rec['upg_xminus1']
    base={key:rec[key] for key in ('index','matrix','x','r','q','L','upg_xminus1')}
    result=[]
    try:
        C,T=A.ctx(M),A.ctx(M[:x])
        if not C.ok or not T.ok:raise ValueError('source/prefix evaluation failed')
        sm,st=states(C),states(T)
        om,ot=collections.defaultdict(list),collections.defaultdict(list)
        for i in range(len(M)):om[C.o(i)].append(i)
        for i in range(x):ot[T.o(i)].append(i)
        for n in (2,3):
            try:
                N=list(map(tuple,B.trio.expand([list(d) for d in M],n))); CN=A.ctx(N)
                if not CN.ok:raise ValueError('target evaluation failed')
                lc,lt=CN.CL(r),T.CL(r); children=[]; frames=[]
                for j,d in enumerate(lc):
                    v=CN.o(d); oldT=T.o(d) if d<x else None
                    oldM=C.o(d) if d<len(M) else None
                    an0,an1=ancestors(C,0,d),ancestors(C,1,d)
                    children.append(dict(column=d, position=j, is_new_q=d==q,
                        block=None if d<r else (d-r)//(x-r),
                        original_index=d if d<r else r+(d-r)%(x-r),
                        k_equals_d=k==d, k_P0_ancestor=k in an0, k_P1_ancestor=k in an1,
                        d_P0_ancestor_k=d in ancestors(C,0,k),
                        upg_M_d=C.upg(d) if d<len(M) else None,
                        upg_T_d=T.upg(d) if d<x else None,
                        upg_N_d=CN.upg(d),
                        target_o=v, prefix_o=oldT, source_o=oldM,
                        relation_T=rel(v,oldT) if oldT is not None else 'outside',
                        relation_M=rel(v,oldM) if oldM is not None else 'outside',
                        equal_o_T_indices=ot.get(v,[]),equal_o_M_indices=om.get(v,[])))
                    a=CN.v(r); state=(a,B.spa(a,B.sumN([CN.o(c) for c in lc[:j]])),B.Z)
                    frames.append(dict(position=j, child=d, state=state, OT=bool(B.isOT(state)),
                        matching_M_frames=sm.get(state,[]),matching_T_frames=st.get(state,[])))
                common=[c for c in children if c['column'] in lt]
                facts=dict(CL_append_q=lc==lt+[q], v_r_equal=CN.v(r)==T.v(r),
                    changed_children_equal_or_Lhd_z=all(c['relation_T'] in ('equal','Lhd_z') for c in common),
                    changed_children_le=all(c['relation_T'] in ('equal','Lhd_z','lt_only') for c in common),
                    changed_children_are_upgraders_to_k=all(c['upg_M_d']==k for c in common if c['relation_T']!='equal'),
                    changed_children_are_k_descendants=all(c['k_P0_ancestor'] or c['k_equals_d'] for c in common if c['relation_T']!='equal'),
                    all_states_source_frames=all(f['matching_M_frames'] for f in frames),
                    all_states_prefix_frames=all(f['matching_T_frames'] for f in frames),
                    all_states_source_r_frames=all(any(i==r for i,j in f['matching_M_frames']) for f in frames),
                    all_states_prefix_r_frames=all(any(i==r for i,j in f['matching_T_frames']) for f in frames),
                    QFO_r=all(f['OT'] for f in frames))
                result.append(dict(base,n=n,status='RESOLVED',CL_T_r=lt,CL_N_r=lc,
                    children=children,frames=frames,candidates={k:bool(v) for k,v in facts.items()}))
            except Exception as e:result.append(dict(base,n=n,status='UNRESOLVED',error=repr(e)))
    except Exception as e:result.append(dict(base,status='UNRESOLVED',error=repr(e)))
    return result


def file_task(filename):
    src=Path(filename); target=OUT/src.name
    if target.exists():return json.loads(target.read_text())['counts']
    data=json.loads(src.read_text()); selected={}
    for rec in data['failures']:
        if rec.get('partition')=='un_false':selected.setdefault(rec['index'],rec)
    records=[]; counts=collections.Counter(C2_sources=len(selected))
    for rec in selected.values():
        for row in one(rec):
            row['set']=data['set']; records.append(row)
            if row['status']=='UNRESOLVED':counts['UNRESOLVED']+=1;continue
            n=row['n'];counts[f'n{n}.frames']+=1
            for name,value in row['candidates'].items():counts[f'n{n}.{name}.{bool(value)}']+=1
            for c in row['children']:
                counts[f'n{n}.child.relation_T.{c["relation_T"]}']+=1
            counts[f'n{n}.changed_children.{sum(c["relation_T"] not in ("equal","outside") for c in row["children"])}']+=1
    F.atomic(target,dict(set=data['set'],shard=data['shard'],counts=counts,records=records))
    return counts


def main():
    p=argparse.ArgumentParser();p.add_argument('--self-test',action='store_true');args=p.parse_args()
    if args.self_test:
        M=[(0,0,0),(1,1,1),(2,1,1),(3,1,0),(1,1,1),(2,1,1),(3,1,0),
           (1,1,1),(2,1,0),(3,2,1),(4,2,1),(5,2,0),(3,2,1),(4,2,1),(5,1,0),(4,2,1)]
        _,fail=F.inspect(0,M); rows=one(fail[0])
        assert len(rows)==2 and all(r['status']=='RESOLVED' for r in rows),rows
        print(json.dumps([dict(n=r['n'],candidates=r['candidates']) for r in rows]));return
    OUT.mkdir(parents=True,exist_ok=True)
    summary=json.loads((F.OUT/'summary.json').read_text());assert summary['complete']
    paths=[str(ROOT/p) for p in summary['checkpoints']]
    counts=collections.Counter()
    # 1 driver + 3 workers; default Unix fork, without a resource-tracker process.
    with multiprocessing.Pool(3) as pool:
        for c in pool.imap_unordered(file_task,paths,chunksize=1):counts.update(c)
    F.atomic(OUT/'summary.json',dict(complete=True,n_samples=[2,3],counts=counts,
        source_summary=str(F.OUT/'summary.json'),checkpoints=len(paths)))
    print(json.dumps(dict(counts)),flush=True)


if __name__=='__main__':main()
