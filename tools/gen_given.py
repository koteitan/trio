"""与えた行列（シートにない中間の行列）の W 0 の証明を gen_gyk の規則で作る。

使い方: python3 tools/gen_given.py OUT.lean NAME1=(0,0,0)(1,1,1)... NAME2=...
"""
import re
import sys
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import gen_gyk as g


def parse(s):
    return [tuple(int(x) for x in m.groups()) for m in re.finditer(r'\((\d+),(\d+),(\d+)\)', s)]


def main():
    out = sys.argv[1]
    name = out.split('/')[-1].replace('.lean', '')
    body = []
    for arg in sys.argv[2:]:
        tag, mat = arg.split('=', 1)
        M = parse(mat)
        roots = [i for i in range(len(M)) if M[i][0] == 0]
        try:
            p = g.tree(M, roots[0])
            for r0 in roots[1:]:
                p = f'(Wg_app {p} {g.tree(M, r0)} (by omega) (by intro p _; simp [entry]))'
        except g.Fail as ex:
            print(tag, 'Fail:', ex)
            continue
        print(tag, 'ok')
        body.append(f'/-- ★ {mat} -/\ntheorem {tag}_mem : ({g.lit(M)} : TrioSeq) ∈ W 0 := by\n'
                    f'  have h := GxB.Wg0_sub_W0 {p}\n  simpa [{g.SIMP}] using h\n')
    hdr = (f'/-\n{name}.lean: tools/gen_given.py が生成。シートの行の間の行列。\n-/\n'
           'import GzJ\nimport GzN\n\nnamespace TRIO\n' f'namespace {name}\n\n'
           'open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY\n'
           'open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzJ GzM GzN\n\n')
    open(out, 'w').write(hdr + '\n'.join(body) + f'\nend {name}\nend TRIO\n')


if __name__ == '__main__':
    main()
