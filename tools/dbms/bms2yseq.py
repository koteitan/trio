#!/usr/bin/env python3
"""bms2yseq — BMS 2 行標準形と Y 数列を相互に変換する CLI。

2 つの変換の合成である。

    BMS 2 行標準形  --conC-->  DBMS 標準形  --順位を数える-->  Y 数列
                    bms2dbms.py              dbms2yseq.py

左半分 `conC` の正しさは Lean 4 / Mathlib で証明済み（`lean/Dbms.lean`,
`lean/DbmsStd.lean`、`sorry` なし・追加公理なし）:

    readC_conC_ST   : ST_PS M -> readCon (conC M) = translate M
    ST_D_conC_final : ST_PS M -> ST_D (conC M)
    conC_injective  : conC M = conC N -> M = N

右半分は 巨大数研究 Wiki の
ユーザーブログ:Koteitan/Dimensional BMS の定義とY数列との対応 の定義そのまま。

使い方は同じディレクトリの README.md を見ること。
"""
from __future__ import annotations

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import bms2dbms as B
import dbms2yseq as D
import rows2
from core import isstd, show

EXIT_OK = 0
EXIT_NOT_STANDARD = 1
EXIT_MISMATCH = 2
EXIT_OUT_OF_DOMAIN = 4
EXIT_USAGE = 3


class DomainError(Exception):
    """2 行の断片の外。"""


def to_pairs(M):
    """行数を 2 に揃える。3 行目以降が非ゼロなら 2 行の断片の外。"""
    for c in M:
        if any(v != 0 for v in c[2:]):
            raise DomainError(
                "%s は 2 行の断片の外（3 行目が非ゼロ）" % D.show_dbms(M))
    return tuple((c[0], c[1] if len(c) > 1 else 0) for c in M)


def bms2y(M, rows=None):
    """BMS 2 行標準形 -> (DBMS 標準形, Y 数列)。"""
    Dm = B.convert(M)
    R = rows if rows is not None else D.rows_for(Dm)
    return Dm, D.dbms2y(Dm, R)


def y2bms(seq, rows=None):
    """Y 数列 -> (DBMS 標準形, BMS 2 行標準形)。"""
    R = rows if rows is not None else max(len(seq), 1)
    Dm = D.y2dbms(seq, R)
    return Dm, B.invert(to_pairs(Dm))


def run_one(s, args, out):
    code = EXIT_OK
    if args.reverse:
        seq = D.parse_y(s)
        Dm, M = y2bms(seq, args.rows)
        src = "Y(%s)" % ",".join(map(str, seq))
        dst = show(M)
        if not args.no_verify:
            if B.convert(M) != to_pairs(Dm):
                sys.stderr.write("bms2yseq: BMS へ戻して往復しない: %s\n" % src)
                code = EXIT_MISMATCH
            if not isstd(M, "BMS"):
                sys.stderr.write("bms2yseq: 戻した行列が BMS 標準形でない: %s\n" % show(M))
                code = EXIT_MISMATCH
    else:
        M = B.parse_input(s)
        if not isstd(M, "BMS"):
            sys.stderr.write("bms2yseq: %s は BMS 標準形ではない\n" % show(M))
            if not args.force:
                return EXIT_NOT_STANDARD
        Dm, seq = bms2y(M, args.rows)
        src = show(M)
        dst = "Y(%s)" % ",".join(map(str, seq))
        if not args.no_verify:
            # 証明されている 2 つ（読みの一致・像が標準形）と、Y 側の往復
            if rows2.readC(list(Dm)) != rows2.translate(list(M)):
                sys.stderr.write("bms2yseq: 読みが一致しない: %s\n" % src)
                code = EXIT_MISMATCH
            if not isstd(Dm, "DBMS"):
                sys.stderr.write("bms2yseq: 像が DBMS 標準形でない: %s\n" % D.show_dbms(Dm))
                code = EXIT_MISMATCH
            R = args.rows if args.rows is not None else D.rows_for(Dm)
            if D.y2dbms(seq, R) != D.pad(Dm, R):
                sys.stderr.write("bms2yseq: Y から戻して往復しない: %s\n" % src)
                code = EXIT_MISMATCH

    if args.quiet:
        out.write("%s\n" % dst)
    else:
        out.write("%s  ->  %s\n" % (src, dst))
    if args.steps:
        out.write("  DBMS  %s\n" % D.show_dbms(Dm))
        R = args.rows if args.rows is not None else D.rows_for(Dm)
        X = D.pad(Dm, R)
        y = D.dbms2y(Dm, R)
        for i in range(len(X)):
            cs = D.candidates(X[:i], R)
            out.write("  %2d: %-12s 候補 %2d 個中 %2d 番目\n"
                      % (i + 1, D.show_dbms((X[i],)), len(cs), y[i]))
    return code


def main(argv=None):
    ap = argparse.ArgumentParser(
        prog="bms2yseq",
        description="BMS 2 行標準形 <-> Y 数列（bms2dbms と dbms2yseq の合成）",
        epilog="引数を渡さないと標準入力を 1 行 1 件として読む。詳しくは README.md。")
    ap.add_argument("arg", nargs="*",
                    help='例: "(0,0)(1,1)(2,2)" 、-r なら "1,2,4,7"。'
                         '末尾の [n] で先に展開する')
    ap.add_argument("-r", "--reverse", action="store_true", help="Y 数列 -> BMS")
    ap.add_argument("-s", "--steps", action="store_true",
                    help="途中の DBMS と各列の順位を表示する")
    ap.add_argument("-q", "--quiet", action="store_true", help="結果だけを出す")
    ap.add_argument("-f", "--force", action="store_true", help="標準形でなくても変換する")
    ap.add_argument("--rows", type=int, default=None, help="DBMS 側の行数")
    ap.add_argument("--no-verify", action="store_true", help="検算を省く")
    args = ap.parse_args(argv)

    items = args.arg
    if not items or items == ["-"]:
        items = [ln for ln in (l.strip() for l in sys.stdin) if ln and not ln.startswith("#")]
    if not items:
        ap.print_usage(sys.stderr)
        return EXIT_USAGE

    worst = EXIT_OK
    for s in items:
        try:
            worst = max(worst, run_one(s, args, sys.stdout))
        except DomainError as e:
            sys.stderr.write("bms2yseq: %s\n" % e)
            worst = max(worst, EXIT_OUT_OF_DOMAIN)
        except (B.InputError, D.InputError) as e:
            sys.stderr.write("bms2yseq: %s\n" % e)
            worst = max(worst, EXIT_USAGE)
    return worst


if __name__ == "__main__":
    sys.exit(main())
