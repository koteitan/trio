#!/usr/bin/env python3
"""dbms2yseq — DBMS 標準形と Y 数列を相互に変換する CLI。

Y 数列と DBMS 標準形の間に成り立つ対応を使う。Y 数列そのものの定義は別にある。
出典: ユーザーブログ:Koteitan/Dimensional BMS の定義とY数列との対応（巨大数研究 Wiki）。

    Y()  = DBMS(())
    Y(1) = DBMS((0))
    Y(Y ⌢ (y)) = DBMS(X ⌢ (x))
        ここで Y(Y) = DBMS(X) であり、x は
        「X の右に置いて X⌢(x) を DBMS 標準形にする列」を
        小さい順に並べたときの y 番目。

つまり DBMS -> Y は「各列が、そこに置ける列の中で何番目に小さいか」を数えるだけ。
Y -> DBMS はその逆で、y 番目の候補を取って伸ばす。

入出力は 2 行の断片に限る（3 行目が非ゼロなら終了コード 4）。ただし候補の
数え上げ自体は一般の行数で行う。行を減らすと候補が抜けて順位がずれるためで、
たとえば (3,1,1) は (3,1) と (3,2) の間に来る。

列の大小は、後ろにゼロを補ってからの辞書式（(2)=(2,0) < (2,1)）。

使い方は同じディレクトリの README.md を見ること。
"""
from __future__ import annotations

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import core
from core import isstd, parse, show

EXIT_OK = 0
EXIT_NOT_STANDARD = 1
EXIT_MISMATCH = 2
EXIT_USAGE = 3
EXIT_OUT_OF_DOMAIN = 4


class InputError(Exception):
    pass


class DomainError(Exception):
    """2 行の断片の外。"""


def check_two_rows(M):
    """3 行目以降が非ゼロなら弾く。候補の数え上げは一般の行数で行うが
    （行が足りないと順位がずれる）、入出力は 2 行に限る。"""
    for c in M:
        if any(v != 0 for v in c[2:]):
            raise DomainError(
                "%s は 2 行の断片の外（3 行目が非ゼロ）" % show_dbms(M))
    return M


def trim(col):
    """後ろのゼロを落とす。表示用。"""
    c = list(col)
    while len(c) > 1 and c[-1] == 0:
        c.pop()
    return tuple(c)


def show_dbms(M):
    if not M:
        return "()"
    return "".join("(" + ",".join(str(v) for v in trim(c)) + ")" for c in M)


def pad(M, Y):
    return tuple(tuple(list(c) + [0] * (Y - len(c))) for c in M)


def rows_for(M):
    """安全な行数。深さ `x` の列は最大で `x+1` 個の非ゼロ成分を持てる
    （対角 `(x, x-1, ..., 1, 0)`）ので、それだけ確保する。行が足りないと
    候補列が取りこぼされ、順位がずれる（`(3,1,1)` は `(3,1)` と `(3,2)` の間）。"""
    if not M:
        return 1
    return max(max(c[0] for c in M) + 1, max(len(c) for c in M), 1)


def candidates(X, Y):
    """`X` の右に置ける列を小さい順に返す。`X` は `Y` 行に揃えてあること。"""
    prev = X[-1][0] if X else -1
    out = []

    def rec(j, cur):
        if j == Y:
            c = tuple(cur)
            if isstd(X + (c,), "DBMS"):
                out.append(c)
            return
        hi = cur[0] - j if j > 0 else prev + 1
        if hi < 0:
            hi = 0
        for v in range(hi + 1):
            rec(j + 1, cur + [v])

    rec(0, [])
    out.sort()
    return out


def dbms2y(M, rows=None):
    """DBMS 標準形 -> Y 数列。"""
    Y = rows if rows is not None else rows_for(M)
    M = pad(M, Y)
    seq = []
    for i in range(len(M)):
        cs = candidates(M[:i], Y)
        try:
            seq.append(cs.index(M[i]) + 1)
        except ValueError:
            raise InputError(
                "%d 列目 %s は %s の右に置けない（DBMS 標準形にならない）"
                % (i + 1, show_dbms((M[i],)), show_dbms(M[:i]) if i else "()"))
    return seq


def y2dbms(seq, rows=None):
    """Y 数列 -> DBMS 標準形。"""
    Y = rows if rows is not None else max(len(seq), 1)
    X = ()
    for i, y in enumerate(seq):
        if y < 1:
            raise InputError("Y 数列の要素は 1 以上（%d 番目が %d）" % (i + 1, y))
        cs = candidates(X, Y)
        if y > len(cs):
            raise InputError(
                "%d 番目の %d が大きすぎる（%s の右に置ける列は %d 個）"
                % (i + 1, y, show_dbms(X) if X else "()", len(cs)))
        X = X + (cs[y - 1],)
    return X


def parse_dbms(s):
    s = s.strip()
    if s in ("", "()"):
        return ()
    try:
        M = parse(s)
    except Exception as e:
        raise InputError("DBMS 行列として読めない: %s (%s)" % (s, e))
    if not M:
        return ()
    return M


def parse_y(s):
    s = s.strip()
    if s.startswith("Y") or s.startswith("y"):
        s = s[1:].strip()
    s = s.strip("()")
    if not s:
        return []
    try:
        return [int(v) for v in s.replace(" ", ",").split(",") if v != ""]
    except ValueError:
        raise InputError("Y 数列として読めない: %s" % s)


def run_one(s, args, out):
    if args.reverse:
        seq = parse_y(s)
        X = y2dbms(seq, args.rows)
        check_two_rows(X)
        Y = args.rows if args.rows is not None else max(len(seq), 1)
        src, dst = "Y(%s)" % ",".join(map(str, seq)), show_dbms(X)
        code = EXIT_OK
        if not args.no_verify and dbms2y(X, Y) != seq:
            sys.stderr.write("dbms2yseq: 往復しない: %s\n" % src)
            code = EXIT_MISMATCH
    else:
        M = parse_dbms(s)
        check_two_rows(M)
        Y = args.rows if args.rows is not None else rows_for(M)
        X = pad(M, Y)
        code = EXIT_OK
        if M and not isstd(M, "DBMS"):
            sys.stderr.write("dbms2yseq: %s は DBMS 標準形ではない\n" % show_dbms(M))
            if not args.force:
                return EXIT_NOT_STANDARD
        seq = dbms2y(M, Y)
        src, dst = show_dbms(M), "Y(%s)" % ",".join(map(str, seq))
        if not args.no_verify and y2dbms(seq, Y) != X:
            sys.stderr.write("dbms2yseq: 往復しない: %s\n" % src)
            code = EXIT_MISMATCH

    if args.quiet:
        out.write("%s\n" % dst)
    else:
        out.write("%s  ->  %s\n" % (src, dst))
    if args.steps:
        for i in range(len(X)):
            cs = candidates(X[:i], Y)
            out.write("  %2d: %-12s 候補 %2d 個中 %2d 番目   %s\n"
                      % (i + 1, show_dbms((X[i],)), len(cs), seq[i],
                         " ".join(show_dbms((c,)) for c in cs)))
    return code


def main(argv=None):
    ap = argparse.ArgumentParser(
        prog="dbms2yseq",
        description="DBMS 標準形 <-> Y 数列（巨大数研究 Wiki の Koteitan 氏が示した対応）",
        epilog="引数を渡さないと標準入力を 1 行 1 件として読む。詳しくは README.md。")
    ap.add_argument("arg", nargs="*", help='例: "(0)(1)(2,1)(3,2,1)" 、-r なら "1,2,4,8"')
    ap.add_argument("-r", "--reverse", action="store_true", help="Y 数列 -> DBMS")
    ap.add_argument("-s", "--steps", action="store_true", help="各列の候補と順位を表示する")
    ap.add_argument("-q", "--quiet", action="store_true", help="結果だけを出す")
    ap.add_argument("-f", "--force", action="store_true", help="標準形でなくても変換する")
    ap.add_argument("--rows", type=int, default=None, help="-r のときの行数（既定は列数）")
    ap.add_argument("--no-verify", action="store_true", help="往復の検算を省く")
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
            sys.stderr.write("dbms2yseq: %s\n" % e)
            worst = max(worst, EXIT_OUT_OF_DOMAIN)
        except InputError as e:
            sys.stderr.write("dbms2yseq: %s\n" % e)
            worst = max(worst, EXIT_USAGE)
    return worst


if __name__ == "__main__":
    sys.exit(main())
