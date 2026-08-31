#!/usr/bin/env python3
"""bms2dbms — BMS 2 行標準形と DBMS 標準形を相互に変換する CLI。

変換 `conC` とその正しさは Lean で証明されている（`lean/Dbms.lean`,
`lean/DbmsStd.lean`）。このスクリプトはその参照実装 `rows2.py` を呼ぶだけで、
Lean 側の定義と 1 対 1 に対応している:

    conC             = rows2.convC          lean/Dbms.lean  conC
    readCon          = rows2.readC          lean/Dbms.lean  readCon
    translate        = rows2.translate      lean/Pair/Term.lean translate

証明されている命題:

    readC_conC_ST   : ST_PS M -> readCon (conC M) = translate M
    ST_D_conC_final : ST_PS M -> ST_D (conC M)
    conC_injective  : ST_PS M -> ST_PS N -> conC M = conC N -> M = N

使い方は同じディレクトリの README.md を見ること。
"""
from __future__ import annotations

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import core
import rows2
from core import expand, isstd, parse, show

EXIT_OK = 0
EXIT_NOT_STANDARD = 1
EXIT_MISMATCH = 2
EXIT_USAGE = 3


class InputError(Exception):
    pass


def parse_input(s: str):
    """`"(0,0)(1,1)(2,2)[3][1]"` を (行列, 展開の並び) に割る。"""
    s = s.strip()
    brackets = []
    while s.endswith("]"):
        i = s.rfind("[")
        if i < 0:
            raise InputError("閉じない ] がある: %s" % s)
        body = s[i + 1:-1].strip()
        if not body.isdigit():
            raise InputError("[] の中は 0 以上の整数だけ: [%s]" % body)
        brackets.append(int(body))
        s = s[:i].rstrip()
    brackets.reverse()
    if not s:
        raise InputError("行列が空")
    try:
        M = parse(s)
    except Exception as e:
        raise InputError("行列として読めない: %s (%s)" % (s, e))
    if not M:
        raise InputError("行列が空")
    if len(M[0]) != 2:
        raise InputError("2 行の行列だけを扱う（この入力は %d 行）" % len(M[0]))
    for n in brackets:
        M = expand(M, n)
    return M


def convert(M):
    """BMS 2 行標準形 -> DBMS 標準形。"""
    return tuple(tuple(c) for c in rows2.convC(list(M)))


def invert(D):
    """DBMS 標準形 -> BMS 2 行標準形（`untranslate . readCon`）。"""
    return tuple(tuple(c) for c in rows2.untranslate(rows2.readC(list(D))))


def term_of(M, ver):
    return rows2.translate(list(M)) if ver == "BMS" else rows2.readC(list(M))


def run_one(src, args, out):
    """1 件を処理して exit code を返す。"""
    src_ver = "DBMS" if args.reverse else "BMS"
    dst_ver = "BMS" if args.reverse else "DBMS"

    std = isstd(src, src_ver)
    if args.check:
        out.write("%s\t%s\n" % ("standard" if std else "non-standard", show(src)))
        return EXIT_OK if std else EXIT_NOT_STANDARD

    if not std:
        sys.stderr.write(
            "bms2dbms: %s は %s 標準形ではない（変換の正しさは標準形でしか"
            "証明されていない）。--force で強行できる。\n" % (show(src), src_ver))
        if not args.force:
            return EXIT_NOT_STANDARD

    dst = invert(src) if args.reverse else convert(src)

    code = EXIT_OK
    if not args.no_verify and std:
        # 証明されている 2 つの性質をその場で確かめる。
        if not isstd(dst, dst_ver):
            sys.stderr.write("bms2dbms: 像が %s 標準形でない: %s\n"
                             % (dst_ver, show(dst)))
            code = EXIT_MISMATCH
        # readC_conC_ST: readCon (conC M) = translate M
        bms, dbms = (dst, src) if args.reverse else (src, dst)
        if rows2.readC(list(dbms)) != rows2.translate(list(bms)):
            sys.stderr.write("bms2dbms: 読みが一致しない: %s\n" % show(src))
            code = EXIT_MISMATCH
        # 逆変換のときは往復も見る（conC の像に入らない DBMS 標準形もありうる）
        if args.reverse and convert(dst) != src:
            sys.stderr.write(
                "bms2dbms: %s は conC の像に入らない（往復しない）\n" % show(src))
            code = EXIT_MISMATCH

    if args.quiet:
        out.write("%s\n" % show(dst))
    else:
        out.write("%s  ->  %s\n" % (show(src), show(dst)))
    if args.tree:
        out.write("  %-5s %s\n" % (src_ver, rows2.show_term(term_of(src, src_ver))))
        out.write("  %-5s %s\n" % (dst_ver, rows2.show_term(term_of(dst, dst_ver))))
    return code


def main(argv=None):
    ap = argparse.ArgumentParser(
        prog="bms2dbms",
        description="BMS 2 行標準形 <-> DBMS 標準形の変換（Lean で正しさを証明済み）",
        epilog="行列を渡さないと標準入力を 1 行 1 件として読む。詳しくは README.md。")
    ap.add_argument("matrix", nargs="*",
                    help='例: "(0,0)(1,1)(2,2)" 。末尾に [n] を付けると先に展開する')
    ap.add_argument("-r", "--reverse", action="store_true",
                    help="DBMS -> BMS（読みを経由した逆変換）")
    ap.add_argument("-c", "--check", action="store_true",
                    help="変換せず、標準形かどうかだけ報告する")
    ap.add_argument("-t", "--tree", action="store_true",
                    help="両側の項（Three）も表示する")
    ap.add_argument("-q", "--quiet", action="store_true",
                    help="結果の行列だけを出す")
    ap.add_argument("-f", "--force", action="store_true",
                    help="標準形でなくても変換する（正しさの保証は無い）")
    ap.add_argument("--no-verify", action="store_true",
                    help="変換後の検算を省く")
    args = ap.parse_args(argv)

    items = args.matrix
    if not items or items == ["-"]:
        items = [ln for ln in (l.strip() for l in sys.stdin) if ln and not ln.startswith("#")]
    if not items:
        ap.print_usage(sys.stderr)
        return EXIT_USAGE

    out = sys.stdout
    worst = EXIT_OK
    for s in items:
        try:
            M = parse_input(s)
        except InputError as e:
            sys.stderr.write("bms2dbms: %s\n" % e)
            worst = max(worst, EXIT_USAGE)
            continue
        worst = max(worst, run_one(M, args, out))
    return worst


if __name__ == "__main__":
    sys.exit(main())
