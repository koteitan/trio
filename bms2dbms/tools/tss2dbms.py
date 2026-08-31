#!/usr/bin/env python3
"""tss2dbms — トリオ数列 (Trio Sequence System, BMS 3 行) と DBMS 3 行を変換する CLI。

変換関数は MrredsharkFan 氏の `bmsToDbms` の Python 版 `mrf3.b2d` を呼ぶ
（出所: <https://github.com/MrredsharkFan/w-Y-global-lngi> の `conv.js`）。

    conv3        = mrf3.b2d              conv.js  bmsToDbms
    conv3 の逆   = mrf3.d2b              conv.js  dbmsToBms
    translate3   = rows3.translate3      lean/Term.lean  translate

**2 行の `bms2dbms.py` と違い、この変換の正しさは Lean で証明されていない**
（測った範囲では単射・全射・順序保存だが、証明ではない）。
だから `--no-verify` を付けない限り、変換のたびに像が DBMS 標準形かを検算する。

扱うのは `z ≤ 1`（行 2 が 0 か 1）の断片。`z ≥ 2` は `--force` で強行できるが
`conv3` の定義域の外である。

使い方は同じディレクトリの README-tss.md を見ること。
"""
from __future__ import annotations

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import rows3
import mrf3
from core import expand, isstd, parse, rows, show

EXIT_OK = 0
EXIT_NOT_STANDARD = 1
EXIT_MISMATCH = 2
EXIT_USAGE = 3

ROWS = 3


class InputError(Exception):
    pass


def parse_input(s: str):
    """`"(0,0,0)(1,1,1)[3][1]"` を読んで、展開まで済ませた 3 行の行列にする。

    列ごとに行数が違う書き方（シートの E 列の `(0)(1)(2,1)(3,2,1)` など）も
    受ける。足りない行は 0 で埋める。
    """
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
    if rows(M) > ROWS:
        raise InputError("3 行までの行列だけを扱う（この入力は %d 行）" % rows(M))
    # 2 行以下は行 2 を 0 で埋めて 3 行として扱う。埋め込み `emb` は展開と可換で
    # （`lean/Pair/Bridge.lean` の `oper_emb`）、`b2d3` の像は 2 行の `convC` の
    # 像に 0 行を足したものに一致する（`≤7` 列 7256 個で違反 0）。
    M = parse(s, ROWS)
    for n in brackets:
        M = expand(M, n)
    return tuple(tuple(c) for c in M)


def show_term3(t):
    """`rows3.translate3` の項を読める形にする（`rows2.show_term` の 3 行版）。
    段は行 1 と行 2 の対。"""
    if t[0] == "Z":
        return "Z"
    return "P%s(%s,%s)" % (t[1], show_term3(t[2]), show_term3(t[3]))


def convert(M):
    """BMS 3 行標準形 -> DBMS 3 行標準形。"""
    return tuple(mrf3.b2d(M))


def invert(D):
    """DBMS 3 行標準形 -> BMS 3 行標準形。"""
    return tuple(mrf3.d2b(D))


def run_one(src, args, out):
    """1 件を処理して exit code を返す。"""
    src_ver = "DBMS" if args.reverse else "BMS"
    dst_ver = "BMS" if args.reverse else "DBMS"

    std = isstd(src, src_ver)
    if args.check:
        out.write("%s\t%s\n" % ("standard" if std else "non-standard", show(src)))
        return EXIT_OK if std else EXIT_NOT_STANDARD

    if not std:
        sys.stderr.write("tss2dbms: %s は %s 標準形ではない。--force で強行できる。\n"
                         % (show(src), src_ver))
        if not args.force:
            return EXIT_NOT_STANDARD

    if any(c[2] > 1 for c in src):
        sys.stderr.write("tss2dbms: %s は z >= 2 を含む（conv3 の定義域の外）。"
                         "--force で強行できる。\n" % show(src))
        if not args.force:
            return EXIT_NOT_STANDARD

    try:
        dst = invert(src) if args.reverse else convert(src)
    except Exception as e:
        sys.stderr.write("tss2dbms: 変換に失敗: %s (%s)\n" % (show(src), e))
        return EXIT_MISMATCH

    code = EXIT_OK
    if not args.no_verify and std:
        # (1) 像が標準形か。conv3 は未完成なのでここが落ちうる。
        if not isstd(dst, dst_ver):
            sys.stderr.write("tss2dbms: 像が %s 標準形でない: %s\n"
                             % (dst_ver, show(dst)))
            code = EXIT_MISMATCH
        # (2) 往復。b2d3 の像の上では d2b3 が逆写像になるはず。
        try:
            back = convert(dst) if args.reverse else invert(dst)
        except Exception as e:
            sys.stderr.write("tss2dbms: 逆変換に失敗: %s (%s)\n" % (show(dst), e))
            code = EXIT_MISMATCH
        else:
            if back != src:
                sys.stderr.write("tss2dbms: 往復しない: %s -> %s -> %s\n"
                                 % (show(src), show(dst), show(back)))
                code = EXIT_MISMATCH

    if args.quiet:
        out.write("%s\n" % show(dst))
    else:
        out.write("%s  ->  %s\n" % (show(src), show(dst)))
    if args.tree:
        bms = dst if args.reverse else src
        out.write("  BMS   %s\n" % show_term3(rows3.translate3(list(bms))))
    return code


def main(argv=None):
    ap = argparse.ArgumentParser(
        prog="tss2dbms",
        description="トリオ数列（BMS 3 行, z<=1）<-> DBMS 3 行 の変換。"
                    "2 行の bms2dbms.py と違い、正しさは証明されていない",
        epilog="行列を渡さないと標準入力を 1 行 1 件として読む。詳しくは README-tss.md。")
    ap.add_argument("matrix", nargs="*",
                    help='例: "(0,0,0)(1,1,1)" 。末尾に [n] を付けると先に展開する')
    ap.add_argument("-r", "--reverse", action="store_true",
                    help="DBMS -> BMS（inv3.d2b3。証明は無い）")
    ap.add_argument("-c", "--check", action="store_true",
                    help="変換せず、標準形かどうかだけ報告する")
    ap.add_argument("-t", "--tree", action="store_true",
                    help="BMS 側の項（translate3）も表示する")
    ap.add_argument("-q", "--quiet", action="store_true",
                    help="結果の行列だけを出す")
    ap.add_argument("-f", "--force", action="store_true",
                    help="標準形でなくても、z>=2 でも変換する")
    ap.add_argument("--no-verify", action="store_true",
                    help="像の標準形チェックと往復チェックを省く")
    args = ap.parse_args(argv)

    items = args.matrix
    if not items or items == ["-"]:
        items = [ln for ln in (l.strip() for l in sys.stdin)
                 if ln and not ln.startswith("#")]
    if not items:
        ap.print_usage(sys.stderr)
        return EXIT_USAGE

    out = sys.stdout
    worst = EXIT_OK
    for s in items:
        try:
            M = parse_input(s)
        except InputError as e:
            sys.stderr.write("tss2dbms: %s\n" % e)
            worst = max(worst, EXIT_USAGE)
            continue
        worst = max(worst, run_one(M, args, out))
    return worst


if __name__ == "__main__":
    sys.exit(main())
