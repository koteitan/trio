/-
`Ebocf.eval` を標準入力の行列に当てる（シートの検算用、ライブラリには入れない）。
入力: 1 行に `行番号<TAB>(0,0,0)(1,1,1)...`（行列）か `行番号<TAB>=[a,b,c]`（項 ψ_a(b)+c、0 は `[]`）。
出力: `行番号<TAB>` と、行列なら `Ebocf.str (Ebocf.eval M)`（循環なら `none`）、項なら `Ebocf.str (Ebocf.sf t)`。
実行: `lake env lean --run EbocfRun.lean < in.tsv`（先に `lake build Ebocf`）。
-/
import Ebocf

open TRIO

def parseMat (s : String) : TrioSeq :=
  ((s.splitOn ")").filterMap fun c =>
    match ((c.replace "(" "").splitOn ",").filter (· ≠ "") |>.map String.toNat! with
    | [x, y, w] => some (x, y, w)
    | [x, y] => some (x, y, 0)
    | [x] => some (x, 0, 0)
    | _ => none)

/-- Parse `[]` or `[a,b,c]`; returns the term and the rest. -/
partial def parseT : List Char → Option (Ebocf.T × List Char)
  | '[' :: ']' :: r => some (.z, r)
  | '[' :: r => do
    let (a, r) ← parseT r
    let r ← match r with | ',' :: r => some r | _ => none
    let (b, r) ← parseT r
    let r ← match r with | ',' :: r => some r | _ => none
    let (c, r) ← parseT r
    match r with | ']' :: r => some (.psi a b c, r) | _ => none
  | _ => none

partial def loop (h : IO.FS.Stream) (o : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  match (line.trimAsciiEnd.toString.splitOn "\t") with
  | [r, m] =>
    if m.startsWith "=" then
      let t := ((parseT ((m.toList.drop 1).filter (· ≠ ' '))).map Prod.fst).getD .z
      o.putStrLn (r ++ "\t" ++ Ebocf.str (Ebocf.sf t))
    else o.putStrLn (r ++ "\t" ++ ((Ebocf.eval (parseMat m)).map Ebocf.str).getD "none")
  | _ => pure ()
  loop h o

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
