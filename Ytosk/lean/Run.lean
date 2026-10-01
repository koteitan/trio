/-
`eval` を標準入力の行列に当てる（シートの検算用、ライブラリには入れない）。
入力: 1 行に `行番号<TAB>(0,0,0)(1,1,1)...`（行列）か `行番号<TAB>=[a,b,c]`（項 ψ_a(b)+c、0 は `[]`）。
出力: `行番号<TAB>` と、行列なら `str (eval M)`（循環なら `none`）と標準形か（`OT`/`notOT`）、項なら `str (sf t)`。
実行: `lake env lean --run Run.lean < in.tsv`（先に `lake build`）。
-/
import Ytosk.Eval
import Ytosk.OT
import Ytosk.BMS
import Ytosk.Eval2

open Ytosk

def parseMat (s : String) : Mat :=
  ((s.splitOn ")").filterMap fun c =>
    match ((c.replace "(" "").splitOn ",").filter (· ≠ "") |>.map String.toNat! with
    | [x, y, w] => some (x, y, w)
    | [x, y] => some (x, y, 0)
    | [x] => some (x, 0, 0)
    | _ => none)

/-- Parse `[]` or `[a,b,c]`; returns the term and the rest. -/
partial def parseT : List Char → Option (T × List Char)
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
    if m.startsWith "~" then
      o.putStrLn (r ++ "\t" ++ ((eval2 (parseMat (m.drop 1).toString)).map str).getD "none")
    else if m.startsWith "@" then
      -- `@n:(matrix)`: print the BM4 expansion
      match (m.drop 1).toString.splitOn ":" with
      | [k, mm] =>
        let e := expand (parseMat mm) k.toNat!
        o.putStrLn (r ++ "\t" ++ String.join (e.map fun (a, b, c) =>
          "(" ++ toString a ++ "," ++ toString b ++ "," ++ toString c ++ ")"))
      | _ => pure ()
    else if m.startsWith "=" then
      let t := ((parseT ((m.toList.drop 1).filter (· ≠ ' '))).map Prod.fst).getD .z
      o.putStrLn (r ++ "\t" ++ str (sf t))
    else
      let e := eval (parseMat m)
      o.putStrLn (r ++ "\t" ++ (e.map str).getD "none" ++ "\t" ++
        (match e with | some t => if isOT t then "OT" else "notOT" | none => "-"))
  | _ => pure ()
  loop h o

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
