import Ytosk.V3TopT2B
open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut stack : List Name := [`Ytosk.trio_terminates_main_V2_cur]
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for c in ci.getUsedConstantsAsSet.toList do
        if (`Ytosk).isPrefixOf c && !seen.contains c then stack := c :: stack
  let targets : List Name := [`Ytosk.AbsDN, `Ytosk.AbsDW, `Ytosk.AbsDWAt, `Ytosk.AbsDWs, `Ytosk.TPLoWs,
    `Ytosk.TPLoWAt, `Ytosk.TPLoW, `Ytosk.TPLoN, `Ytosk.Inv3V2.adn, `Ytosk.Inv3V2.adw, `Ytosk.Inv3V2.tplow,
    `Ytosk.Inv3V2.tplon, `Ytosk.TakeFrameV2.adn, `Ytosk.TakeFrameV2.adw, `Ytosk.TakeFrameV2.tplow,
    `Ytosk.TakeFrameV2.tplon, `Ytosk.absDN_at, `Ytosk.t0_absDN, `Ytosk.Inv3V2.adwAt, `Ytosk.Inv3V2.tplowAt,
    `Ytosk.AbsDNAt, `Ytosk.T0AbsDNRes, `Ytosk.QV2]
  for t in targets do
    let mut us : Array Name := #[]
    for n in seen.toList do
      if let some ci := env.find? n then
        if ci.getUsedConstantsAsSet.contains t then us := us.push n
    IO.println s!"{t} live={seen.contains t} users={us.toList}"
  IO.println s!"total {seen.size}"
