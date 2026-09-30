import SweepCheck

open SweepCheck

/-- Check one proof log and report. -/
def checkOne (u h : Nat) (path : System.FilePath) : IO Bool := do
  let d ← IO.FS.readBinFile path
  let t0 ← IO.monoMsNow
  let ok ← IO.lazyPure (fun _ => checkLog u h d)
  let t1 ← IO.monoMsNow
  let ms := t1 - t0
  IO.println s!"u = {u}, h = {h}: log of {d.size} bytes {if ok then "accepted" else "REJECTED"} ({ms / 1000}.{(ms % 1000) / 100} s)"
  return ok

/-- `sweepcheck DIR` checks the logs `DIR/sweep_U_H.bin` for `U = 2, …, 8` and `H = hval U`, which
is the hypothesis `hlog` of `SweepCheck.upper_bounds`.  `sweepcheck U H FILE` checks one log. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [dir] =>
    let mut all := true
    for u in [2, 3, 4, 5, 6, 7, 8] do
      let ok ← checkOne u (hval u) (System.FilePath.mk dir / s!"sweep_{u}_{hval u}.bin")
      all := all && ok
    if all then
      IO.println "all logs accepted: the hypothesis of SweepCheck.upper_bounds holds"
      return 0
    else
      IO.println "some log was rejected"
      return 1
  | [us, hs, path] =>
    let ok ← checkOne us.toNat! hs.toNat! path
    return (if ok then 0 else 1)
  | _ =>
    IO.println "usage: sweepcheck DIR  or  sweepcheck U H FILE"
    return 2
