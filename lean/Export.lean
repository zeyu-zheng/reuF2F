import Lean

open Lean Elab Command

namespace Export

/-- Export each target's universe parameters, named `u0, u1, ...`, so the task can
    state its refutation as `¬ type_of% @target.{u0, ...}`. -/
elab "#reuf2f_export_types " manifestPath:str " to " outputPath:str : command => do
  let text ← liftIO <| IO.FS.readFile manifestPath.getString
  let .ok manifest := Json.parse text | throwError "Invalid task manifest"
  let .ok entries := manifest.getArr? | throwError "Task manifest must be an array"
  let mut results : Array Json := #[]
  for entry in entries do
    let .ok name := entry.getObjValAs? String "declaration"
      | throwError "Task has no declaration"
    let info ← getConstInfo name.toName
    unless info.isTheorem do throwError "Not a theorem: {name}"
    let levels := info.levelParams.zipIdx.map fun (_, i) => s!"u{i}"
    results := results.push <| Json.mkObj
      [("declaration", toJson name), ("universes", toJson levels)]
  liftIO <| IO.FS.writeFile outputPath.getString (Json.arr results).pretty

end Export
