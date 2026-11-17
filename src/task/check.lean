import reuF2F
import Lean

/-!
Kernel-environment and problem-manifest checks for the open-only benchmark.
Run from the checkout's `lean/` directory after `lake build`;
`reuf2f dataset check .` runs it:

`cd lean && lake env lean ../src/task/check.lean`

The targets are the `declaration` fields of `metadata.jsonl`. Only target proofs
may depend on `sorryAx`. Check every imported repository declaration's type and
every supporting declaration's value, including generated instances and helpers,
then check the manifest against the root's modules and their declarations. This
inspects declaration identity only; it does not execute submitted proofs, and it
complements, not replaces, source review.
-/

open Lean Elab Command

private partial def targetIsSorry (value : Expr) : Bool :=
  match value.consumeMData with
  | .lam _ _ body _ => targetIsSorry body
  | body => body.isNonSyntheticSorry

/-- The item modules `reuF2F.lean` imports, in import order. -/
private def rootModules : IO (Array Name) := do
  let text ← IO.FS.readFile "reuF2F.lean"
  let mut modules := #[]
  for line in text.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.startsWith "import reuF2F." then
      modules := modules.push (line.drop 7).toString.trimAscii.toString.toName
  return modules

/-- `metadata.jsonl` holds one JSON object per line. -/
private def manifestEntries : CommandElabM (Array Json) := do
  let raw ← liftIO <| IO.FS.readFile "metadata.jsonl"
  let mut entries : Array Json := #[]
  for line in raw.splitOn "\n" do
    let line := line.trimAscii.toString
    unless line.isEmpty do
      let .ok entry := Json.parse line
        | throwError "Invalid problem manifest JSON line: {line}"
      entries := entries.push entry
  return entries

run_cmd do
  let env ← getEnv
  let mut expected : NameSet := {}
  for mod in ← liftIO rootModules do
    expected := expected.insert mod
  let mut targetNames : NameSet := {}
  for entry in ← manifestEntries do
    let .ok declarationText := entry.getObjValAs? String "declaration"
      | throwError "Problem entry has no declaration"
    targetNames := targetNames.insert declarationText.toName
  let mut seenModules : NameSet := {}
  let mut targetCount : Nat := 0
  let mut supportingCount : Nat := 0
  for name in targetNames do
    unless env.contains name do
      throwError "Unknown benchmark target: {name}"
    let some idx := env.getModuleIdxFor? name
      | throwError "Unowned benchmark target: {name}"
    let mod := env.header.moduleNames[idx.toNat]!
    unless expected.contains mod do
      throwError "Target is outside root-imported item modules: {name} ({mod})"
    if seenModules.contains mod then
      throwError "More than one target in item module: {mod}"
    seenModules := seenModules.insert mod
    targetCount := targetCount + 1
  for mod in expected do
    unless seenModules.contains mod do
      throwError "Missing open target in root-imported item: {mod}"
  -- Imported repository axioms are forbidden even if not used by a target.
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      if info matches .axiomInfo _ then
        if (← liftIO <| (System.FilePath.mk (mod.toString.replace "." "/" ++ ".lean")).pathExists) then
          throwError "Repository-local axiom: {name} in {mod}"
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      if mod == `reuF2F || mod.toString.startsWith "reuF2F." then
        let deps := info.type.getUsedConstants ++
          ((info.value? true).map Expr.getUsedConstants).getD #[]
        for dep in deps do
          if let some depIdx := env.getModuleIdxFor? dep then
            let depMod := env.header.moduleNames[depIdx.toNat]!
            if depMod.toString.startsWith "reuF2F." && depMod != mod then
              throwError "Cross-item dependency: {name} ({mod}) uses {dep} ({depMod})"
        if info.type.getUsedConstants.contains ``sorryAx then
          throwError "Sorry directly in repository declaration type: {name}"
        if targetNames.contains name then
          unless info matches .thmInfo _ do
            throwError "Target is not a theorem: {name}"
          unless (info.value? true).any targetIsSorry do
            throwError "Target body is not an intentional sorry: {name}"
          -- A target's type may not depend on any admitted declaration.
          for dep in info.type.getUsedConstants do
            if (← collectAxioms dep).contains ``sorryAx then
              throwError "Target statement {name} depends on admitted declaration {dep}"
        else
          supportingCount := supportingCount + 1
          if (← collectAxioms name).contains ``sorryAx then
            throwError "Supporting declaration depends on sorryAx: {name}"
          if info matches .axiomInfo _ then
            throwError "Repository-specific axiom: {name}"
  logInfo m!"Open-only environment check: {targetCount} open targets; {supportingCount} supporting declarations checked."

run_cmd do
  let env ← getEnv
  let mut expected : NameSet := {}
  for mod in ← liftIO rootModules do
    expected := expected.insert mod
  let entries ← manifestEntries
  let mut seenModules : NameSet := {}
  let mut seenDeclarations : NameSet := {}
  for entry in entries do
    let .ok moduleText := entry.getObjValAs? String "module"
      | throwError "Problem entry has no module"
    let .ok declarationText := entry.getObjValAs? String "declaration"
      | throwError "Problem entry has no declaration"
    let mod := moduleText.toName
    let name := declarationText.toName
    unless expected.contains mod do
      throwError "Problem target is not in the final open inventory: {name}"
    if seenModules.contains mod || seenDeclarations.contains name then
      throwError "Duplicate problem module or declaration: {name}"
    let some info := env.find? name
      | throwError "Unknown problem declaration: {name}"
    unless info matches .thmInfo _ do
      throwError "Problem target is not a theorem: {name}"
    let some idx := env.getModuleIdxFor? name
      | throwError "Problem target has no owning module: {name}"
    unless env.header.moduleNames[idx.toNat]! == mod do
      throwError "Problem module does not own declaration: {name}"
    seenModules := seenModules.insert mod
    seenDeclarations := seenDeclarations.insert name
  for mod in expected do
    unless seenModules.contains mod do
      throwError "Final item missing from problem manifest: {mod}"
  logInfo m!"Problem manifest check: {entries.size} final open targets verified."
