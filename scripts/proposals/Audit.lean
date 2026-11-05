import Lean

open Lean

/-- Inspect expressions directly; do not trust a candidate's printed audit or cached axiom list. -/
partial def dependencies (env : Environment) (todo : List Name)
    (seen : NameHashSet := {}) (axioms : Array Name := #[]) : IO (Array Name) := do
  match todo with
  | [] => return axioms
  | name :: rest =>
    if seen.contains name then return ← dependencies env rest seen axioms
    let some ci := env.checked.get.find? name | throw <| IO.userError s!"Missing declaration {name}"
    let used := ci.type.getUsedConstants.toList ++
      ((ci.value? true).map (·.getUsedConstants.toList) |>.getD []) ++
      (match ci with | .inductInfo info => info.ctors | _ => [])
    dependencies env (used ++ rest) (seen.insert name)
      (if ci.isAxiom then axioms.push name else axioms)

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let witness := args == ["witness"]
  -- Loading no environment extensions prevents candidate initializers from running in this audit.
  withImportModules #[{module := if witness then `HodgeWitness else `HodgeTarget}] {} fun trusted => do
    withImportModules #[{module := `HodgeChecked}] {} fun env => do
      -- A submission must not replace any declaration from the protected environment.
      for (name, ci) in trusted.constants.toList do
        let some actual := env.find? name | throw <| IO.userError s!"Missing protected declaration {name}"
        unless ci.type == actual.type && ci.value? true == actual.value? true &&
            ci.levelParams == actual.levelParams && ci.isAxiom == actual.isAxiom do
          throw <| IO.userError s!"Changed protected declaration {name}"
      let some (.thmInfo result) := env.find? `HodgeSubmission.checked
        | throw <| IO.userError "Missing final theorem"
      let expected := mkApp3 (mkConst `HodgeComputer.HasCertificate)
        (mkConst `HodgeSubmission.F) (mkConst `HodgeSubmission.A) (mkConst `HodgeSubmission.q)
      unless result.levelParams.isEmpty && result.type == expected do
        throw <| IO.userError "Final theorem does not have the protected existential statement"
      if witness then
        let some (.thmInfo checkedWitness) := env.find? `HodgeSubmission.checkedWitness
          | throw <| IO.userError "Missing witness theorem"
        let witnessType := mkAppN (mkConst `HodgeComputer.Verify) #[
          mkConst `HodgeSubmission.F, mkConst `HodgeSubmission.A, mkConst `HodgeSubmission.q,
          mkConst `HodgeWitness.d, mkConst `HodgeWitness.D, mkConst `HodgeWitness.N, mkConst `HodgeWitness.Q]
        unless checkedWitness.levelParams.isEmpty && checkedWitness.type == witnessType do
          throw <| IO.userError "Witness theorem does not bind the submitted polynomial data"
      let axes ← dependencies env ([`HodgeSubmission.checked] ++ if witness then [`HodgeSubmission.checkedWitness] else [])
      let allowed := [`propext, `Classical.choice, `Quot.sound]
      for ax in axes do
        unless allowed.contains ax do throw <| IO.userError s!"Unapproved axiom: {ax}"
      IO.println <| Json.compress <| Json.mkObj [
        ("theorem", toJson "HodgeSubmission.checked"),
        ("witnessChecked", toJson witness),
        ("axioms", toJson (axes.map Name.toString))]
      return 0
