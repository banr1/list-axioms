import Lean
import Mathlib.Topology.Basic

open Lean Elab Command

/-!
Lists the declarations (axioms/defs/inductives, etc.) that appear in the type
of a given constant, recursively. This approximates “what is needed to state
the concept”. We intentionally do NOT unfold/descend into values/proofs to avoid
pulling in large proof dependencies — we only follow type dependencies and, for
inductives/structures, also the constructor types.

Usage in this script (at the bottom):
  #list_deps TopologicalSpace
Change the identifier to analyze another declaration.
-/

namespace ListConceptDeps

private def collectConsts (e : Expr) (acc : NameSet := {}) : NameSet :=
  match e with
  | .const n _ => acc.insert n
  | .app f a => collectConsts f (collectConsts a acc)
  | .lam _ d b _ => collectConsts b (collectConsts d acc)
  | .forallE _ d b _ => collectConsts b (collectConsts d acc)
  | .letE _ t v b _ =>
    let acc := collectConsts t acc
    let acc := collectConsts v acc
    collectConsts b acc
  | .mdata _ b => collectConsts b acc
  | .proj _ _ b => collectConsts b acc
  | .sort _ => acc
  | .lit _ => acc
  | .fvar _ => acc
  | .bvar _ => acc
  | .mvar _ => acc

structure Deps where
  seen : NameSet := {}
  result : NameSet := {}
  deriving Inhabited

private def addResult (d : Deps) (n : Name) : Deps :=
  { d with result := d.result.insert n }

private partial def go (env : Environment) (target : Name) (d : Deps) : Deps :=
  if d.seen.contains target then d else
  match env.find? target with
  | none => { d with seen := d.seen.insert target } -- unknown (perhaps binder), skip
  | some ci =>
    let d := { d with seen := d.seen.insert target }
    let d := addResult d target
    -- Always follow type dependencies
    let deps0 := collectConsts ci.type {}
    -- For inductives/structures, also follow constructor types
    let deps :=
      match ci with
      | .inductInfo ii =>
        ii.ctors.foldl (init := deps0) fun acc ctorName =>
          match env.find? ctorName with
          | some (.ctorInfo cinfo) => collectConsts cinfo.type acc
          | _ => acc
      | _ => deps0
    -- Recurse
    deps.fold (init := d) (fun d n => go env n d)

private def gatherDeps (env : Environment) (root : Name) : Deps :=
  go env root ({} : Deps)

private def nameOrd (a b : Name) : Bool := a.toString < b.toString

private def ppKind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo ii => if ii.isRec then "inductive" else "structure/inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .defnInfo di => if di.safety == .unsafe then "def (unsafe)" else if di.hints.isAbbrev then "abbrev" else "def"

private def formatList (env : Environment) (ns : Array Name) : Array String :=
  ns.map fun n =>
    match env.find? n with
    | some ci => s!"{n} : {ppKind ci}"
    | none => s!"{n} : (unknown)"

/-! `#list_deps C` prints the declarations used (by type dependencies) to state `C`.
It prints two groups: axioms and non-axioms. -/
syntax (name := listDepsCmd) "#list_deps" ident : command

@[command_elab listDepsCmd]
def elabListDeps : CommandElab := fun stx => do
  let env ← getEnv
  let id := stx[1].getId
  match env.find? id with
  | none =>
    logError m!"unknown constant: {id}"
  | some _ =>
    let d := gatherDeps env id
    -- Convert to array and sort
    let arr := d.result.toList.toArray.qsort nameOrd
    let axioms := arr.filter fun n => match env.find? n with | some ci => ci.isAxiom | _ => false
    let nonAxioms := arr.filter fun n => match env.find? n with | some ci => not ci.isAxiom | _ => true
    logInfo m!"Dependencies for {id} (by type):"
    -- Axioms first
    if axioms.size > 0 then
      for s in formatList env axioms do
        logInfo s
      logInfo m!"(axioms: {axioms.size})"
    else
      logInfo "(axioms: 0)"
    -- Then non-axioms
    for s in formatList env nonAxioms do
      logInfo s
    logInfo m!"(non-axioms: {nonAxioms.size})"
    logInfo m!"(total: {arr.size})"

end ListConceptDeps

open ListConceptDeps

-- Example: list what’s needed to state TopologicalSpace
#list_deps TopologicalSpace
