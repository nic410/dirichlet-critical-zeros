/-
Statement-content pin for the two headlines (`scripts/audit.sh`, section "statement pin").

`Families.thmMain : thmMain_Statement` and `Families.Hybrid.thmH : thmH_Statement` are checked by the audit by
*name*: their types must be literally these constants. This script pins what the names *mean*. Starting
from the roots below, it collects every declaration of the `Families` / `FamiliesH` modules that the
statements unfold to (the transitive closure through the types and bodies of definitions, and the
constructors of structures and inductives; theorems are not followed, since a proof term inside a
definition cannot change its meaning, and declarations of Mathlib / Zeta23 are pinned by
`lake-manifest.json`). For each declaration, sorted by name, it prints its kind, name, universe parameters,
type and body (pretty-printed with the options fixed below; docstrings are not printed) and a structural
hash of the type and body expressions, which also catches differences the pretty-printer hides
(coercions, implicit arguments).

The expected output is `scripts/Statements.baseline.txt`; `scripts/audit.sh` requires an exact match.
Any change to the meaning of either headline (a constant, a quantifier, the family, the weights, the
zero counts, `p(C)`, `p(β; F_C)`, `β(κ)`, `κ_T`, …) changes this output and fails the audit. A
deliberate change must regenerate the baseline:
  lake env lean scripts/Statements.lean > scripts/Statements.baseline.txt
Run (after `lake build`):  lake env lean scripts/Statements.lean
-/
import Families
import FamiliesH

open Lean Elab Command Meta

set_option pp.fullNames true
set_option pp.unicode.fun true
set_option format.width 110
set_option pp.numericTypes true
set_option pp.proofs false
set_option pp.funBinderTypes true
set_option pp.structureInstances true
set_option pp.fieldNotation false

namespace StatementsPin

/-- The roots: both headline statements, and (redundantly, so the list documents them) the definitions
they are built from. -/
def roots : List Name :=
  [``Families.thmMain_Statement, ``Families.ProportionsAtLeast, ``Families.pC,
   ``Families.Hybrid.thmH_Statement, ``Families.Hybrid.ProportionsAtLeastH, ``Families.Hybrid.pB,
   ``Families.Hybrid.certH_Statement, ``Families.Hybrid.betaK, ``Families.Hybrid.kappaT,
   ``Families.Nfam, ``Families.Ns0, ``Families.Nstar0, ``Families.Nd, ``Families.zerosI,
   ``Families.Weight, ``Families.primChars, ``Families.Qf, ``Families.FC, ``Families.AdmissibleWindow,
   ``Families.Hybrid.AdmissibleWindowB, ``Families.wSharpFun, ``Families.wSmoothFun]

/-- Is `n` declared in a module of this project (`Families.*`, `FamiliesH.*`)? -/
def isOurs (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i =>
    let m := env.header.moduleNames[i.toNat]!
    (`Families).isPrefixOf m || (`FamiliesH).isPrefixOf m
  | none => false

/-- The declaration that carries the meaning of `n` (constructors and recursors → their inductive). -/
def owner (env : Environment) (n : Name) : Name :=
  match env.find? n with
  | some (.ctorInfo v) => v.induct
  | some (.recInfo v) => v.all.headD n
  | _ => n

/-- The constants a declaration's meaning depends on (theorems: none). -/
def deps (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.axiomInfo v) => v.type.getUsedConstants
  | some (.inductInfo v) => v.ctors.foldl (init := v.type.getUsedConstants) fun acc c =>
      match env.find? c with
      | some ci => acc ++ ci.type.getUsedConstants
      | none => acc
  | _ => #[]

def closure (env : Environment) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := roots.toArray
  let mut out : Array Name := #[]
  while !todo.isEmpty do
    let n := owner env todo.back!
    todo := todo.pop
    if seen.contains n || !isOurs env n then continue
    seen := seen.insert n
    if let some (.thmInfo _) := env.find? n then continue
    out := out.push n
    todo := todo ++ deps env n
  return out.qsort (·.toString < ·.toString)

def kindOf (env : Environment) : ConstantInfo → String
  | .inductInfo v => if isStructure env v.name then "structure" else "inductive"
  | .defnInfo _ => "def" | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem" | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor" | .quotInfo _ => "quot"

end StatementsPin

open StatementsPin in
run_cmd liftTermElabM do
  let env ← getEnv
  for r in roots do
    unless env.contains r do throwError "root {r} not found"
  let names := closure env
  IO.println s!"== statement pin: {names.size} declarations (closure of {roots.length} roots) =="
  for n in names do
    let some ci := env.find? n | continue
    let us := if ci.levelParams.isEmpty then "" else s!".\{{", ".intercalate (ci.levelParams.map toString)}}"
    IO.println ""
    IO.println s!"{kindOf env ci} {n}{us}"
    IO.println s!"  : {← ppExpr ci.type}"
    let mut h : UInt64 := ci.type.hash
    match ci with
    | .defnInfo v =>
      IO.println s!"  := {← ppExpr v.value}"
      h := mixHash h v.value.hash
    | .opaqueInfo v =>
      IO.println s!"  := {← ppExpr v.value}"
      h := mixHash h v.value.hash
    | .inductInfo v =>
      for c in v.ctors do
        let some cc := env.find? c | continue
        IO.println s!"  | {c} : {← ppExpr cc.type}"
        h := mixHash h cc.type.hash
    | _ => pure ()
    IO.println s!"  hash {h}"
