/-
Axiom and dependency audit of the library `FamiliesH` (Theorem 1.4(a), `Families.Hybrid.thmH`). Expected
result: no sorry roots, no declaration depending on `sorryAx`, and `thmH` with exactly the three standard axioms.
Run (after `lake build`, from the project directory):  lake env lean scripts/AuditH.lean
(or `scripts/audit.sh`, which checks both headlines).

Prints
1. a global scan of every declaration in the `FamiliesH.*` modules: `axiom` declarations (must be none),
   axioms other than `propext`, `Classical.choice`, `Quot.sound`, `sorryAx` (must be none; this includes
   `Lean.ofReduceBool` = `native_decide`), the sorry roots (own body is `sorry`) and the declarations
   depending on `sorryAx` only transitively;
2. the glue and statement checks (must not depend on `sorryAx`);
3. the headline: its hypotheses (must be none), whether its type is literally `thmH_Statement`, and its
   axioms.
-/
import FamiliesH

open Lean Elab Command

namespace FamiliesHAudit

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The glue and the statement checks: proved, must be sorry-free. -/
def glue : List (Name × String) :=
  [(``Families.Hybrid.thmH_of_parts, "glue: components → Theorem 1.4(a)"),
   (``Families.Hybrid.thmHcell_of_parts, "glue: components → one-cell theorem (§9.4)"),
   (``Families.Hybrid.thmH_of_cells, "glue: one-cell theorem + lem:Mbeta → height-dependent target (§9.4)"),
   (``Families.Hybrid.assembly_fixedH, "glue helper: prop:zeroH + prop:secondH at fixed data"),
   (``Families.Hybrid.bandLSH_of_MV, "glue helper: band constant, intervals anywhere"),
   (``Families.Hybrid.betaK_ratio_le, "glue helper: β(a)/β(b) − 1 ≤ (b−a)/2"),
   (``Families.Hybrid.pB_two, "check: pB 2 C = Families.pC C"),
   (``Families.Hybrid.admissibleB_two_iff, "check: admissible class at β = 2"),
   (``Families.Hybrid.kappaT_rpow, "check: κ_T(Q^κ) = κ"),
   (``Families.Hybrid.thmMain_of_thmH, "check: lem:Mbeta + thmH ⇒ Families.thmMain_Statement")]

def showNames (l : List Name) : String :=
  if l.isEmpty then "—" else ", ".intercalate (l.map fun n =>
    (n.replacePrefix `Families.Hybrid .anonymous |>.replacePrefix `Families .anonymous).toString)

def usesSorryDirectly (ci : ConstantInfo) : Bool :=
  match ci with
  | .thmInfo v => v.value.getUsedConstants.contains ``sorryAx
  | .defnInfo v => v.value.getUsedConstants.contains ``sorryAx
  | .opaqueInfo v => v.value.getUsedConstants.contains ``sorryAx
  | _ => false

end FamiliesHAudit

open FamiliesHAudit in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut nDecl := 0
  let mut axiomDecls : Array Name := #[]
  let mut nonstd : Array (Name × Name) := #[]
  let mut roots : Array Name := #[]
  let mut transitive : Array Name := #[]
  for i in [0:mods.size] do
    let m := mods[i]!
    unless (`FamiliesH).isPrefixOf m do continue
    for n in env.header.moduleData[i]!.constNames do
      if n.isInternal then continue
      let some ci := env.find? n | continue
      nDecl := nDecl + 1
      if ci matches .axiomInfo _ then axiomDecls := axiomDecls.push n
      let axs ← collectAxioms n
      for a in axs do
        unless standardAxioms.contains a || a == ``sorryAx do nonstd := nonstd.push (n, a)
      if axs.contains ``sorryAx then
        if usesSorryDirectly ci then roots := roots.push n else transitive := transitive.push n
  IO.println "== 1. Global scan of the FamiliesH.* modules =="
  IO.println s!"declarations scanned (non-internal): {nDecl}"
  IO.println s!"`axiom` declarations: {if axiomDecls.isEmpty then "none" else toString axiomDecls}"
  IO.println s!"axioms other than propext / Classical.choice / Quot.sound / sorryAx: {if nonstd.isEmpty then "none" else toString nonstd}"
  IO.println s!"sorry roots (own body is `sorry`), {roots.size}: {showNames roots.toList}"
  IO.println s!"declarations depending on sorryAx only transitively, {transitive.size}: {showNames transitive.toList}"
  IO.println ""
  IO.println "== 2. Glue and statement checks (must not depend on sorryAx) =="
  for (n, lab) in glue do
    let some _ := env.find? n | IO.println s!"MISSING {n}"
    let axs ← collectAxioms n
    let tag := if axs.contains ``sorryAx then "SORRY" else "ok"
    IO.println s!"glue {showNames [n]}: {tag} [{showNames (axs.toList.filter (· != ``sorryAx))}] — {lab}"
  IO.println ""
  IO.println "== 3. Headline =="
  let some hCi := env.find? ``Families.Hybrid.thmH | IO.println "thmH: MISSING"
  let binderTys : List Name := Id.run do
    let mut t := hCi.type
    let mut acc : List Name := []
    repeat
      match t with
      | .forallE _ ty body _ =>
        acc := acc ++ [ty.getAppFn.constName?.getD `_]
        t := body
      | _ => break
    return acc
  IO.println s!"thmH hypotheses: {if binderTys.isEmpty then "none" else showNames binderTys}"
  let isStmt := hCi.type == .const ``Families.Hybrid.thmH_Statement []
  IO.println s!"thmH type: {if isStmt then "thmH_Statement" else toString hCi.type}"
  let hax ← collectAxioms ``Families.Hybrid.thmH
  IO.println s!"thmH axioms: {showNames hax.toList}"
