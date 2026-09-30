/-
Axiom and dependency audit of the library `Families` (Theorem 1.1, `Families.thmMain`).
Run (after `lake build`):  lake env lean scripts/Audit.lean     (or `scripts/audit.sh`, which checks the output)

Prints
1. a global scan of every declaration in the `Families.*` modules: `axiom` declarations (must be none),
   uses of `Lean.ofReduceBool` / `Lean.trustCompiler` (`native_decide`; must be none), any axiom other
   than `propext`, `Classical.choice`, `Quot.sound`, `sorryAx` (must be none), the `sorry` roots
   (declarations whose own body is `sorry`; must be none) and the declarations that depend on `sorryAx`
   only transitively (must be none);
2. a table for every (a) target on the headline chain, the glue and the headline: `sorry` (direct /
   transitive / none), the axioms, the named (b) hypotheses and the (a) statements occurring in its type;
   2b. the results that are stated but not proved (`X_Statement : Prop`, with no theorem `X`);
3. the (b) definitions (must not depend on `sorryAx`);
4. the headline's hypotheses: the types of the binders of `thmMain` (**must be none**: the headline is
   unconditional), whether `thmMain`'s type is literally `thmMain_Statement`, and the fields of the bundles
   `ClassicalInputs`, `ClassicalInputsReduced`, `PortedReductions`, `PortedReductionsReduced` (used only by the
   conditional variants of the headline).
-/
import Families
-- Also import the FamiliesH root, so that the global scan below sees every `Families.*` module that is built,
-- including one reachable only through `FamiliesH`. The scan filters by the module prefix `Families`, which does
-- not match `FamiliesH.*` (those modules are scanned by scripts/AuditH.lean).
import FamiliesH

open Lean Elab Command

namespace FamiliesAudit

/-- The classical named hypotheses ((b1)–(b5), `Families/Classical.lean`) and their bundle. -/
def bClassical : List Name :=
  [``Families.MV_LargeSieve, ``Families.Montgomery69_Density, ``Families.PNT_dlVP,
   ``Families.StirlingDigamma, ``Families.lemWH_Statement, ``Families.ClassicalInputs,
   ``Families.ClassicalInputsReduced]

/-- The ported reductions ((b6)–(b7), the paper's own §4/§5; `Families/Classical/Reductions.lean`) and
their bundle. -/
def bPorted : List Name :=
  [``Families.ZeroSideReduction, ``Families.SecondMomentAssembly, ``Families.PortedReductions, ``Families.PortedReductionsReduced]

/-- All named hypotheses ((b)). -/
def bNames : List Name := bClassical ++ bPorted

/-- (a) targets on the headline chain, with the TeX label. -/
def aChain : List (Name × String) :=
  [(``Families.lemOmega_ac, "lem:Omega (a),(c)"),
   (``Families.lemOmega_d, "lem:Omega (d)"),
   (``Families.lemOmega_e, "lem:Omega (e)"),
   (``Families.lemfS, "lem:fS"),
   (``Families.lemDual, "lem:dual"),
   (``Families.propCount, "prop:count"),
   (``Families.lemC, "lem:C"),
   (``Families.propSharpLS, "prop:sharpLS"),
   (``Families.lemCTlimit, "lem:CTlimit"),
   (``Families.lemB1, "lem:B1"),
   (``Families.eqBMrat, "eqB:Mrat"),
   (``Families.lemB2, "lem:B2"),
   (``Families.propTIsharp, "prop:TIsharp"),
   (``Families.assemblyLimit, "§7.3 limit (lem:windows + DCT)")]

/-- Results of the paper that are stated in Lean (as `Prop` definitions `X_Statement`) but not proved in this
project. There is no theorem for them; the audit checks that the definition exists and that no constant `X`
(the former `sorry` placeholder) is declared. -/
def statedOnly : List (Name × String) :=
  [(``Families.thmConditional_Statement, "thm:conditional"),
   (``Families.thmGauss_Statement, "thm:gauss (Theorem 1.2)"),
   (``Families.thmFixed_Statement, "thm:fixed (Theorem 1.3)"),
   (``Families.lemA_Statement, "lem:A"),
   (``Families.lemHarm_Statement, "lem:harm"),
   (``Families.lemRwlog_Statement, "lem:Rwlog"),
   (``Families.lemRwlog_numeric_Statement, "lem:Rwlog (numeric)"),
   (``Families.lemWH_ratio_Statement, "lem:WH (ratio)"),
   (``Families.propTI_Statement, "prop:TI"),
   (``Families.propCTfixed_Statement, "prop:CTfixed")]

/-- The glue and the headline. -/
def headline : List (Name × String) :=
  [(``Families.thmMain_of_parts, "glue: (a) statements + MV + Stirling + lem:WH + zero-side conclusion + §5 assembly → thm:main"),
   (``Families.thmMain_of_components, "glue (bundled form): (a) statements + ClassicalInputs + PortedReductions → thm:main"),
   (``Families.thmMain_of_montgomery, "conditional variant: ClassicalInputsReduced (full Montgomery69_Density) → thm:main"),
   (``Families.thmMain, "HEADLINE: thm:main, unconditional (no hypotheses)"),
   (``Families.Ported.Zero.propZero_unconditional, "zero side, unconditional: prop:zero ∧ lem:RvM (lower)"),
   (``Families.Hyp.Montgomery.Montgomery69_Density_upTo_proof, "Montgomery 1969, q-aspect range T' ≤ Q^A"),
   (``Families.assembly_fixed, "glue helper: prop:zero + prop:second at fixed data"),
   (``Families.CTp_ge_one, "glue helper: C_T^+ ≥ 1"),
   (``Families.bandLS_of_MV, "glue helper: band constant from eq:MVLS"),
   (``Families.bandProfile_spec, "glue helper: the smooth profile C̃_ε")]

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The `_Statement` of an (a) target (`X` ↦ `X_Statement`). -/
def stmtOf (n : Name) : Name := n.appendAfter "_Statement"

def aStatements : List Name :=
  (aChain.map (stmtOf ·.1)) ++ (statedOnly.map (·.1))

def showNames (l : List Name) : String :=
  if l.isEmpty then "—" else ", ".intercalate (l.map fun n => n.replacePrefix `Families .anonymous |>.toString)

/-- Whether the declaration's own body mentions `sorryAx` (`ConstantInfo.value?` returns `none` for
theorems in this Lean version, so match on the constructors). -/
def usesSorryDirectly (ci : ConstantInfo) : Bool :=
  match ci with
  | .thmInfo v => v.value.getUsedConstants.contains ``sorryAx
  | .defnInfo v => v.value.getUsedConstants.contains ``sorryAx
  | .opaqueInfo v => v.value.getUsedConstants.contains ``sorryAx
  | _ => false

end FamiliesAudit

open FamiliesAudit in
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
    unless (`Families).isPrefixOf m do continue
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
  IO.println "== 1. Global scan of the Families.* modules =="
  IO.println s!"declarations scanned (non-internal): {nDecl}"
  IO.println s!"`axiom` declarations: {if axiomDecls.isEmpty then "none" else toString axiomDecls}"
  IO.println s!"axioms other than propext / Classical.choice / Quot.sound / sorryAx (incl. Lean.ofReduceBool = native_decide, Lean.trustCompiler): {if nonstd.isEmpty then "none" else toString nonstd}"
  IO.println s!"sorry roots (own body is `sorry`), {roots.size}: {showNames roots.toList}"
  IO.println s!"declarations depending on sorryAx only transitively, {transitive.size}: {showNames transitive.toList}"
  IO.println ""
  let row (n : Name) (label cls : String) : CommandElabM Unit := do
    let some ci := env.find? n | IO.println s!"| {n} | MISSING | | | | |"
    let axs ← collectAxioms n
    let sorryStr := if usesSorryDirectly ci then "sorry" else if axs.contains ``sorryAx then "via (a)" else "none"
    let tyConsts := ci.type.getUsedConstants.toList
    let bs := bNames.filter tyConsts.contains
    let as := aStatements.filter tyConsts.contains
    let axStr := showNames (axs.toList.filter (· != ``sorryAx))
    IO.println s!"| {n.replacePrefix `Families .anonymous} | {label} | {cls} | {sorryStr} | {axStr} | {showNames bs} | {showNames as} |"
  IO.println "== 2. Targets =="
  IO.println "| declaration | TeX / role | class | sorry | standard axioms | (b) hypotheses in type | (a) statements in type |"
  IO.println "|---|---|---|---|---|---|---|"
  for (n, tex) in aChain do row n tex "(a)"
  for (n, lab) in headline do row n lab "glue"
  IO.println ""
  IO.println "== 2b. Stated only (Prop definition), not proved =="
  IO.println "| definition | TeX | status | depends on sorryAx | proof constant |"
  IO.println "|---|---|---|---|---|"
  for (n, tex) in statedOnly do
    let base := n.getString!
    let proofName := Name.mkStr n.getPrefix (String.ofList (base.toList.take (base.length - "_Statement".length)))
    match env.find? n with
    | none => IO.println s!"| {n.replacePrefix `Families .anonymous} | {tex} | MISSING | | |"
    | some _ =>
      let axs ← collectAxioms n
      let prf := if (env.find? proofName).isSome then s!"PRESENT: {proofName}" else "none"
      IO.println s!"| {n.replacePrefix `Families .anonymous} | {tex} | stated only (Prop definition), not proved | {if axs.contains ``sorryAx then "SORRY" else "no"} | {prf} |"
  IO.println ""
  IO.println "== 3. Named hypotheses (b): definitions, must not depend on sorryAx =="
  for n in bNames do
    let axs ← collectAxioms n
    let cls := if bClassical.contains n then "classical" else "ported reduction (paper §4/§5)"
    IO.println s!"{n.replacePrefix `Families .anonymous} [{cls}]: axioms {showNames axs.toList}"
  IO.println ""
  IO.println "== 4. Headline hypotheses (must be none) and the bundles of the conditional variants =="
  let some mainCi := env.find? ``Families.thmMain | IO.println "thmMain: MISSING"
  let binderTys : List Name := Id.run do
    let mut t := mainCi.type
    let mut acc : List Name := []
    repeat
      match t with
      | .forallE _ ty body _ =>
        acc := acc ++ [ty.getAppFn.constName?.getD `_]
        t := body
      | _ => break
    return acc
  IO.println s!"thmMain hypotheses: {if binderTys.isEmpty then "none" else showNames binderTys}"
  let isStmt := mainCi.type == .const ``Families.thmMain_Statement []
  IO.println s!"thmMain type: {if isStmt then "thmMain_Statement" else toString mainCi.type}"
  for bundle in [``Families.ClassicalInputs, ``Families.ClassicalInputsReduced, ``Families.PortedReductions,
      ``Families.PortedReductionsReduced] do
    let fields := (getStructureFields env bundle).toList
    let fieldTys : List Name := fields.filterMap fun f =>
      (env.find? (bundle ++ f)).bind fun ci => Id.run do
        -- the projection has type `∀ (self : bundle), T`; report `T`'s head constant
        match ci.type with
        | .forallE _ _ body _ => return body.getAppFn.constName?
        | _ => return none
    IO.println s!"{bundle.replacePrefix `Families .anonymous} fields: {showNames fieldTys}"
