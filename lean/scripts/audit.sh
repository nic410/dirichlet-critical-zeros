#!/usr/bin/env bash
# The audit of both headlines of this project. Run from anywhere after `lake build`:
#   scripts/audit.sh            (CORES=8-15 LEAN_NUM_THREADS=8 scripts/audit.sh to pin to other cores)
# CORES (default 0-3) is a CPU list for `taskset`; the pinning is skipped if `taskset` is not available (e.g. macOS)
# or cannot pin to CORES, and CORES= (empty) disables it. LEAN_NUM_THREADS defaults to 4.
# One command, one final line: `AUDIT PASSED` (or `AUDIT FAILED`).
#
# Library `Families`, paper Theorem 1.1 (`Families.thmMain`):
# (1) no `native_decide` and no `axiom` declarations in the sources (textual; also for FamiliesH);
# (1') no `sorry` / `admit` token anywhere in the Lean sources (comments and string literals stripped; also covers
#     files that no library root imports);
# (2) scripts/Audit.lean: global scan (axioms, sorry roots: none, transitive sorry users: none; Audit.lean imports
#     both roots, so the scan covers every built `Families.*` module), the target table, the ten results that are
#     stated only (each `X_Statement` exists, no constant `X`, no sorryAx), the headline's hypotheses (must be none)
#     and type (`thmMain_Statement`), and the bundle fields;
# (3) regression: every line of scripts/PrintAxioms.baseline.txt is reproduced unchanged, no printed declaration
#     depends on `sorryAx`, and `#print axioms Families.thmMain` is exactly the three standard axioms.
# Library `FamiliesH`, paper Theorem 1.4(a) (`Families.Hybrid.thmH`; STATEMENTS-H.md):
# (4) scripts/AuditH.lean: no axiom declarations, no non-standard axioms, NO sorry roots and no declaration
#     depending on sorryAx, the glue and statement checks (incl. `thmMain_of_thmH`) are sorry-free, thmH has no
#     hypotheses and type `thmH_Statement`, and its axioms are exactly propext, Classical.choice, Quot.sound;
# (5) regression: every line of scripts/PrintAxiomsH.baseline.txt is reproduced unchanged, no printed declaration
#     depends on `sorryAx`, and `#print axioms Families.Hybrid.thmH` is exactly the three standard axioms.
# Both:
# (6) statement pin: the output of scripts/Statements.lean (the printed types and bodies of every project
#     declaration that `thmMain_Statement` and `thmH_Statement` unfold to, with structural hashes) must equal
#     scripts/Statements.baseline.txt exactly. (2) and (4) pin the headlines' types by name; (6) pins what the
#     names mean.
# (7) non-vacuity: scripts/NonVacuity.lean compiles without errors, and each of its theorems (N > 0 eventually,
#     uniformly in T, for both height ranges; the ratio form N^s_0/N >= p - eps of both headlines; the height ranges
#     are eventually nonempty; the weights exist for 0 < eta < 1/2; ...) depends only on propext, Classical.choice,
#     Quot.sound.
# (0) `lake build --no-build Families FamiliesH` succeeds: the checked .olean files are those of the current sources.
# Provenance (printed, not enforced): a sha256 over the project's files (`git ls-files`, or, outside a git
# checkout, every file except `.lake/`).
set -u
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
CORES=${CORES-0-3}
PIN=""
if [ -n "$CORES" ] && command -v taskset >/dev/null 2>&1 && taskset -c "$CORES" true >/dev/null 2>&1; then
  PIN="taskset -c $CORES"
fi
RUN="env LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4} $PIN lake env lean"
fail=0

echo "== provenance (printed, not enforced) =="
if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  files=$(git ls-files --cached --others --exclude-standard . | LC_ALL=C sort -u); src="git ls-files, tracked and untracked-unignored"
else
  files=$(find . -path ./.lake -prune -o -type f -print | sed 's|^\./||' | LC_ALL=C sort); src="all files except .lake/"
fi
nfiles=$(echo "$files" | sed '/^$/d' | wc -l)
digest=$(echo "$files" | sed '/^$/d' | while IFS= read -r f; do [ -f "$f" ] && sha256sum -- "$f"; done | sha256sum | cut -d' ' -f1)
echo "sha256 over $nfiles files ($src; sha256sum lines, sorted by path): $digest"
echo

echo "== the build is up to date with the sources =="
# Everything below reads the built .olean files; a source edited after the last `lake build` would not be seen.
if nb_out=$($PIN lake build --no-build Families FamiliesH 2>&1); then
  echo "lake build --no-build Families FamiliesH: $(echo "$nb_out" | tail -1)"
else
  echo "$nb_out" | grep -v '^Note: \|^warning\|^⚠' | tail -5
  echo "FAIL: the build is not up to date (run \`lake build\` first; it must succeed)"; fail=1
fi
echo

echo "== textual checks (Families, FamiliesH) =="
# (occurrences inside backticks are documentation, e.g. "no `native_decide`"; the authoritative
#  check is the `Lean.ofReduceBool` scan in scripts/Audit.lean and scripts/AuditH.lean)
if grep -rnP '(?<![`\w])native_decide(?![`\w])' Families Families.lean FamiliesH FamiliesH.lean --include=*.lean ; then
  echo "FAIL: native_decide found"; fail=1; else echo "native_decide: none"; fi
if grep -rnE '^\s*(private |protected )?axiom\s' Families Families.lean FamiliesH FamiliesH.lean --include=*.lean ; then
  echo "FAIL: axiom declaration found"; fail=1; else echo "axiom declarations: none"; fi
# `sorry` / `admit` as a Lean token anywhere in the sources (comments and string literals are stripped first), also
# in files that no library root imports and that the declaration scans below therefore do not see
sorry_hits=$(find Families FamiliesH scripts -name '*.lean' -print0 | LC_ALL=C sort -z | xargs -0 perl -e '
  for my $f (@ARGV) { open(my $h, "<:encoding(UTF-8)", $f) or die "$f: $!"; local $/; my $s = <$h>; close $h;
    my ($o, $d, $i, $n) = ("", 0, 0, length $s);
    while ($i < $n) { my $c = substr($s, $i, 2);
      if ($c eq "/-") { $d++; $i += 2; next }
      if ($d > 0) { if ($c eq "-/") { $d--; $i += 2 } else { $o .= "\n" if substr($s, $i, 1) eq "\n"; $i++ } next }
      if ($c eq "--") { $i++ while $i < $n && substr($s, $i, 1) ne "\n"; next }
      if (substr($s, $i, 1) eq "\"") { $i++; while ($i < $n && substr($s, $i, 1) ne "\"") { $i += (substr($s, $i, 1) eq "\\") ? 2 : 1 } $i++; next }
      $o .= substr($s, $i, 1); $i++ }
    my $ln = 0; for my $l (split /\n/, $o) { $ln++; print "$f:$ln: $l\n" if $l =~ /(?<![\w.])(sorry|admit)(?![\w])/ } }' Families.lean FamiliesH.lean)
if [ -n "$sorry_hits" ]; then echo "$sorry_hits"; echo "FAIL: sorry/admit in the sources"; fail=1
else echo "sorry/admit (outside comments and strings; Families, FamiliesH, scripts): none"; fi
echo

echo "######## Families: Theorem 1.1 (Families.thmMain) ########"
audit_out=$($RUN scripts/Audit.lean 2>&1)
echo "$audit_out"
echo
echo "$audit_out" | grep -q '^`axiom` declarations: none$' || { echo "FAIL: axiom declarations"; fail=1; }
echo "$audit_out" | grep -q '^axioms other than .*: none$' || { echo "FAIL: non-standard axioms"; fail=1; }
# No sorry anywhere: no declaration of Families.* has `sorry` in its own body, and none depends on sorryAx
if echo "$audit_out" | grep -q '^sorry roots (own body is `sorry`), 0: —$'; then echo "Families sorry roots: none"
else echo "FAIL: Families has sorry roots (expected none): $(echo "$audit_out" | sed -n 's/^sorry roots (own body is `sorry`), //p')"; fail=1; fi
echo "$audit_out" | grep -q '^declarations depending on sorryAx only transitively, 0: —$' \
  || { echo "FAIL: some Families declaration depends on sorryAx (expected none)"; fail=1; }
# The results stated but not proved: each `X_Statement` exists, no constant `X` is declared, none depends on sorryAx
if echo "$audit_out" | grep -q '^| .* | \(MISSING\|.*| SORRY |\|.*| PRESENT: \)'; then
  echo "FAIL: a stated-only result is missing, depends on sorryAx, or has a proof constant again"; fail=1
else
  n_so=$(echo "$audit_out" | grep -c '| stated only (Prop definition), not proved | no | none |')
  if [ "$n_so" -eq 10 ]; then echo "stated-only results: 10 Prop definitions, no proof constants, no sorryAx"
  else echo "FAIL: expected 10 stated-only Prop definitions, found $n_so"; fail=1; fi
fi
# Unconditional headline: thmMain takes no hypotheses and its type is thmMain_Statement
echo "$audit_out" | grep -q '^thmMain hypotheses: none$' \
  || { echo "FAIL: thmMain has hypotheses (expected none: the headline is unconditional)"; fail=1; }
echo "$audit_out" | grep -q '^thmMain type: thmMain_Statement$' \
  || { echo "FAIL: thmMain's type is not literally thmMain_Statement"; fail=1; }
# The bundles below are used only by the conditional variants thmMain_of_components, thmMain_of_montgomery; fields fixed
echo "$audit_out" | grep -q '^ClassicalInputs fields: MV_LargeSieve, Montgomery69_Density, PNT_dlVP, StirlingDigamma, lemWH_Statement$' \
  || { echo "FAIL: ClassicalInputs fields changed"; fail=1; }
# MV large sieve, PNT, Stirling (Families/Hyp) and lem:WH (Families.lemWH) are theorems; this bundle keeps only Montgomery 1969
echo "$audit_out" | grep -q '^ClassicalInputsReduced fields: Montgomery69_Density$' \
  || { echo "FAIL: ClassicalInputsReduced fields changed"; fail=1; }
echo "$audit_out" | grep -q '^PortedReductions fields: ZeroSideReduction, SecondMomentAssembly$' \
  || { echo "FAIL: PortedReductions fields changed"; fail=1; }
# ZeroSideReduction is a theorem (Families/Ported/Zero); this bundle keeps only the §5 assembly
echo "$audit_out" | grep -q '^PortedReductionsReduced fields: SecondMomentAssembly$' \
  || { echo "FAIL: PortedReductionsReduced fields changed"; fail=1; }

echo "== regression against scripts/PrintAxioms.baseline.txt =="
pa_out=$($RUN scripts/PrintAxioms.lean 2>&1)
missing=$(comm -23 <(sort -u scripts/PrintAxioms.baseline.txt) <(echo "$pa_out" | sort -u))
if [ -n "$missing" ]; then echo "FAIL: baseline lines changed or missing:"; echo "$missing"; fail=1
else echo "all $(wc -l < scripts/PrintAxioms.baseline.txt) baseline lines reproduced unchanged"; fi
if echo "$pa_out" | grep -q sorryAx; then echo "FAIL: a printed declaration depends on sorryAx"; fail=1
else echo "PrintAxioms: $(echo "$pa_out" | grep -c 'axioms') declarations, none depends on sorryAx"; fi
# the headline: exactly the three standard axioms
if echo "$pa_out" | grep -qxF "'Families.thmMain' depends on axioms: [propext, Classical.choice, Quot.sound]"
then echo "thmMain axioms: propext, Classical.choice, Quot.sound"
else echo "FAIL: #print axioms Families.thmMain is not exactly [propext, Classical.choice, Quot.sound]"; fail=1; fi
echo

echo "######## FamiliesH: Theorem 1.4(a) (Families.Hybrid.thmH) ########"
auditH_out=$($RUN scripts/AuditH.lean 2>&1)
echo "$auditH_out"
echo
echo "$auditH_out" | grep -q '^`axiom` declarations: none$' || { echo "FAIL: axiom declarations (FamiliesH)"; fail=1; }
echo "$auditH_out" | grep -q '^axioms other than .*: none$' || { echo "FAIL: non-standard axioms (FamiliesH)"; fail=1; }
# No sorry roots: all 15 components are proved (packages V, F, Z, S and TS)
if echo "$auditH_out" | grep -q '^sorry roots (own body is `sorry`), 0: —$'; then
  echo "FamiliesH sorry roots: none (all 15 components proved: packages V, F, Z, S and TS)"
else echo "FAIL: FamiliesH sorry roots remain"; fail=1; fi
# no declaration of FamiliesH depends on sorryAx, not even the headline
echo "$auditH_out" | grep -q '^declarations depending on sorryAx only transitively, 0: —$' \
  || { echo "FAIL: some FamiliesH declaration depends on sorryAx"; fail=1; }
# the glue and the statement checks (among them thmMain_of_thmH) are present and sorry-free
if echo "$auditH_out" | grep -q '^glue .*: SORRY'; then echo "FAIL: a glue theorem depends on sorryAx"; fail=1
else echo "glue and statement checks: sorry-free"; fi
if echo "$auditH_out" | grep -q '^MISSING'; then echo "FAIL: a glue declaration is missing"; fail=1; fi
echo "$auditH_out" | grep -q '^glue thmMain_of_thmH: ok \[propext, Classical.choice, Quot.sound\]' \
  || { echo "FAIL: the check thmMain_of_thmH (lem:Mbeta + thmH ⇒ thmMain_Statement) is missing or not sorry-free"; fail=1; }
echo "$auditH_out" | grep -q '^thmH hypotheses: none$' \
  || { echo "FAIL: thmH has hypotheses (expected none)"; fail=1; }
echo "$auditH_out" | grep -q '^thmH type: thmH_Statement$' \
  || { echo "FAIL: thmH's type is not literally thmH_Statement"; fail=1; }
echo "$auditH_out" | grep -q '^thmH axioms: propext, Classical.choice, Quot.sound$' \
  || { echo "FAIL: thmH axioms are not exactly propext, Classical.choice, Quot.sound"; fail=1; }

echo "== regression against scripts/PrintAxiomsH.baseline.txt =="
paH_out=$($RUN scripts/PrintAxiomsH.lean 2>&1)
missing=$(comm -23 <(sort -u scripts/PrintAxiomsH.baseline.txt) <(echo "$paH_out" | sort -u))
if [ -n "$missing" ]; then echo "FAIL: baseline lines changed or missing:"; echo "$missing"; fail=1
else echo "all $(wc -l < scripts/PrintAxiomsH.baseline.txt) baseline lines reproduced unchanged"; fi
if echo "$paH_out" | grep -q sorryAx; then echo "FAIL: a printed declaration depends on sorryAx"; fail=1
else echo "PrintAxiomsH: $(echo "$paH_out" | grep -c 'axioms') declarations, none depends on sorryAx"; fi
if echo "$paH_out" | grep -qxF "'Families.Hybrid.thmH' depends on axioms: [propext, Classical.choice, Quot.sound]"
then echo "thmH axioms (#print axioms): propext, Classical.choice, Quot.sound"
else echo "FAIL: #print axioms Families.Hybrid.thmH is not exactly [propext, Classical.choice, Quot.sound]"; fail=1; fi
echo

echo "######## statement pin (both headlines) ########"
st_out=$($RUN scripts/Statements.lean 2>&1)
if [ "$st_out" = "$(cat scripts/Statements.baseline.txt)" ]; then
  echo "statement pin: $(echo "$st_out" | head -1 | sed -n 's/^== statement pin: \([0-9]*\) declarations.*/\1/p') declarations, identical to scripts/Statements.baseline.txt"
else
  echo "FAIL: the statements differ from scripts/Statements.baseline.txt (the meaning of a headline changed):"
  diff <(cat scripts/Statements.baseline.txt) <(echo "$st_out") | head -60
  fail=1
fi
echo

echo "######## non-vacuity checks (scripts/NonVacuity.lean) ########"
nv_out=$($RUN scripts/NonVacuity.lean 2>&1); nv_rc=$?
echo "$nv_out"
std_re="'Families\.NonVacuity\.[A-Za-z0-9_]+' (does not depend on any axioms|depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\])"
nv_bad=$(echo "$nv_out" | sed '/^$/d' | grep -vxE "$std_re")
nv_n=$(echo "$nv_out" | grep -cxE "$std_re")
if [ $nv_rc -ne 0 ] || [ -n "$nv_bad" ]; then
  echo "FAIL: scripts/NonVacuity.lean has errors, or a theorem there uses an axiom other than propext, Classical.choice, Quot.sound"; fail=1
elif [ "$nv_n" -ne 17 ]; then echo "FAIL: expected 17 non-vacuity theorems, found $nv_n"; fail=1
else
  for t in weights_exist heights_main_nonempty heights_hybrid_eventually_nonempty Nfam_pos_main Nfam_pos_hybrid \
           thmMain_ratio thmMain_ratio_numeric thmH_ratio; do
    echo "$nv_out" | grep -q "^'Families\.NonVacuity\.$t' " || { echo "FAIL: non-vacuity theorem $t missing"; fail=1; }
  done
  echo "non-vacuity: $nv_n theorems, each with axioms among propext, Classical.choice, Quot.sound"
fi
echo
if [ $fail -eq 0 ]; then
  echo "thmMain, thmH: no hypotheses; axioms propext, Classical.choice, Quot.sound; statements match the pin"
  echo "non-vacuity: N > 0 eventually (uniformly in T), ratio forms, nonempty height ranges, weights exist"
  echo "AUDIT PASSED"
else echo "AUDIT FAILED"; fi
exit $fail
