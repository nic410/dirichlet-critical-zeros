#!/usr/bin/env bash
# Assemble the arXiv source bundle of the paper and check that it compiles from a clean unpack.
#
# Usage: paper/make-arxiv-bundle.sh [OUT_DIR]        (default OUT_DIR: paper/build/arxiv)
#
# The bundle contains
#   main.tex, macros.tex, lemmas/*.tex (the files main.tex inputs), main.bbl (generated here with bibtex),
#   anc/ (the ancillary files of paper/anc/), anc/lean/ (a copy of the top-level lean/ directory,
#   without .lake/ and other build products), and the licence texts ../LICENSE and ../LICENSE-CC-BY-4.0 as
#   anc/LICENSE and anc/LICENSE-CC-BY-4.0.
# It is written as OUT_DIR/arxiv-source.tar.gz. The tarball is then unpacked into a fresh directory and
# compiled there with pdflatex only (using the shipped main.bbl, as arXiv does); the script fails on any
# LaTeX error or undefined reference.
# Set TEXBIN to a directory containing pdflatex/bibtex to use a specific TeX installation.
set -euo pipefail
PAPER=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
ROOT=$(cd "$PAPER/.." && pwd)
OUT=${1:-$PAPER/build/arxiv}
mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
if [ -n "${TEXBIN:-}" ]; then export PATH="$TEXBIN:$PATH"
elif ! command -v pdflatex >/dev/null && [ -x "$HOME/.TinyTeX/bin/x86_64-linux/pdflatex" ]; then
  export PATH="$HOME/.TinyTeX/bin/x86_64-linux:$PATH"
fi
for t in pdflatex bibtex tar gzip; do command -v "$t" >/dev/null || { echo "ERROR: $t not found" >&2; exit 1; }; done

WORK=$(mktemp -d "${TMPDIR:-/tmp}/arxiv-bundle.XXXXXX")
trap 'rm -rf "$WORK"' EXIT
SRC=$WORK/src; mkdir -p "$SRC"

# 1. TeX sources: main.tex and every file it \input's or \inputlemma's.
cd "$PAPER"
strip_comments() { sed -e 's/\(^\|[^\\]\)%.*$/\1/' "$1"; }
declare -A SEEN=(); QUEUE=(main.tex); SOURCES=()
while [ ${#QUEUE[@]} -gt 0 ]; do
  f=${QUEUE[0]}; QUEUE=("${QUEUE[@]:1}")
  [ -n "${SEEN[$f]:-}" ] && continue; SEEN[$f]=1
  [ -f "$f" ] || { echo "ERROR: $f (input by the paper) not found" >&2; exit 1; }
  SOURCES+=("$f")
  while IFS= read -r r; do
    [ -z "$r" ] && continue; case "$r" in *'#'*) continue ;; esac
    case "$r" in *.tex) ;; *) r=$r.tex ;; esac; QUEUE+=("$r")
  done < <(strip_comments "$f" | grep -oE '\\input\{[^}]+\}' | sed -E 's/^\\input\{(.*)\}$/\1/')
  while IFS= read -r r; do
    [ -z "$r" ] && continue; case "$r" in *'#'*) continue ;; esac
    QUEUE+=("lemmas/$r.tex")
  done < <(strip_comments "$f" | grep -oE '\\inputlemma\{[^}]+\}' | sed -E 's/^\\inputlemma\{(.*)\}$/\1/')
done
for f in "${SOURCES[@]}"; do mkdir -p "$SRC/$(dirname "$f")"; cp -p "$f" "$SRC/$f"; done
echo "sources: ${SOURCES[*]}"

# 2. main.bbl
B=$WORK/bbl; mkdir -p "$B"; cp -a "$SRC/." "$B/"; cp -p refs.bib "$B/"
( cd "$B"
  pdflatex -interaction=nonstopmode -halt-on-error main >/dev/null
  bibtex main >/dev/null
  pdflatex -interaction=nonstopmode -halt-on-error main >/dev/null ) \
  || { echo "ERROR: generating main.bbl failed (see $B/main.log)" >&2; trap - EXIT; exit 1; }
cp -p "$B/main.bbl" "$SRC/main.bbl"
echo "main.bbl: $(grep -c '\\bibitem' "$SRC/main.bbl") entries"

# 3. Ancillary files, and the Lean project as anc/lean.
mkdir -p "$SRC/anc"
(cd anc && find . -type f ! -name '*.pyc' ! -path '*/__pycache__/*' ! -path './lean/*' -print0) |
  while IFS= read -r -d '' a; do mkdir -p "$SRC/anc/$(dirname "$a")"; cp -p "anc/$a" "$SRC/anc/$a"; done
(cd "$ROOT/lean" && find . -path ./.lake -prune -o -type f ! -name '*.olean' ! -name '*.ilean' ! -name '*.pyc' \
    ! -path '*/__pycache__/*' -print0) |
  while IFS= read -r -d '' a; do mkdir -p "$SRC/anc/lean/$(dirname "$a")"; cp -p "$ROOT/lean/$a" "$SRC/anc/lean/$a"; done
for l in LICENSE LICENSE-CC-BY-4.0; do
  [ -f "$ROOT/$l" ] || { echo "ERROR: $ROOT/$l not found" >&2; exit 1; }
  cp -p "$ROOT/$l" "$SRC/anc/$l"
done
if find "$SRC/anc" -type f \( -name '*.tex' -o -name '*.sty' -o -name '*.cls' -o -name '*.bbl' \) | grep -q .; then
  echo "ERROR: anc/ contains TeX files (arXiv does not allow them there)" >&2; exit 1
fi
echo "anc/: $(find "$SRC/anc" -type f | wc -l) files ($(find "$SRC/anc/lean" -type f | wc -l) in anc/lean)"

# 4. Tarball (reproducible ordering and ownership).
TARBALL=$OUT/arxiv-source.tar.gz
(cd "$SRC" && find . -type f | sed 's#^\./##' | LC_ALL=C sort) > "$WORK/filelist"
tar --sort=name --owner=0 --group=0 --numeric-owner -C "$SRC" -cf - -T "$WORK/filelist" | gzip -9n > "$TARBALL"

# 5. Clean unpack and compile with pdflatex only.
V=$WORK/verify; mkdir -p "$V"; tar -xzf "$TARBALL" -C "$V"
( cd "$V"
  for i in 1 2 3 4; do
    pdflatex -interaction=nonstopmode -halt-on-error main >/dev/null
    grep -qE 'Rerun to get|may have changed' main.log || break
  done ) || { echo "ERROR: pdflatex failed on the unpacked bundle" >&2; grep -m3 -A3 '^!' "$V/main.log" >&2 || true; exit 1; }
if grep -qE "LaTeX Warning: (Reference|Citation) .* undefined|There were undefined references" "$V/main.log"; then
  echo "ERROR: undefined references or citations in the unpacked build" >&2; exit 1
fi
PAGES=$(grep -oE 'Output written on main.pdf \([0-9]+ pages' "$V/main.log" | grep -oE '[0-9]+ pages')
echo "bundle : $TARBALL ($(du -h "$TARBALL" | cut -f1), $(wc -l < "$WORK/filelist") files, sha256 $(sha256sum "$TARBALL" | cut -c1-16)...)"
echo "verify : clean unpack compiles with pdflatex (shipped main.bbl): $PAGES, no errors, no undefined references"
