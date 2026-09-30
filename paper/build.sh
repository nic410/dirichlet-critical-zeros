#!/usr/bin/env bash
# Build paper/main.pdf from the sources in this directory.
#
# Usage: paper/build.sh            (from anywhere)
#
# Uses latexmk if it is available, otherwise pdflatex, bibtex, pdflatex, pdflatex.
# Auxiliary files go to paper/build/; the result is copied to paper/main.pdf.
# Set TEXBIN to a directory containing pdflatex/bibtex to use a specific TeX installation.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
if [ -n "${TEXBIN:-}" ]; then export PATH="$TEXBIN:$PATH"
elif ! command -v pdflatex >/dev/null && [ -x "$HOME/.TinyTeX/bin/x86_64-linux/pdflatex" ]; then
  export PATH="$HOME/.TinyTeX/bin/x86_64-linux:$PATH"
fi
command -v pdflatex >/dev/null || { echo "ERROR: pdflatex not found (set TEXBIN)" >&2; exit 1; }
OUT=build
mkdir -p "$OUT"
if command -v latexmk >/dev/null; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir="$OUT" main.tex
else
  command -v bibtex >/dev/null || { echo "ERROR: bibtex not found" >&2; exit 1; }
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$OUT" main.tex
  (cd "$OUT" && BIBINPUTS="..:${BIBINPUTS:-}" BSTINPUTS="..:${BSTINPUTS:-}" bibtex main)
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$OUT" main.tex
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$OUT" main.tex
fi
cp "$OUT/main.pdf" main.pdf
echo "built $(pwd)/main.pdf"
if grep -qE "LaTeX Warning: (Reference|Citation) .* undefined|There were undefined references" "$OUT/main.log"; then
  echo "WARNING: undefined references or citations (see $OUT/main.log)" >&2
fi
