#!/bin/bash
# Build a searchable declaration index for MeTTapedia
# Output: DECLARATIONS.tsv (tab-separated: file, line, kind, name)
# Usage: ./scripts/build_index.sh

set -uo pipefail
cd "$(dirname "$0")/.."

INDEX="DECLARATIONS.tsv"

echo "Building declaration index..."
echo -e "file\tline\tkind\tname" > "$INDEX"

find Mettapedia -name "*.lean" -not -path "*/.lake/*" | sort | while read f; do
  grep -n "^theorem \|^lemma \|^def \|^noncomputable def \|^protected def \|^structure \|^class \|^inductive \|^abbrev " "$f" 2>/dev/null | while IFS=: read lineno rest; do
    kind=$(echo "$rest" | awk '{print $1}')
    name=$(echo "$rest" | awk '{print $2}')
    # Strip trailing markers
    name=${name%% *}
    name=${name%%:*}
    name=${name%%(}
    echo -e "$f\t$lineno\t$kind\t$name"
  done
done >> "$INDEX"

total=$(wc -l < "$INDEX")
echo "Done: $((total - 1)) declarations indexed → $INDEX"
echo ""
echo "Search examples:"
echo "  grep -i bisimul DECLARATIONS.tsv"
echo "  grep -i weakness DECLARATIONS.tsv"
echo "  grep 'structure' DECLARATIONS.tsv | grep -i quantale"
echo "  awk -F'\t' '\$3==\"theorem\"' DECLARATIONS.tsv | wc -l"
