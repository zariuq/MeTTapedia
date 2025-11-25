#!/bin/bash
# Search utility for probability & measure theory in MetaMath and Mizar libraries

# Colors for output
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
METAMATH_DIR="$SCRIPT_DIR/metamath/mmmg"
MIZAR_DIR="$SCRIPT_DIR/mizar/mmlmg"

# Default search term
SEARCH_TERM="${1:-prob}"
MODE="${2:-files}"  # files, content, or both

echo -e "${BLUE}=== Searching for: ${YELLOW}$SEARCH_TERM${BLUE} ===${NC}\n"

# Search MetaMath library
if [ -d "$METAMATH_DIR" ]; then
    echo -e "${GREEN}MetaMath set.mm (40,558 theorems with proofs):${NC}"
    cd "$METAMATH_DIR"

    if [ "$MODE" = "files" ] || [ "$MODE" = "both" ]; then
        echo "Files matching '$SEARCH_TERM':"
        ls -1 | grep -i "$SEARCH_TERM" | head -20
        COUNT=$(ls -1 | grep -i "$SEARCH_TERM" | wc -l)
        echo "Total: $COUNT files"
    fi

    if [ "$MODE" = "content" ] || [ "$MODE" = "both" ]; then
        echo -e "\nFiles containing '$SEARCH_TERM':"
        grep -l -i "$SEARCH_TERM" *.mg 2>/dev/null | head -20
        COUNT=$(grep -l -i "$SEARCH_TERM" *.mg 2>/dev/null | wc -l)
        echo "Total: $COUNT files"
    fi

    echo ""
else
    echo -e "${YELLOW}MetaMath library not found at: $METAMATH_DIR${NC}\n"
fi

# Search Mizar library
if [ -d "$MIZAR_DIR" ]; then
    echo -e "${GREEN}Mizar MML (58,684 definitions, no proofs):${NC}"
    cd "$MIZAR_DIR"

    if [ "$MODE" = "files" ] || [ "$MODE" = "both" ]; then
        echo "Files matching '$SEARCH_TERM':"
        ls -1 | grep -i "$SEARCH_TERM" | head -20
        COUNT=$(ls -1 | grep -i "$SEARCH_TERM" | wc -l)
        echo "Total: $COUNT files"
    fi

    if [ "$MODE" = "content" ] || [ "$MODE" = "both" ]; then
        echo -e "\nFiles containing '$SEARCH_TERM':"
        grep -l -i "$SEARCH_TERM" *.mg 2>/dev/null | head -20
        COUNT=$(grep -l -i "$SEARCH_TERM" *.mg 2>/dev/null | wc -l)
        echo "Total: $COUNT files"
    fi

    echo ""
else
    echo -e "${YELLOW}Mizar library not found at: $MIZAR_DIR${NC}\n"
fi

echo -e "${BLUE}=== Usage ===${NC}"
echo "Search by filename:  ./search_probability.sh <term>"
echo "Search by content:   ./search_probability.sh <term> content"
echo "Search both:         ./search_probability.sh <term> both"
echo ""
echo "Examples:"
echo "  ./search_probability.sh conditional"
echo "  ./search_probability.sh measure content"
echo "  ./search_probability.sh sigma both"
