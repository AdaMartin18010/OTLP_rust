#!/bin/bash
# Document Format Scanner
# Analyzes markdown documents for format inconsistencies

TARGET_DIR="${1:-.}"

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📋 Document Format Scanner"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "🔍 Scanning: $TARGET_DIR"
echo ""

# Counters
total=0
large=0
with_toc=0
without_toc=0
with_numbering=0
without_numbering=0
with_metadata=0
without_metadata=0

# Find markdown files
find "$TARGET_DIR" -name "*.md" -type f -size +1k | while read file; do
    # Skip certain files
    filename=$(basename "$file")
    if [[ "$filename" == "CHANGELOG.md" ]] || [[ "$filename" == "LICENSE.md" ]]; then
        continue
    fi
    
    # Get file size in KB
    size=$(du -k "$file" | cut -f1)
    
    # Read content
    content=$(cat "$file")
    
    # Check for TOC
    has_toc=0
    if echo "$content" | grep -q -E "##\s*(Table of Contents|目录|📋)"; then
        has_toc=1
    fi
    
    # Check for numbering
    has_numbering=0
    if echo "$content" | grep -q -E "###?\s+[0-9]+\."; then
        has_numbering=1
    fi
    
    # Check for metadata
    has_metadata=0
    if echo "$content" | grep -q -E "\*\*版本\*\*:|>\s*\*\*版本\*\*:|Version:|最后更新"; then
        has_metadata=1
    fi
    
    # Report issues for large files
    if [ $size -gt 5 ]; then
        if [ $has_toc -eq 0 ]; then
            echo "  ❌ Missing TOC: $file ($size KB)"
        fi
        if [ $has_metadata -eq 0 ]; then
            echo "  ⚠️  Missing metadata: $file ($size KB)"
        fi
    fi
done

echo ""
echo "✅ Scan complete!"
echo ""

