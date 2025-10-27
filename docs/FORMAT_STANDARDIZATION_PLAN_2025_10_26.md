# 📋 Document Format Standardization Plan

**Date**: October 26, 2025  
**Status**: 🔄 In Progress  
**Priority**: High

---

## 🎯 Overview

This document outlines the plan to standardize all markdown documentation across the OTLP Rust project, ensuring consistency in structure, formatting, and presentation.

---

## 📊 Current Status Analysis

### Format Issues Discovered

**docs/ Directory (110 files)**:
- ❌ **Missing TOC**: 37+ files (large files >5KB without table of contents)
- ⚠️  **Missing Metadata**: 15+ files (no version/date information)
- ℹ️  **Inconsistent Numbering**: Mixed use of numbered vs unnumbered sections

**crates/otlp/docs/ (190 files)**:
- ✅ **Good Numbering**: Most files use numbered sections
- ❌ **Mixed TOC Usage**: ~50% have TOC, ~50% don't
- ⚠️  **Inconsistent Metadata**: Varies across files

**analysis/ Directory (131 files)**:
- 📋 To be analyzed

---

## 📏 Standard Format Definition

### 1. Document Structure

All markdown documents MUST follow this structure:

```markdown
# Document Title

**Version**: 1.0  
**Last Updated**: 2025-10-26  
**Status**: 🟢 Active | 🟡 Draft | 🔴 Deprecated

> **Summary**: One-line description of the document

---

## 📋 Table of Contents

- [Document Title](#document-title)
  - [📋 Table of Contents](#-table-of-contents)
  - [Section 1](#section-1)
    - [Subsection 1.1](#subsection-11)
    - [Subsection 1.2](#subsection-12)
  - [Section 2](#section-2)
  - [References](#references)

---

## Section 1

Content...

### Subsection 1.1

Content...

### Subsection 1.2

Content...

## Section 2

Content...

---

## 📚 References

- [Related Doc 1](link1.md)
- [Related Doc 2](link2.md)
- [External Resource](https://example.com)

---

**Maintainer**: Team Name  
**Contact**: [GitHub Issues](link)

*Last reviewed: 2025-10-26*
```

### 2. Metadata Requirements

#### Required Fields (All Documents)
- **Version**: Semantic versioning (e.g., 1.0, 2.1)
- **Last Updated**: ISO date format (YYYY-MM-DD)
- **Status**: Current status indicator

#### Optional Fields
- **Author**: Document author(s)
- **Reviewers**: List of reviewers
- **Related**: Links to related documents

### 3. Table of Contents (TOC) Rules

#### When TOC is REQUIRED
- ✅ All files > 5KB (approximately 200+ lines)
- ✅ All tutorial/guide documents
- ✅ All API reference documents
- ✅ All architecture documents

#### When TOC is OPTIONAL
- ➖ Small files < 5KB
- ➖ Simple README files
- ➖ Index/listing files

#### TOC Format
- Must be placed after metadata, before main content
- Must use `## 📋 Table of Contents` heading
- Must include emoji for visual distinction
- Must use proper nesting (2-space indentation)
- Must use anchor links to sections

### 4. Section Numbering

#### Numbering Strategy

**Option A: Numbered Sections** (Recommended for technical docs)
```markdown
## 1. Introduction
### 1.1 Background
### 1.2 Objectives
## 2. Architecture
### 2.1 Components
### 2.2 Data Flow
```

**Option B: Unnumbered Sections** (For guides and README files)
```markdown
## Introduction
### Background
### Objectives
## Architecture
### Components
### Data Flow
```

#### Selection Criteria
- **Use Numbered**: Technical specifications, API references, formal documentation
- **Use Unnumbered**: Guides, tutorials, README files, marketing content

### 5. Heading Hierarchy

```markdown
# H1 - Document Title (Only ONE per document)

## H2 - Major Sections

### H3 - Subsections

#### H4 - Detail Sections

##### H5 - Minimal use, avoid if possible
```

**Rules**:
- Never skip levels (e.g., H2 → H4)
- Maximum depth: H4 (H5 sparingly)
- Use consistent emoji prefixes for special sections:
  - 📋 Table of Contents
  - 🎯 Objectives/Goals
  - 📊 Data/Statistics
  - 🏗️ Architecture
  - 🚀 Quick Start
  - 💡 Tips/Notes
  - ⚠️ Warnings
  - 📚 References

### 6. Code Block Standards

```markdown
\`\`\`rust
// Always specify language
fn example() {
    println!("Hello");
}
\`\`\`

\`\`\`bash
# Use bash for shell commands
cargo build
\`\`\`

\`\`\`text
# Use text for output
Output here
\`\`\`
```

### 7. Link Format

```markdown
<!-- Internal links (relative) -->
[Related Document](../other/doc.md)
[Section Link](#section-name)

<!-- External links (absolute) -->
[Rust Official](https://www.rust-lang.org/)
<https://opentelemetry.io/>
```

### 8. List Format

```markdown
<!-- Unordered lists: use hyphen -->
- Item 1
- Item 2
  - Nested item
  - Nested item
- Item 3

<!-- Ordered lists: use numbers -->
1. First step
2. Second step
3. Third step

<!-- Task lists -->
- [ ] TODO item
- [x] Completed item
```

---

## 🔄 Implementation Plan

### Phase 1: Standard Definition ✅
- [x] Define format standards
- [x] Create this document
- [x] Get team approval

### Phase 2: Tool Development
- [ ] Create format validator script
- [ ] Create auto-formatter tool
- [ ] Create TOC generator

### Phase 3: High-Priority Fixes
- [ ] Add TOC to all large files (>5KB)
- [ ] Add metadata to all documentation
- [ ] Fix heading hierarchy issues

### Phase 4: Comprehensive Update
- [ ] Update docs/ directory (110 files)
- [ ] Update crates/*/docs/ directories (659 files)
- [ ] Update analysis/ directory (131 files)

### Phase 5: Validation & Review
- [ ] Run format validator on all files
- [ ] Manual review of critical documents
- [ ] Team review and approval

### Phase 6: Documentation & Training
- [ ] Update CONTRIBUTING.md
- [ ] Create format examples
- [ ] Add CI/CD format checks

---

## 📝 Priority Files for Immediate Fix

### High Priority (Frequently accessed)

**docs/ Directory**:
1. `00_INDEX/README.md` - Main navigation document
2. `00_INDEX/STANDARDS.md` - Documentation standards
3. `00_INDEX/MAIN_INDEX.md` - Complete index
4. `02_THEORETICAL_FRAMEWORK/README.md` - Theory overview
5. `03_API_REFERENCE/*.md` - All API docs
6. `09_CRATES/README.md` - Crate documentation overview
7. `12_GUIDES/*.md` - User guides

**crates/otlp/docs/**:
1. `README.md` - Main entry point
2. `USER_GUIDE.md` - User documentation
3. `API_REFERENCE.md` - API documentation
4. All files in `02_核心概念/` directory
5. All files in `04_架构设计/` directory

### Medium Priority
- All files in docs/10_DEVELOPMENT/
- All files in docs/11_EXAMPLES/
- All files in docs/14_TECHNICAL/

### Low Priority
- Historical documents in archives/
- Deprecated documentation
- Internal notes

---

## 🛠️ Tools and Automation

### Format Validator
```bash
# Check format compliance
./scripts/doc_maintenance/format_checker.sh <directory>
```

### TOC Generator
```bash
# Auto-generate TOC for a file
./scripts/doc_maintenance/generate_toc.sh <file>
```

### Metadata Adder
```bash
# Add metadata to files
./scripts/doc_maintenance/add_metadata.sh <file>
```

---

## 📊 Success Metrics

### Target Metrics
- ✅ 100% of large files (>5KB) have TOC
- ✅ 100% of documents have metadata
- ✅ 95%+ format compliance rate
- ✅ Consistent numbering strategy across similar document types
- ✅ All links validated and working

### Current vs Target

| Metric | Current | Target | Gap |
|--------|---------|--------|-----|
| Files with TOC | ~40% | 100% (large files) | 60% |
| Files with Metadata | ~30% | 100% | 70% |
| Format Compliance | ~50% | 95% | 45% |
| Consistent Numbering | ~60% | 90% | 30% |

---

## 📋 Action Items

### Immediate Actions (Today)
1. ✅ Create standardization plan document
2. [ ] Get team approval on standards
3. [ ] Create TOC generator tool
4. [ ] Fix top 10 priority files

### Short-term (This Week)
1. [ ] Fix all files in docs/00_INDEX/
2. [ ] Fix all files in docs/03_API_REFERENCE/
3. [ ] Fix all README files
4. [ ] Update STANDARDS.md with new format

### Medium-term (Next Week)
1. [ ] Systematic fix of docs/ directory
2. [ ] Systematic fix of crates/otlp/docs/
3. [ ] Create CI/CD format checker
4. [ ] Update contributor guidelines

---

## 🎯 Success Criteria

This standardization effort will be considered successful when:

1. **Consistency**: All documents follow the same structure and format
2. **Completeness**: All documents have required metadata and TOC where appropriate
3. **Quality**: Documents are easy to navigate and understand
4. **Maintainability**: New contributors can easily follow the format standards
5. **Automation**: Format checks are integrated into CI/CD pipeline

---

## 📚 References

- [Documentation Standards](00_INDEX/STANDARDS.md)
- [Review Process](00_INDEX/REVIEW_PROCESS.md)
- [Maintenance Guide](00_INDEX/MAINTENANCE_GUIDE.md)
- [Markdown Style Guide](https://www.markdownguide.org/)

---

**Plan Status**: 🔄 In Progress  
**Expected Completion**: 2025-10-27  
**Owner**: Documentation Team  

*This is a living document and will be updated as the standardization progresses.*

