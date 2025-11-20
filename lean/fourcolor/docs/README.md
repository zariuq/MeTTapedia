# Documentation Organization

This directory contains organized documentation for the Four Color Theorem formalization project.

## Directory Structure

### `/sessions` (30 files)
Session-by-session progress logs and implementation notes.
- `SESSION_2025-11-*.md` - Daily session summaries
- `PROGRESS_2025-11-*.md` - Progress reports

**Latest**: `SESSION_2025-11-12_GUARDRAILS.md` - Canonical Kempe theorem implementation

### `/planning` (7 files)
Project planning, checklists, and status documents.
- `EXECUTION_PLAN.md` - Overall project plan
- `CHECKLIST.md` - Task checklist
- `AXIOMS.md` - Axiom usage documentation
- `INDUCTIVE_PROOF_STATUS.md` - Inductive proof progress
- `GPT5_BRIEFING.md` - High-level project briefing

### `/technical` (35 files)
Technical analyses, proof strategies, and deep dives.
- `KEMPE_SWAP_STRATEGY.md` - Kempe swap implementation strategy
- `TAIT_FORMALIZATION_ANALYSIS.md` - Tait formulation analysis
- `F2_PROOF_*.md` - F2 field proof documentation
- `AXIOM_*.md` - Axiom analysis documents
- `DECIDABILITY_*.md` - Decidability investigation
- Various dated technical reports

## Key Documents

### For Understanding the Project
1. **`/planning/GPT5_BRIEFING.md`** - High-level overview
2. **`/sessions/SESSION_2025-11-12_GUARDRAILS.md`** - Latest major work
3. **`/technical/KEMPE_SWAP_STRATEGY.md`** - Core algorithm strategy

### For Understanding Progress
1. **`/planning/INDUCTIVE_PROOF_STATUS.md`** - Current proof status
2. **`/sessions/SESSION_2025-11-11_KEMPE_IMPLEMENTATION.md`** - Kempe implementation
3. **`/planning/CHECKLIST.md`** - Task completion status

### For Understanding Technical Details
1. **`/technical/TAIT_FORMALIZATION_ANALYSIS.md`** - Tait formulation
2. **`/technical/F2_PROOF_COMPLETE_2025-11-10.md`** - F2 field proofs
3. **`/technical/DECIDABILITY_ROADBLOCK_2025-11-09.md`** - Decidability issues

## Root Documentation

- **`../README.md`** - Project README
- **`../how-to-lean.md`** - Lean language guide for this project

## Chronological Reading Order

For someone new to the project, read in this order:

1. `../README.md` - Project overview
2. `/planning/GPT5_BRIEFING.md` - High-level architecture
3. `/planning/EXECUTION_PLAN.md` - Implementation plan
4. `/technical/TAIT_FORMALIZATION_ANALYSIS.md` - Core formulation
5. `/sessions/SESSION_2025-11-12_GUARDRAILS.md` - Latest progress

## Status as of 2025-11-12

**Proof Progress**: ~90% complete
**Remaining Sorries**: 2 (tractable)
**Key Achievement**: Canonical Kempe theorem implemented
**Next Step**: Refactor main proof to use canonical iff

See `/sessions/SESSION_2025-11-12_GUARDRAILS.md` for details.
