# Archive Directory

This directory contains old/deprecated files that are kept for historical reference but are no longer part of the active build.

## Files

### Tait_OLD.lean
- **Archived**: 2025-11-09
- **Reason**: Replaced by refactored `FourColor/Tait.lean`
- **Sorry Count**: 7 sorries
- **Status**: No longer maintained, kept for historical reference

The current `Tait.lean` (in `FourColor/`) has been refactored and improved:
- Better structure
- Clearer proofs
- Only 2 sorries (down from 7)

## Adding Files to Archive

When archiving files:
1. Move to this directory: `mv FourColor/OldFile.lean archive/`
2. Update this README with:
   - File name
   - Date archived
   - Reason for archiving
   - Any relevant notes

## Restoring Archived Files

If you need to reference or restore an archived file:
```bash
# View the file
cat archive/Tait_OLD.lean

# Copy back (if needed)
cp archive/Tait_OLD.lean FourColor/
```

---

**Note**: Archived files are not built by `lake build` and may not compile with current dependencies.
