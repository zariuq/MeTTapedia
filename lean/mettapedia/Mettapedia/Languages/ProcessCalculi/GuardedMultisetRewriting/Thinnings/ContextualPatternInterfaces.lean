import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns

/-!
# Changing contextual occurrence interfaces on an existing pattern

Only metavariable occurrence metadata is mapped. Constructor heads, object
indices, field binders and the pattern's ambient scope remain in the original
tree. Instantiation commutes with this operation whenever the supplied bodies
reconstruct the same value at each actual occurrence.

No restriction is imposed on forward argument spines, and no second pattern
interpreter or binding-tree representation is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatternInterfaces

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

variable {Head V W : Type}

mutual
def mapTree (mapping : ContextualPatterns.Occurrence Head V → ContextualPatterns.Occurrence Head W) :
    TreePat Head (ContextualPatterns.Occurrence Head V) → TreePat Head (ContextualPatterns.Occurrence Head W)
  | .mvar occurrence => .mvar (mapping occurrence)
  | .idx index => .idx index
  | .node head fields => .node head (mapFields mapping fields)

def mapFields (mapping : ContextualPatterns.Occurrence Head V → ContextualPatterns.Occurrence Head W) :
    TreePatFields Head (ContextualPatterns.Occurrence Head V) → TreePatFields Head (ContextualPatterns.Occurrence Head W)
  | .nil => .nil
  | .cons depth pattern rest => .cons depth (mapTree mapping pattern) (mapFields mapping rest)
end

mutual
theorem mapTree_vars [DecidableEq Head] [DecidableEq V] [DecidableEq W]
    (mapping : ContextualPatterns.Occurrence Head V → ContextualPatterns.Occurrence Head W)
    (pattern : TreePat Head (ContextualPatterns.Occurrence Head V)) :
    (mapTree mapping pattern).vars = pattern.vars.image mapping := by
  cases pattern with
  | mvar occurrence => simp [mapTree, TreePat.vars]
  | idx index => simp [mapTree, TreePat.vars]
  | node head fields => exact mapFields_vars mapping fields

theorem mapFields_vars [DecidableEq Head] [DecidableEq V] [DecidableEq W]
    (mapping : ContextualPatterns.Occurrence Head V → ContextualPatterns.Occurrence Head W)
    (fields : TreePatFields Head (ContextualPatterns.Occurrence Head V)) :
    (mapFields mapping fields).vars = fields.vars.image mapping := by
  cases fields with
  | nil => simp [mapFields, TreePatFields.vars]
  | cons depth pattern rest =>
      simp only [mapFields, TreePatFields.vars, mapTree_vars mapping pattern,
        mapFields_vars mapping rest, Finset.image_union]
end

mutual
theorem mapTree_inst (mapping : ContextualPatterns.Occurrence Head V → ContextualPatterns.Occurrence Head W)
    (assignment : Subst (ContextualPatterns.Occurrence Head W) (Term Head))
    (pattern : TreePat Head (ContextualPatterns.Occurrence Head V)) :
    (mapTree mapping pattern).inst assignment = pattern.inst (fun occurrence => assignment (mapping occurrence)) := by
  cases pattern with
  | mvar occurrence => rfl
  | idx index => rfl
  | node head fields =>
      exact congrArg (Option.map (Term.node head)) (mapFields_inst mapping assignment fields)

theorem mapFields_inst (mapping : ContextualPatterns.Occurrence Head V → ContextualPatterns.Occurrence Head W)
    (assignment : Subst (ContextualPatterns.Occurrence Head W) (Term Head))
    (fields : TreePatFields Head (ContextualPatterns.Occurrence Head V)) :
    (mapFields mapping fields).inst assignment = fields.inst (fun occurrence => assignment (mapping occurrence)) := by
  cases fields with
  | nil => rfl
  | cons depth pattern rest =>
      simp only [mapFields, TreePatFields.inst, mapTree_inst mapping assignment pattern,
        mapFields_inst mapping assignment rest]
end

def reinterface (mapping : ContextualPatterns.Occurrence Head V → ContextualPatterns.Occurrence Head W)
    (pattern : ContextualPatterns.Pattern Head V) : ContextualPatterns.Pattern Head W :=
  ⟨pattern.scope, mapTree mapping pattern.tree⟩

theorem reinterface_inst [DecidableEq Head] [DecidableEq V]
    (mapping : ContextualPatterns.Occurrence Head V → ContextualPatterns.Occurrence Head W)
    (pattern : ContextualPatterns.Pattern Head V) (oldAssignment : Subst V (Term Head))
    (newAssignment : Subst W (Term Head))
    (same : ∀ occurrence ∈ pattern.tree.vars,
      ContextualPatterns.Pattern.atOccurrence newAssignment (mapping occurrence) =
        ContextualPatterns.Pattern.atOccurrence oldAssignment occurrence) :
    (reinterface mapping pattern).inst newAssignment = pattern.inst oldAssignment := by
  unfold ContextualPatterns.Pattern.inst
  change ((mapTree mapping pattern.tree).inst (ContextualPatterns.Pattern.atOccurrence newAssignment)).bind _ = _
  rw [mapTree_inst, TreePat.inst_local _ (ContextualPatterns.Pattern.atOccurrence oldAssignment) pattern.tree same]
  rfl

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatternInterfaces
