import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ScopedApplication

/-!
# Substitution of contextual pattern interfaces

Ambient substitution acts on literal indices and on occurrence arguments.
Bodies assigned to schematic variables remain in their declared parameter
contexts. The existing sorted ABT substitution supplies binder lifting.
The main law proves that instantiating a substituted contextual pattern is
substituting its instance, for every permitted ambient substitution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns

open Mettapedia.GSLT.LanguageDef
open SignatureIndexedABT
open SignatureIndexedABT.SingleSort
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

variable {Head V : Type}

/-- The already defined sorted lifting, specialized through the carrier isomorphism. -/
def underBinders (depth : Nat) (σ : Nat → Term Head) (index : Nat) : Term Head :=
  SingleSort.decode (SortedSignatureIndexedABT.Term.liftSubstitution (List.replicate depth ())
    (fun _ : Unit => fun i => SingleSort.encode (σ i)) () index)

def substituteFields (σ : Nat → Term Head) (fields : Fields Head) : Fields Head :=
  SingleSort.decodeFields (SortedSignatureIndexedABT.Term.Fields.parallelSubstitute
    (fun _ : Unit => fun i => SingleSort.encode (σ i)) (SingleSort.encodeFields fields))

theorem substitute_node (σ : Nat → Term Head) (head : Head) (fields : Fields Head) :
    Term.substituteMany σ (.node head fields) = .node head (substituteFields σ fields) := rfl

theorem substitute_fields_nil (σ : Nat → Term Head) :
    substituteFields σ .nil = .nil := rfl

theorem substitute_fields_cons (σ : Nat → Term Head) (depth : Nat)
    (body : Term Head) (rest : Fields Head) :
    substituteFields σ (.cons depth body rest) =
      .cons depth (Term.substituteMany (underBinders depth σ) body) (substituteFields σ rest) := by
  have liftEq : (fun _ : Unit => fun i => SingleSort.encode (underBinders depth σ i)) =
      SortedSignatureIndexedABT.Term.liftSubstitution (List.replicate depth ())
        (fun _ : Unit => fun i => SingleSort.encode (σ i)) := by
    funext sort i
    cases sort
    exact SingleSort.encode_decode _
  simp only [substituteFields, SingleSort.encodeFields, SortedSignatureIndexedABT.Term.Fields.parallelSubstitute,
    SingleSort.decodeFields, Term.substituteMany, liftEq, List.length_replicate]

theorem lift_zero_eq_renameMany {Head : Type} (shift : Nat) (t : Term Head) :
    Term.lift 0 shift t = Term.renameMany (fun i => shift + i) t := by
  rw [lift_eq_rename, ← ScopedApplication.renameMany_selection]
  congr 1
  funext i
  simp [Thin.keepN, Thin.sel_dropN]

theorem underBinders_eq {Head : Type} (depth : Nat) (assignment : Nat → Term Head) (i : Nat) :
    underBinders depth assignment i =
      if i < depth then .idx i else Term.lift 0 depth (assignment (i - depth)) := by
  unfold underBinders SortedSignatureIndexedABT.Term.liftSubstitution
  simp only [SortedSignatureIndexedABT.Term.binderCount, List.count_replicate, beq_self_eq_true,
    ite_true]
  split
  · rfl
  · rw [lift_zero_eq_renameMany]
    have shifts : SortedSignatureIndexedABT.Term.weakenRenaming (List.replicate depth ()) =
        (fun _ : Unit => fun i => depth + i) := by
      funext sort index
      cases sort
      simp [SortedSignatureIndexedABT.Term.weakenRenaming,
        SortedSignatureIndexedABT.Term.binderCount]
    rw [shifts]
    rfl

@[simp] theorem underBinders_zero {Head : Type} (assignment : Nat → Term Head) :
    underBinders 0 assignment = assignment := by
  funext i
  rw [underBinders_eq]
  simp only [Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  rw [lift_zero_eq_renameMany]
  have unchanged : (fun i : Nat => 0 + i) = id := funext Nat.zero_add
  rw [unchanged]
  exact Term.renameMany_id (assignment i)

mutual
/-- Embed a literal existing term in the existing pattern syntax. -/
def literal : Term Head → TreePat Head V
  | .idx i => .idx i
  | .node head fields => .node head (literalFields fields)

def literalFields : Fields Head → TreePatFields Head V
  | .nil => .nil
  | .cons depth body rest => .cons depth (literal body) (literalFields rest)
end

mutual
theorem literal_inst (σ : Subst V (Term Head)) (body : Term Head) :
    (literal body).inst σ = some body := by
  cases body with
  | idx i => rfl
  | node head fields => simp [literal, TreePat.inst, literalFields_inst σ fields]

theorem literalFields_inst (σ : Subst V (Term Head)) (fields : Fields Head) :
    (literalFields fields).inst σ = some fields := by
  cases fields with
  | nil => rfl
  | cons depth body rest =>
    simp [literalFields, TreePatFields.inst, literal_inst σ body, literalFields_inst σ rest]
end

mutual
def substitutePattern (σ : Nat → Term Head) :
    TreePat Head (Occurrence Head V) → TreePat Head (Occurrence Head V)
  | .mvar occurrence => .mvar { occurrence with arguments := occurrence.arguments.map (Term.substituteMany σ) }
  | .idx i => literal (σ i)
  | .node head fields => .node head (substitutePatternFields σ fields)

def substitutePatternFields (σ : Nat → Term Head) :
    TreePatFields Head (Occurrence Head V) → TreePatFields Head (Occurrence Head V)
  | .nil => .nil
  | .cons depth body rest =>
    .cons depth (substitutePattern (underBinders depth σ) body) (substitutePatternFields σ rest)
end

mutual
theorem instantiate_substitutePattern (assignment : Subst V (Term Head))
    (σ : Nat → Term Head) (p : TreePat Head (Occurrence Head V)) :
    (substitutePattern σ p).inst (Pattern.atOccurrence assignment) =
      (p.inst (Pattern.atOccurrence assignment)).map (Term.substituteMany σ) := by
  cases p with
  | mvar occurrence => exact Pattern.occurrence_substitution assignment occurrence σ
  | idx i => simpa [substitutePattern, TreePat.inst] using
      literal_inst (Pattern.atOccurrence assignment) (σ i)
  | node head fields =>
    simp only [substitutePattern, TreePat.inst, instantiate_substitutePatternFields assignment σ fields]
    cases fields.inst (Pattern.atOccurrence assignment) with
    | none => rfl
    | some fs => simp [substitute_node]

theorem instantiate_substitutePatternFields (assignment : Subst V (Term Head))
    (σ : Nat → Term Head) (fields : TreePatFields Head (Occurrence Head V)) :
    (substitutePatternFields σ fields).inst (Pattern.atOccurrence assignment) =
      (fields.inst (Pattern.atOccurrence assignment)).map (substituteFields σ) := by
  cases fields with
  | nil => rfl
  | cons depth body rest =>
    simp only [substitutePatternFields, TreePatFields.inst,
      instantiate_substitutePattern assignment (underBinders depth σ) body,
      instantiate_substitutePatternFields assignment σ rest]
    cases body.inst (Pattern.atOccurrence assignment) <;>
      cases rest.inst (Pattern.atOccurrence assignment) <;>
      simp [substitute_fields_cons]
end

namespace Pattern

def substitute (target : Nat) (σ : Nat → Term Head) (p : Pattern Head V) : Pattern Head V :=
  ⟨target, substitutePattern σ p.tree⟩

/-- General capture-free substitution preserves every accepted contextual instance. -/
theorem inst_substitute {assignment : Subst V (Term Head)} {p : Pattern Head V}
    {body : Term Head} (applied : p.inst assignment = some body)
    {target : Nat} (σ : Nat → Term Head)
    (permitted : ∀ i < p.scope, Term.supportedAt target (σ i) = true) :
    (p.substitute target σ).inst assignment = some (Term.substituteMany σ body) := by
  obtain ⟨raw, scopedBody⟩ := (inst_iff assignment p body).mp applied
  apply (inst_iff assignment (p.substitute target σ) _).mpr
  constructor
  · change (substitutePattern σ p.tree).inst (atOccurrence assignment) = _
    rw [instantiate_substitutePattern, raw]
    rfl
  · exact Term.substituteMany_supported permitted body scopedBody

end Pattern

section Variables

variable [DecidableEq V]

mutual
theorem literal_vars (t : Term Head) : (literal t : TreePat Head V).vars = ∅ := by
  cases t with
  | idx i => rfl
  | node h fs => exact literalFields_vars fs

theorem literalFields_vars (fs : Fields Head) : (literalFields fs : TreePatFields Head V).vars = ∅ := by
  cases fs with
  | nil => rfl
  | cons d t rest => simp [literalFields, TreePatFields.vars, literal_vars t, literalFields_vars rest]
end

variable [DecidableEq Head]

mutual
theorem substitutePattern_names (σ : Nat → Term Head) (p : TreePat Head (Occurrence Head V)) :
    (substitutePattern σ p).vars.image Occurrence.name = p.vars.image Occurrence.name := by
  cases p with
  | mvar o => simp [substitutePattern, TreePat.vars]
  | idx i => simp [substitutePattern, literal_vars, TreePat.vars]
  | node h fs => exact substitutePatternFields_names σ fs

theorem substitutePatternFields_names (σ : Nat → Term Head)
    (fs : TreePatFields Head (Occurrence Head V)) :
    (substitutePatternFields σ fs).vars.image Occurrence.name = fs.vars.image Occurrence.name := by
  cases fs with
  | nil => rfl
  | cons d p rest =>
    simp only [substitutePatternFields, TreePatFields.vars, Finset.image_union,
      substitutePattern_names (underBinders d σ) p, substitutePatternFields_names σ rest]
end

theorem Pattern.substitute_vars (p : Pattern Head V) (target : Nat) (σ : Nat → Term Head) :
    (p.substitute target σ).vars = p.vars := substitutePattern_names σ p.tree

end Variables

namespace SubstitutionControls

def ambient : Pattern Nat Nat := ⟨1, .node 1 (.cons 1 (.mvar ⟨0, 1, [.idx 1]⟩) .nil)⟩

theorem ambient_substitution_avoids_capture :
    ((ambient.substitute 1 (fun _ => .idx 0)).inst Controls.assignment) =
      some (.node 1 (.cons 1 (.idx 1) .nil)) := by decide

theorem compound_substitution_beneath_binder :
    ((ambient.substitute 0 (fun _ => Controls.seven)).inst Controls.assignment) =
      some (.node 1 (.cons 1 Controls.seven .nil)) := by decide

end SubstitutionControls
end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns
