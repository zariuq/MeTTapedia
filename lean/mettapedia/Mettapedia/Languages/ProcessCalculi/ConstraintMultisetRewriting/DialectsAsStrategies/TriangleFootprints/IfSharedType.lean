import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.IfUncovered

/-!
# Why `if` inside bodies needs more than the entry: the shared `$t` of the raw lookup

The every-run theorems of `IfBranches` to `IfBags` start from HE's entry configuration. Inside an
equation body, `if` is evaluated at the frame the body's unifier reached, and an `if` evaluated after
another one sees the frame the first left. Under HE's historical (raw) type lookup the stored arrow is
returned verbatim, so **every invocation of `if` shares the one type variable `$t`**:

* `raw_return_shared`: every selection of `if` under the raw lookup, at every frame, live list and
  scope, selects a signature whose return type is `.var "t"` itself.

The branch an `if` takes is cast against `$t`. A branch of type `Number` records `t := Number` in the
answer's frame. A later `if` whose branch is a Boolean then meets that binding:

* `fresh_frame_accepts_bool` (positive): at a frame that does not bind `t`, `$t` matches `Bool`.
* `number_frame_rejects_bool` (negative): at a frame binding `t := Number`, no type match of `$t`
  with `Bool` exists, so the cast of the second `if`'s branch is rejected.

So, under the raw lookup, the answer of an `if` inside a body can depend on the frame it is evaluated
at, which the frame-universal statements of `MarkedValues` (`HERunsTo`, `RunsDetermined`, quantified
over every activation) do not allow. The scoped lookup selects arrows fresh for the protected names
(`InvocationSelectionRel.selected_fresh`), which removes the sharing.

## Capture by a renamed equation variable

The fixed name `t` also meets the renaming of equation variables. A renamed rule variable must avoid
only the names visible in the query, the live atoms and the incoming bindings
(`Steps.AlphaVariantRel`); the type variable of a stored arrow is none of these. For the row
`(= (choose $b) (if $b 1 2))` and the query `(choose True)`:

* `capture_allowed`: renaming `$b` to `$t` is an admissible fresh variant, so a frontier of the query
  may bind `t := True`, and the body is then read as `(if True 1 2)` at a frame binding `t`;
* `true_frame_rejects_number`: at a frame binding `t := True`, no type match of `$t` with `Number`
  exists, so on such a run the cast of the taken branch `1` against `if`'s return type `$t` is
  rejected, while on a run that renames `$b` to any other name it succeeds.

So under the raw lookup an `if` inside a body whose branch has a declared type has complete runs that
differ by the choice of fresh names; a branch without declared type meets `$t` by `undefinedRight` on
every frame and is unaffected. HE's own space index renames a stored atom's variables at every query,
so its arrows carry a fresh type variable per invocation, as the scoped lookup does.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace IfSharedType

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (MatchRel MergeRel MergeConstraintsRel
  AddVarBindingRel equalityGroundedSemantic ValuesAgree)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open ServiceFootprints EntryToQuery AnswerBags IfEveryRun IfBranches
open AnswerBags.Controls (sym app)

/-- **Under the raw lookup every selection of `if` returns the same `$t`.** -/
theorem raw_return_shared {atoms : List Atom} (program : IfProgram atoms) {policy : Policy}
    {live : List Atom} {scope : List String} {expression expected : Atom} {before : Frame}
    {signature : SelectedTypePolicy} {frames : List Frame}
    (chosen : Completed.InvocationSelectionRel (Space.ofList atoms) Completed.rawLookup policy live
      scope expression (.symbol "if") expected before (.selected signature frames)) :
    signature.returnType = .var "t" := by
  obtain ⟨candidates, queried, scanned⟩ := chosen
  have same := StorageTypesRel.unique
    (show StorageTypesRel (Space.ofList atoms) (.symbol "if") candidates from queried) program.types
  subst same
  have origin := scanned.selected_origin signature frames rfl
  rw [List.mem_singleton] at origin
  exact (if_projections origin).2

/-- **At a frame that does not bind `t`, `$t` matches `Bool`.** -/
theorem fresh_frame_accepts_bool :
    ∃ out, TypeMatchRel (.var "t") (sym "Bool") Bindings.empty out := by
  refine ⟨Bindings.empty.assign "t" (sym "Bool"), .structural (by simp [Atom.undefinedType])
    (by simp [Atom.atomType]) (by simp [Atom.undefinedType]) (by simp [Atom.atomType])
    (.varNonVar rfl (Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.semanticLoopFree_single_assignment
      (by intro occurs; cases occurs)))
    (.mk (order := [.value "t" (sym "Bool")]) (by decide)
      (.value (.fresh (by decide)) .nil))⟩

/-- The bindings `{t := Number}`. -/
abbrev numberFrame : Bindings := Bindings.empty.assign "t" (sym "Number")

theorem numberFrame_values : numberFrame.classValues "t" = [sym "Number"] := by decide

theorem perm_singleton_cons {first x : Atom} {rest : List Atom} (perm : (first :: rest).Perm [x]) :
    first = x ∧ rest = [] := by
  have same := List.perm_singleton.mp perm
  simp only [List.cons.injEq] at same
  exact same

/-- **At a frame binding `t := Number`, `$t` matches no Boolean.** -/
theorem number_frame_rejects_bool :
    ¬ ∃ out, TypeMatchRel (.var "t") (sym "Bool") numberFrame out := by
  rintro ⟨out, matched⟩
  generalize sameE : Atom.var "t" = E at matched
  generalize sameA : sym "Bool" = A at matched
  cases matched with
  | undefinedLeft => cases sameE
  | atomLeft => cases sameE
  | undefinedRight => simp [Atom.undefinedType] at sameA
  | atomRight => simp [Atom.atomType] at sameA
  | structural _ _ _ _ inner merged =>
      subst sameE sameA
      cases inner with
      | varNonVar _ _ =>
          obtain ⟨perm, folded⟩ := merged
          have constraintsEq : Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.constraints
              (Bindings.empty.assign "t" (sym "Bool")) = [.value "t" (sym "Bool")] := by decide
          rw [constraintsEq] at perm
          obtain rfl := List.perm_singleton.mp perm
          cases folded with
          | value added _ =>
              cases added with
              | fresh hvalues =>
                  rw [numberFrame_values] at hvalues
                  cases hvalues
              | same hvalues _ same =>
                  rw [numberFrame_values] at hvalues
                  obtain ⟨rfl, rfl⟩ := perm_singleton_cons hvalues
                  simp at same
              | conflict hvalues _ _ matching _ =>
                  rw [numberFrame_values] at hvalues
                  obtain ⟨rfl, rfl⟩ := perm_singleton_cons hvalues
                  generalize sameL : sym "Number" = L at matching
                  generalize sameR : sym "Bool" = R at matching
                  cases matching <;> simp_all
              | reconcile hvalues notAgree _ _ =>
                  rw [numberFrame_values] at hvalues
                  obtain ⟨rfl, rfl⟩ := perm_singleton_cons hvalues
                  exact notAgree (by simp [ValuesAgree])

/-! ## Capture -/

/-- `(choose $b)`, `(if $b 1 2)` and their variants with `$t`. -/
abbrev chooseLeft (v : String) : Atom := app "choose" [.var v]
abbrev chooseRight (v : String) : Atom := app "if" [.var v, .grounded (.int 1), .grounded (.int 2)]

/-- **Renaming `$b` to `$t` is an admissible fresh variant** of `(= (choose $b) (if $b 1 2))` for the
query `(choose True)` at the entry (live `%Undefined%`, no incoming bindings). -/
theorem capture_allowed :
    Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.AlphaVariantRel [Atom.undefinedType]
      (app "choose" [.grounded (.bool true)]) Bindings.empty
      (chooseLeft "b") (chooseRight "b") (chooseLeft "t") (chooseRight "t") := by
  have swapped : (Equiv.swap "b" "t") "b" = "t" := Equiv.swap_apply_left _ _
  refine ⟨Equiv.swap "b" "t", (Equiv.swap "b" "t").injective, ?_, ?_, ?_⟩
  · have renamed : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.AlphaRenameAtomRel
        ⇑(Equiv.swap "b" "t") (chooseLeft "b")
        (.expression [.symbol "choose", .var ((Equiv.swap "b" "t") "b")]) :=
      .expression (.cons (.symbol _) (.cons (.variable _) .nil))
    rwa [swapped] at renamed
  · have renamed : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.AlphaRenameAtomRel
        ⇑(Equiv.swap "b" "t") (chooseRight "b")
        (.expression [.symbol "if", .var ((Equiv.swap "b" "t") "b"), .grounded (.int 1),
          .grounded (.int 2)]) :=
      .expression (.cons (.symbol _) (.cons (.variable _) (.cons (.grounded _)
        (.cons (.grounded _) .nil))))
    rwa [swapped] at renamed
  · intro name occurs
    have isB : name = "b" := by
      rcases occurs with inLeft | inRight
      · have member :=
          (Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars _ _).mp inLeft
        simpa [TypeSubst.typeVars, TypeSubst.typeVarsList] using member
      · have member :=
          (Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars _ _).mp inRight
        simpa [TypeSubst.typeVars, TypeSubst.typeVarsList] using member
    subst isB
    rw [swapped]
    rintro (inQuery | ⟨atom, member, inLive⟩ | ⟨value, assigned⟩ | ⟨key, value, assigned, _⟩ |
      ⟨left, right, equal, _⟩)
    · have member :=
        (Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars _ _).mp inQuery
      simp [TypeSubst.typeVars, TypeSubst.typeVarsList] at member
    · rw [List.mem_singleton] at member
      subst member
      cases inLive
    · simp [Bindings.empty] at assigned
    · simp [Bindings.empty] at assigned
    · simp [Bindings.empty] at equal

/-- The bindings `{t := True}`. -/
abbrev trueFrame : Bindings := Bindings.empty.assign "t" (.grounded (.bool true))

theorem trueFrame_values : trueFrame.classValues "t" = [.grounded (.bool true)] := by decide

/-- **At a frame binding `t := True`, `$t` matches no `Number`.** -/
theorem true_frame_rejects_number :
    ¬ ∃ out, TypeMatchRel (.var "t") (sym "Number") trueFrame out := by
  rintro ⟨out, matched⟩
  generalize sameE : Atom.var "t" = E at matched
  generalize sameA : sym "Number" = A at matched
  cases matched with
  | undefinedLeft => cases sameE
  | atomLeft => cases sameE
  | undefinedRight => simp [Atom.undefinedType] at sameA
  | atomRight => simp [Atom.atomType] at sameA
  | structural _ _ _ _ inner merged =>
      subst sameE sameA
      cases inner with
      | varNonVar _ _ =>
          obtain ⟨perm, folded⟩ := merged
          have constraintsEq : Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.constraints
              (Bindings.empty.assign "t" (sym "Number")) = [.value "t" (sym "Number")] := by decide
          rw [constraintsEq] at perm
          obtain rfl := List.perm_singleton.mp perm
          cases folded with
          | value added _ =>
              cases added with
              | fresh hvalues =>
                  rw [trueFrame_values] at hvalues
                  cases hvalues
              | same hvalues _ same =>
                  rw [trueFrame_values] at hvalues
                  obtain ⟨rfl, rfl⟩ := perm_singleton_cons hvalues
                  simp at same
              | conflict hvalues _ _ matching _ =>
                  rw [trueFrame_values] at hvalues
                  obtain ⟨rfl, rfl⟩ := perm_singleton_cons hvalues
                  generalize sameL : Atom.grounded (.bool true) = L at matching
                  generalize sameR : sym "Number" = R at matching
                  cases matching <;> simp_all [equalityGroundedSemantic]
              | reconcile hvalues notAgree _ _ =>
                  rw [trueFrame_values] at hvalues
                  obtain ⟨rfl, rfl⟩ := perm_singleton_cons hvalues
                  exact notAgree (by simp [ValuesAgree])

/-- **Positive control**: at a frame that does not bind `t`, `$t` matches `Number`. -/
theorem fresh_frame_accepts_number :
    ∃ out, TypeMatchRel (.var "t") (sym "Number") Bindings.empty out := by
  refine ⟨Bindings.empty.assign "t" (sym "Number"), .structural (by simp [Atom.undefinedType])
    (by simp [Atom.atomType]) (by simp [Atom.undefinedType]) (by simp [Atom.atomType])
    (.varNonVar rfl (Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.semanticLoopFree_single_assignment
      (by intro occurs; cases occurs)))
    (.mk (order := [.value "t" (sym "Number")]) (by decide)
      (.value (.fresh (by decide)) .nil))⟩

#print axioms raw_return_shared
#print axioms fresh_frame_accepts_bool
#print axioms number_frame_rejects_bool
#print axioms capture_allowed
#print axioms true_frame_rejects_number
#print axioms fresh_frame_accepts_number

end IfSharedType

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
