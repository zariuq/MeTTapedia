import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.DeclaredHeads
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.EveryRun
import Mettapedia.Languages.MeTTa.HE.HOLContract.Runtime

/-!
# The measured type fragment: ground declaration subjects and no subtype rows

HE's type query unifies the subject of a declaration with the atom it asks about: with `(: $x Foo)`
in the space every atom has the type `Foo`. It also reads subtype rows `(:< A B)`: an atom of type
`A` has the type `B` too, and is accepted where `B` is required. The tree's HE model compares
subjects literally (`Spec.Type.annotationType?`), and its storage types (`Spec.Type.StorageTypesRel`)
read no subtype row. The HE lane has no unifying type query and no subtype relation in its lookups;
its contract module names the subtype rows (`HOLContract.subtypeEdges`, `HOLContract.SubtypeFree`)
and its judgments ignore them.

So on programs whose declarations have ground subjects and which have no subtype row
(`MeasuredTypeFragment`) these two causes of difference are absent:

* `annotation_ignores_variable_subject`: the model's declared types of a ground atom do not see a
  declaration whose subject is a variable;
* `annotation_ignores_subtype_row`: nor a subtype row.

A theorem of this folder whose HE side reads the type lookup can be HE's on this fragment only.
That the model's type answers are HE's there is measured on the programs of the typed theorems,
not proved, and one difference remains inside the fragment: HE gives its grounded operations types
(its type of `+` is `(-> Number Number Number)`) and checks their calls against them, and the model
gives them none. The typed theorems state that their programs lie in it
(`TypedEveryRun.typed_every_run`,
`DeclaredEveryRun.declared_every_run`, `DeclaredErrors.Controls.arity_three`,
`DeclaredErrors.Controls.first_mismatch_only`); the programs of the other theorems have no subtype
row and, where they declare anything, ground subjects.

## Controls: each condition is needed

* `Controls.variable_subject_needed`: on `{(= (f $x) yes), (: $y (-> Number Number))}`, every complete
  run of the model on `(f b)` publishes `yes`, as on the program without the declaration, while HE
  answers `(Error (f b) (BadArgType 1 Number (-> Number Number)))`: the declaration gives `f` and
  `b` the arrow type.
* `DeclaredErrors.Controls.subtype_row_needed`: with `(:< Bool Number)` added to the declared
  program, every complete run of the model on `(f b)` still publishes the `BadArgType` error, while
  HE answers `yes`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace TypeQueryFragment

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (annotationType?)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (load)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (isGroundAtom)
open ServiceFootprints EntryToQuery AnswerBags EveryRun
open AnswerBags.Controls (sym app rule rule_consFree)

/-- A declaration row's subject has no variable; other rows pass. -/
def groundSubject : Atom → Bool
  | .expression [.symbol ":", subject, _] => isGroundAtom subject
  | _ => true

/-- **Every declaration of the program has a ground subject.** -/
def GroundSubjects (atoms : List Atom) : Prop := atoms.all groundSubject = true

instance (atoms : List Atom) : Decidable (GroundSubjects atoms) :=
  inferInstanceAs (Decidable (_ = _))

/-- **The measured type fragment**: declarations with ground subjects, and no subtype row. The two
measured causes that make the model's type query differ from HE's are absent on it. -/
def MeasuredTypeFragment (atoms : List Atom) : Prop :=
  GroundSubjects atoms ∧ Mettapedia.Languages.MeTTa.HE.HOLContract.SubtypeFree (Space.ofList atoms)

/-- **The model's declared types of a ground atom do not see a declaration with a variable
subject**; HE's do, since its query unifies the subject. -/
theorem annotation_ignores_variable_subject {target : Atom} (ground : isGroundAtom target = true)
    (name : String) (type : Atom) :
    annotationType? target (.expression [.symbol ":", .var name, type]) = none := by
  have different : (Atom.var name == target) = false := by
    cases target with
    | var other => simp [isGroundAtom] at ground
    | symbol other => rfl
    | grounded value => rfl
    | expression items => rfl
  simp [annotationType?, different]

/-- **The model's declared types do not see a subtype row**; HE's do. -/
theorem annotation_ignores_subtype_row (target sub super : Atom) :
    annotationType? target (.expression [.symbol ":<", sub, super]) = none := by
  simp [annotationType?]

/-- The declared program of the typed theorems lies in the fragment. -/
theorem fragment_declaredRows : MeasuredTypeFragment DeclaredHeads.declaredRows :=
  ⟨by decide, by unfold Mettapedia.Languages.MeTTa.HE.HOLContract.SubtypeFree; decide⟩

/-- So does the program without the head's declaration. -/
theorem fragment_headUndeclared :
    MeasuredTypeFragment (DeclaredHeads.headUndeclared DeclaredHeads.declaredRows "f") := by
  rw [DeclaredHeads.headUndeclared_declaredRows]
  exact ⟨by decide, by unfold Mettapedia.Languages.MeTTa.HE.HOLContract.SubtypeFree; decide⟩

namespace Controls

open WholeRunWords.Double (noHost)

/-- The undeclared program of `DeclaredHeads.Controls.plainRows`, with a declaration whose subject
is a variable. -/
abbrev variableSubjectRows : List Atom :=
  [rule (app "f" [.var "x"]) (sym "yes"),
   .expression [.symbol ":", .var "y", .expression [.symbol "->", sym "Number", sym "Number"]]]

/-- **Control: ground subjects are needed.** On `{(= (f $x) yes), (: $y (-> Number Number))}`, outside
the fragment, a complete run of the model on `(f b)` exists, and every complete run publishes `yes`:
the model sees no declaration of `f` or `b`. HE gives both the arrow type and answers
`(Error (f b) (BadArgType 1 Number (-> Number Number)))`. -/
theorem variable_subject_needed (policy : Policy) :
    ¬ GroundSubjects variableSubjectRows ∧
      (∃ heAnswers : List Result,
        Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList variableSubjectRows) DeclaredHeads.declaredCall Atom.undefinedType)
          ⟨Space.ofList variableSubjectRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result,
        Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList variableSubjectRows) DeclaredHeads.declaredCall Atom.undefinedType)
          ⟨Space.ofList variableSubjectRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [sym "yes"] := by
  have program : ∀ row ∈ variableSubjectRows, RegionsWithVariables.ConsFreeHeads row := by
    intro row member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact rule_consFree fun a member => by
        simp only [List.mem_singleton] at member
        subst member
        exact .var _
    · intro lhs rhs same
      simp at same
  have ordinary : Ordinary noHost variableSubjectRows "f" [sym "b"] :=
    ⟨.symbol (by decide) (by decide), fun a member => by
      simp only [List.mem_singleton] at member
      subst member
      exact .symbol (by decide) (by decide), by decide +kernel, fun impossible => impossible,
      by decide +kernel, by decide, by decide, by decide +kernel, by decide, by decide⟩
  have bodies : regionBodies variableSubjectRows "f" [sym "b"] = [sym "yes"] := by decide +kernel
  have settles : Settles noHost variableSubjectRows DeclaredHeads.declaredCall := by
    refine .call ordinary (by rw [bodies]; simp) ?_
    rw [bodies]
    intro b member
    rw [List.mem_singleton] at member
    subst member
    exact .data (.symbol (by decide) (by decide)) (by decide)
  have computed : Streaming.values (Streaming.advance (translate variableSubjectRows) 40
      (Streaming.enter { state := store variableSubjectRows } DeclaredHeads.declaredCall)) =
        [sym "yes"] := by
    decide +kernel
  have finished : (Streaming.advance (translate variableSubjectRows) 40
      (Streaming.enter { state := store variableSubjectRows }
        DeclaredHeads.declaredCall)).agenda.length = 0 := by
    decide +kernel
  obtain ⟨⟨heAnswers, path, _⟩, _⟩ := answer_bags_every_run noHost policy program settles
  obtain ⟨N, every⟩ := every_complete_run noHost policy program settles
  refine ⟨by decide, ⟨heAnswers, path⟩, fun emitted run => ?_⟩
  have bag := every (max N 40) (le_max_left _ _) emitted run
  rw [advance_stable (List.eq_nil_of_length_eq_zero finished) (max N 40) (le_max_right _ _),
    computed] at bag
  exact List.perm_singleton.mp (Multiset.coe_eq_coe.mp bag.symm)

end Controls

#print axioms annotation_ignores_variable_subject
#print axioms annotation_ignores_subtype_row
#print axioms fragment_declaredRows
#print axioms fragment_headUndeclared
#print axioms Controls.variable_subject_needed

end TypeQueryFragment

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
