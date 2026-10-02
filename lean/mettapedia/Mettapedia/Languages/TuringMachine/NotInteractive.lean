import Mettapedia.Languages.TuringMachine.LanguageDef
import Mettapedia.GSLT.LanguageDef.Interaction.Presentability
import Mettapedia.GSLT.LanguageDef.InteractionCut
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# The naive Turing machine admits no interactive presentation

The only place where a Turing machine's steps happen is the contact between
the finite control and the tape, and in the naive presentation that contact
is the constructor `Run`.  It is an ordered binary contact, and it heads every
rewrite.  What it is not is a contact between two things of one sort: its
operands are a state and a tape, and its result is a configuration.  No
constructor of the presentation brings two operands of its own sort together
at the head of a rule, so no interactive presentation exists.

The presentation is nevertheless a theory with real steps: the machine of
`appendOne` runs, and halts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- The constructor at which the control meets the tape. -/
def runConstructor : GrammarRule :=
  { label := "Run", category := "Config",
    params := [.simple "control" (.base "State"), .simple "tape" (.base "Tape")],
    syntaxPattern := [.nonTerminal "control", .nonTerminal "tape"] }

theorem runConstructor_mem (machine : Machine) :
    runConstructor ∈ (turingMachine machine).terms := by
  show runConstructor ∈ terms
  decide +kernel

/-- `Run` is the only declared constructor with that label. -/
theorem eq_runConstructor_of_label (machine : Machine) {constructor : GrammarRule}
    (membership : constructor ∈ (turingMachine machine).terms)
    (label : constructor.label = "Run") : constructor = runConstructor := by
  change constructor ∈ terms at membership
  simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | exact absurd label (by decide)

/-- The control and the tape meet in an ordered binary contact at the sort of
configurations. -/
theorem run_is_ordered_binary_contact :
    coreContactRepresentation? (TypeDecl.plain "Config") runConstructor =
      some .binary := by
  rfl

/-- That contact is not between operands of one sort: at no sort is `Run` a
same-sort contact. -/
theorem run_is_not_same_sort_contact (sort : TypeDecl) :
    contactRepresentation? sort runConstructor = none :=
  contactRepresentation?_binary_eq_none (left := "State") (right := "Tape")
    rfl (by decide)

/-- **Non-example 8.1.**  The naive presentation of a Turing machine admits
no interactive presentation: every rewrite is headed by `Run`, whose operands
have different sorts. -/
theorem turingMachine_not_interactive (machine : Machine) :
    ¬ AdmitsInteractivePresentation (turingMachine machine) := by
  apply not_admitsInteractivePresentation_of_heads
  intro rewrite membership
  obtain ⟨control, tape, left⟩ := rewrites_headed_by_run machine rewrite membership
  refine ⟨"Run", [control, tape], left, ?_⟩
  intro constructor constructorMember label sort
  rw [eq_runConstructor_of_label machine constructorMember label]
  exact run_is_not_same_sort_contact sort

/-- The same obstruction without reference to validation: no declared
constructor is a same-sort contact heading a rewrite. -/
theorem turingMachine_no_same_sort_head (machine : Machine)
    (sort : TypeDecl) (constructor : GrammarRule)
    (constructorMember : constructor ∈ (turingMachine machine).terms)
    (rewrite : RewriteRule) (rewriteMember : rewrite ∈ (turingMachine machine).rewrites)
    (representation : ContactRepresentation)
    (represents : contactRepresentation? sort constructor = some representation) :
    ¬ InteractionHeaded representation constructor rewrite.left := by
  obtain ⟨control, tape, left⟩ := rewrites_headed_by_run machine rewrite rewriteMember
  rw [left]
  cases representation with
  | binary =>
      intro headed
      have same : constructor = runConstructor :=
        eq_runConstructor_of_label machine constructorMember headed.symm
      rw [same, run_is_not_same_sort_contact] at represents
      cases represents
  | collection collectionType =>
      intro headed
      exact headed

/-- No constructor of the signature brings two operands of its own sort
together.  The obstruction does not depend on which rule is selected, nor on
whether the contact is required at the head of the rule or merely inside it. -/
theorem no_same_sort_contact :
    ∀ constructor ∈ terms, ∀ sort : TypeDecl,
      contactRepresentation? sort constructor = none := by
  intro constructor membership sort
  simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact contactRepresentation?_nullary_eq_none rfl
      | exact contactRepresentation?_unary_eq_none rfl
      | exact contactRepresentation?_binary_eq_none rfl (by decide)
      | exact contactRepresentation?_eq_none_of_three_le (by decide)

/-- The signature alone excludes an interactive presentation, for every
transition table. -/
theorem turingMachine_no_contact (machine : Machine) :
    ¬ AdmitsInteractivePresentation (turingMachine machine) :=
  not_admitsInteractivePresentation_of_no_contact fun constructor membership sort =>
    no_same_sort_contact constructor membership sort

/-- The presentation of `appendOne` is a theory with real steps: its first
configuration reduces in the generated GSLT. -/
theorem appendOne_semantic_step :
    (langGSLT (turingMachine appendOne)).Step appendOneStart appendOneSecond :=
  langReducesUsing_to_semantic RelationEnv.empty (turingMachine appendOne)
    appendOne_first_step

end Mettapedia.Languages.TuringMachine
