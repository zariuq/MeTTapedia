import Mettapedia.Languages.Transducers.LanguageDef
import Mettapedia.GSLT.LanguageDef.Interaction.Presentability
import Mettapedia.GSLT.LanguageDef.InteractionCut
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Moore and Mealy machines admit no interactive presentation

A transducer is an automaton reading a stream, and the only place where its
steps happen is the contact between the control and the stream: the
constructor `Feed`.  As for the Turing machine, that contact is ordered and
binary, and its two operands have different sorts.  The other rules evaluate
the transition and output functions, or say where evaluation may take place;
none of them is headed by a constructor that brings two operands of its own
sort together either.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Transducers

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- The constructor at which the control meets the stream. -/
def feedConstructor : GrammarRule :=
  { label := "Feed", category := "Config",
    params := [.simple "control" (.base "State"), .simple "stream" (.base "Stream")],
    syntaxPattern := [.nonTerminal "control", .nonTerminal "stream"] }

theorem feedConstructor_mem (discipline : Discipline) :
    feedConstructor ∈ terms discipline := by
  cases discipline <;> decide +kernel

/-- The control and the stream meet in an ordered binary contact at the sort
of configurations. -/
theorem feed_is_ordered_binary_contact :
    coreContactRepresentation? (TypeDecl.plain "Config") feedConstructor =
      some .binary := by
  rfl

/-- That contact is not between operands of one sort. -/
theorem feed_is_not_same_sort_contact (sort : TypeDecl) :
    contactRepresentation? sort feedConstructor = none :=
  contactRepresentation?_binary_eq_none (left := "State") (right := "Stream")
    rfl (by decide)

/-- No constructor of a transducer's signature brings two operands of its own
sort together. -/
theorem no_same_sort_contact (discipline : Discipline) :
    ∀ constructor ∈ terms discipline, ∀ sort : TypeDecl,
      contactRepresentation? sort constructor = none := by
  intro constructor membership sort
  cases discipline <;>
    simp only [terms, outputParameters, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at membership <;>
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact contactRepresentation?_nullary_eq_none rfl
      | exact contactRepresentation?_unary_eq_none rfl
      | exact contactRepresentation?_binary_eq_none rfl (by decide)

/-- **Non-example 8.2.**  Neither transducer admits an interactive
presentation. -/
theorem transducer_not_interactive {discipline : Discipline}
    (machine : Machine discipline) :
    ¬ AdmitsInteractivePresentation (transducer machine) := by
  apply not_admitsInteractivePresentation_of_heads
  intro rewrite membership
  obtain ⟨label, arguments, left, -⟩ := rewrites_headed machine rewrite membership
  refine ⟨label, arguments, left, ?_⟩
  intro constructor constructorMember _ sort
  exact no_same_sort_contact discipline constructor constructorMember sort

/-- The signature alone excludes an interactive presentation, for every
transition and output table. -/
theorem transducer_no_contact {discipline : Discipline} (machine : Machine discipline) :
    ¬ AdmitsInteractivePresentation (transducer machine) :=
  not_admitsInteractivePresentation_of_no_contact fun constructor membership sort =>
    no_same_sort_contact discipline constructor membership sort

/-- The parity machine's presentation is a theory with real steps. -/
theorem parity_semantic_step :
    (langGSLT (transducer parity)).Step parityStart parityMet :=
  langReducesUsing_to_semantic RelationEnv.empty (transducer parity) parity_meets

/-- The change detector's presentation is a theory with real steps. -/
theorem change_semantic_step :
    (langGSLT (transducer change)).Step changeStart changeMet :=
  langReducesUsing_to_semantic RelationEnv.empty (transducer change) change_meets

end Mettapedia.Languages.Transducers
