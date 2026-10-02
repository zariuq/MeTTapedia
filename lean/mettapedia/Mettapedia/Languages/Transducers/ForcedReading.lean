import Mettapedia.Languages.Transducers.NotInteractive
import Mettapedia.GSLT.LanguageDef.Interaction.HeterogeneousCut

/-!
# Moore and Mealy under a forced cut reading

Neither transducer is interactive.  Read nevertheless the rule at which the
control meets the stream as a cut: the program is the control state, the
environment is the stream with its first symbol, and the residual one
observes is the value the machine emits.

* The Moore machine's emitted value does not read the stream.  It is the same
  whatever symbol was consumed: on the data axis, nothing migrates.
* The Mealy machine's emitted value reads the consumed symbol: the datum of
  the environment reaches the residual.

The split is a statement about the emitted value.  The next control state is
a function of the consumed symbol under both disciplines, so the contraction
taken whole reads the stream in the Moore machine too.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Transducers

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- The value the feed rule emits. -/
def emittedValue (discipline : Discipline) : Pattern :=
  outputCall discipline (.fvar "q") (.fvar "a")

/-- The configuration the feed rule continues in. -/
def continuing : Pattern :=
  feed (delta (.fvar "q") (.fvar "a")) (.fvar "rest")

/-- The contractum of the feed rule is the emitted value followed by the
continuing configuration. -/
theorem feedRule_right (discipline : Discipline) :
    (feedRule discipline).right = emit (emittedValue discipline) continuing :=
  rfl

/-- The feed rule belongs to every transducer of its discipline. -/
theorem feedRule_mem {discipline : Discipline} (machine : Machine discipline) :
    feedRule discipline ∈ (transducer machine).rewrites := by
  show feedRule discipline ∈ rewrites machine
  simp [rewrites, fixedRules]

/-- The feed rule read as a cut between the control and the stream, observing
the emitted value. -/
def emissionReading {discipline : Discipline} (machine : Machine discipline) :
    HeterogeneousCutReading (transducer machine) where
  rule := feedRule discipline
  ruleMember := feedRule_mem machine
  contact := feedConstructor
  contactMember := feedConstructor_mem discipline
  sort := TypeDecl.plain "Config"
  ordered := feed_is_ordered_binary_contact
  heterogeneous := feed_is_not_same_sort_contact
  program := .fvar "q"
  environment := next (.fvar "a") (.fvar "rest")
  source := rfl
  observed := emittedValue discipline
  position := .apply "Emit" [] .hole [continuing]
  selects := rfl

/-- The same rule, observing the next control state. -/
def controlReading {discipline : Discipline} (machine : Machine discipline) :
    HeterogeneousCutReading (transducer machine) where
  rule := feedRule discipline
  ruleMember := feedRule_mem machine
  contact := feedConstructor
  contactMember := feedConstructor_mem discipline
  sort := TypeDecl.plain "Config"
  ordered := feed_is_ordered_binary_contact
  heterogeneous := feed_is_not_same_sort_contact
  program := .fvar "q"
  environment := next (.fvar "a") (.fvar "rest")
  source := rfl
  observed := delta (.fvar "q") (.fvar "a")
  position :=
    .apply "Emit" [emittedValue discipline]
      (.apply "Feed" [] .hole [.fvar "rest"]) []
  selects := rfl

/-- What the stream brings: the consumed symbol and the rest. -/
theorem emissionReading_environmentVariables {discipline : Discipline}
    (machine : Machine discipline) :
    (emissionReading machine).environmentVariables = ["a", "rest"] := by
  show environmentOwned (.fvar "q") (next (.fvar "a") (.fvar "rest")) = ["a", "rest"]
  decide +kernel

/-- **Moore: null migration.**  The emitted value reads nothing of the
stream. -/
theorem moore_dataMode (machine : Machine .moore) :
    (emissionReading machine).dataMode = .none := by
  show dataModeOf (.fvar "q") (next (.fvar "a") (.fvar "rest")) (emittedValue .moore) = .none
  decide +kernel

/-- **Mealy: the datum migrates.**  The emitted value reads the consumed
symbol. -/
theorem mealy_dataMode (machine : Machine .mealy) :
    (emissionReading machine).dataMode = .binding := by
  show dataModeOf (.fvar "q") (next (.fvar "a") (.fvar "rest")) (emittedValue .mealy) =
    .binding
  decide +kernel

/-- Under both disciplines the next control state reads the consumed symbol. -/
theorem control_dataMode {discipline : Discipline} (machine : Machine discipline) :
    (controlReading machine).dataMode = .binding := by
  show dataModeOf (.fvar "q") (next (.fvar "a") (.fvar "rest"))
    (delta (.fvar "q") (.fvar "a")) = .binding
  decide +kernel

/-- The Moore machine's emitted value is the same whatever the stream was. -/
theorem moore_emitted_independent_of_stream (machine : Machine .moore)
    {first second : Bindings}
    (agree : ∀ name, name ∉ (["a", "rest"] : List String) →
      first.find? (fun entry => entry.1 == name) =
        second.find? (fun entry => entry.1 == name)) :
    applyBindings first (emittedValue .moore) =
      applyBindings second (emittedValue .moore) :=
  (emissionReading machine).observed_independent_of_environment
    (by
      show readsOwned (.fvar "q") (next (.fvar "a") (.fvar "rest")) (emittedValue .moore) =
        false
      decide +kernel)
    (by rw [emissionReading_environmentVariables]; exact agree)

/-- The Mealy machine's emitted value differs with the consumed symbol: one
state, two symbols, two emitted terms. -/
theorem mealy_emitted_depends_on_symbol :
    applyBindings [("q", stateTerm 0), ("a", inputTerm 0)] (emittedValue .mealy) ≠
      applyBindings [("q", stateTerm 0), ("a", inputTerm 1)] (emittedValue .mealy) := by
  decide +kernel

/-- The Mealy machine's feed rule reads the stream in its contractum: a
variable that only the stream binds occurs in the right side of the authored
rule. -/
theorem mealy_contractum_reads_stream (machine : Machine .mealy) :
    ∃ name ∈ (["a", "rest"] : List String), name ∈ (feedRule .mealy).right.schemaVariables := by
  have reads := (emissionReading machine).contractum_reads_environment
    ((emissionReading machine).readsEnvironment_of_binding (mealy_dataMode machine))
  rwa [emissionReading_environmentVariables] at reads

/-- The constructor the transducers are read across has two operands that
are not both configurations. -/
theorem feed_operands_not_both_configurations {discipline : Discipline}
    (machine : Machine discipline) :
    ∃ first firstType second secondType,
      feedConstructor.params = [.simple first firstType, .simple second secondType] ∧
        ¬ (firstType = .base "Config" ∧ secondType = .base "Config") :=
  (emissionReading machine).operands_not_both_of_sort

/-- Neither reading makes a transducer interactive: `Feed` is selected by no
interactive presentation, and none exists. -/
theorem emissionReading_not_interactive {discipline : Discipline}
    (machine : Machine discipline) :
    ¬ AdmitsInteractivePresentation (transducer machine) ∧
      ∀ presentation : InteractivePresentation,
        presentation.contactConstructor.1 ≠ (emissionReading machine).contact :=
  ⟨transducer_not_interactive machine, (emissionReading machine).contact_not_selected⟩

end Mettapedia.Languages.Transducers
