import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterValuePolicy

/-! The whole-program printer preserves the declared identifier policy,
including ordered arguments, duplicate statements and all directive names. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.Policy

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.Datalog

theorem mapM_holds {α : Type} (build : α → Except String Pattern)
    (safe : ∀ value pattern, build value = .ok pattern → Holds pattern)
    (values : List α) (patterns : List Pattern) (built : values.mapM build = .ok patterns) :
    ChildrenHold patterns := by
  induction values generalizing patterns with
  | nil => cases Except.ok.inj built; trivial
  | cons first rest ih =>
    rw [List.mapM_cons] at built
    obtain ⟨head, headRead, built⟩ := bind_ok built
    obtain ⟨tail, tailRead, built⟩ := bind_ok built
    cases Except.ok.inj built
    exact ⟨safe first head headRead, ih tail tailRead⟩

theorem nonempty_separated_holds (one more : String)
    (oneSafe : one ≠ "identifier-one" ∧ one ≠ "identifier-more")
    (moreSafe : more ≠ "identifier-one" ∧ more ≠ "identifier-more")
    (first : Pattern) (rest : List Pattern) (head : Holds first) (tail : ChildrenHold rest) :
    Holds (nonemptySeparated one more first rest) := by
  cases rest with
  | nil => exact node_holds _ _ oneSafe.1 oneSafe.2 ⟨head, empty_holds, trivial⟩
  | cons second rest =>
    exact node_holds _ _ moreSafe.1 moreSafe.2
      ⟨head, empty_holds, space_holds,
        nonempty_separated_holds one more oneSafe moreSafe second rest tail.1 tail.2, trivial⟩
termination_by rest.length

theorem separated_holds (zero one more : String)
    (zeroSafe : zero ≠ "identifier-one" ∧ zero ≠ "identifier-more")
    (oneSafe : one ≠ "identifier-one" ∧ one ≠ "identifier-more")
    (moreSafe : more ≠ "identifier-one" ∧ more ≠ "identifier-more")
    (patterns : List Pattern) (holds : ChildrenHold patterns) : Holds (separated zero one more patterns) := by
  cases patterns with
  | nil => exact node_holds _ _ zeroSafe.1 zeroSafe.2 trivial
  | cons first rest => exact nonempty_separated_holds one more oneSafe moreSafe first rest holds.1 holds.2

theorem argument_holds (argument : Argument) (pattern : Pattern) (built : argument? argument = .ok pattern) :
    Holds pattern := by
  cases argument with
  | literal value =>
    obtain ⟨child, read, built⟩ := bind_ok built
    cases Except.ok.inj built
    exact node_holds _ _ (by decide) (by decide) ⟨value_holds _ _ read, trivial⟩
  | var name =>
    obtain ⟨child, read, built⟩ := bind_ok built
    cases Except.ok.inj built
    exact node_holds _ _ (by decide) (by decide) ⟨identifier_holds _ _ read, trivial⟩
  | anonymous => cases Except.ok.inj built; exact node_holds _ _ (by decide) (by decide) trivial

theorem atom_holds (atom : Mettapedia.Languages.Datalog.Atom) (pattern : Pattern)
    (built : atom? atom = .ok pattern) : Holds pattern := by
  obtain ⟨name, nameRead, built⟩ := bind_ok built
  obtain ⟨arguments, argsRead, built⟩ := bind_ok built
  cases Except.ok.inj built
  exact node_holds _ _ (by decide) (by decide) ⟨qualified_holds _ _ nameRead, empty_holds, empty_holds,
    separated_holds _ _ _ (by decide) (by decide) (by decide) arguments
      (mapM_holds argument? argument_holds _ _ argsRead), trivial⟩

theorem fact_holds (fact : GroundFact) (pattern : Pattern) (built : fact? fact = .ok pattern) : Holds pattern := by
  obtain ⟨name, nameRead, built⟩ := bind_ok built
  obtain ⟨values, valuesRead, built⟩ := bind_ok built
  cases Except.ok.inj built
  exact node_holds _ _ (by decide) (by decide)
    ⟨node_holds _ _ (by decide) (by decide) ⟨qualified_holds _ _ nameRead, empty_holds, empty_holds,
      separated_holds _ _ _ (by decide) (by decide) (by decide) values
        (mapM_holds value? value_holds _ _ valuesRead), trivial⟩, empty_holds, trivial⟩

theorem operator_holds (op : ComparisonOperator) : Holds (operator op) := by
  cases op <;> exact node_holds _ _ (by decide) (by decide) trivial

theorem premise_holds (premise : Mettapedia.Languages.Datalog.Premise) (pattern : Pattern)
    (built : premise? premise = .ok pattern) : Holds pattern := by
  cases premise with
  | atom atom =>
    obtain ⟨child, read, built⟩ := bind_ok built
    cases Except.ok.inj built
    exact node_holds _ _ (by decide) (by decide) ⟨atom_holds _ _ read, trivial⟩
  | comparison comparison =>
    obtain ⟨left, leftRead, built⟩ := bind_ok built
    obtain ⟨right, rightRead, built⟩ := bind_ok built
    cases Except.ok.inj built
    exact node_holds _ _ (by decide) (by decide)
      ⟨node_holds _ _ (by decide) (by decide) ⟨argument_holds _ _ leftRead, space_holds,
        operator_holds _, space_holds, argument_holds _ _ rightRead, trivial⟩, trivial⟩

theorem clause_holds (clause : Clause) (pattern : Pattern) (built : clause? clause = .ok pattern) : Holds pattern := by
  unfold clause? at built
  split at built
  · cases built
  · obtain ⟨head, headRead, built⟩ := bind_ok built
    obtain ⟨body, bodyRead, built⟩ := bind_ok built
    have bodySafe := mapM_holds premise? premise_holds _ _ bodyRead
    cases body with
    | nil => cases built
    | cons first rest =>
      cases Except.ok.inj built
      exact node_holds _ _ (by decide) (by decide) ⟨atom_holds _ _ headRead, space_holds, space_holds,
        nonempty_separated_holds _ _ (by decide) (by decide) first rest bodySafe.1 bodySafe.2, trivial⟩

theorem attribute_type_holds (type : AttributeType) (pattern : Pattern)
    (built : attributeType? type = .ok pattern) : Holds pattern := by
  cases type <;> try { cases Except.ok.inj built; exact node_holds _ _ (by decide) (by decide) trivial }
  cases built

theorem attribute_holds (column : Attribute) (pattern : Pattern) (built : attribute? column = .ok pattern) : Holds pattern := by
  obtain ⟨name, nameRead, built⟩ := bind_ok built
  obtain ⟨type, typeRead, built⟩ := bind_ok built
  cases Except.ok.inj built
  exact node_holds _ _ (by decide) (by decide)
    ⟨identifier_holds _ _ nameRead, empty_holds, space_holds, attribute_type_holds _ _ typeRead, trivial⟩

theorem declaration_holds (declaration : RelationDeclaration) (pattern : Pattern)
    (built : declaration? declaration = .ok pattern) : Holds pattern := by
  unfold declaration? at built
  split at built
  · obtain ⟨name, nameRead, built⟩ := bind_ok built
    obtain ⟨attributes, attrsRead, built⟩ := bind_ok built
    cases Except.ok.inj built
    exact node_holds _ _ (by decide) (by decide) ⟨directive_holds,
      node_holds _ _ (by decide) (by decide) ⟨identifier_holds _ _ nameRead, trivial⟩, empty_holds, empty_holds,
      separated_holds _ _ _ (by decide) (by decide) (by decide) attributes
        (mapM_holds attribute? attribute_holds _ _ attrsRead), trivial⟩
  · cases built

theorem statement_holds (statement : Statement) (pattern : Pattern) (built : statement? statement = .ok pattern) :
    Holds pattern := by
  cases statement with
  | declaration declaration =>
    obtain ⟨child, read, built⟩ := bind_ok built; cases Except.ok.inj built
    exact node_holds _ _ (by decide) (by decide) ⟨declaration_holds _ _ read, trivial⟩
  | fact fact =>
    obtain ⟨child, read, built⟩ := bind_ok built; cases Except.ok.inj built
    exact node_holds _ _ (by decide) (by decide) ⟨fact_holds _ _ read, trivial⟩
  | rule clause =>
    obtain ⟨child, read, built⟩ := bind_ok built; cases Except.ok.inj built
    exact node_holds _ _ (by decide) (by decide) ⟨clause_holds _ _ read, trivial⟩
  | input name =>
    obtain ⟨child, read, built⟩ := bind_ok built; cases Except.ok.inj built
    exact node_holds _ _ (by decide) (by decide)
      ⟨node_holds _ _ (by decide) (by decide) ⟨directive_holds, qualified_holds _ _ read, trivial⟩, trivial⟩
  | output name =>
    obtain ⟨child, read, built⟩ := bind_ok built; cases Except.ok.inj built
    exact node_holds _ _ (by decide) (by decide)
      ⟨node_holds _ _ (by decide) (by decide) ⟨directive_holds, qualified_holds _ _ read, trivial⟩, trivial⟩

theorem items_holds (patterns : List Pattern) (holds : ChildrenHold patterns) : Holds (items patterns) := by
  cases patterns with
  | nil => exact node_holds _ _ (by decide) (by decide) trivial
  | cons first rest =>
    exact node_holds _ _ (by decide) (by decide)
      ⟨holds.1, newline_holds, items_holds rest holds.2, trivial⟩
termination_by patterns.length

theorem program_holds (program : Program) (pattern : Pattern) (built : programTree? program = .ok pattern) :
    Holds pattern := by
  obtain ⟨statements, statementsRead, built⟩ := bind_ok built
  cases Except.ok.inj built
  exact node_holds _ _ (by decide) (by decide)
    ⟨empty_holds, items_holds _ (mapM_holds statement? statement_holds _ _ statementsRead), trivial⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.Policy
