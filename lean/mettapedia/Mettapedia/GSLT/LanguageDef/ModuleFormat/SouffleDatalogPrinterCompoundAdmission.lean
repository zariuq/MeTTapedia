import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterValueAdmission

/-! Admitted independent-IR arguments, atoms, facts and premises construct
formed source syntax through the existing printer operations. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.Datalog
open Formation

theorem empty_formed : Formed "DlTrivia" empty := Formation.trivia_empty
theorem space_formed : Formed "DlTrivia" space :=
  Formation.trivia_space (ScalarSyntaxCore.Formed.scalar (description := description) ⟨7, by decide⟩ 32 (by decide +kernel)) empty_formed
theorem newline_formed : Formed "DlTrivia" newline :=
  Formation.trivia_space (ScalarSyntaxCore.Formed.scalar (description := description) ⟨7, by decide⟩ 10 (by decide +kernel)) empty_formed
theorem directive_formed : Formed "DlDirectiveSpace" directiveSpace :=
  Formation.directive_space (ScalarSyntaxCore.Formed.scalar (description := description) ⟨8, by decide⟩ 32 (by decide +kernel)) empty_formed

theorem mapM_total {α : Type} (build : α → Except String Pattern) (sort : String) (values : List α)
    (admitted : ∀ value ∈ values, ∃ pattern, build value = .ok pattern ∧ Formed sort pattern) :
    ∃ patterns, values.mapM build = .ok patterns ∧ patterns.length = values.length ∧
      ∀ pattern ∈ patterns, Formed sort pattern := by
  induction values with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | cons first rest ih =>
    obtain ⟨head, headRead, headFormed⟩ := admitted first List.mem_cons_self
    obtain ⟨tail, tailRead, length, formed⟩ := ih (fun value member => admitted value (List.mem_cons_of_mem _ member))
    refine ⟨head :: tail, ?_, by simp [length], ?_⟩
    · simp [List.mapM_cons, headRead, tailRead, bind, Except.bind, pure, Except.pure]
    · intro pattern member
      rcases List.mem_cons.mp member with rfl | later
      · exact headFormed
      · exact formed pattern later

theorem nonempty_separated_formed (sort childSort one more : String)
    (single : ∀ pattern, Formed childSort pattern → Formed sort (node one [pattern, empty]))
    (cons : ∀ head tail, Formed childSort head → Formed sort tail → Formed sort (node more [head, empty, space, tail]))
    (head : Pattern) (rest : List Pattern) (first : Formed childSort head)
    (others : ∀ pattern ∈ rest, Formed childSort pattern) :
    Formed sort (nonemptySeparated one more head rest) := by
  induction rest generalizing head with
  | nil => exact single head first
  | cons next rest ih =>
    exact cons head _ first (ih next (others next List.mem_cons_self)
      (fun pattern member => others pattern (List.mem_cons_of_mem _ member)))

theorem separated_formed (sort childSort emptyName one more : String)
    (empty : Formed sort (node emptyName []))
    (single : ∀ pattern, Formed childSort pattern → Formed sort (node one [pattern, SourcePrinter.empty]))
    (cons : ∀ head tail, Formed childSort head → Formed sort tail → Formed sort (node more [head, SourcePrinter.empty, space, tail]))
    (patterns : List Pattern) (formed : ∀ pattern ∈ patterns, Formed childSort pattern) :
    Formed sort (separated emptyName one more patterns) := by
  cases patterns with
  | nil => exact empty
  | cons first rest =>
    exact nonempty_separated_formed sort childSort one more single cons first rest
      (formed first List.mem_cons_self) (fun pattern member => formed pattern (List.mem_cons_of_mem _ member))

def ArgumentAdmitted : Argument → Prop
  | .literal value => ValueAdmitted value
  | .var name => Identifier name
  | .anonymous => True

def AtomAdmitted (atom : Mettapedia.Languages.Datalog.Atom) : Prop :=
  Qualified atom.relation ∧ ∀ argument ∈ atom.arguments, ArgumentAdmitted argument

def FactAdmitted (fact : GroundFact) : Prop :=
  Qualified fact.relation ∧ ∀ value ∈ fact.values, ValueAdmitted value

def PremiseAdmitted : Mettapedia.Languages.Datalog.Premise → Prop
  | .atom atom => AtomAdmitted atom
  | .comparison comparison => ArgumentAdmitted comparison.left ∧ ArgumentAdmitted comparison.right

theorem argument_total (argument : Argument) (admitted : ArgumentAdmitted argument) :
    ∃ pattern, argument? argument = .ok pattern ∧ Formed "DlTerm" pattern := by
  cases argument with
  | literal value =>
    obtain ⟨source, built, formed⟩ := value_total value admitted
    exact ⟨_, by simp [argument?, built, bind, Except.bind, pure, Except.pure], Formation.term_constant formed⟩
  | var name =>
    obtain ⟨source, built, formed⟩ := identifier_total name admitted
    exact ⟨_, by simp [argument?, built, bind, Except.bind, pure, Except.pure], Formation.term_variable formed⟩
  | anonymous => exact ⟨_, rfl, Formation.term_anonymous⟩

theorem atom_total (atom : Mettapedia.Languages.Datalog.Atom) (admitted : AtomAdmitted atom) :
    ∃ pattern, atom? atom = .ok pattern ∧ Formed "DlAtom" pattern := by
  obtain ⟨name, nameRead, nameFormed⟩ := qualified_total atom.relation admitted.1
  obtain ⟨arguments, argumentsRead, _, argumentsFormed⟩ := mapM_total argument? "DlTerm" atom.arguments
    (fun value member => argument_total value (admitted.2 value member))
  refine ⟨node "atom" [name, empty, empty, separated "terms-empty" "terms-one" "terms-more" arguments], ?_, ?_⟩
  · simp [atom?, nameRead, argumentsRead, bind, Except.bind, pure, Except.pure]
  · apply Formation.atom nameFormed empty_formed empty_formed
    exact separated_formed "DlTerms" "DlTerm" "terms-empty" "terms-one" "terms-more"
      Formation.terms_empty (fun _ formed => Formation.terms_one formed empty_formed)
      (fun _ _ head tail => Formation.terms_more head empty_formed space_formed tail) arguments argumentsFormed

theorem fact_total (fact : GroundFact) (admitted : FactAdmitted fact) :
    ∃ pattern, fact? fact = .ok pattern ∧ Formed "DlFact" pattern := by
  obtain ⟨name, nameRead, nameFormed⟩ := qualified_total fact.relation admitted.1
  obtain ⟨values, valuesRead, _, valuesFormed⟩ := mapM_total value? "DlConstant" fact.values
    (fun value member => value_total value (admitted.2 value member))
  refine ⟨node "fact" [node "ground-atom" [name, empty, empty,
    separated "constants-empty" "constants-one" "constants-more" values], empty], ?_, ?_⟩
  · simp [fact?, nameRead, valuesRead, bind, Except.bind, pure, Except.pure]
  · apply Formation.fact (Formation.ground_atom nameFormed empty_formed empty_formed ?_) empty_formed
    exact separated_formed "DlConstants" "DlConstant" "constants-empty" "constants-one" "constants-more"
      Formation.constants_empty (fun _ formed => Formation.constants_one formed empty_formed)
      (fun _ _ head tail => Formation.constants_more head empty_formed space_formed tail) values valuesFormed

theorem operator_formed (op : ComparisonOperator) : Formed "DlComparisonOperator" (operator op) := by
  cases op
  · exact Formation.comparison_equal
  · exact Formation.comparison_different
  · exact Formation.comparison_less
  · exact Formation.comparison_less_equal
  · exact Formation.comparison_greater
  · exact Formation.comparison_greater_equal

theorem premise_total (premise : Mettapedia.Languages.Datalog.Premise) (admitted : PremiseAdmitted premise) :
    ∃ pattern, premise? premise = .ok pattern ∧ Formed "DlPositiveLiteral" pattern := by
  cases premise with
  | atom atom =>
    obtain ⟨source, built, formed⟩ := atom_total atom admitted
    exact ⟨_, by simp [premise?, built, bind, Except.bind, pure, Except.pure], Formation.positive_atom formed⟩
  | comparison comparison =>
    obtain ⟨left, leftRead, leftFormed⟩ := argument_total comparison.left admitted.1
    obtain ⟨right, rightRead, rightFormed⟩ := argument_total comparison.right admitted.2
    exact ⟨_, by simp [premise?, leftRead, rightRead, bind, Except.bind, pure, Except.pure],
      Formation.positive_comparison (Formation.comparison leftFormed space_formed (operator_formed comparison.operator) space_formed rightFormed)⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
