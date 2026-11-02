import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterComposition

/-! Atom and fact printing preserve relation components, argument positions
and literal values through the authored projection and normalization. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog
open ProgramProjection

theorem relation_normalize (names : List String) (source : Pattern)
    (built : qualifiedName? names = .ok source) :
    Frontend.normalize? (Reference.relation source) = some (IRCodec.relation names) := by
  change ((Frontend.qualifiedName? source).bind fun names => some (IRCodec.relation names)) = _
  rw [qualified_name_read names source built]
  rfl

theorem normalize_node (label : String) (inputs outputs : List Pattern)
    (plain : SourceMeaning.PlainNode label inputs)
    (children : Frontend.normalizeChildren? inputs = some outputs) :
    Frontend.normalize? (.apply label inputs) = some (.apply label outputs) := by
  rw [SourceMeaning.plain_normalization label inputs plain, children]
  rfl

theorem normalize_vector (inputs outputs : List Pattern)
    (children : Frontend.normalizeChildren? inputs = some outputs) :
    Frontend.normalize? (Reference.vector inputs) = some (Reference.vector outputs) := by
  change (Frontend.normalizeChildren? inputs).bind (fun values => some (Pattern.collection .vec values none)) = _
  rw [children]
  rfl

theorem normalize_tuple (inputs outputs : List Pattern)
    (children : Frontend.normalizeChildren? inputs = some outputs) :
    Frontend.normalize? (Reference.tuple inputs) = some (Reference.tuple outputs) := by
  apply normalize_node _ _ _ (by simp [SourceMeaning.PlainNode])
  simp only [Frontend.normalizeChildren?, normalize_vector _ _ children, Option.bind_eq_bind, Option.bind_some]
  rfl

theorem normalize_ground_tuple (inputs outputs : List Pattern)
    (children : Frontend.normalizeChildren? inputs = some outputs) :
    Frontend.normalize? (Reference.groundTuple inputs) = some (Reference.groundTuple outputs) := by
  apply normalize_node _ _ _ (by simp [SourceMeaning.PlainNode])
  simp only [Frontend.normalizeChildren?, normalize_vector _ _ children, Option.bind_eq_bind, Option.bind_some]
  rfl

theorem atom_read (atom : Mettapedia.Languages.Datalog.Atom) (source : Pattern)
    (built : atom? atom = .ok source) :
    ∃ name arguments, Reference.atom? source = some (name,arguments) ∧
      Frontend.normalize? name = some (IRCodec.relation atom.relation) ∧
      Frontend.normalize? arguments = some (IRCodec.tuple atom.arguments) := by
  cases nameRead : qualifiedName? atom.relation with
  | error reason => simp only [atom?, nameRead] at built; cases built
  | ok name =>
      cases argsRead : atom.arguments.mapM argument? with
      | error reason => simp only [atom?, nameRead, argsRead] at built; cases built
      | ok arguments =>
          simp only [atom?, nameRead, argsRead] at built
          have same : node "atom" [name,empty,empty,separated "terms-empty" "terms-one" "terms-more" arguments] = source :=
            Except.ok.inj built
          subst source
          have read := arguments_read atom.arguments arguments argsRead
          cases projected : Reference.terms? (separated "terms-empty" "terms-one" "terms-more" arguments) with
          | none => simp [projected] at read
          | some terms =>
              simp only [projected, Option.bind_some] at read
              refine ⟨Reference.relation name, Reference.tuple terms, ?_, relation_normalize _ _ nameRead, ?_⟩
              · change (Reference.terms? (separated "terms-empty" "terms-one" "terms-more" arguments)).map _ = _
                rw [projected]
                rfl
              · exact normalize_tuple _ _ read


theorem fact_read (fact : GroundFact) (source : Pattern) (built : fact? fact = .ok source) :
    (Reference.fact? source).bind Frontend.normalize? = some (IRCodec.groundFact fact) := by
  cases nameRead : qualifiedName? fact.relation with
  | error reason => simp only [fact?, nameRead] at built; cases built
  | ok name =>
      cases valuesRead : fact.values.mapM value? with
      | error reason => simp only [fact?, nameRead, valuesRead] at built; cases built
      | ok values =>
          simp only [fact?, nameRead, valuesRead] at built
          have same : node "fact" [node "ground-atom"
              [name,empty,empty,separated "constants-empty" "constants-one" "constants-more" values],empty] = source :=
            Except.ok.inj built
          subst source
          have read := constants_read fact.values values valuesRead
          cases projected : Reference.constants? (separated "constants-empty" "constants-one" "constants-more" values) with
          | none => simp [projected] at read
          | some terms =>
              simp only [projected, Option.bind_some] at read
              change ((Reference.constants? (separated "constants-empty" "constants-one" "constants-more" values)).map
                (fun terms => Pattern.apply "GroundFact" [Reference.relation name,Reference.groundTuple terms])).bind
                Frontend.normalize? = _
              rw [projected]
              change Frontend.normalize? (.apply "GroundFact" [Reference.relation name,Reference.groundTuple terms]) = _
              apply normalize_node _ _ _ (by simp [SourceMeaning.PlainNode])
              simp only [Frontend.normalizeChildren?, relation_normalize _ _ nameRead,
                normalize_ground_tuple _ _ read, Option.bind_eq_bind, Option.bind_some]
              rfl

theorem positive_atom_read (atom : Mettapedia.Languages.Datalog.Atom) (source : Pattern)
    (built : atom? atom = .ok source) :
    (Reference.positiveLiteral? (node "positive-atom" [source])).bind Frontend.normalize? =
      some (IRCodec.premise (.atom atom)) := by
  obtain ⟨name,arguments,projected,nameRead,argumentsRead⟩ := atom_read atom source built
  change ((Reference.atom? source).map fun (name,arguments) => Pattern.apply "PositiveAtom" [name,arguments]).bind
    Frontend.normalize? = _
  rw [projected]
  change Frontend.normalize? (.apply "PositiveAtom" [name,arguments]) = _
  apply normalize_node _ _ _ (by simp [SourceMeaning.PlainNode])
  simp only [Frontend.normalizeChildren?, nameRead, argumentsRead, Option.bind_eq_bind, Option.bind_some]
  rfl

theorem operator_read (op : ComparisonOperator) (left right : Pattern) :
    Reference.comparisonOperator? (operator op) left right = some (.apply (IRCodec.operator op) [left,right]) := by
  cases op <;> rfl

theorem operator_normalize (op : ComparisonOperator) (left right leftValue rightValue : Pattern)
    (leftRead : Frontend.normalize? left = some leftValue)
    (rightRead : Frontend.normalize? right = some rightValue) :
    Frontend.normalize? (.apply (IRCodec.operator op) [left,right]) =
      some (.apply (IRCodec.operator op) [leftValue,rightValue]) := by
  apply normalize_node _ _ _ (by cases op <;> simp [IRCodec.operator, SourceMeaning.PlainNode])
  simp only [Frontend.normalizeChildren?, leftRead, rightRead, Option.bind_eq_bind, Option.bind_some]
  rfl


theorem premise_read (premise : Mettapedia.Languages.Datalog.Premise) (source : Pattern)
    (built : premise? premise = .ok source) :
    (Reference.positiveLiteral? source).bind Frontend.normalize? = some (IRCodec.premise premise) := by
  cases premise with
  | atom atom =>
      cases read : atom? atom with
      | error reason => simp only [premise?, read] at built; cases built
      | ok atomSource =>
          have same : node "positive-atom" [atomSource] = source := by simpa [premise?, read] using built
          subst source
          exact positive_atom_read atom atomSource read
  | comparison comparison =>
      cases leftBuilt : argument? comparison.left with
      | error reason => simp only [premise?, leftBuilt] at built; cases built
      | ok left =>
          cases rightBuilt : argument? comparison.right with
          | error reason => simp only [premise?, leftBuilt, rightBuilt] at built; cases built
          | ok right =>
              simp only [premise?, leftBuilt, rightBuilt] at built
              have same : node "positive-comparison" [node "comparison"
                  [left,space,operator comparison.operator,space,right]] = source := Except.ok.inj built
              subst source
              have leftRead := argument_read comparison.left left leftBuilt
              have rightRead := argument_read comparison.right right rightBuilt
              cases leftProjected : Reference.term? left with
              | none => simp [leftProjected] at leftRead
              | some leftCode =>
                  cases rightProjected : Reference.term? right with
                  | none => simp [rightProjected] at rightRead
                  | some rightCode =>
                      simp only [leftProjected, Option.bind_some] at leftRead
                      simp only [rightProjected, Option.bind_some] at rightRead
                      have projected : Reference.comparison? (node "comparison"
                          [left,space,operator comparison.operator,space,right]) =
                          some (.apply (IRCodec.operator comparison.operator) [leftCode,rightCode]) := by
                        change ((Reference.term? left).bind fun l => (Reference.term? right).bind fun r =>
                          Reference.comparisonOperator? (operator comparison.operator) l r) = _
                        rw [leftProjected, rightProjected]
                        exact operator_read _ _ _
                      change ((Reference.comparison? (node "comparison"
                          [left,space,operator comparison.operator,space,right])).map
                          (fun code => Pattern.apply "Comparison" [code])).bind Frontend.normalize? = _
                      rw [projected]
                      change Frontend.normalize? (.apply "Comparison"
                        [.apply (IRCodec.operator comparison.operator) [leftCode,rightCode]]) = _
                      apply normalize_node _ _ _ (by simp [SourceMeaning.PlainNode])
                      simp only [Frontend.normalizeChildren?, operator_normalize _ _ _ _ _ leftRead rightRead,
                        Option.bind_eq_bind, Option.bind_some]
                      rfl

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
