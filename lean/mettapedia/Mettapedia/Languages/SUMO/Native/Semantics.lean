import Mettapedia.Languages.SUMO.Native.Substitution

/-!
# General world semantics for SUMO's native logical core

A model has one carrier for every SUO-KIF term category. Constants, literals,
function operators, relation operators, and formula intensions therefore
coexist without a static Church-style type split. Relation application yields
a world-indexed proposition; a quoted formula is mapped back into the same
carrier, and `holds` evaluates such a carrier as a proposition. The quote/holds
law gives native meaning to SUMO formula variables such as `(not ?FORMULA)`.

Operators also carry their minimum arity, variable-arity status, and semantic
domain sequence.  This is the native meaning needed when the operator itself
is denoted by a variable or computed term: its argument restrictions cannot be
looked up from a constant name during source elaboration.

The fields deliberately impose neither functional nor Boolean extensionality
on formula intensions. Individual SUMO modal doctrines may add frame and
intension laws, but the native core does not silently choose them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.SUMO.Native

universe uSymbol uLiteral uModel

/-- A unityped, world-indexed model of the native SUMO core. -/
structure Model (Symbol : Type uSymbol) (Literal : Type uLiteral) where
  World : Type uModel
  Carrier : Type uModel
  symbol : Symbol -> Carrier
  literal : Literal -> Carrier
  applyFunction : Carrier -> List Carrier -> Carrier
  applyRelation : Carrier -> List Carrier -> World -> Prop
  /-- Minimum number of arguments accepted by an operator. -/
  operatorArity : Carrier -> Nat
  /-- Whether arguments beyond the minimum arity are accepted. -/
  variableArity : Carrier -> Bool
  /-- Zero-based operator domain sequence.  For a variable-arity operator the
  entry at its minimum arity governs every later optional argument. -/
  operatorDomain : Carrier -> Nat -> Carrier
  /-- World-indexed membership of a value in a denoted operator domain. -/
  domainMember : Carrier -> Carrier -> World -> Prop
  quote : (World -> Prop) -> Carrier
  holds : Carrier -> World -> Prop
  holds_quote : forall (intension : World -> Prop) (world : World),
    holds (quote intension) world <-> intension world
  kappa : (Carrier -> World -> Prop) -> Carrier

namespace Model

variable {Symbol : Type uSymbol} {Literal : Type uLiteral}
variable {ordinary rows : Nat}
variable (model : Model Symbol Literal)

abbrev ObjectEnvironment (ordinary : Nat) := Fin ordinary -> model.Carrier
abbrev RowEnvironment (rows : Nat) := Fin rows -> List model.Carrier

/-- Term results in the common model universe used by the mutual evaluator. -/
abbrev LiftedCarrier := model.Carrier

/-- Expanded spines in the common model universe used by the mutual evaluator. -/
abbrev LiftedSpine := List model.Carrier

/-- World-indexed formula truth inhabits the same common evaluator universe. -/
abbrev LiftedFormula := model.World -> Prop

/-- The unique environment for a closed ordinary-variable context. -/
def emptyObjects : model.ObjectEnvironment 0 := Fin.elim0

/-- The unique environment for a closed row-variable context. -/
def emptyRows : model.RowEnvironment 0 := Fin.elim0

/-- The domain-sequence position governing an argument position.  Optional
arguments of a variable-arity operator repeat the final declared domain. -/
def effectiveDomainPosition (operator : model.Carrier) (position : Nat) : Nat :=
  if model.variableArity operator then
    if position < model.operatorArity operator then position
    else model.operatorArity operator
  else position

/-- A single argument belongs to the effective domain selected by its
zero-based position. -/
def inOperatorDomainAt
    (operator : model.Carrier) (position : Nat)
    (argument : model.Carrier) (world : model.World) : Prop :=
  model.domainMember argument
    (model.operatorDomain operator
      (model.effectiveDomainPosition operator position)) world

/-- Pointwise domain membership for an exact argument tail. -/
def everyTailArgumentInDomain
    (operator : model.Carrier) (firstPosition : Nat) :
    List model.Carrier -> model.World -> Prop
  | [], _ => True
  | argument :: rest, world =>
      model.inOperatorDomainAt operator firstPosition argument world /\
        everyTailArgumentInDomain operator (firstPosition + 1) rest world

/-- The exact tail has a lawful length and every one of its entries belongs to
the effective domain at its position.  The prefix preceding `firstPosition` is
assumed to contain exactly that many already elaborated arguments. -/
def tailInOperatorDomainFrom
    (operator : model.Carrier) (firstPosition : Nat)
    (arguments : List model.Carrier) (world : model.World) : Prop :=
  (if model.variableArity operator then
      model.operatorArity operator - firstPosition <= arguments.length
    else
      firstPosition <= model.operatorArity operator /\
        arguments.length = model.operatorArity operator - firstPosition) /\
    model.everyTailArgumentInDomain operator firstPosition arguments world

mutual
  /-- Internal lifted denotation of a unityped SUMO term. -/
  def denoteTermLifted
      {ordinary rows : Nat}
      (objects : model.ObjectEnvironment ordinary)
      (rowValues : model.RowEnvironment rows) :
      Term Symbol Literal ordinary rows -> model.LiftedCarrier
    | .var index => objects index
    | .constant name => model.symbol name
    | .literal value => model.literal value
    | .application operator arguments =>
        model.applyFunction
          (denoteTermLifted objects rowValues operator)
          (denoteSpineLifted objects rowValues arguments)
    | .quote body =>
        model.quote (denoteFormulaLifted objects rowValues body)
    | .kappa body =>
        model.kappa (fun value =>
          denoteFormulaLifted
            (Fin.cases value objects) rowValues body)

  /-- Internal lifted expansion of an exact argument spine. -/
  def denoteSpineLifted
      {ordinary rows : Nat}
      (objects : model.ObjectEnvironment ordinary)
      (rowValues : model.RowEnvironment rows) :
      Spine Symbol Literal ordinary rows -> model.LiftedSpine
    | .nil => []
    | .term value rest =>
        denoteTermLifted objects rowValues value ::
          denoteSpineLifted objects rowValues rest
    | .row index rest =>
        rowValues index ++ denoteSpineLifted objects rowValues rest

  /-- Internal lifted world intension of a native SUMO formula. -/
  def denoteFormulaLifted
      {ordinary rows : Nat}
      (objects : model.ObjectEnvironment ordinary)
      (rowValues : model.RowEnvironment rows) :
      Formula Symbol Literal ordinary rows -> model.LiftedFormula
    | .top => fun _ => True
    | .bottom => fun _ => False
    | .atom operator arguments =>
        fun world =>
          model.applyRelation
            (denoteTermLifted objects rowValues operator)
            (denoteSpineLifted objects rowValues arguments)
            world
    | .asserted value =>
        fun world =>
          model.holds (denoteTermLifted objects rowValues value) world
    | .equal left right =>
        fun _ =>
          denoteTermLifted objects rowValues left =
            denoteTermLifted objects rowValues right
    | .inOperatorDomain operator position argument =>
        fun world =>
          model.inOperatorDomainAt
            (denoteTermLifted objects rowValues operator) position
            (denoteTermLifted objects rowValues argument) world
    | .tailInOperatorDomain operator firstPosition arguments =>
        fun world =>
          model.tailInOperatorDomainFrom
            (denoteTermLifted objects rowValues operator) firstPosition
            (denoteSpineLifted objects rowValues arguments) world
    | .not body =>
        fun world =>
          Not (denoteFormulaLifted objects rowValues body world)
    | .and left right =>
        fun world =>
          denoteFormulaLifted objects rowValues left world /\
            denoteFormulaLifted objects rowValues right world
    | .or left right =>
        fun world =>
          denoteFormulaLifted objects rowValues left world \/
            denoteFormulaLifted objects rowValues right world
    | .implies left right =>
        fun world =>
          denoteFormulaLifted objects rowValues left world ->
            denoteFormulaLifted objects rowValues right world
    | .iff left right =>
        fun world =>
          denoteFormulaLifted objects rowValues left world <->
            denoteFormulaLifted objects rowValues right world
    | .allInSpine arguments body =>
        fun world =>
          forall value,
            value ∈ denoteSpineLifted objects rowValues arguments ->
              denoteFormulaLifted
                (Fin.cases value objects) rowValues body world
    | .allObject body =>
        fun world =>
          forall value : model.Carrier,
            denoteFormulaLifted
              (Fin.cases value objects) rowValues body world
    | .someObject body =>
        fun world =>
          exists value : model.Carrier,
            denoteFormulaLifted
              (Fin.cases value objects) rowValues body world
    | .allRow body =>
        fun world =>
          forall values : List model.Carrier,
            denoteFormulaLifted objects
              (Fin.cases values rowValues) body world
    | .someRow body =>
        fun world =>
          exists values : List model.Carrier,
            denoteFormulaLifted objects
              (Fin.cases values rowValues) body world
end

/-- Denote a unityped SUMO term. -/
def denoteTerm
    {ordinary rows : Nat}
    (objects : model.ObjectEnvironment ordinary)
    (rowValues : model.RowEnvironment rows)
    (value : Term Symbol Literal ordinary rows) : model.Carrier :=
  model.denoteTermLifted objects rowValues value

/-- Expand and denote an exact argument spine. -/
def denoteSpine
    {ordinary rows : Nat}
    (objects : model.ObjectEnvironment ordinary)
    (rowValues : model.RowEnvironment rows)
    (arguments : Spine Symbol Literal ordinary rows) : List model.Carrier :=
  model.denoteSpineLifted objects rowValues arguments

/-- World-indexed truth of a native SUMO formula. -/
def denoteFormula
    {ordinary rows : Nat}
    (objects : model.ObjectEnvironment ordinary)
    (rowValues : model.RowEnvironment rows)
    (body : Formula Symbol Literal ordinary rows) : model.World -> Prop :=
  model.denoteFormulaLifted objects rowValues body

/-- Truth of a native SUMO formula at a world. -/
def satisfies
    {ordinary rows : Nat}
    (objects : model.ObjectEnvironment ordinary)
    (rowValues : model.RowEnvironment rows)
    (body : Formula Symbol Literal ordinary rows)
    (world : model.World) : Prop :=
  model.denoteFormula objects rowValues body world

/-- A formula is valid in a model when it holds at every environment and
world. -/
def Valid
    (body : Formula Symbol Literal ordinary rows) : Prop :=
  forall (objects : model.ObjectEnvironment ordinary)
    (rowValues : model.RowEnvironment rows) (world : model.World),
      model.satisfies objects rowValues body world

/-- A closed formula is true at every world of a model. -/
def ValidSentence (body : Sentence Symbol Literal) : Prop :=
  forall world : model.World,
    model.satisfies model.emptyObjects model.emptyRows body world

end Model

/-! ## Semantic canaries -/

namespace SemanticsCanary

/-- Self-application is interpreted directly by the model's relation action;
no typed copy of `instance` is introduced. -/
theorem selfApplication_denotes
    (model : Model String Unit) (world : model.World) :
    model.satisfies model.emptyObjects model.emptyRows
        SyntaxCanary.selfApplication world <->
      model.applyRelation (model.symbol "instance")
        [model.symbol "instance", model.symbol "BinaryPredicate"] world := by
  rfl

/-- Relation variables are interpreted from the ordinary environment in
operator position. -/
theorem variableRelation_denotes
    (model : Model String Unit) (operator : model.Carrier)
    (world : model.World) :
    model.satisfies (Fin.cases operator model.emptyObjects)
        model.emptyRows SyntaxCanary.variableRelation world <->
      model.applyRelation operator [model.symbol "Human"] world := by
  rfl

/-- A row occurrence contributes exactly the supplied finite sequence. -/
theorem exact_row_denotes
    (model : Model String Unit) (values : List model.Carrier) :
    model.denoteSpine model.emptyObjects
        (Fin.cases values model.emptyRows)
        (.row 0 .nil : Spine String Unit 0 1) = values := by
  change values ++ [] = values
  exact List.append_nil values

/-- Consequently, the native row semantics has no fixed finite arity bound. -/
theorem exact_row_length
    (model : Model String Unit) (values : List model.Carrier) :
    (model.denoteSpine model.emptyObjects
        (Fin.cases values model.emptyRows)
        (.row 0 .nil : Spine String Unit 0 1)).length = values.length := by
  rw [exact_row_denotes]

/-- A bounded universal over two explicit arguments means exactly that its
body holds of each denoted argument. -/
theorem allInSpine_two_denotes
    (model : Model String Unit)
    (body : Formula String Unit 1 0)
    (world : model.World) :
    model.satisfies model.emptyObjects model.emptyRows
        (.allInSpine
          (Spine.ofTerms [(.constant "a"), (.constant "b")]) body) world <->
      (model.satisfies
          (Fin.cases (model.symbol "a") model.emptyObjects)
          model.emptyRows body world /\
       model.satisfies
          (Fin.cases (model.symbol "b") model.emptyObjects)
          model.emptyRows body world) := by
  change
    (forall value,
      value ∈ [model.symbol "a", model.symbol "b"] ->
        model.satisfies (Fin.cases value model.emptyObjects)
          model.emptyRows body world) <-> _
  constructor
  · intro everyMember
    exact ⟨everyMember (model.symbol "a") (by simp),
      everyMember (model.symbol "b") (by simp)⟩
  · rintro ⟨first, second⟩ value membership
    simp at membership
    rcases membership with equality | equality
    · subst value
      exact first
    · subst value
      exact second

/-! ### Denoted operator-domain witnesses -/

inductive DomainToken where
  | fixedOperator
  | variadicOperator
  | firstDomain
  | repeatedDomain
  | firstValue
  | repeatedValue
  | outsider
  deriving DecidableEq, Repr

abbrev DomainCarrier := Sum (Unit -> Prop) DomainToken

private def token (value : DomainToken) : DomainCarrier := .inr value

/-- A small model with one fixed binary operator and one variadic operator of
minimum arity one.  Its optional arguments repeat the second domain entry. -/
def operatorDomainModel : Model Unit Unit where
  World := Unit
  Carrier := DomainCarrier
  symbol := fun _ => token .outsider
  literal := fun _ => token .outsider
  applyFunction := fun _ _ => token .outsider
  applyRelation := fun _ _ _ => False
  operatorArity
    | .inr .fixedOperator => 2
    | .inr .variadicOperator => 1
    | _ => 0
  variableArity
    | .inr .variadicOperator => true
    | _ => false
  operatorDomain
    | .inr .fixedOperator, 0 => token .firstDomain
    | .inr .fixedOperator, _ => token .repeatedDomain
    | .inr .variadicOperator, 0 => token .firstDomain
    | .inr .variadicOperator, _ => token .repeatedDomain
    | _, _ => token .outsider
  domainMember
    | .inr .firstValue, .inr .firstDomain, _ => True
    | .inr .repeatedValue, .inr .repeatedDomain, _ => True
    | _, _, _ => False
  quote := .inl
  holds
    | .inl intension, world => intension world
    | .inr _, _ => False
  holds_quote := fun _ _ => Iff.rfl
  kappa := fun _ => token .outsider

/-- The exact two-entry tail satisfies the fixed binary profile. -/
theorem fixed_tail_accepted :
    operatorDomainModel.tailInOperatorDomainFrom
      (token .fixedOperator) 0
      [token .firstValue, token .repeatedValue] () := by
  simp [Model.tailInOperatorDomainFrom, Model.everyTailArgumentInDomain,
    Model.inOperatorDomainAt, Model.effectiveDomainPosition,
    operatorDomainModel, token]

/-- A fixed binary operator rejects a tail with the wrong length even when
every supplied entry has the right point domain. -/
theorem fixed_short_tail_rejected :
    Not (operatorDomainModel.tailInOperatorDomainFrom
      (token .fixedOperator) 0 [token .firstValue] ()) := by
  simp [Model.tailInOperatorDomainFrom, operatorDomainModel, token]

/-- Optional arguments of a variadic operator repeat its final domain. -/
theorem variadic_repeated_domain_accepted :
    operatorDomainModel.tailInOperatorDomainFrom
      (token .variadicOperator) 0
      [token .firstValue, token .repeatedValue, token .repeatedValue] () := by
  simp [Model.tailInOperatorDomainFrom, Model.everyTailArgumentInDomain,
    Model.inOperatorDomainAt, Model.effectiveDomainPosition,
    operatorDomainModel, token]

/-- Repetition does not weaken membership: an optional argument in the wrong
domain is rejected. -/
theorem variadic_wrong_optional_domain_rejected :
    Not (operatorDomainModel.tailInOperatorDomainFrom
      (token .variadicOperator) 0
      [token .firstValue, token .outsider] ()) := by
  simp [Model.tailInOperatorDomainFrom, Model.everyTailArgumentInDomain,
    Model.inOperatorDomainAt, Model.effectiveDomainPosition,
    operatorDomainModel, token]

/-- A comparison model with exactly the same function and relation actions,
but a permissive operator-domain judgment. -/
def permissiveOperatorDomainModel : Model Unit Unit :=
  { operatorDomainModel with domainMember := fun _ _ _ => True }

/-- Application behavior alone does not determine admissible operator
arguments.  The domain judgment is genuine semantic structure. -/
theorem application_behavior_does_not_determine_domains :
    (operatorDomainModel.applyFunction =
        permissiveOperatorDomainModel.applyFunction /\
      operatorDomainModel.applyRelation =
        permissiveOperatorDomainModel.applyRelation) /\
    Not (operatorDomainModel.inOperatorDomainAt
      (token .fixedOperator) 0 (token .outsider) () <->
      permissiveOperatorDomainModel.inOperatorDomainAt
        (token .fixedOperator) 0 (token .outsider) ()) := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  simp [Model.inOperatorDomainAt, Model.effectiveDomainPosition,
    operatorDomainModel, permissiveOperatorDomainModel, token]

/-! ### A two-world witness against current-world formula collapse -/

/-- A small model whose carrier consists of world predicates. -/
def twoWorldModel : Model Unit Bool where
  World := Bool
  Carrier := Bool -> Prop
  symbol := fun _ _ => False
  literal := fun value world => world = value
  applyFunction := fun _ _ _ => False
  applyRelation := fun operator _ world => operator world
  operatorArity := fun _ => 0
  variableArity := fun _ => false
  operatorDomain := fun operator _ => operator
  domainMember := fun value domain _ => value = domain
  quote := fun intension => intension
  holds := fun intension world => intension world
  holds_quote := fun _ _ => Iff.rfl
  kappa := fun _ _ => False

/-- Evaluating a quoted formula returns its truth at the current world. -/
theorem asserted_quote_denotes
    (model : Model String Unit) (body : Sentence String Unit)
    (world : model.World) :
    model.satisfies model.emptyObjects model.emptyRows
        (.asserted (.quote body)) world <->
      model.satisfies model.emptyObjects model.emptyRows body world := by
  exact model.holds_quote _ world

/-- True only at the `false` world. -/
def hereOnly : Sentence Unit Bool :=
  .atom (.literal false) .nil

/-- True at every world. -/
def everywhere : Sentence Unit Bool := .top

theorem same_at_false :
    twoWorldModel.satisfies twoWorldModel.emptyObjects
      twoWorldModel.emptyRows hereOnly false /\
    twoWorldModel.satisfies twoWorldModel.emptyObjects
      twoWorldModel.emptyRows everywhere false := by
  exact ⟨rfl, trivial⟩

/-- Although `hereOnly` and `everywhere` agree at the current `false` world,
their quoted formula intensions are distinct. An endpoint truth value is
therefore not a sound replacement for a SUMO formula argument. -/
theorem current_truth_does_not_determine_quote :
    twoWorldModel.denoteTerm twoWorldModel.emptyObjects
        twoWorldModel.emptyRows (.quote hereOnly) ≠
      twoWorldModel.denoteTerm twoWorldModel.emptyObjects
        twoWorldModel.emptyRows (.quote everywhere) := by
  intro equality
  have atTrue := congrFun equality true
  change ((true = false : Prop) = True) at atTrue
  have impossible : False := by
    have contradiction : true = false := by
      rw [atTrue]
      trivial
    exact Bool.noConfusion contradiction
  exact impossible.elim

end SemanticsCanary

end Mettapedia.Languages.SUMO.Native
