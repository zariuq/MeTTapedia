import Mettapedia.Languages.SUMO.Native.Syntax

/-!
# Renaming and simultaneous substitution for native SUMO syntax

Ordinary variables substitute to unityped terms. Row variables substitute to
exact finite spines and are spliced into their surrounding argument spine.
The two operations are lifted independently beneath their corresponding
binders, which makes capture avoidance a structural property of the API.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.SUMO.Native

universe uSymbol uLiteral

abbrev OrdinaryRenaming (source target : Nat) := Fin source -> Fin target
abbrev RowRenaming (source target : Nat) := Fin source -> Fin target

namespace Renaming

variable {Symbol : Type uSymbol} {Literal : Type uLiteral}
variable {source target ordinary ordinary' rows rows' : Nat}

/-- Lift an ordinary-variable renaming beneath one ordinary binder. -/
def underObject (mapping : OrdinaryRenaming source target) :
    OrdinaryRenaming (source + 1) (target + 1) :=
  Fin.cases 0 (fun index => Fin.succ (mapping index))

/-- Lift a row-variable renaming beneath one row binder. -/
def underRow (mapping : RowRenaming source target) :
    RowRenaming (source + 1) (target + 1) :=
  Fin.cases 0 (fun index => Fin.succ (mapping index))

mutual
  /-- Rename ordinary and row variables in a term. -/
  def term
      {ordinary ordinary' rows rows' : Nat}
      (ordinaryMap : OrdinaryRenaming ordinary ordinary')
      (rowMap : RowRenaming rows rows') :
      Term Symbol Literal ordinary rows ->
      Term Symbol Literal ordinary' rows'
    | .var index => .var (ordinaryMap index)
    | .constant symbol => .constant symbol
    | .literal value => .literal value
    | .application operator arguments =>
        .application (term ordinaryMap rowMap operator)
          (spine ordinaryMap rowMap arguments)
    | .quote body => .quote (formula ordinaryMap rowMap body)
    | .kappa body =>
        .kappa (formula (underObject ordinaryMap) rowMap body)

  /-- Rename ordinary and row variables in an exact spine. -/
  def spine
      {ordinary ordinary' rows rows' : Nat}
      (ordinaryMap : OrdinaryRenaming ordinary ordinary')
      (rowMap : RowRenaming rows rows') :
      Spine Symbol Literal ordinary rows ->
      Spine Symbol Literal ordinary' rows'
    | .nil => .nil
    | .term value rest =>
        .term (term ordinaryMap rowMap value) (spine ordinaryMap rowMap rest)
    | .row index rest =>
        .row (rowMap index) (spine ordinaryMap rowMap rest)

  /-- Rename ordinary and row variables in a formula. -/
  def formula
      {ordinary ordinary' rows rows' : Nat}
      (ordinaryMap : OrdinaryRenaming ordinary ordinary')
      (rowMap : RowRenaming rows rows') :
      Formula Symbol Literal ordinary rows ->
      Formula Symbol Literal ordinary' rows'
    | .top => .top
    | .bottom => .bottom
    | .atom operator arguments =>
        .atom (term ordinaryMap rowMap operator)
          (spine ordinaryMap rowMap arguments)
    | .asserted value => .asserted (term ordinaryMap rowMap value)
    | .equal left right =>
        .equal (term ordinaryMap rowMap left) (term ordinaryMap rowMap right)
    | .inOperatorDomain operator position argument =>
        .inOperatorDomain (term ordinaryMap rowMap operator) position
          (term ordinaryMap rowMap argument)
    | .tailInOperatorDomain operator firstPosition arguments =>
        .tailInOperatorDomain (term ordinaryMap rowMap operator) firstPosition
          (spine ordinaryMap rowMap arguments)
    | .not body => .not (formula ordinaryMap rowMap body)
    | .and left right =>
        .and (formula ordinaryMap rowMap left) (formula ordinaryMap rowMap right)
    | .or left right =>
        .or (formula ordinaryMap rowMap left) (formula ordinaryMap rowMap right)
    | .implies left right =>
        .implies (formula ordinaryMap rowMap left)
          (formula ordinaryMap rowMap right)
    | .iff left right =>
        .iff (formula ordinaryMap rowMap left) (formula ordinaryMap rowMap right)
    | .allInSpine arguments body =>
        .allInSpine (spine ordinaryMap rowMap arguments)
          (formula (underObject ordinaryMap) rowMap body)
    | .allObject body =>
        .allObject (formula (underObject ordinaryMap) rowMap body)
    | .someObject body =>
        .someObject (formula (underObject ordinaryMap) rowMap body)
    | .allRow body =>
        .allRow (formula ordinaryMap (underRow rowMap) body)
    | .someRow body =>
        .someRow (formula ordinaryMap (underRow rowMap) body)
end

/-- Weaken a term by one fresh ordinary variable. -/
def weakenObjectTerm (value : Term Symbol Literal ordinary rows) :
    Term Symbol Literal (ordinary + 1) rows :=
  term Fin.succ (fun index => index) value

/-- Weaken a spine by one fresh ordinary variable. -/
def weakenObjectSpine (arguments : Spine Symbol Literal ordinary rows) :
    Spine Symbol Literal (ordinary + 1) rows :=
  spine Fin.succ (fun index => index) arguments

/-- Weaken a formula by one fresh ordinary variable. -/
def weakenObjectFormula (body : Formula Symbol Literal ordinary rows) :
    Formula Symbol Literal (ordinary + 1) rows :=
  formula Fin.succ (fun index => index) body

/-- Weaken a term by one fresh row variable. -/
def weakenRowTerm (value : Term Symbol Literal ordinary rows) :
    Term Symbol Literal ordinary (rows + 1) :=
  term (fun index => index) Fin.succ value

/-- Weaken a spine by one fresh row variable. -/
def weakenRowSpine (arguments : Spine Symbol Literal ordinary rows) :
    Spine Symbol Literal ordinary (rows + 1) :=
  spine (fun index => index) Fin.succ arguments

/-- Weaken a formula by one fresh row variable. -/
def weakenRowFormula (body : Formula Symbol Literal ordinary rows) :
    Formula Symbol Literal ordinary (rows + 1) :=
  formula (fun index => index) Fin.succ body

end Renaming

/-! ## Partial renaming

Partial renaming is the scope-safe operation needed to move a formula outward
across a binder only when it does not mention that binder.  Failure is
structural: no arbitrary replacement is supplied for an escaping variable. -/

abbrev OrdinaryPartialRenaming (source target : Nat) :=
  Fin source -> Option (Fin target)

abbrev RowPartialRenaming (source target : Nat) :=
  Fin source -> Option (Fin target)

namespace PartialRenaming

variable {Symbol : Type uSymbol} {Literal : Type uLiteral}
variable {source target ordinary ordinary' rows rows' : Nat}

/-- Lift a partial ordinary-variable renaming beneath one ordinary binder. -/
def underObject (mapping : OrdinaryPartialRenaming source target) :
    OrdinaryPartialRenaming (source + 1) (target + 1) :=
  Fin.cases (some 0) (fun index => (mapping index).map Fin.succ)

/-- Lift a partial row-variable renaming beneath one row binder. -/
def underRow (mapping : RowPartialRenaming source target) :
    RowPartialRenaming (source + 1) (target + 1) :=
  Fin.cases (some 0) (fun index => (mapping index).map Fin.succ)

mutual
  /-- Partially rename ordinary and row variables in a term. -/
  def term
      {ordinary ordinary' rows rows' : Nat}
      (ordinaryMap : OrdinaryPartialRenaming ordinary ordinary')
      (rowMap : RowPartialRenaming rows rows') :
      Term Symbol Literal ordinary rows ->
        Option (Term Symbol Literal ordinary' rows')
    | .var index => (ordinaryMap index).map .var
    | .constant symbol => some (.constant symbol)
    | .literal value => some (.literal value)
    | .application operator arguments => do
        let renamedOperator <- term ordinaryMap rowMap operator
        let renamedArguments <- spine ordinaryMap rowMap arguments
        pure (.application renamedOperator renamedArguments)
    | .quote body => (formula ordinaryMap rowMap body).map .quote
    | .kappa body =>
        (formula (underObject ordinaryMap) rowMap body).map .kappa

  /-- Partially rename ordinary and row variables in an exact spine. -/
  def spine
      {ordinary ordinary' rows rows' : Nat}
      (ordinaryMap : OrdinaryPartialRenaming ordinary ordinary')
      (rowMap : RowPartialRenaming rows rows') :
      Spine Symbol Literal ordinary rows ->
        Option (Spine Symbol Literal ordinary' rows')
    | .nil => some .nil
    | .term value rest => do
        let renamedValue <- term ordinaryMap rowMap value
        let renamedRest <- spine ordinaryMap rowMap rest
        pure (.term renamedValue renamedRest)
    | .row index rest =>
        match rowMap index, spine ordinaryMap rowMap rest with
        | some renamedIndex, some renamedRest =>
            some (.row renamedIndex renamedRest)
        | _, _ => none

  /-- Partially rename ordinary and row variables in a formula. -/
  def formula
      {ordinary ordinary' rows rows' : Nat}
      (ordinaryMap : OrdinaryPartialRenaming ordinary ordinary')
      (rowMap : RowPartialRenaming rows rows') :
      Formula Symbol Literal ordinary rows ->
        Option (Formula Symbol Literal ordinary' rows')
    | .top => some .top
    | .bottom => some .bottom
    | .atom operator arguments => do
        let renamedOperator <- term ordinaryMap rowMap operator
        let renamedArguments <- spine ordinaryMap rowMap arguments
        pure (.atom renamedOperator renamedArguments)
    | .asserted value => (term ordinaryMap rowMap value).map .asserted
    | .equal left right => do
        let renamedLeft <- term ordinaryMap rowMap left
        let renamedRight <- term ordinaryMap rowMap right
        pure (.equal renamedLeft renamedRight)
    | .inOperatorDomain operator position argument => do
        let renamedOperator <- term ordinaryMap rowMap operator
        let renamedArgument <- term ordinaryMap rowMap argument
        pure (.inOperatorDomain renamedOperator position renamedArgument)
    | .tailInOperatorDomain operator firstPosition arguments => do
        let renamedOperator <- term ordinaryMap rowMap operator
        let renamedArguments <- spine ordinaryMap rowMap arguments
        pure (.tailInOperatorDomain renamedOperator firstPosition renamedArguments)
    | .not body => (formula ordinaryMap rowMap body).map .not
    | .and left right => do
        let renamedLeft <- formula ordinaryMap rowMap left
        let renamedRight <- formula ordinaryMap rowMap right
        pure (.and renamedLeft renamedRight)
    | .or left right => do
        let renamedLeft <- formula ordinaryMap rowMap left
        let renamedRight <- formula ordinaryMap rowMap right
        pure (.or renamedLeft renamedRight)
    | .implies left right => do
        let renamedLeft <- formula ordinaryMap rowMap left
        let renamedRight <- formula ordinaryMap rowMap right
        pure (.implies renamedLeft renamedRight)
    | .iff left right => do
        let renamedLeft <- formula ordinaryMap rowMap left
        let renamedRight <- formula ordinaryMap rowMap right
        pure (.iff renamedLeft renamedRight)
    | .allInSpine arguments body => do
        let renamedArguments <- spine ordinaryMap rowMap arguments
        let renamedBody <- formula (underObject ordinaryMap) rowMap body
        pure (.allInSpine renamedArguments renamedBody)
    | .allObject body =>
        (formula (underObject ordinaryMap) rowMap body).map .allObject
    | .someObject body =>
        (formula (underObject ordinaryMap) rowMap body).map .someObject
    | .allRow body =>
        (formula ordinaryMap (underRow rowMap) body).map .allRow
    | .someRow body =>
        (formula ordinaryMap (underRow rowMap) body).map .someRow
end

end PartialRenaming

/-- A simultaneous, scope-changing substitution for both SUMO binder classes. -/
structure Substitution
    (Symbol : Type uSymbol) (Literal : Type uLiteral)
    (ordinary rows ordinary' rows' : Nat) where
  object : Fin ordinary -> Term Symbol Literal ordinary' rows'
  row : Fin rows -> Spine Symbol Literal ordinary' rows'

namespace Substitution

variable {Symbol : Type uSymbol} {Literal : Type uLiteral}
variable {ordinary rows ordinary' rows' : Nat}

/-- Lift a substitution beneath an ordinary binder. -/
def underObject
    (substitution : Substitution Symbol Literal ordinary rows ordinary' rows') :
    Substitution Symbol Literal (ordinary + 1) rows (ordinary' + 1) rows' where
  object := Fin.cases (.var 0) (fun index =>
    Renaming.weakenObjectTerm (substitution.object index))
  row := fun index => Renaming.weakenObjectSpine (substitution.row index)

/-- Lift a substitution beneath a row binder. -/
def underRow
    (substitution : Substitution Symbol Literal ordinary rows ordinary' rows') :
    Substitution Symbol Literal ordinary (rows + 1) ordinary' (rows' + 1) where
  object := fun index => Renaming.weakenRowTerm (substitution.object index)
  row := Fin.cases (.row 0 .nil) (fun index =>
    Renaming.weakenRowSpine (substitution.row index))

mutual
  /-- Simultaneously substitute a native SUMO term. -/
  def term
      {ordinary rows ordinary' rows' : Nat}
      (substitution : Substitution Symbol Literal ordinary rows ordinary' rows') :
      Term Symbol Literal ordinary rows ->
      Term Symbol Literal ordinary' rows'
    | .var index => substitution.object index
    | .constant symbol => .constant symbol
    | .literal value => .literal value
    | .application operator arguments =>
        .application (term substitution operator) (spine substitution arguments)
    | .quote body => .quote (formula substitution body)
    | .kappa body => .kappa (formula (underObject substitution) body)

  /-- Simultaneously substitute an exact spine. Row images are spliced rather
  than inserted as opaque single arguments. -/
  def spine
      {ordinary rows ordinary' rows' : Nat}
      (substitution : Substitution Symbol Literal ordinary rows ordinary' rows') :
      Spine Symbol Literal ordinary rows ->
      Spine Symbol Literal ordinary' rows'
    | .nil => .nil
    | .term value rest =>
        .term (term substitution value) (spine substitution rest)
    | .row index rest =>
        Spine.append (substitution.row index) (spine substitution rest)

  /-- Simultaneously substitute a native SUMO formula. -/
  def formula
      {ordinary rows ordinary' rows' : Nat}
      (substitution : Substitution Symbol Literal ordinary rows ordinary' rows') :
      Formula Symbol Literal ordinary rows ->
      Formula Symbol Literal ordinary' rows'
    | .top => .top
    | .bottom => .bottom
    | .atom operator arguments =>
        .atom (term substitution operator) (spine substitution arguments)
    | .asserted value => .asserted (term substitution value)
    | .equal left right =>
        .equal (term substitution left) (term substitution right)
    | .inOperatorDomain operator position argument =>
        .inOperatorDomain (term substitution operator) position
          (term substitution argument)
    | .tailInOperatorDomain operator firstPosition arguments =>
        .tailInOperatorDomain (term substitution operator) firstPosition
          (spine substitution arguments)
    | .not body => .not (formula substitution body)
    | .and left right => .and (formula substitution left) (formula substitution right)
    | .or left right => .or (formula substitution left) (formula substitution right)
    | .implies left right =>
        .implies (formula substitution left) (formula substitution right)
    | .iff left right => .iff (formula substitution left) (formula substitution right)
    | .allInSpine arguments body =>
        .allInSpine (spine substitution arguments)
          (formula (underObject substitution) body)
    | .allObject body => .allObject (formula (underObject substitution) body)
    | .someObject body => .someObject (formula (underObject substitution) body)
    | .allRow body => .allRow (formula (underRow substitution) body)
    | .someRow body => .someRow (formula (underRow substitution) body)
end

/-- The identity substitution. -/
def identity : Substitution Symbol Literal ordinary rows ordinary rows where
  object := .var
  row := fun index => .row index .nil

/-- Replace the newest ordinary variable by one term. -/
def replaceObject (value : Term Symbol Literal ordinary rows) :
    Substitution Symbol Literal (ordinary + 1) rows ordinary rows where
  object := Fin.cases value .var
  row := fun index => .row index .nil

/-- Replace the newest row variable by one exact finite spine. -/
def replaceRow (arguments : Spine Symbol Literal ordinary rows) :
    Substitution Symbol Literal ordinary (rows + 1) ordinary rows where
  object := .var
  row := Fin.cases arguments (fun index => .row index .nil)

/-- Instantiate the newest ordinary variable in a term. -/
def instantiateObjectTerm
    (value : Term Symbol Literal ordinary rows)
    (body : Term Symbol Literal (ordinary + 1) rows) :
    Term Symbol Literal ordinary rows :=
  term (replaceObject value) body

/-- Instantiate the newest ordinary variable in a formula. -/
def instantiateObjectFormula
    (value : Term Symbol Literal ordinary rows)
    (body : Formula Symbol Literal (ordinary + 1) rows) :
    Formula Symbol Literal ordinary rows :=
  formula (replaceObject value) body

/-- Instantiate the newest row variable in a term. -/
def instantiateRowTerm
    (arguments : Spine Symbol Literal ordinary rows)
    (body : Term Symbol Literal ordinary (rows + 1)) :
    Term Symbol Literal ordinary rows :=
  term (replaceRow arguments) body

/-- Instantiate the newest row variable in a formula. -/
def instantiateRowFormula
    (arguments : Spine Symbol Literal ordinary rows)
    (body : Formula Symbol Literal ordinary (rows + 1)) :
    Formula Symbol Literal ordinary rows :=
  formula (replaceRow arguments) body

end Substitution

/-! ## Exact-row and capture-avoidance canaries -/

namespace SubstitutionCanary

private def eightArguments : List (Term String Unit 0 0) :=
  [(.constant "a"), (.constant "b"), (.constant "c"), (.constant "d"),
    (.constant "e"), (.constant "f"), (.constant "g"), (.constant "h")]

/-- Row instantiation has no fixed arity bound: this eight-argument instance
is obtained by the same operation as every other finite length. -/
example :
    Substitution.instantiateRowFormula (Spine.ofTerms eightArguments)
        SyntaxCanary.exactRow =
      .atom (.constant "holds") (Spine.ofTerms eightArguments) := by
  rfl

/-- Substitution beneath an ordinary quantifier leaves its new bound variable
at index zero instead of capturing it. -/
private def outside : Term String Unit 0 0 := .constant "outside"

private def quantifiedOuter : Formula String Unit 1 0 :=
  .allObject
    (.atom (.var 0)
      (.singleton (.var 1)))

private def expectedQuantifiedOuter : Formula String Unit 0 0 :=
  .allObject
    (.atom (.var 0)
      (.singleton (.constant "outside")))

example :
    Substitution.formula (Substitution.replaceObject outside)
        quantifiedOuter = expectedQuantifiedOuter := by
  rfl

end SubstitutionCanary

end Mettapedia.Languages.SUMO.Native
