import Mettapedia.Languages.SUMO.Native.SourceElaboration

/-!
# Native elaboration of SUMO domain guards

SUMO uses `domain` and `domainSubclass` declarations to restrict variables
implicitly.  This module makes that source convention explicit in the native
formula:

* a universally bound object's missing guards imply its body;
* an existentially bound object's missing guards conjoin with its body;
* a `KappaFn` binder uses the same conjunctive discipline as existence;
* redundant superclass restrictions are removed using the source subclass
  graph;
* restrictions inherited through `subrelation` and the final-position rule
  for variable-arity operators are respected.

Uniform restrictions over a row spread become a native bounded universal over
the row's exact argument spine.  Every row spread additionally receives an
exact-tail judgment, while variables passed to a nonconstant operator receive
point judgments against that operator's denoted domain sequence.  No finite
arity is guessed during elaboration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.SUMO.Native.DomainGuardElaboration

open Mettapedia.Languages.SUMO.Native
open Mettapedia.Languages.SUMO.Native.SourceElaboration

inductive GuardIssueKind where
  | undischargedDependentDomain
  deriving DecidableEq, Repr

structure Result where
  sentence : Sentence String String
  issues : List GuardIssueKind
  deriving DecidableEq, Repr

private abbrev NativeTerm (ordinary rows : Nat) :=
  Term String String ordinary rows

private abbrev NativeSpine (ordinary rows : Nat) :=
  Spine String String ordinary rows

private abbrev NativeFormula (ordinary rows : Nat) :=
  Formula String String ordinary rows

private def directRequirement
    {ordinary rows : Nat}
    (signature : SourceSignature) (operator : Option String)
    (position : Option Nat) (target : Fin ordinary)
    (value : NativeTerm ordinary rows) : List DomainRestriction :=
  match operator, position, value with
  | some name, some argumentPosition, .var index =>
      if index = target then
        signature.argumentRestrictions name argumentPosition
      else []
  | _, _, _ => []

mutual
  private def requirementsTerm
      {ordinary rows : Nat}
      (signature : SourceSignature) (target : Fin ordinary) :
      NativeTerm ordinary rows -> List DomainRestriction
    | .var _ | .constant _ | .literal _ => []
    | .application operator arguments =>
        requirementsTerm signature target operator ++
          requirementsSpine signature
            (match operator with | .constant name => some name | _ => none)
            (some 1) target arguments
    | .quote body => requirementsFormula signature target body
    | .kappa body => requirementsFormula signature target.succ body

  private def requirementsSpine
      {ordinary rows : Nat}
      (signature : SourceSignature) (operator : Option String)
      (position : Option Nat) (target : Fin ordinary) :
      NativeSpine ordinary rows -> List DomainRestriction
    | .nil => []
    | .term value rest =>
        directRequirement signature operator position target value ++
          requirementsTerm signature target value ++
          requirementsSpine signature operator (position.map (· + 1)) target rest
    | .row _ rest =>
        let nextPosition := match operator, position with
          | some name, some firstPosition =>
              if (signature.uniformRowRestrictions name firstPosition).isSome then
                some firstPosition
              else none
          | _, _ => none
        requirementsSpine signature operator nextPosition target rest

  private def requirementsFormula
      {ordinary rows : Nat}
      (signature : SourceSignature) (target : Fin ordinary) :
      NativeFormula ordinary rows -> List DomainRestriction
    | .top | .bottom => []
    | .atom operator arguments =>
        requirementsTerm signature target operator ++
          requirementsSpine signature
            (match operator with | .constant name => some name | _ => none)
            (some 1) target arguments
    | .asserted value => requirementsTerm signature target value
    | .equal left right =>
        requirementsTerm signature target left ++
          requirementsTerm signature target right
    | .inOperatorDomain operator _ argument =>
        requirementsTerm signature target operator ++
          requirementsTerm signature target argument
    | .tailInOperatorDomain operator _ arguments =>
        requirementsTerm signature target operator ++
          requirementsSpine signature none none target arguments
    | .not body => requirementsFormula signature target body
    | .and left right | .or left right | .implies left right | .iff left right =>
        requirementsFormula signature target left ++
          requirementsFormula signature target right
    | .allInSpine arguments body =>
        requirementsSpine signature none (some 1) target arguments ++
          requirementsFormula signature target.succ body
    | .allObject body | .someObject body =>
        requirementsFormula signature target.succ body
    | .allRow body | .someRow body => requirementsFormula signature target body
end

private def directRowRequirement
    {rows : Nat}
    (signature : SourceSignature) (operator : Option String)
    (position : Option Nat) (target : Fin rows) (index : Fin rows) :
    List DomainRestriction :=
  match operator, position with
  | some name, some firstPosition =>
      if index = target then
        (signature.uniformRowRestrictions name firstPosition).getD []
      else []
  | _, _ => []

mutual
  private def requirementsRowTerm
      {ordinary rows : Nat}
      (signature : SourceSignature) (target : Fin rows) :
      NativeTerm ordinary rows -> List DomainRestriction
    | .var _ | .constant _ | .literal _ => []
    | .application operator arguments =>
        requirementsRowTerm signature target operator ++
          requirementsRowSpine signature
            (match operator with | .constant name => some name | _ => none)
            (some 1) target arguments
    | .quote body => requirementsRowFormula signature target body
    | .kappa body => requirementsRowFormula signature target body

  private def requirementsRowSpine
      {ordinary rows : Nat}
      (signature : SourceSignature) (operator : Option String)
      (position : Option Nat) (target : Fin rows) :
      NativeSpine ordinary rows -> List DomainRestriction
    | .nil => []
    | .term value rest =>
        requirementsRowTerm signature target value ++
          requirementsRowSpine signature operator (position.map (· + 1)) target rest
    | .row index rest =>
        let own := directRowRequirement signature operator position target index
        let nextPosition := match operator, position with
          | some name, some firstPosition =>
              if (signature.uniformRowRestrictions name firstPosition).isSome then
                some firstPosition
              else none
          | _, _ => none
        own ++ requirementsRowSpine signature operator nextPosition target rest

  private def requirementsRowFormula
      {ordinary rows : Nat}
      (signature : SourceSignature) (target : Fin rows) :
      NativeFormula ordinary rows -> List DomainRestriction
    | .top | .bottom => []
    | .atom operator arguments =>
        requirementsRowTerm signature target operator ++
          requirementsRowSpine signature
            (match operator with | .constant name => some name | _ => none)
            (some 1) target arguments
    | .asserted value => requirementsRowTerm signature target value
    | .equal left right =>
        requirementsRowTerm signature target left ++
          requirementsRowTerm signature target right
    | .inOperatorDomain operator _ argument =>
        requirementsRowTerm signature target operator ++
          requirementsRowTerm signature target argument
    | .tailInOperatorDomain operator _ arguments =>
        requirementsRowTerm signature target operator ++
          requirementsRowSpine signature none none target arguments
    | .not body => requirementsRowFormula signature target body
    | .and left right | .or left right | .implies left right | .iff left right =>
        requirementsRowFormula signature target left ++
          requirementsRowFormula signature target right
    | .allInSpine arguments body =>
        requirementsRowSpine signature none (some 1) target arguments ++
          requirementsRowFormula signature target body
    | .allObject body | .someObject body => requirementsRowFormula signature target body
    | .allRow body | .someRow body => requirementsRowFormula signature target.succ body
end

private def statedRestriction?
    {ordinary rows : Nat} (target : Fin ordinary) :
    NativeFormula ordinary rows -> Option DomainRestriction
  | .atom (.constant predicate)
      (.term (.var index) (.term (.constant className) .nil)) =>
      if index = target then
        if predicate = "instance" then
          some ⟨predicate, 1, .object, className⟩
        else if predicate = "subclass" then
          some ⟨predicate, 1, .class, className⟩
        else none
      else none
  | _ => none

private def statedConjunctiveRestrictions
    {ordinary rows : Nat} (target : Fin ordinary) :
    NativeFormula ordinary rows -> List DomainRestriction
  | .and left right =>
      statedConjunctiveRestrictions target left ++
        statedConjunctiveRestrictions target right
  | formula => (statedRestriction? target formula).toList

private inductive GuardPolarity
  | universal
  | conjunctive

private def statedRestrictions
    {ordinary rows : Nat} (polarity : GuardPolarity)
    (body : NativeFormula (ordinary + 1) rows) : List DomainRestriction :=
  match polarity, body with
  | .universal, .implies antecedent _ =>
      statedConjunctiveRestrictions 0 antecedent
  | .universal, _ => []
  | .conjunctive, formula => statedConjunctiveRestrictions 0 formula

private def missingRestrictions
    {ordinary rows : Nat}
    (signature : SourceSignature) (polarity : GuardPolarity)
    (body : NativeFormula (ordinary + 1) rows) : List DomainRestriction :=
  let required := signature.reduceRestrictions
    (requirementsFormula signature 0 body)
  let stated := statedRestrictions polarity body
  required.filter fun restriction =>
    !(stated.any fun existing => signature.restrictionCovers existing restriction)

private def statedRowRestriction?
    {ordinary rows : Nat} (target : Fin rows) :
    NativeFormula ordinary rows -> Option DomainRestriction
  | .allInSpine (.row index .nil) body =>
      if index = target then statedRestriction? 0 body else none
  | _ => none

private def statedRowConjunctiveRestrictions
    {ordinary rows : Nat} (target : Fin rows) :
    NativeFormula ordinary rows -> List DomainRestriction
  | .and left right =>
      statedRowConjunctiveRestrictions target left ++
        statedRowConjunctiveRestrictions target right
  | formula => (statedRowRestriction? target formula).toList

private def statedRowRestrictions
    {ordinary rows : Nat} (polarity : GuardPolarity)
    (body : NativeFormula ordinary (rows + 1)) : List DomainRestriction :=
  match polarity, body with
  | .universal, .implies antecedent _ =>
      statedRowConjunctiveRestrictions 0 antecedent
  | .universal, _ => []
  | .conjunctive, formula => statedRowConjunctiveRestrictions 0 formula

private def missingRowRestrictions
    {ordinary rows : Nat}
    (signature : SourceSignature) (polarity : GuardPolarity)
    (body : NativeFormula ordinary (rows + 1)) : List DomainRestriction :=
  let required := signature.reduceRestrictions
    (requirementsRowFormula signature 0 body)
  let stated := statedRowRestrictions polarity body
  required.filter fun restriction =>
    !(stated.any fun existing => signature.restrictionCovers existing restriction)

private def restrictionFormula
    {ordinary rows : Nat} (target : Fin ordinary)
    (restriction : DomainRestriction) : NativeFormula ordinary rows :=
  let predicate := match restriction.kind with
    | .object => "instance"
    | .class => "subclass"
  .atom (.constant predicate)
    (.term (.var target) (.term (.constant restriction.className) .nil))

private def rowRestrictionFormula
    {ordinary rows : Nat} (target : Fin rows)
    (restriction : DomainRestriction) : NativeFormula ordinary rows :=
  .allInSpine (.row target .nil) (restrictionFormula 0 restriction)

private def restrictionConjunction
    {ordinary rows : Nat} (target : Fin ordinary) :
    List DomainRestriction -> Option (NativeFormula ordinary rows)
  | [] => none
  | restriction :: rest =>
      let head := restrictionFormula target restriction
      match restrictionConjunction target rest with
      | none => some head
      | some tail => some (.and head tail)

private def rowRestrictionConjunction
    {ordinary rows : Nat} (target : Fin rows) :
    List DomainRestriction -> Option (NativeFormula ordinary rows)
  | [] => none
  | restriction :: rest =>
      let head := rowRestrictionFormula target restriction
      match rowRestrictionConjunction target rest with
      | none => some head
      | some tail => some (.and head tail)

private def implyMissing
    {ordinary rows : Nat} (restrictions : List DomainRestriction)
    (body : NativeFormula (ordinary + 1) rows) :
    NativeFormula (ordinary + 1) rows :=
  match restrictionConjunction 0 restrictions with
  | none => body
  | some guard => .implies guard body

private def conjoinMissing
    {ordinary rows : Nat} (restrictions : List DomainRestriction)
    (body : NativeFormula (ordinary + 1) rows) :
    NativeFormula (ordinary + 1) rows :=
  restrictions.foldr (fun restriction rest =>
    .and (restrictionFormula 0 restriction) rest) body

private def implyMissingRow
    {ordinary rows : Nat} (restrictions : List DomainRestriction)
    (body : NativeFormula ordinary (rows + 1)) :
    NativeFormula ordinary (rows + 1) :=
  match rowRestrictionConjunction 0 restrictions with
  | none => body
  | some guard => .implies guard body

private def conjoinMissingRow
    {ordinary rows : Nat} (restrictions : List DomainRestriction)
    (body : NativeFormula ordinary (rows + 1)) :
    NativeFormula ordinary (rows + 1) :=
  restrictions.foldr (fun restriction rest =>
    .and (rowRestrictionFormula 0 restriction) rest) body

mutual
  private def guardTerm
      {ordinary rows : Nat} (signature : SourceSignature) :
      NativeTerm ordinary rows -> NativeTerm ordinary rows
    | .var index => .var index
    | .constant name => .constant name
    | .literal value => .literal value
    | .application operator arguments =>
        .application (guardTerm signature operator) (guardSpine signature arguments)
    | .quote body => .quote (guardFormula signature body)
    | .kappa body =>
        let restrictions := missingRestrictions signature .conjunctive body
        .kappa (conjoinMissing restrictions (guardFormula signature body))

  private def guardSpine
      {ordinary rows : Nat} (signature : SourceSignature) :
      NativeSpine ordinary rows -> NativeSpine ordinary rows
    | .nil => .nil
    | .term value rest =>
        .term (guardTerm signature value) (guardSpine signature rest)
    | .row index rest => .row index (guardSpine signature rest)

  private def guardFormula
      {ordinary rows : Nat} (signature : SourceSignature) :
      NativeFormula ordinary rows -> NativeFormula ordinary rows
    | .top => .top
    | .bottom => .bottom
    | .atom operator arguments =>
        .atom (guardTerm signature operator) (guardSpine signature arguments)
    | .asserted value => .asserted (guardTerm signature value)
    | .equal left right =>
        .equal (guardTerm signature left) (guardTerm signature right)
    | .inOperatorDomain operator position argument =>
        .inOperatorDomain (guardTerm signature operator) position
          (guardTerm signature argument)
    | .tailInOperatorDomain operator firstPosition arguments =>
        .tailInOperatorDomain (guardTerm signature operator) firstPosition
          (guardSpine signature arguments)
    | .not body => .not (guardFormula signature body)
    | .and left right =>
        .and (guardFormula signature left) (guardFormula signature right)
    | .or left right =>
        .or (guardFormula signature left) (guardFormula signature right)
    | .implies left right =>
        .implies (guardFormula signature left) (guardFormula signature right)
    | .iff left right =>
        .iff (guardFormula signature left) (guardFormula signature right)
    | .allInSpine arguments body =>
        .allInSpine (guardSpine signature arguments) (guardFormula signature body)
    | .allObject body =>
        let restrictions := missingRestrictions signature .universal body
        .allObject (implyMissing restrictions (guardFormula signature body))
    | .someObject body =>
        let restrictions := missingRestrictions signature .conjunctive body
        .someObject (conjoinMissing restrictions (guardFormula signature body))
    | .allRow body =>
        let restrictions := missingRowRestrictions signature .universal body
        .allRow (implyMissingRow restrictions (guardFormula signature body))
    | .someRow body =>
        let restrictions := missingRowRestrictions signature .conjunctive body
        .someRow (conjoinMissingRow restrictions (guardFormula signature body))
end

/-! ## Denoted-operator domain guards

For a variable or computed operator, the applicable domain sequence is itself
denoted at runtime.  The following pass generates native domain judgments and
moves each one outward only across binders it does not mention.  The closest
referenced binder consumes the judgment using the polarity appropriate to its
quantifier. -/

private def guardFormulaConjunction
    {ordinary rows : Nat} :
    List (NativeFormula ordinary rows) -> Option (NativeFormula ordinary rows)
  | [] => none
  | head :: rest =>
      match guardFormulaConjunction rest with
      | none => some head
      | some tail => some (.and head tail)

private def implyFormulaGuards
    {ordinary rows : Nat} (guards : List (NativeFormula ordinary rows))
    (body : NativeFormula ordinary rows) : NativeFormula ordinary rows :=
  match guardFormulaConjunction guards.eraseDups with
  | none => body
  | some guard => .implies guard body

private def conjoinFormulaGuards
    {ordinary rows : Nat} (guards : List (NativeFormula ordinary rows))
    (body : NativeFormula ordinary rows) : NativeFormula ordinary rows :=
  guards.eraseDups.foldr Formula.and body

private def dropNewestObjectFormula?
    {ordinary rows : Nat}
    (body : NativeFormula (ordinary + 1) rows) :
    Option (NativeFormula ordinary rows) :=
  PartialRenaming.formula
    (Fin.cases (none : Option (Fin ordinary)) (fun index => some index))
    (fun index => some index) body

private def dropNewestRowFormula?
    {ordinary rows : Nat}
    (body : NativeFormula ordinary (rows + 1)) :
    Option (NativeFormula ordinary rows) :=
  PartialRenaming.formula
    (fun index => some index)
    (Fin.cases (none : Option (Fin rows)) (fun index => some index)) body

private structure ObjectGuardSplit (ordinary rows : Nat) where
  retained : List (NativeFormula (ordinary + 1) rows)
  escaped : List (NativeFormula ordinary rows)

private def splitObjectGuards
    {ordinary rows : Nat} :
    List (NativeFormula (ordinary + 1) rows) -> ObjectGuardSplit ordinary rows
  | [] => ⟨[], []⟩
  | guard :: rest =>
      let tail := splitObjectGuards rest
      match dropNewestObjectFormula? guard with
      | some escaped => ⟨tail.retained, escaped :: tail.escaped⟩
      | none => ⟨guard :: tail.retained, tail.escaped⟩

private structure RowGuardSplit (ordinary rows : Nat) where
  retained : List (NativeFormula ordinary (rows + 1))
  escaped : List (NativeFormula ordinary rows)

private def splitRowGuards
    {ordinary rows : Nat} :
    List (NativeFormula ordinary (rows + 1)) -> RowGuardSplit ordinary rows
  | [] => ⟨[], []⟩
  | guard :: rest =>
      let tail := splitRowGuards rest
      match dropNewestRowFormula? guard with
      | some escaped => ⟨tail.retained, escaped :: tail.escaped⟩
      | none => ⟨guard :: tail.retained, tail.escaped⟩

private structure DenotedDomainTermResult (ordinary rows : Nat) where
  value : NativeTerm ordinary rows
  pendingGuards : List (NativeFormula ordinary rows)

private structure DenotedDomainSpineResult (ordinary rows : Nat) where
  value : NativeSpine ordinary rows
  pendingGuards : List (NativeFormula ordinary rows)

private structure DenotedDomainFormulaResult (ordinary rows : Nat) where
  value : NativeFormula ordinary rows
  pendingGuards : List (NativeFormula ordinary rows)

/-- Generate point guards for direct variables under a denoted operator.  The
first row occurrence instead receives one exact-tail guard, which also covers
every trailing argument and the operator's arity condition. -/
private def operatorSpineGuards
    {ordinary rows : Nat} (operator : NativeTerm ordinary rows) :
    Nat -> NativeSpine ordinary rows -> List (NativeFormula ordinary rows)
  | _, .nil => []
  | position, .term argument rest =>
      let point := match operator, argument with
        | .constant _, _ => []
        | _, .var _ => [.inOperatorDomain operator position argument]
        | _, _ => []
      point ++ operatorSpineGuards operator (position + 1) rest
  | position, .row index rest =>
      [.tailInOperatorDomain operator position (.row index rest)]

mutual
  private def insertDenotedTermGuards
      {ordinary rows : Nat} :
      NativeTerm ordinary rows -> DenotedDomainTermResult ordinary rows
    | .var index => ⟨.var index, []⟩
    | .constant name => ⟨.constant name, []⟩
    | .literal value => ⟨.literal value, []⟩
    | .application operator arguments =>
        let guardedOperator := insertDenotedTermGuards operator
        let guardedArguments := insertDenotedSpineGuards arguments
        let ownGuards := operatorSpineGuards guardedOperator.value 0
          guardedArguments.value
        ⟨.application guardedOperator.value guardedArguments.value,
          (guardedOperator.pendingGuards ++ guardedArguments.pendingGuards ++
            ownGuards).eraseDups⟩
    | .quote body =>
        let guardedBody := insertDenotedFormulaGuards body
        ⟨.quote guardedBody.value, guardedBody.pendingGuards⟩
    | .kappa body =>
        let guardedBody := insertDenotedFormulaGuards body
        let split := splitObjectGuards guardedBody.pendingGuards
        ⟨.kappa (conjoinFormulaGuards split.retained guardedBody.value),
          split.escaped⟩

  private def insertDenotedSpineGuards
      {ordinary rows : Nat} :
      NativeSpine ordinary rows -> DenotedDomainSpineResult ordinary rows
    | .nil => ⟨.nil, []⟩
    | .term value rest =>
        let guardedValue := insertDenotedTermGuards value
        let guardedRest := insertDenotedSpineGuards rest
        ⟨.term guardedValue.value guardedRest.value,
          (guardedValue.pendingGuards ++ guardedRest.pendingGuards).eraseDups⟩
    | .row index rest =>
        let guardedRest := insertDenotedSpineGuards rest
        ⟨.row index guardedRest.value, guardedRest.pendingGuards⟩

  private def insertDenotedFormulaGuards
      {ordinary rows : Nat} :
      NativeFormula ordinary rows -> DenotedDomainFormulaResult ordinary rows
    | .top => ⟨.top, []⟩
    | .bottom => ⟨.bottom, []⟩
    | .atom operator arguments =>
        let guardedOperator := insertDenotedTermGuards operator
        let guardedArguments := insertDenotedSpineGuards arguments
        let ownGuards := operatorSpineGuards guardedOperator.value 0
          guardedArguments.value
        ⟨.atom guardedOperator.value guardedArguments.value,
          (guardedOperator.pendingGuards ++ guardedArguments.pendingGuards ++
            ownGuards).eraseDups⟩
    | .asserted value =>
        let guardedValue := insertDenotedTermGuards value
        ⟨.asserted guardedValue.value, guardedValue.pendingGuards⟩
    | .equal left right =>
        let guardedLeft := insertDenotedTermGuards left
        let guardedRight := insertDenotedTermGuards right
        ⟨.equal guardedLeft.value guardedRight.value,
          (guardedLeft.pendingGuards ++ guardedRight.pendingGuards).eraseDups⟩
    | .inOperatorDomain operator position argument =>
        let guardedOperator := insertDenotedTermGuards operator
        let guardedArgument := insertDenotedTermGuards argument
        ⟨.inOperatorDomain guardedOperator.value position guardedArgument.value,
          (guardedOperator.pendingGuards ++
            guardedArgument.pendingGuards).eraseDups⟩
    | .tailInOperatorDomain operator firstPosition arguments =>
        let guardedOperator := insertDenotedTermGuards operator
        let guardedArguments := insertDenotedSpineGuards arguments
        ⟨.tailInOperatorDomain guardedOperator.value firstPosition
            guardedArguments.value,
          (guardedOperator.pendingGuards ++
            guardedArguments.pendingGuards).eraseDups⟩
    | .not body =>
        let guardedBody := insertDenotedFormulaGuards body
        ⟨.not guardedBody.value, guardedBody.pendingGuards⟩
    | .and left right =>
        let guardedLeft := insertDenotedFormulaGuards left
        let guardedRight := insertDenotedFormulaGuards right
        ⟨.and guardedLeft.value guardedRight.value,
          (guardedLeft.pendingGuards ++ guardedRight.pendingGuards).eraseDups⟩
    | .or left right =>
        let guardedLeft := insertDenotedFormulaGuards left
        let guardedRight := insertDenotedFormulaGuards right
        ⟨.or guardedLeft.value guardedRight.value,
          (guardedLeft.pendingGuards ++ guardedRight.pendingGuards).eraseDups⟩
    | .implies left right =>
        let guardedLeft := insertDenotedFormulaGuards left
        let guardedRight := insertDenotedFormulaGuards right
        ⟨.implies guardedLeft.value guardedRight.value,
          (guardedLeft.pendingGuards ++ guardedRight.pendingGuards).eraseDups⟩
    | .iff left right =>
        let guardedLeft := insertDenotedFormulaGuards left
        let guardedRight := insertDenotedFormulaGuards right
        ⟨.iff guardedLeft.value guardedRight.value,
          (guardedLeft.pendingGuards ++ guardedRight.pendingGuards).eraseDups⟩
    | .allInSpine arguments body =>
        let guardedArguments := insertDenotedSpineGuards arguments
        let guardedBody := insertDenotedFormulaGuards body
        let split := splitObjectGuards guardedBody.pendingGuards
        ⟨.allInSpine guardedArguments.value
            (implyFormulaGuards split.retained guardedBody.value),
          (guardedArguments.pendingGuards ++ split.escaped).eraseDups⟩
    | .allObject body =>
        let guardedBody := insertDenotedFormulaGuards body
        let split := splitObjectGuards guardedBody.pendingGuards
        ⟨.allObject (implyFormulaGuards split.retained guardedBody.value),
          split.escaped⟩
    | .someObject body =>
        let guardedBody := insertDenotedFormulaGuards body
        let split := splitObjectGuards guardedBody.pendingGuards
        ⟨.someObject (conjoinFormulaGuards split.retained guardedBody.value),
          split.escaped⟩
    | .allRow body =>
        let guardedBody := insertDenotedFormulaGuards body
        let split := splitRowGuards guardedBody.pendingGuards
        ⟨.allRow (implyFormulaGuards split.retained guardedBody.value),
          split.escaped⟩
    | .someRow body =>
        let guardedBody := insertDenotedFormulaGuards body
        let split := splitRowGuards guardedBody.pendingGuards
        ⟨.someRow (conjoinFormulaGuards split.retained guardedBody.value),
          split.escaped⟩
end

/-- Insert static ontology guards and denoted-operator domain judgments.  A
closed sentence should discharge every generated judgment at one of its own
binders; an unexpected survivor is retained as an explicit assembly issue. -/
def apply (signature : SourceSignature) (sentence : Sentence String String) :
    Result :=
  let guarded := insertDenotedFormulaGuards (guardFormula signature sentence)
  { sentence := guarded.value
    issues := if guarded.pendingGuards.isEmpty then []
      else [.undischargedDependentDomain] }

/-- Elaborate one source sentence, then make its implicit domain guards
explicit in the native SUMO formula. -/
def elaborateSentence
    (signature : SourceSignature) (source : KIF.Term) :
    Except ElaborationIssue Result := do
  let sentence <- SourceElaboration.elaborateSentence signature source
  pure (apply signature sentence)

end Mettapedia.Languages.SUMO.Native.DomainGuardElaboration
