import Mettapedia.Data.Option.Constructor
import Mettapedia.Data.List.FiniteLookup
import Mettapedia.GSLT.LanguageDef.NativeOpsSyntax

/-!
# Admission of typed native expressions and lexical blocks

The checks follow the operational source compiler's required fragment.  An
address of a field of a value record requires a genuine location for the
record; a reference record permits an evaluated base.  Blocks extend local
scope only within the block, and declarations cannot shadow an active name.
Switches do not create a loop scope for `break` and `continue`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

def lookupVariable (scope : Scope) (name : String) : Option NativeType :=
  (scope.find? (fun binding => binding.1 == name)).map Prod.snd

mutual
  def inferExpr (interface : Interface) (scope : Scope) : Expr → Option NativeType
    | .word _ => some .word
    | .byte _ => some .byte
    | .bool _ => some .bool
    | .variable name => lookupVariable scope name
    | .zero type => if validType interface type true then some type else none
    | .null type => match type with
        | .ref _ => if validType interface type false then some type else none
        | _ => none
    | .new type => match type with
        | .ref _ => none
        | _ => if validType interface type true then some (.ref type) else none
    | .newArray element count => do
        if !(validType interface element true) then none else
          let countType ← inferExpr interface scope count
          if countType = .word then some (.array element) else none
    | .field base field => do
        let baseType ← inferExpr interface scope base
        match baseType with
        | .named record | .ref (.named record) => lookupField interface record field
        | _ => none
    | .index array index => do
        let arrayType ← inferExpr interface scope array
        let indexType ← inferExpr interface scope index
        match arrayType with
        | .array element => if indexType = .word then some element else none
        | _ => none
    | .length array => do
        let arrayType ← inferExpr interface scope array
        match arrayType with
        | .array _ => some .word
        | _ => none
    | .slice array start count => do
        let arrayType ← inferExpr interface scope array
        let startType ← inferExpr interface scope start
        let countType ← inferExpr interface scope count
        match arrayType with
        | .array _ => if startType = .word ∧ countType = .word then some arrayType else none
        | _ => none
    | .address location => (inferLocation interface scope location).map NativeType.ref
    | .load reference => do
        let referenceType ← inferExpr interface scope reference
        match referenceType with
        | .ref element => if validType interface element true then some element else none
        | _ => none
    | .call name arguments => do
        let header ← lookupFunction interface name
        let argumentsTypes ← inferExprList interface scope arguments
        if argumentsTypes = header.parameters.map Parameter.type then some header.result else none
    | .unary operation operand => do
        let type ← inferExpr interface scope operand
        unaryType operation type
    | .binary operation left right => do
        let leftType ← inferExpr interface scope left
        let rightType ← inferExpr interface scope right
        if leftType = rightType then binaryType operation leftType else none
  termination_by expression => 2 * sizeOf expression
  decreasing_by
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega

  def inferExprList (interface : Interface) (scope : Scope) : List Expr → Option (List NativeType)
    | [] => some []
    | expression :: rest => do
        let type ← inferExpr interface scope expression
        let tail ← inferExprList interface scope rest
        pure (type :: tail)
  termination_by expressions => 2 * sizeOf expressions
  decreasing_by
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega

  def inferLocation (interface : Interface) (scope : Scope) : Expr → Option NativeType
    | .variable name => lookupVariable scope name
    | .field base field => do
        let baseType ← inferExpr interface scope base
        match baseType with
        | .ref (.named record) => lookupField interface record field
        | .named record => do
            let _ ← inferLocation interface scope base
            lookupField interface record field
        | _ => none
    | .index array index => inferExpr interface scope (.index array index)
    | .load reference => inferExpr interface scope (.load reference)
    | _ => none
  termination_by expression => 2 * sizeOf expression + 1
  decreasing_by
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega
end

mutual
  def checkBlock (interface : Interface) (result : NativeType) (loops : Nat)
      (scope : Scope) : List Statement → Option Scope
    | [] => some scope
    | statement :: rest => do
        let next ← checkStatement interface result loops scope statement
        checkBlock interface result loops next rest
  termination_by body => sizeOf body
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def checkStatement (interface : Interface) (result : NativeType) (loops : Nat)
      (scope : Scope) : Statement → Option Scope
    | .declare name type initializer => do
        if (lookupVariable scope name).isSome || !(validType interface type true) then none else
          let actual ← inferExpr interface scope initializer
          if actual = type then some ((name, type) :: scope) else none
    | .set location value => do
        let locationType ← inferLocation interface scope location
        let valueType ← inferExpr interface scope value
        if locationType = valueType then some scope else none
    | .branch condition thenBody elseBody => do
        let conditionType ← inferExpr interface scope condition
        if conditionType ≠ .bool then none else
          let _ ← checkBlock interface result loops scope thenBody
          let _ ← checkBlock interface result loops scope elseBody
          some scope
    | .while condition body => do
        let conditionType ← inferExpr interface scope condition
        if conditionType ≠ .bool then none else
          let _ ← checkBlock interface result (loops + 1) scope body
          some scope
    | .switch selector cases default => do
        let selectorType ← inferExpr interface scope selector
        if selectorType ≠ .word ∨ ¬(cases.map Prod.fst).Nodup then none else
          let _ ← checkCases interface result loops scope cases
          let _ ← checkBlock interface result loops scope default
          some scope
    | .break | .continue => if loops = 0 then none else some scope
    | .effect expression => do
        let _ ← inferExpr interface scope expression
        some scope
    | .free expression => do
        let type ← inferExpr interface scope expression
        match type with
        | .ref element | .array element =>
            if validType interface element true then some scope else none
        | _ => none
    | .return none => if result = .unit then some scope else none
    | .return (some expression) => do
        let type ← inferExpr interface scope expression
        if type = result ∧ result ≠ .unit then some scope else none
    | .block body => do
        let _ ← checkBlock interface result loops scope body
        some scope
  termination_by statement => sizeOf statement
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def checkCases (interface : Interface) (result : NativeType) (loops : Nat)
      (scope : Scope) : List (NativeWord64.Word × List Statement) → Option Unit
    | [] => some ()
    | (_, body) :: rest => do
        let _ ← checkBlock interface result loops scope body
        checkCases interface result loops scope rest
  termination_by cases => sizeOf cases
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  def returnsBlock : List Statement → Bool
    | [] => false
    | statement :: rest => returnsStatement statement || returnsBlock rest
  termination_by body => sizeOf body
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def returnsStatement : Statement → Bool
    | .return _ => true
    | .block body => returnsBlock body
    | .branch _ thenBody elseBody => returnsBlock thenBody && returnsBlock elseBody
    | .switch _ cases default => returnsBlock default && returnsCases cases
    | _ => false
  termination_by statement => sizeOf statement
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def returnsCases : List (NativeWord64.Word × List Statement) → Bool
    | [] => true
    | (_, body) :: rest => returnsBlock body && returnsCases rest
  termination_by cases => sizeOf cases
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def checkFunction (interface : Interface) (function : Function) : Bool :=
  let header := function.header
  (header.parameters.map Parameter.name).Nodup &&
    header.parameters.all (fun parameter => validType interface parameter.type true) &&
    validType interface header.result (header.result != .unit) &&
    (checkBlock interface header.result 0
      (header.parameters.map fun parameter => (parameter.name, parameter.type)) function.body).isSome &&
    (header.result == .unit || returnsBlock function.body)

theorem check_function_entry_contract {interface : Interface} {function : Function}
    (checked : checkFunction interface function = true) :
    (function.header.parameters.map Parameter.name).Nodup ∧
      (checkBlock interface function.header.result 0
        (function.header.parameters.map fun parameter => (parameter.name, parameter.type))
        function.body).isSome = true ∧
      (function.header.result = .unit ∨ returnsBlock function.body = true) := by
  simp only [checkFunction, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at checked
  rcases checked with ⟨⟨⟨⟨distinct, _validParameters⟩, _validResult⟩, body⟩, returned⟩
  exact ⟨distinct, body, returned⟩

/-- Two lexical presentations agree when every name has the same declared
    type. Occurrence order and duplicate-name priority are retained by lookup. -/
def ScopeLookupAgreement (left right : Scope) : Prop :=
  ∀ name, lookupVariable left name = lookupVariable right name

theorem ScopeLookupAgreement.refl (scope : Scope) : ScopeLookupAgreement scope scope :=
  fun _ => rfl

theorem ScopeLookupAgreement.symm {left right : Scope} (same : ScopeLookupAgreement left right) :
    ScopeLookupAgreement right left := fun name => (same name).symm

theorem ScopeLookupAgreement.trans {first middle last : Scope}
    (one : ScopeLookupAgreement first middle) (two : ScopeLookupAgreement middle last) :
    ScopeLookupAgreement first last := fun name => (one name).trans (two name)

theorem ScopeLookupAgreement.cons {left right : Scope} (same : ScopeLookupAgreement left right)
    (name : String) (type : NativeType) :
    ScopeLookupAgreement ((name, type) :: left) ((name, type) :: right) := by
  intro query
  simp only [lookupVariable, List.find?_cons]
  split
  · rfl
  · exact same query

/-- Admission's distinct-name condition permits reversal of the lexical
    presentation. Without it, reversal can change which declaration wins. -/
theorem scope_lookup_agreement_reverse {scope : Scope}
    (distinct : (scope.map Prod.fst).Nodup) : ScopeLookupAgreement scope.reverse scope := by
  intro name
  apply congrArg (Option.map Prod.snd)
    (List.find?_reverse_of_unique_matches scope (fun binding => binding.1 == name) ?_)
  intro a ma b mb yesA yesB
  apply List.inj_on_of_nodup_map distinct ma mb
  simp only [beq_iff_eq] at yesA yesB
  exact yesA.trans yesB.symm

mutual
  theorem infer_expr_scope_agreement {left right : Scope}
      (same : ScopeLookupAgreement left right) (interface : Interface) (expression : Expr) :
      inferExpr interface left expression = inferExpr interface right expression := by
    cases expression with
    | word _ | byte _ | bool _ | zero _ => simp only [inferExpr]
    | null type | «new» type => cases type <;> simp only [inferExpr]
    | «variable» name => simpa only [inferExpr] using same name
    | newArray _ count =>
        simp only [inferExpr, infer_expr_scope_agreement same interface count]
    | field base _ =>
        simp only [inferExpr, infer_expr_scope_agreement same interface base]
    | index array index =>
        simp only [inferExpr, infer_expr_scope_agreement same interface array,
          infer_expr_scope_agreement same interface index]
    | length array =>
        simp only [inferExpr, infer_expr_scope_agreement same interface array]
    | slice array start count =>
        simp only [inferExpr, infer_expr_scope_agreement same interface array,
          infer_expr_scope_agreement same interface start, infer_expr_scope_agreement same interface count]
    | address location =>
        simp only [inferExpr, infer_location_scope_agreement same interface location]
    | load reference =>
        simp only [inferExpr, infer_expr_scope_agreement same interface reference]
    | call _ arguments =>
        simp only [inferExpr, infer_expr_list_scope_agreement same interface arguments]
    | unary _ operand =>
        simp only [inferExpr, infer_expr_scope_agreement same interface operand]
    | binary _ first second =>
        simp only [inferExpr, infer_expr_scope_agreement same interface first,
          infer_expr_scope_agreement same interface second]
  termination_by 2 * sizeOf expression
  decreasing_by
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega

  theorem infer_expr_list_scope_agreement {left right : Scope}
      (same : ScopeLookupAgreement left right) (interface : Interface) (expressions : List Expr) :
      inferExprList interface left expressions = inferExprList interface right expressions := by
    cases expressions with
    | nil => simp only [inferExprList]
    | cons first rest =>
        simp only [inferExprList, infer_expr_scope_agreement same interface first,
          infer_expr_list_scope_agreement same interface rest]
  termination_by 2 * sizeOf expressions
  decreasing_by
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega

  theorem infer_location_scope_agreement {left right : Scope}
      (same : ScopeLookupAgreement left right) (interface : Interface) (expression : Expr) :
      inferLocation interface left expression = inferLocation interface right expression := by
    cases expression with
    | «variable» name => simpa only [inferLocation] using same name
    | field base _ =>
        simp only [inferLocation, infer_expr_scope_agreement same interface base,
          infer_location_scope_agreement same interface base]
    | index array index => simpa only [inferLocation] using infer_expr_scope_agreement same interface (.index array index)
    | load reference => simpa only [inferLocation] using infer_expr_scope_agreement same interface (.load reference)
    | word _ | byte _ | bool _ | zero _ | null _ | «new» _ | newArray _ _ | length _ | slice _ _ _ | address _ | call _ _ | unary _ _ | binary _ _ _ => first | rfl | simp only [inferLocation]
  termination_by 2 * sizeOf expression + 1
  decreasing_by
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega
end

mutual
  /-- Admission compares the actual extended scopes on success, and preserves
      refusal when either lexical presentation refuses the authored block. -/
  theorem check_block_scope_agreement {left right : Scope}
      (same : ScopeLookupAgreement left right) (interface : Interface) (result : NativeType)
      (loops : Nat) (body : List Statement) :
      Option.Rel ScopeLookupAgreement (checkBlock interface result loops left body)
        (checkBlock interface result loops right body) := by
    cases body with
    | nil => simpa only [checkBlock] using Option.Rel.some same
    | cons statement rest =>
        simp only [checkBlock]
        apply (check_statement_scope_agreement same interface result loops statement).bind
        intro nextLeft nextRight nextSame
        exact check_block_scope_agreement nextSame interface result loops rest
  termination_by sizeOf body
  decreasing_by
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega

  theorem check_statement_scope_agreement {left right : Scope}
      (same : ScopeLookupAgreement left right) (interface : Interface) (result : NativeType)
      (loops : Nat) (statement : Statement) :
      Option.Rel ScopeLookupAgreement (checkStatement interface result loops left statement)
        (checkStatement interface result loops right statement) := by
    cases statement with
    | declare name type initializer =>
        simp only [checkStatement, same name, infer_expr_scope_agreement same interface initializer]
        split
        · exact .none
        · apply (Option.Rel.of_eq rfl).bind
          intro actualLeft actualRight equal
          cases equal
          split
          · exact .some (same.cons name type)
          · exact .none
    | set location value =>
        simp only [checkStatement, infer_location_scope_agreement same interface location,
          infer_expr_scope_agreement same interface value]
        apply (Option.Rel.of_eq rfl).bind
        intro typeLeft typeRight equal
        cases equal
        apply (Option.Rel.of_eq rfl).bind
        intro valueLeft valueRight equal
        cases equal
        split
        · exact .some same
        · exact .none
    | branch condition whenTrue whenFalse =>
        simp only [checkStatement, infer_expr_scope_agreement same interface condition]
        apply (Option.Rel.of_eq rfl).bind
        intro typeLeft typeRight equal
        cases equal
        split
        · exact .none
        · apply (check_block_scope_agreement same interface result loops whenTrue).bind
          intro _ _ _
          apply (check_block_scope_agreement same interface result loops whenFalse).bind
          intro _ _ _
          exact .some same
    | «while» condition body =>
        simp only [checkStatement, infer_expr_scope_agreement same interface condition]
        apply (Option.Rel.of_eq rfl).bind
        intro typeLeft typeRight equal
        cases equal
        split
        · exact .none
        · apply (check_block_scope_agreement same interface result (loops + 1) body).bind
          intro _ _ _
          exact .some same
    | switch selector cases otherwise =>
        simp only [checkStatement, infer_expr_scope_agreement same interface selector]
        apply (Option.Rel.of_eq rfl).bind
        intro typeLeft typeRight equal
        cases equal
        split
        · exact .none
        · apply (check_cases_scope_agreement same interface result loops cases).bind
          intro _ _ _
          apply (check_block_scope_agreement same interface result loops otherwise).bind
          intro _ _ _
          exact .some same
    | «break» | «continue» =>
        simp only [checkStatement]
        split
        · exact .none
        · exact .some same
    | effect expression =>
        simp only [checkStatement, infer_expr_scope_agreement same interface expression]
        apply (Option.Rel.of_eq rfl).bind
        intro _ _ _
        exact .some same
    | free expression =>
        simp only [checkStatement, infer_expr_scope_agreement same interface expression]
        apply (Option.Rel.of_eq rfl).bind
        intro typeLeft typeRight equal
        cases equal
        cases typeLeft <;> dsimp only <;> first
          | exact .none
          | (split; exact .some same; exact .none)
    | «return» expression =>
        cases expression with
        | none =>
            simp only [checkStatement]
            split
            · exact .some same
            · exact .none
        | some expression =>
            simp only [checkStatement, infer_expr_scope_agreement same interface expression]
            apply (Option.Rel.of_eq rfl).bind
            intro typeLeft typeRight equal
            cases equal
            split
            · exact .some same
            · exact .none
    | block body =>
        simp only [checkStatement]
        apply (check_block_scope_agreement same interface result loops body).bind
        intro _ _ _
        exact .some same
  termination_by sizeOf statement
  decreasing_by
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega

  theorem check_cases_scope_agreement {left right : Scope}
      (same : ScopeLookupAgreement left right) (interface : Interface) (result : NativeType)
      (loops : Nat) (cases : List (NativeWord64.Word × List Statement)) :
      Option.Rel Eq (checkCases interface result loops left cases)
        (checkCases interface result loops right cases) := by
    cases cases with
    | nil => simpa only [checkCases] using Option.Rel.some rfl
    | cons first rest =>
        rcases first with ⟨_, body⟩
        simp only [checkCases]
        apply (check_block_scope_agreement same interface result loops body).bind
        intro _ _ _
        exact check_cases_scope_agreement same interface result loops rest
  termination_by sizeOf cases
  decreasing_by
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega
end

end Mettapedia.GSLT.LanguageDef.NativeOps
