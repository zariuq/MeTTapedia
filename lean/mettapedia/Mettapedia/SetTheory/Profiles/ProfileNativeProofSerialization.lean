import Mettapedia.SetTheory.Profiles.ProfileNativeProofCompilation
import Mettapedia.SetTheory.Profiles.CommonCoreSyntax
import Mettapedia.Logic.HOL.Syntax.DecidableEq
import Mettapedia.Logic.HOL.Soundness

/-!
# Typed recovery of retained material proof data

The raw carrier contains finite constructor data, object-variable indices and
hypothesis positions. Its decoder constructs actual retained HOL proofs after
checking every type, context and conclusion. The native rendering and the C
reader are distinct boundaries. Structural equality proof forms require an
explicit native logical-equality bundle. Runtime qualification of that
reader is separate from kernel recovery of the annotated constructor data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.SetTheory.Profiles.ProfileNativeProofSerialization

open Mettapedia.Logic
open HOL
open ProfileNativeProofCompilation
open Mettapedia.TypeTheory.MaterialSets.Hypersets

instance : DecidableEq MaterialBase := fun a b => by
  cases a
  cases b
  exact .isTrue rfl

instance (type : Ty MaterialBase) : DecidableEq (MaterialConstant type) := fun a b => by
  cases a
  cases b
  exact .isTrue rfl

deriving instance Repr for MaterialBase

abbrev ObjectType := Ty MaterialBase
abbrev ObjectContext := Ctx MaterialBase

def variableIndex {context : ObjectContext} {type : ObjectType} : Var context type → Nat
  | .vz => 0
  | .vs previous => variableIndex previous + 1

def decodeVariable : (context : ObjectContext) → (type : ObjectType) → Nat →
    Option (Var context type)
  | [], _, _ => none
  | first :: _rest, type, 0 =>
      if same : first = type then some (same ▸ Var.vz) else none
  | _ :: rest, type, index+1 => Var.vs <$> decodeVariable rest type index

@[simp] theorem decodeVariable_encode {context : ObjectContext} {type : ObjectType}
    (slot : Var context type) :
    decodeVariable context type (variableIndex slot) = some slot := by
  induction slot with
  | vz => simp [decodeVariable, variableIndex]
  | vs previous ih => simp [decodeVariable, variableIndex, ih]

inductive RawTerm where
  | variable (index : Nat)
  | member
  | app (domain : ObjectType) (function argument : RawTerm)
  | lam (body : RawTerm)
  | top | bottom
  | both (left right : RawTerm)
  | either (left right : RawTerm)
  | imply (left right : RawTerm)
  | negative (body : RawTerm)
  | equal (type : ObjectType) (left right : RawTerm)
  | all (domain : ObjectType) (body : RawTerm)
  | exist (domain : ObjectType) (body : RawTerm)
  deriving DecidableEq, Repr

def encodeTerm {context : ObjectContext} {type : ObjectType} :
    Term MaterialConstant context type → RawTerm
  | .var slot => .variable (variableIndex slot)
  | .const .member => .member
  | @Term.app _ _ _ domain _ function argument =>
      .app domain (encodeTerm function) (encodeTerm argument)
  | .lam body => .lam (encodeTerm body)
  | .top => .top
  | .bot => .bottom
  | .and left right => .both (encodeTerm left) (encodeTerm right)
  | .or left right => .either (encodeTerm left) (encodeTerm right)
  | .imp left right => .imply (encodeTerm left) (encodeTerm right)
  | .not body => .negative (encodeTerm body)
  | @Term.eq _ _ _ carrier left right => .equal carrier (encodeTerm left) (encodeTerm right)
  | @Term.all _ _ domain _ body => .all domain (encodeTerm body)
  | @Term.ex _ _ domain _ body => .exist domain (encodeTerm body)

def RawTerm.depth : RawTerm → Nat
  | .variable _ | .member | .top | .bottom => 1
  | .app _ left right | .both left right | .either left right | .imply left right |
      .equal _ left right => max left.depth right.depth + 1
  | .lam body | .negative body | .all _ body | .exist _ body => body.depth + 1

def decodeTerm : Nat → (context : ObjectContext) → (type : ObjectType) → RawTerm →
    Option (Term MaterialConstant context type)
  | 0, _, _, _ => none
  | fuel+1, context, type, raw =>
    match raw with
    | .variable index => Term.var <$> decodeVariable context type index
    | .member =>
        if same : (.arr setType (.arr setType .prop) : ObjectType) = type then
          some (same ▸ Term.const MaterialConstant.member)
        else none
    | .app domain function argument => do
        return .app (← decodeTerm fuel context (.arr domain type) function)
          (← decodeTerm fuel context domain argument)
    | .lam body => match type with
        | .arr domain codomain => Term.lam <$> decodeTerm fuel (domain :: context) codomain body
        | _ => none
    | .top => match type with
        | .prop => some .top
        | _ => none
    | .bottom => match type with
        | .prop => some .bot
        | _ => none
    | .both left right => match type with
        | .prop => do
            return .and (← decodeTerm fuel context .prop left) (← decodeTerm fuel context .prop right)
        | _ => none
    | .either left right => match type with
        | .prop => do
            return .or (← decodeTerm fuel context .prop left) (← decodeTerm fuel context .prop right)
        | _ => none
    | .imply left right => match type with
        | .prop => do
            return .imp (← decodeTerm fuel context .prop left) (← decodeTerm fuel context .prop right)
        | _ => none
    | .negative body => match type with
        | .prop => Term.not <$> decodeTerm fuel context .prop body
        | _ => none
    | .equal carrier left right => match type with
        | .prop => do
            return .eq (← decodeTerm fuel context carrier left) (← decodeTerm fuel context carrier right)
        | _ => none
    | .all domain body => match type with
        | .prop => Term.all <$> decodeTerm fuel (domain :: context) .prop body
        | _ => none
    | .exist domain body => match type with
        | .prop => Term.ex <$> decodeTerm fuel (domain :: context) .prop body
        | _ => none

theorem decodeTerm_encode {context : ObjectContext} {type : ObjectType}
    (term : Term MaterialConstant context type) (fuel : Nat)
    (enough : (encodeTerm term).depth ≤ fuel) :
    decodeTerm fuel context type (encodeTerm term) = some term := by
  induction term generalizing fuel with
  | var slot => cases fuel <;> simp_all [encodeTerm, RawTerm.depth, decodeTerm]
  | const constant =>
      cases constant
      change 1 ≤ fuel at enough
      cases fuel with
      | zero => omega
      | succ fuel => rfl
  | top => cases fuel <;> simp_all [encodeTerm, RawTerm.depth, decodeTerm]
  | bot => cases fuel <;> simp_all [encodeTerm, RawTerm.depth, decodeTerm]
  | app function argument functionIH argumentIH =>
      cases fuel with
      | zero => simp [encodeTerm, RawTerm.depth] at enough
      | succ fuel =>
          have first : (encodeTerm function).depth ≤ fuel := by
            simp only [encodeTerm, RawTerm.depth] at enough; omega
          have second : (encodeTerm argument).depth ≤ fuel := by
            simp only [encodeTerm, RawTerm.depth] at enough; omega
          simp [encodeTerm, decodeTerm, functionIH fuel first, argumentIH fuel second]
  | lam body ih =>
      cases fuel with
      | zero => simp [encodeTerm, RawTerm.depth] at enough
      | succ fuel =>
          have bodyBound : (encodeTerm body).depth ≤ fuel := by
            simp only [encodeTerm, RawTerm.depth] at enough; omega
          simp [encodeTerm, decodeTerm, ih fuel bodyBound]
  | and left right leftIH rightIH =>
      cases fuel with
      | zero => simp [encodeTerm, RawTerm.depth] at enough
      | succ fuel =>
          have first : (encodeTerm left).depth ≤ fuel := by
            simp only [encodeTerm, RawTerm.depth] at enough; omega
          have second : (encodeTerm right).depth ≤ fuel := by
            simp only [encodeTerm, RawTerm.depth] at enough; omega
          simp [encodeTerm, decodeTerm, leftIH fuel first, rightIH fuel second]
  | or left right leftIH rightIH =>
      cases fuel with
      | zero => simp [encodeTerm, RawTerm.depth] at enough
      | succ fuel =>
          have first : (encodeTerm left).depth ≤ fuel := by
            simp only [encodeTerm, RawTerm.depth] at enough; omega
          have second : (encodeTerm right).depth ≤ fuel := by
            simp only [encodeTerm, RawTerm.depth] at enough; omega
          simp [encodeTerm, decodeTerm, leftIH fuel first, rightIH fuel second]
  | imp left right leftIH rightIH =>
      cases fuel with
      | zero => simp [encodeTerm, RawTerm.depth] at enough
      | succ fuel =>
          have first : (encodeTerm left).depth ≤ fuel := by
            simp only [encodeTerm, RawTerm.depth] at enough; omega
          have second : (encodeTerm right).depth ≤ fuel := by
            simp only [encodeTerm, RawTerm.depth] at enough; omega
          simp [encodeTerm, decodeTerm, leftIH fuel first, rightIH fuel second]
  | eq left right leftIH rightIH =>
      cases fuel with
      | zero => simp [encodeTerm, RawTerm.depth] at enough
      | succ fuel =>
          have first : (encodeTerm left).depth ≤ fuel := by
            simp only [encodeTerm, RawTerm.depth] at enough; omega
          have second : (encodeTerm right).depth ≤ fuel := by
            simp only [encodeTerm, RawTerm.depth] at enough; omega
          simp [encodeTerm, decodeTerm, leftIH fuel first, rightIH fuel second]
  | not body ih =>
      cases fuel with
      | zero => simp [encodeTerm, RawTerm.depth] at enough
      | succ fuel =>
          have bodyBound : (encodeTerm body).depth ≤ fuel := by
            simp only [encodeTerm, RawTerm.depth] at enough; omega
          simp [encodeTerm, decodeTerm, ih fuel bodyBound]
  | all body ih =>
      cases fuel with
      | zero => simp [encodeTerm, RawTerm.depth] at enough
      | succ fuel =>
          have bodyBound : (encodeTerm body).depth ≤ fuel := by
            simp only [encodeTerm, RawTerm.depth] at enough; omega
          simp [encodeTerm, decodeTerm, ih fuel bodyBound]
  | ex body ih =>
      cases fuel with
      | zero => simp [encodeTerm, RawTerm.depth] at enough
      | succ fuel =>
          have bodyBound : (encodeTerm body).depth ≤ fuel := by
            simp only [encodeTerm, RawTerm.depth] at enough; omega
          simp [encodeTerm, decodeTerm, ih fuel bodyBound]

theorem encodeTerm_injective {context : ObjectContext} {type : ObjectType} :
    Function.Injective (encodeTerm (context := context) (type := type)) := by
  intro first second same
  let fuel := max (encodeTerm first).depth (encodeTerm second).depth
  have recovered := congrArg (decodeTerm fuel context type) same
  rw [decodeTerm_encode first fuel (Nat.le_max_left _ _),
    decodeTerm_encode second fuel (Nat.le_max_right _ _)] at recovered
  exact Option.some.inj recovered

inductive RawProof where
  | hypothesis (position : Nat)
  | topIntro
  | bottomElim (previous : RawProof)
  | bothIntro (left right : RawProof)
  | bothLeft (other : RawTerm) (previous : RawProof)
  | bothRight (other : RawTerm) (previous : RawProof)
  | eitherLeft (previous : RawProof)
  | eitherRight (previous : RawProof)
  | eitherElim (left right : RawTerm) (previous first second : RawProof)
  | implyIntro (previous : RawProof)
  | implyElim (premise : RawTerm) (function argument : RawProof)
  | notIntro (previous : RawProof)
  | notElim (premise : RawTerm) (negative positive : RawProof)
  | allIntro (previous : RawProof)
  | allElim (domain : ObjectType) (body witness : RawTerm) (previous : RawProof)
  | existIntro (witness : RawTerm) (previous : RawProof)
  | existElim (domain : ObjectType) (body : RawTerm) (previous branch : RawProof)
  | equalRefl (type : ObjectType) (term : RawTerm)
  | equalSymm (previous : RawProof)
  | equalTrans (middle : RawTerm) (first second : RawProof)
  | equalPropIntro (left right : RawTerm) (first second : RawProof)
  | equalPropLeft (previous : RawProof)
  | equalPropRight (previous : RawProof)
  | equalApp (domain codomain : ObjectType) (first second argument : RawTerm) (previous : RawProof)
  | equalAppArg (domain codomain : ObjectType) (function first second : RawTerm) (previous : RawProof)
  | equalLam (domain codomain : ObjectType) (first second : RawTerm) (previous : RawProof)
  | functionExt (domain codomain : ObjectType) (first second : RawTerm) (previous : RawProof)
  | beta (domain codomain : ObjectType) (argument body : RawTerm)
  | eta (domain codomain : ObjectType) (function : RawTerm)
  deriving DecidableEq, Repr

def encodeProof {context : ObjectContext} {assumptions : List (Formula MaterialConstant context)}
    {conclusion : Formula MaterialConstant context} :
    ProofSyntax MaterialConstant assumptions conclusion → RawProof
  | .hyp position => .hypothesis position.val
  | .topI => .topIntro
  | .botE previous => .bottomElim (encodeProof previous)
  | .andI left right => .bothIntro (encodeProof left) (encodeProof right)
  | @ProofSyntax.andEL _ _ _ _ _ other previous => .bothLeft (encodeTerm other) (encodeProof previous)
  | @ProofSyntax.andER _ _ _ _ other _ previous => .bothRight (encodeTerm other) (encodeProof previous)
  | .orIL previous => .eitherLeft (encodeProof previous)
  | .orIR previous => .eitherRight (encodeProof previous)
  | @ProofSyntax.orE _ _ _ _ left right _ previous first second =>
      .eitherElim (encodeTerm left) (encodeTerm right)
        (encodeProof previous) (encodeProof first) (encodeProof second)
  | .impI previous => .implyIntro (encodeProof previous)
  | @ProofSyntax.impE _ _ _ _ premise _ function argument =>
      .implyElim (encodeTerm premise) (encodeProof function) (encodeProof argument)
  | .notI previous => .notIntro (encodeProof previous)
  | @ProofSyntax.notE _ _ _ _ premise negative positive =>
      .notElim (encodeTerm premise) (encodeProof negative) (encodeProof positive)
  | .allI previous => .allIntro (encodeProof previous)
  | @ProofSyntax.allE _ _ _ _ domain body witness previous =>
      .allElim domain (encodeTerm body) (encodeTerm witness) (encodeProof previous)
  | .exI witness previous => .existIntro (encodeTerm witness) (encodeProof previous)
  | @ProofSyntax.exE _ _ _ _ domain body _ previous branch =>
      .existElim domain (encodeTerm body) (encodeProof previous) (encodeProof branch)
  | @ProofSyntax.eqRefl _ _ _ _ type term => .equalRefl type (encodeTerm term)
  | .eqSymm previous => .equalSymm (encodeProof previous)
  | @ProofSyntax.eqTrans _ _ _ _ _ _ middle _ first second =>
      .equalTrans (encodeTerm middle) (encodeProof first) (encodeProof second)
  | @ProofSyntax.eqPropI _ _ _ _ left right first second =>
      .equalPropIntro (encodeTerm left) (encodeTerm right) (encodeProof first) (encodeProof second)
  | .eqPropEL previous => .equalPropLeft (encodeProof previous)
  | .eqPropER previous => .equalPropRight (encodeProof previous)
  | @ProofSyntax.eqApp _ _ _ _ domain codomain first second argument previous =>
      .equalApp domain codomain (encodeTerm first) (encodeTerm second)
        (encodeTerm argument) (encodeProof previous)
  | @ProofSyntax.eqAppArg _ _ _ _ domain codomain function first second previous =>
      .equalAppArg domain codomain (encodeTerm function) (encodeTerm first)
        (encodeTerm second) (encodeProof previous)
  | @ProofSyntax.eqLam _ _ _ _ domain codomain first second previous =>
      .equalLam domain codomain (encodeTerm first) (encodeTerm second) (encodeProof previous)
  | @ProofSyntax.funExt _ _ _ _ domain codomain first second previous =>
      .functionExt domain codomain (encodeTerm first) (encodeTerm second) (encodeProof previous)
  | @ProofSyntax.beta _ _ _ _ domain codomain argument body =>
      .beta domain codomain (encodeTerm argument) (encodeTerm body)
  | @ProofSyntax.eta _ _ _ _ domain codomain function =>
      .eta domain codomain (encodeTerm function)

def RawProof.depth : RawProof → Nat
  | .hypothesis _ | .topIntro => 1
  | .bottomElim previous | .eitherLeft previous | .eitherRight previous |
      .implyIntro previous | .notIntro previous | .allIntro previous |
      .equalSymm previous | .equalPropLeft previous | .equalPropRight previous => previous.depth + 1
  | .bothIntro left right => left.depth + right.depth + 1
  | .bothLeft other previous | .bothRight other previous => other.depth + previous.depth + 1
  | .eitherElim left right previous first second =>
      left.depth + right.depth + previous.depth + first.depth + second.depth + 1
  | .implyElim premise function argument | .notElim premise function argument =>
      premise.depth + function.depth + argument.depth + 1
  | .allElim _ body witness previous => body.depth + witness.depth + previous.depth + 1
  | .existIntro witness previous => witness.depth + previous.depth + 1
  | .existElim _ body previous branch => body.depth + previous.depth + branch.depth + 1
  | .equalRefl _ term => term.depth + 1
  | .equalTrans middle first second => middle.depth + first.depth + second.depth + 1
  | .equalPropIntro left right first second => left.depth + right.depth + first.depth + second.depth + 1
  | .equalApp _ _ first second argument previous |
      .equalAppArg _ _ first second argument previous =>
      first.depth + second.depth + argument.depth + previous.depth + 1
  | .equalLam _ _ first second previous | .functionExt _ _ first second previous =>
      first.depth + second.depth + previous.depth + 1
  | .beta _ _ argument body => argument.depth + body.depth + 1
  | .eta _ _ function => function.depth + 1

def checkConclusion {context : ObjectContext} {assumptions : List (Formula MaterialConstant context)}
    {actual : Formula MaterialConstant context} (expected : Formula MaterialConstant context)
    (proof : ProofSyntax MaterialConstant assumptions actual) :
    Option (ProofSyntax MaterialConstant assumptions expected) :=
  if same : actual = expected then some (proof.castIndices rfl same) else none

@[simp] theorem checkConclusion_self {context : ObjectContext}
    {assumptions : List (Formula MaterialConstant context)} {actual : Formula MaterialConstant context}
    (proof : ProofSyntax MaterialConstant assumptions actual) : checkConclusion actual proof = some proof := by
  simp [checkConclusion, ProofSyntax.castIndices]

def decodeProof : Nat → (context : ObjectContext) →
    (assumptions : List (Formula MaterialConstant context)) →
    (goal : Formula MaterialConstant context) → RawProof →
    Option (ProofSyntax MaterialConstant assumptions goal)
  | 0, _, _, _, _ => none
  | fuel+1, context, assumptions, goal, raw =>
    match raw with
    | .hypothesis position =>
        if bound : position < assumptions.length then
          checkConclusion goal (.hyp ⟨position, bound⟩) else none
    | .topIntro => checkConclusion goal .topI
    | .bottomElim previous => do
        return .botE (← decodeProof fuel context assumptions .bot previous)
    | .bothIntro left right =>
        match goal with
        | .and first second => do
            return .andI (← decodeProof fuel context assumptions first left)
              (← decodeProof fuel context assumptions second right)
        | _ => none
    | .bothLeft other previous => do
        let second ← decodeTerm fuel context .prop other
        return .andEL (← decodeProof fuel context assumptions (.and goal second) previous)
    | .bothRight other previous => do
        let first ← decodeTerm fuel context .prop other
        return .andER (← decodeProof fuel context assumptions (.and first goal) previous)
    | .eitherLeft previous =>
        match goal with
        | .or first _ => do return .orIL (← decodeProof fuel context assumptions first previous)
        | _ => none
    | .eitherRight previous =>
        match goal with
        | .or _ second => do return .orIR (← decodeProof fuel context assumptions second previous)
        | _ => none
    | .eitherElim left right previous first second => do
        let leftFormula ← decodeTerm fuel context .prop left
        let rightFormula ← decodeTerm fuel context .prop right
        return .orE (← decodeProof fuel context assumptions (.or leftFormula rightFormula) previous)
          (← decodeProof fuel context (leftFormula :: assumptions) goal first)
          (← decodeProof fuel context (rightFormula :: assumptions) goal second)
    | .implyIntro previous =>
        match goal with
        | .imp premise result => do
            return .impI (← decodeProof fuel context (premise :: assumptions) result previous)
        | _ => none
    | .implyElim premise function argument => do
        let premiseFormula ← decodeTerm fuel context .prop premise
        return .impE (← decodeProof fuel context assumptions (.imp premiseFormula goal) function)
          (← decodeProof fuel context assumptions premiseFormula argument)
    | .notIntro previous =>
        match goal with
        | .not premise => do return .notI (← decodeProof fuel context (premise :: assumptions) .bot previous)
        | _ => none
    | .notElim premise negative positive => do
        let premiseFormula ← decodeTerm fuel context .prop premise
        let negativeProof ← decodeProof fuel context assumptions (.not premiseFormula) negative
        let positiveProof ← decodeProof fuel context assumptions premiseFormula positive
        checkConclusion goal (.notE negativeProof positiveProof)
    | .allIntro previous =>
        match goal with
        | @Term.all _ _ domain _ body => do
            return .allI (← decodeProof fuel (domain :: context) (weakenHyps assumptions) body previous)
        | _ => none
    | .allElim domain body witness previous => do
        let bodyFormula ← decodeTerm fuel (domain :: context) .prop body
        let witnessTerm ← decodeTerm fuel context domain witness
        let previousProof ← decodeProof fuel context assumptions (.all bodyFormula) previous
        checkConclusion goal (.allE witnessTerm previousProof)
    | .existIntro witness previous =>
        match goal with
        | @Term.ex _ _ domain _ body => do
            let witnessTerm ← decodeTerm fuel context domain witness
            return .exI witnessTerm
              (← decodeProof fuel context assumptions (instantiate witnessTerm body) previous)
        | _ => none
    | .existElim domain body previous branch => do
        let bodyFormula ← decodeTerm fuel (domain :: context) .prop body
        return .exE (← decodeProof fuel context assumptions (.ex bodyFormula) previous)
          (← decodeProof fuel (domain :: context) (bodyFormula :: weakenHyps assumptions)
            (weaken goal) branch)
    | .equalRefl type term => do
        let decoded ← decodeTerm fuel context type term
        checkConclusion goal (.eqRefl decoded)
    | .equalSymm previous =>
        match goal with
        | .eq left right => do return .eqSymm (← decodeProof fuel context assumptions (.eq right left) previous)
        | _ => none
    | .equalTrans middle first second =>
        match goal with
        | @Term.eq _ _ _ type left right => do
            let middleTerm ← decodeTerm fuel context type middle
            return .eqTrans (← decodeProof fuel context assumptions (.eq left middleTerm) first)
              (← decodeProof fuel context assumptions (.eq middleTerm right) second)
        | _ => none
    | .equalPropIntro left right first second => do
        let leftFormula ← decodeTerm fuel context .prop left
        let rightFormula ← decodeTerm fuel context .prop right
        let firstProof ← decodeProof fuel context assumptions (.imp leftFormula rightFormula) first
        let secondProof ← decodeProof fuel context assumptions (.imp rightFormula leftFormula) second
        checkConclusion goal (.eqPropI firstProof secondProof)
    | .equalPropLeft previous =>
        match goal with
        | .imp left right => do return .eqPropEL (← decodeProof fuel context assumptions (.eq left right) previous)
        | _ => none
    | .equalPropRight previous =>
        match goal with
        | .imp left right => do return .eqPropER (← decodeProof fuel context assumptions (.eq right left) previous)
        | _ => none
    | .equalApp domain codomain first second argument previous => do
        let firstTerm ← decodeTerm fuel context (.arr domain codomain) first
        let secondTerm ← decodeTerm fuel context (.arr domain codomain) second
        let argumentTerm ← decodeTerm fuel context domain argument
        let previousProof ← decodeProof fuel context assumptions (.eq firstTerm secondTerm) previous
        checkConclusion goal (.eqApp argumentTerm previousProof)
    | .equalAppArg domain codomain function first second previous => do
        let functionTerm ← decodeTerm fuel context (.arr domain codomain) function
        let firstTerm ← decodeTerm fuel context domain first
        let secondTerm ← decodeTerm fuel context domain second
        let previousProof ← decodeProof fuel context assumptions (.eq firstTerm secondTerm) previous
        checkConclusion goal (.eqAppArg functionTerm previousProof)
    | .equalLam domain codomain first second previous => do
        let firstTerm ← decodeTerm fuel (domain :: context) codomain first
        let secondTerm ← decodeTerm fuel (domain :: context) codomain second
        let previousProof ← decodeProof fuel (domain :: context) (weakenHyps assumptions)
          (.eq firstTerm secondTerm) previous
        checkConclusion goal (.eqLam previousProof)
    | .functionExt domain codomain first second previous => do
        let firstTerm ← decodeTerm fuel context (.arr domain codomain) first
        let secondTerm ← decodeTerm fuel context (.arr domain codomain) second
        let previousProof ← decodeProof fuel context assumptions
          (.all (.eq (.app (weaken firstTerm) (.var .vz))
            (.app (weaken secondTerm) (.var .vz)))) previous
        checkConclusion goal (.funExt previousProof)
    | .beta domain codomain argument body => do
        let argumentTerm ← decodeTerm fuel context domain argument
        let bodyTerm ← decodeTerm fuel (domain :: context) codomain body
        checkConclusion goal (.beta argumentTerm bodyTerm)
    | .eta domain codomain function => do
        let functionTerm ← decodeTerm fuel context (.arr domain codomain) function
        checkConclusion goal (.eta functionTerm)

theorem decodeProof_encode {context : ObjectContext}
    {assumptions : List (Formula MaterialConstant context)}
    {goal : Formula MaterialConstant context}
    (proof : ProofSyntax MaterialConstant assumptions goal) (fuel : Nat)
    (enough : (encodeProof proof).depth ≤ fuel) :
    decodeProof fuel context assumptions goal (encodeProof proof) = some proof := by
  induction proof generalizing fuel
  all_goals
    cases fuel with
    | zero =>
        dsimp [encodeProof, RawProof.depth] at enough
        exfalso
        omega
    | succ fuel =>
        dsimp [encodeProof, RawProof.depth] at enough
        simp (disch := omega) [encodeProof, decodeProof, decodeTerm_encode, *]

theorem encodeProof_injective {context : ObjectContext}
    {assumptions : List (Formula MaterialConstant context)}
    {goal : Formula MaterialConstant context} :
    Function.Injective (encodeProof (assumptions := assumptions) (conclusion := goal)) := by
  intro first second same
  let fuel := max (encodeProof first).depth (encodeProof second).depth
  have recovered := congrArg (decodeProof fuel context assumptions goal) same
  rw [decodeProof_encode first fuel (Nat.le_max_left _ _),
    decodeProof_encode second fuel (Nat.le_max_right _ _)] at recovered
  exact Option.some.inj recovered

universe u v

/-- The source compiler never introduces propositional equality introduction,
reverse propositional elimination, abstraction congruence, functional
extensionality or eta. This checks actual proof constructors. -/
def SourceEqualityRules {Base : Type u} {Const : Ty Base → Type v} {context : Ctx Base}
    {assumptions : List (Formula Const context)} {goal : Formula Const context} :
    ProofSyntax Const assumptions goal → Prop
  | .hyp _ => True
  | .topI => True
  | .eqRefl _ => True
  | .beta _ _ => True
  | .botE previous => SourceEqualityRules previous
  | .andEL previous => SourceEqualityRules previous
  | .andER previous => SourceEqualityRules previous
  | .orIL previous => SourceEqualityRules previous
  | .orIR previous => SourceEqualityRules previous
  | .impI previous => SourceEqualityRules previous
  | .notI previous => SourceEqualityRules previous
  | .allI previous => SourceEqualityRules previous
  | .allE _ previous => SourceEqualityRules previous
  | .exI _ previous => SourceEqualityRules previous
  | .eqSymm previous => SourceEqualityRules previous
  | .eqPropEL previous => SourceEqualityRules previous
  | .eqApp _ previous => SourceEqualityRules previous
  | .eqAppArg _ previous => SourceEqualityRules previous
  | .andI first second => SourceEqualityRules first ∧ SourceEqualityRules second
  | .impE first second => SourceEqualityRules first ∧ SourceEqualityRules second
  | .notE first second => SourceEqualityRules first ∧ SourceEqualityRules second
  | .exE first second => SourceEqualityRules first ∧ SourceEqualityRules second
  | .eqTrans first second => SourceEqualityRules first ∧ SourceEqualityRules second
  | .orE previous first second =>
      SourceEqualityRules previous ∧ SourceEqualityRules first ∧ SourceEqualityRules second
  | .eqPropI _ _ | .eqPropER _ | .eqLam _ | .funExt _ | .eta _ => False

theorem sourceEqualityRules_cast {Base : Type u} {Const : Ty Base → Type v} {context : Ctx Base}
    {assumptions : List (Formula Const context)}
    {goal result : Formula Const context} (same : goal = result)
    (proof : ProofSyntax Const assumptions goal) :
    SourceEqualityRules (same ▸ proof : ProofSyntax Const assumptions result) ↔
      SourceEqualityRules proof := by
  cases same
  rfl

theorem sourceEqualityRules_castIndices {Base : Type u} {Const : Ty Base → Type v} {context : Ctx Base}
    {assumptions changed : List (Formula Const context)}
    {goal result : Formula Const context}
    (sameAssumptions : assumptions = changed) (sameConclusion : goal = result)
    (proof : ProofSyntax Const assumptions goal) :
    SourceEqualityRules (proof.castIndices sameAssumptions sameConclusion) ↔ SourceEqualityRules proof := by
  cases sameAssumptions
  cases sameConclusion
  rfl

@[simp] theorem sourceEqualityRules_mono {Base : Type u} {Const : Ty Base → Type v} {context : Ctx Base}
    {assumptions changed : List (Formula Const context)}
    {goal : Formula Const context}
    (transport : ProofSyntax.OccurrenceMap assumptions changed)
    (proof : ProofSyntax Const assumptions goal) :
    SourceEqualityRules (proof.mono transport) ↔ SourceEqualityRules proof :=
  match proof with
  | .hyp occurrence => by
      simp only [ProofSyntax.mono]
      rw [sourceEqualityRules_cast]
      rfl
  | .topI | .eqRefl _ | .beta _ _ | .eqPropI _ _ | .eqPropER _ |
      .eqLam _ | .funExt _ | .eta _ => Iff.rfl
  | .botE previous | .andEL previous | .andER previous | .orIL previous |
      .orIR previous | .allE _ previous | .exI _ previous | .eqSymm previous |
      .eqPropEL previous | .eqApp _ previous | .eqAppArg _ previous =>
      sourceEqualityRules_mono transport previous
  | .impI previous | .notI previous => sourceEqualityRules_mono (transport.lift _) previous
  | .allI previous => sourceEqualityRules_mono (transport.map (weaken (σ := _))) previous
  | .andI first second | .impE first second | .notE first second |
      .eqTrans first second => and_congr
      (sourceEqualityRules_mono transport first) (sourceEqualityRules_mono transport second)
  | .exE first second => and_congr (sourceEqualityRules_mono transport first)
      (sourceEqualityRules_mono ((transport.map (weaken (σ := _))).lift _) second)
  | .orE previous first second => and_congr (sourceEqualityRules_mono transport previous)
      (and_congr (sourceEqualityRules_mono (transport.lift _) first)
        (sourceEqualityRules_mono (transport.lift _) second))

@[simp] theorem sourceEqualityRules_rename {Base : Type u} {Const : Ty Base → Type v} {context changed : Ctx Base}
    {assumptions : List (Formula Const context)}
    {goal : Formula Const context}
    (mapping : Rename Base context changed)
    (proof : ProofSyntax Const assumptions goal) :
    SourceEqualityRules (proof.rename mapping) ↔ SourceEqualityRules proof := by
  induction proof generalizing changed with
  | _ => simp_all only [ProofSyntax.rename, sourceEqualityRules_castIndices, SourceEqualityRules]

namespace ExpansionRules

open ImpredicativeConnectives

variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
variable {Δ : List (Formula Const Γ)}

 theorem conjunctionBeta_supported (p q : Formula Const Γ) :
    SourceEqualityRules (conjunctionBeta (Δ := Δ) p q) := by
  simp only [conjunctionBeta, sourceEqualityRules_castIndices, SourceEqualityRules, and_self]

 theorem disjunctionBeta_supported (p q : Formula Const Γ) :
    SourceEqualityRules (disjunctionBeta (Δ := Δ) p q) := by
  simp only [disjunctionBeta, sourceEqualityRules_castIndices, SourceEqualityRules, and_self]

 theorem existentialBeta_supported {σ : Ty Base} (predicate : Term Const Γ (σ ⇒ .prop)) :
    SourceEqualityRules (existentialBeta (Δ := Δ) predicate) := by
  simp only [existentialBeta, sourceEqualityRules_castIndices, SourceEqualityRules]

 theorem conjunctionIntro_supported {p q : Formula Const Γ}
    (left : ProofSyntax Const Δ p) (right : ProofSyntax Const Δ q) :
    SourceEqualityRules (conjunctionIntro left right) ↔ SourceEqualityRules left ∧ SourceEqualityRules right := by
  change SourceEqualityRules
    (.impE (.eqPropEL (.eqSymm (conjunctionBeta p q)))
      (.allI (.impI (.impE (.impE (.hyp 0)
        ((left.rename Rename.weaken).prepend _))
          ((right.rename Rename.weaken).prepend _))))) ↔ _
  simp only [SourceEqualityRules, conjunctionBeta_supported, sourceEqualityRules_mono,
    sourceEqualityRules_rename, ProofSyntax.prepend, true_and]

 theorem conjunctionLeft_supported {p q : Formula Const Γ}
    (previous : ProofSyntax Const Δ (.app (.app conjunction p) q)) :
    SourceEqualityRules (conjunctionLeft previous) ↔ SourceEqualityRules previous := by
  unfold conjunctionLeft
  simp only [SourceEqualityRules, sourceEqualityRules_castIndices, and_true]
  change SourceEqualityRules (.impE (.eqPropEL (conjunctionBeta p q)) previous) ↔ _
  simp only [SourceEqualityRules, conjunctionBeta_supported, true_and]

 theorem conjunctionRight_supported {p q : Formula Const Γ}
    (previous : ProofSyntax Const Δ (.app (.app conjunction p) q)) :
    SourceEqualityRules (conjunctionRight previous) ↔ SourceEqualityRules previous := by
  unfold conjunctionRight
  simp only [SourceEqualityRules, sourceEqualityRules_castIndices, and_true]
  change SourceEqualityRules (.impE (.eqPropEL (conjunctionBeta p q)) previous) ↔ _
  simp only [SourceEqualityRules, conjunctionBeta_supported, true_and]

 theorem disjunctionLeft_supported {p q : Formula Const Γ}
    (previous : ProofSyntax Const Δ p) :
    SourceEqualityRules (disjunctionLeft (q := q) previous) ↔ SourceEqualityRules previous := by
  change SourceEqualityRules
    (.impE (.eqPropEL (.eqSymm (disjunctionBeta p q)))
      (.allI (.impI (.impI (.impE (.hyp 1)
        (((previous.rename Rename.weaken).prepend _).prepend _)))))) ↔ _
  simp only [SourceEqualityRules, disjunctionBeta_supported, sourceEqualityRules_mono,
    sourceEqualityRules_rename, ProofSyntax.prepend, true_and]

 theorem disjunctionRight_supported {p q : Formula Const Γ}
    (previous : ProofSyntax Const Δ q) :
    SourceEqualityRules (disjunctionRight (p := p) previous) ↔ SourceEqualityRules previous := by
  change SourceEqualityRules
    (.impE (.eqPropEL (.eqSymm (disjunctionBeta p q)))
      (.allI (.impI (.impI (.impE (.hyp 0)
        (((previous.rename Rename.weaken).prepend _).prepend _)))))) ↔ _
  simp only [SourceEqualityRules, disjunctionBeta_supported, sourceEqualityRules_mono,
    sourceEqualityRules_rename, ProofSyntax.prepend, true_and]

 theorem disjunctionElim_supported {p q r : Formula Const Γ}
    (previous : ProofSyntax Const Δ (.app (.app disjunction p) q))
    (first : ProofSyntax Const (p :: Δ) r) (second : ProofSyntax Const (q :: Δ) r) :
    SourceEqualityRules (disjunctionElim previous first second) ↔
      SourceEqualityRules previous ∧ SourceEqualityRules first ∧ SourceEqualityRules second := by
  unfold disjunctionElim
  simp only [SourceEqualityRules, sourceEqualityRules_castIndices]
  change (SourceEqualityRules (.impE (.eqPropEL (disjunctionBeta p q)) previous) ∧
    SourceEqualityRules first) ∧ SourceEqualityRules second ↔ _
  simp only [SourceEqualityRules, disjunctionBeta_supported, true_and, and_assoc]

 theorem existentialIntro_supported {σ : Ty Base} (predicate : Term Const Γ (σ ⇒ .prop))
    (witness : Term Const Γ σ) (previous : ProofSyntax Const Δ (.app predicate witness)) :
    SourceEqualityRules (existentialIntro predicate witness previous) ↔ SourceEqualityRules previous := by
  unfold existentialIntro
  change SourceEqualityRules (.impE (.eqPropEL (.eqSymm (existentialBeta predicate))) _) ↔ _
  simp only [SourceEqualityRules, existentialBeta_supported, sourceEqualityRules_castIndices,
    ProofSyntax.prepend, sourceEqualityRules_mono, true_and]
  change SourceEqualityRules (previous.rename Rename.weaken) ↔ SourceEqualityRules previous
  exact sourceEqualityRules_rename _ _

 theorem existentialElim_supported {σ : Ty Base} {predicate : Term Const Γ (σ ⇒ .prop)}
    {result : Formula Const Γ}
    (previous : ProofSyntax Const Δ (.app (existential σ) predicate))
    (branch : ProofSyntax Const (.app (weaken predicate) (.var .vz) :: weakenHyps Δ) (weaken result)) :
    SourceEqualityRules (existentialElim previous branch) ↔
      SourceEqualityRules previous ∧ SourceEqualityRules branch := by
  unfold existentialElim
  simp only [SourceEqualityRules, sourceEqualityRules_castIndices]
  change SourceEqualityRules (.impE (.eqPropEL (existentialBeta predicate)) previous) ∧
    SourceEqualityRules branch ↔ _
  simp only [SourceEqualityRules, existentialBeta_supported, true_and]

/-- A beta proof at the freshly introduced variable, with its exact
transported conclusion retained. -/
def binderBeta {σ τ : Ty Base} (body : Term Const (σ :: Γ) τ)
    {assumptions : List (Formula Const (σ :: Γ))} :
    ProofSyntax Const assumptions (.eq (.app (weaken (.lam body)) (.var .vz)) body) := by
  have same : instantiate (Term.var (Var.vz : Var (σ :: Γ) σ))
      (rename (Rename.lift Rename.weaken) body) = body := by
    unfold instantiate
    rw [subst_rename]
    calc
      _ = subst Subst.id body := by
        apply subst_ext
        intro _ index
        cases index <;> rfl
      _ = body := subst_id body
  exact ProofSyntax.castIndices rfl (by simp only [weaken, rename, same])
    (ProofSyntax.beta (.var .vz) (rename (Rename.lift Rename.weaken) body))

 theorem binderBeta_supported {σ τ : Ty Base} (body : Term Const (σ :: Γ) τ)
    {assumptions : List (Formula Const (σ :: Γ))} :
    SourceEqualityRules (binderBeta body (assumptions := assumptions)) := by
  simp only [binderBeta, sourceEqualityRules_castIndices, SourceEqualityRules]

end ExpansionRules

theorem sourceEqualityRules_expand {Base : Type u} {Const : Ty Base → Type v} {context : Ctx Base}
    {assumptions : List (Formula Const context)} {goal : Formula Const context}
    (proof : ProofSyntax Const assumptions goal) :
    SourceEqualityRules (ImpredicativeConnectives.expandProof proof) ↔ SourceEqualityRules proof := by
  induction proof with
  | @exI Γ Δ σ body witness previous ih =>
      simp only [ImpredicativeConnectives.expandProof, ExpansionRules.existentialIntro_supported]
      change SourceEqualityRules (.impE
        (.eqPropEL (.eqSymm (ProofSyntax.beta (ImpredicativeConnectives.expand witness)
          (ImpredicativeConnectives.expand body))))
        (ProofSyntax.castIndices rfl _ (ImpredicativeConnectives.expandProof previous))) ↔ _
      simp only [SourceEqualityRules, sourceEqualityRules_castIndices, true_and, ih]
  | @exE Γ Δ σ body result previous branch firstIH secondIH =>
      simp only [ImpredicativeConnectives.expandProof, ExpansionRules.existentialElim_supported,
        SourceEqualityRules, ProofSyntax.prepend, sourceEqualityRules_mono,
        sourceEqualityRules_castIndices, firstIH, secondIH]
      change SourceEqualityRules previous ∧ (SourceEqualityRules branch ∧
        SourceEqualityRules (.impE (.eqPropEL (ExpansionRules.binderBeta
          (ImpredicativeConnectives.expand body)))
            (.hyp (Δ := (.app (weaken (.lam (ImpredicativeConnectives.expand body)))
              (.var .vz)) :: weakenHyps (Δ.map ImpredicativeConnectives.expand)) 0))) ↔ _
      simp only [SourceEqualityRules, ExpansionRules.binderBeta_supported, and_true]
  | _ =>
      simp_all only [ImpredicativeConnectives.expandProof,
        ImpredicativeConnectives.truthIntro, ImpredicativeConnectives.falsityElim,
        ExpansionRules.conjunctionIntro_supported, ExpansionRules.conjunctionLeft_supported,
        ExpansionRules.conjunctionRight_supported, ExpansionRules.disjunctionLeft_supported,
        ExpansionRules.disjunctionRight_supported, ExpansionRules.disjunctionElim_supported,
        SourceEqualityRules, sourceEqualityRules_castIndices]

/-- The source equality eliminator uses transport, symmetry, transitivity
and application congruence. It introduces no proposition extensionality,
function extensionality, lambda congruence or eta rule. -/
theorem equalityElimination_supported {count : Nat} {context : ObjectContext}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {body : ContextualMaterialLogic.Formula (count + 1)} {first second : Fin count}
    (environment : Environment count context)
    (same : ProofSyntax MaterialConstant (hypotheses assumptions environment)
      (formula (.equal first second) environment))
    (previous : ProofSyntax MaterialConstant (hypotheses assumptions environment)
      (formula (ContextualMaterialLogic.substitute
        (ContextualMaterialLogic.instantiate first) body) environment)) :
    SourceEqualityRules (equalityElimination environment same previous) ↔
      SourceEqualityRules same ∧ SourceEqualityRules previous := by
  simp only [equalityElimination, SourceEqualityRules, sourceEqualityRules_castIndices,
    true_and, and_true]

/-- Every source derivation, including its quantifier and equality rules,
has the smaller equality inventory implemented by the native bundle. -/
theorem sourceProof_supported {count : Nat} {context : ObjectContext}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {conclusion : ContextualMaterialLogic.Formula count}
    (deduction : GraphRealizedDeduction.Proof assumptions conclusion)
    (environment : Environment count context) :
    SourceEqualityRules (ProfileNativeProofCompilation.proof deduction environment) := by
  induction deduction generalizing context with
  | _ =>
      simp_all only [ProfileNativeProofCompilation.proof, SourceEqualityRules,
        sourceEqualityRules_castIndices, sourceEqualityRules_mono,
        equalityElimination_supported, true_and]

theorem compiledSource_supported {count : Nat} {context : ObjectContext}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {conclusion : ContextualMaterialLogic.Formula count}
    (deduction : GraphRealizedDeduction.Proof assumptions conclusion)
    (environment : Environment count context) :
    SourceEqualityRules (coreProof deduction environment) := by
  rw [coreProof, sourceEqualityRules_expand]
  exact sourceProof_supported deduction environment

/-- The exact twelve proof constructors of the authored native target.
Term formation is a separate check; derived source connectives are expanded
before this target is serialized. -/
def NativeRules {Base : Type u} {Const : Ty Base → Type v} {context : Ctx Base}
    {assumptions : List (Formula Const context)} {goal : Formula Const context} :
    ProofSyntax Const assumptions goal → Prop
  | .hyp _ | .eqRefl _ | .beta _ _ => True
  | .impI body | .allI body | .allE _ body | .eqSymm body | .eqPropEL body |
      .eqApp _ body | .eqAppArg _ body => NativeRules body
  | .impE first second | .eqTrans first second => NativeRules first ∧ NativeRules second
  | .topI | .botE _ | .andI _ _ | .andEL _ | .andER _ | .orIL _ | .orIR _ |
      .orE _ _ _ | .notI _ | .notE _ _ | .exI _ _ | .exE _ _ |
      .eqPropI _ _ | .eqPropER _ | .eqLam _ | .funExt _ | .eta _ => False

theorem sourceCore_nativeRules {Base : Type u} {Const : Ty Base → Type v} {context : Ctx Base}
    {assumptions : List (Formula Const context)} {goal : Formula Const context}
    (proof : ProofSyntax Const assumptions goal)
    (core : ImpredicativeConnectives.IsCoreProof proof) (source : SourceEqualityRules proof) :
    NativeRules proof := by
  induction proof <;>
    simp_all only [NativeRules, ImpredicativeConnectives.IsCoreProof, SourceEqualityRules, true_and]

theorem compiledSource_nativeRules {count : Nat} {context : ObjectContext}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {conclusion : ContextualMaterialLogic.Formula count}
    (deduction : GraphRealizedDeduction.Proof assumptions conclusion)
    (environment : Environment count context) : NativeRules (coreProof deduction environment) :=
  sourceCore_nativeRules _ (coreProof_isCore deduction environment)
    (compiledSource_supported deduction environment)

/-- A finite annotated native proof tree. The annotations are raw typed
term codes. No original proof, erased admission or semantic truth is stored
inside a code. Every child keeps its exact conclusion. -/
inductive NativeCode where
  | hypothesis (goal : RawTerm) (occurrence : Nat)
  | implyIntro (goal : RawTerm) (body : NativeCode)
  | implyElim (goal : RawTerm) (function argument : NativeCode)
  | allIntro (goal : RawTerm) (body : NativeCode)
  | allElim (goal : RawTerm) (function : NativeCode) (argument : RawTerm)
  | equalRefl (goal : RawTerm) (type : ObjectType) (term : RawTerm)
  | equalSymm (goal : RawTerm) (body : NativeCode)
  | equalTrans (goal : RawTerm) (first second : NativeCode)
  | equalPropLeft (goal : RawTerm) (body : NativeCode)
  | equalApp (goal : RawTerm) (domain codomain : ObjectType)
      (body : NativeCode) (argument : RawTerm)
  | equalAppArg (goal : RawTerm) (domain codomain : ObjectType)
      (function : RawTerm) (body : NativeCode)
  | beta (goal : RawTerm) (domain codomain : ObjectType) (argument lambda : RawTerm)
  deriving DecidableEq, Repr

def NativeCode.goal : NativeCode → RawTerm
  | .hypothesis goal _ | .implyIntro goal _ | .implyElim goal _ _ |
      .allIntro goal _ | .allElim goal _ _ | .equalRefl goal _ _ |
      .equalSymm goal _ | .equalTrans goal _ _ | .equalPropLeft goal _ |
      .equalApp goal _ _ _ _ | .equalAppArg goal _ _ _ _ | .beta goal _ _ _ _ => goal

def encodeNative {context : ObjectContext} {assumptions : List (Formula MaterialConstant context)}
    {goal : Formula MaterialConstant context}
    (proof : ProofSyntax MaterialConstant assumptions goal) : Option NativeCode :=
  let conclusion := encodeTerm goal
  match proof with
  | .hyp occurrence => some (.hypothesis conclusion occurrence.val)
  | .impI body => (encodeNative body).map (.implyIntro conclusion)
  | .impE function argument =>
      (encodeNative function).bind fun functionCode =>
        (encodeNative argument).map (.implyElim conclusion functionCode)
  | .allI body => (encodeNative body).map (.allIntro conclusion)
  | .allE argument function =>
      (encodeNative function).map (fun code => .allElim conclusion code (encodeTerm argument))
  | @ProofSyntax.eqRefl _ _ _ _ type term => some (.equalRefl conclusion type (encodeTerm term))
  | .eqSymm body => (encodeNative body).map (.equalSymm conclusion)
  | .eqTrans first second =>
      (encodeNative first).bind fun firstCode =>
        (encodeNative second).map (.equalTrans conclusion firstCode)
  | .eqPropEL body => (encodeNative body).map (.equalPropLeft conclusion)
  | @ProofSyntax.eqApp _ _ _ _ domain codomain _ _ argument body =>
      (encodeNative body).map (fun code => .equalApp conclusion domain codomain code (encodeTerm argument))
  | @ProofSyntax.eqAppArg _ _ _ _ domain codomain function _ _ body =>
      (encodeNative body).map (.equalAppArg conclusion domain codomain (encodeTerm function))
  | @ProofSyntax.beta _ _ _ _ domain codomain argument body =>
      some (.beta conclusion domain codomain (encodeTerm argument) (.lam (encodeTerm body)))
  | .topI | .botE _ | .andI _ _ | .andEL _ | .andER _ | .orIL _ | .orIR _ |
      .orE _ _ _ | .notI _ | .notE _ _ | .exI _ _ | .exE _ _ |
      .eqPropI _ _ | .eqPropER _ | .eqLam _ | .funExt _ | .eta _ => none

theorem encodeNative_defined_iff {context : ObjectContext}
    {assumptions : List (Formula MaterialConstant context)} {goal : Formula MaterialConstant context}
    (proof : ProofSyntax MaterialConstant assumptions goal) :
    (∃ code, encodeNative proof = some code) ↔ NativeRules proof := by
  induction proof <;> simp_all [encodeNative, NativeRules, Option.bind_eq_some_iff]

@[simp] theorem encodedNative_goal {context : ObjectContext}
    {assumptions : List (Formula MaterialConstant context)} {goal : Formula MaterialConstant context}
    (proof : ProofSyntax MaterialConstant assumptions goal) (code : NativeCode)
    (encoded : encodeNative proof = some code) : code.goal = encodeTerm goal := by
  cases proof <;> simp only [encodeNative, Option.map_eq_some_iff,
    Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq] at encoded
  all_goals
    first
    | solve | rcases encoded with rfl; rfl
    | solve | rcases encoded with ⟨_, _, rfl⟩; rfl
    | solve | rcases encoded with ⟨_, _, _, _, rfl⟩; rfl

/-- Recover the original finite HOL rule code from the native rule tree.
Parameters omitted from a surface rule, such as the middle of transitivity,
come from the retained typed child conclusion. -/
def NativeCode.toRaw : NativeCode → Option RawProof
  | .hypothesis _ occurrence => some (.hypothesis occurrence)
  | .implyIntro _ body => .implyIntro <$> body.toRaw
  | .implyElim _ function argument => do
      let premise ← match function.goal with
        | .imply premise _ => some premise
        | _ => none
      let first ← function.toRaw
      let second ← argument.toRaw
      pure (.implyElim premise first second)
  | .allIntro _ body => .allIntro <$> body.toRaw
  | .allElim _ function argument => do
      let (domain, body) ← match function.goal with
        | .all domain body => some (domain, body)
        | _ => none
      .allElim domain body argument <$> function.toRaw
  | .equalRefl _ type term => some (.equalRefl type term)
  | .equalSymm _ body => .equalSymm <$> body.toRaw
  | .equalTrans _ first second => do
      let middle ← match first.goal with
        | .equal _ _ middle => some middle
        | _ => none
      let firstCode ← first.toRaw
      let secondCode ← second.toRaw
      pure (.equalTrans middle firstCode secondCode)
  | .equalPropLeft _ body => .equalPropLeft <$> body.toRaw
  | .equalApp _ domain codomain body argument => do
      let (first, second) ← match body.goal with
        | .equal _ first second => some (first, second)
        | _ => none
      .equalApp domain codomain first second argument <$> body.toRaw
  | .equalAppArg _ domain codomain function body => do
      let (first, second) ← match body.goal with
        | .equal _ first second => some (first, second)
        | _ => none
      .equalAppArg domain codomain function first second <$> body.toRaw
  | .beta _ domain codomain argument (.lam body) => some (.beta domain codomain argument body)
  | .beta _ _ _ _ _ => none

theorem nativeCode_recovers_raw {context : ObjectContext}
    {assumptions : List (Formula MaterialConstant context)} {goal : Formula MaterialConstant context}
    (proof : ProofSyntax MaterialConstant assumptions goal) (code : NativeCode)
    (encoded : encodeNative proof = some code) : code.toRaw = some (encodeProof proof) := by
  induction proof generalizing code
  all_goals
    simp only [encodeNative, Option.map_eq_some_iff, Option.bind_eq_some_iff,
      Option.some.injEq, reduceCtorEq] at encoded
  all_goals
    first
    | solve | rcases encoded with rfl; rfl
    | rcases encoded with ⟨body, bodyEncoded, rfl⟩
      have bodyGoal := encodedNative_goal _ body bodyEncoded
      simp_all [NativeCode.toRaw, encodeProof, encodeTerm]
    | rcases encoded with ⟨first, firstEncoded, second, secondEncoded, rfl⟩
      have firstGoal := encodedNative_goal _ first firstEncoded
      have secondGoal := encodedNative_goal _ second secondEncoded
      simp_all [NativeCode.toRaw, encodeProof, encodeTerm]

/-- Decoding constructs a typed HOL proof first and checks all native
annotations by re-encoding that recovered proof. Code alone creates no
profile declaration and grants no equality-rule authority. -/
def decodeNative (fuel : Nat) (context : ObjectContext)
    (assumptions : List (Formula MaterialConstant context))
    (goal : Formula MaterialConstant context) (code : NativeCode) :
    Option (ProofSyntax MaterialConstant assumptions goal) := do
  let raw ← code.toRaw
  let proof ← decodeProof fuel context assumptions goal raw
  if encodeNative proof = some code then some proof else none

theorem decodeNative_encode {context : ObjectContext}
    {assumptions : List (Formula MaterialConstant context)} {goal : Formula MaterialConstant context}
    (proof : ProofSyntax MaterialConstant assumptions goal) (code : NativeCode)
    (encoded : encodeNative proof = some code) (fuel : Nat)
    (enough : (encodeProof proof).depth ≤ fuel) :
    decodeNative fuel context assumptions goal code = some proof := by
  simp [decodeNative, nativeCode_recovers_raw proof code encoded,
    decodeProof_encode proof fuel enough, encoded]

theorem nativeCode_preserves_proof {context : ObjectContext}
    {assumptions : List (Formula MaterialConstant context)} {goal : Formula MaterialConstant context}
    (first second : ProofSyntax MaterialConstant assumptions goal) (code : NativeCode)
    (firstEncoded : encodeNative first = some code) (secondEncoded : encodeNative second = some code) :
    first = second := by
  apply encodeProof_injective
  exact Option.some.inj ((nativeCode_recovers_raw first code firstEncoded).symm.trans
    (nativeCode_recovers_raw second code secondEncoded))

theorem decodedNative_sound {context : ObjectContext}
    {assumptions : List (Formula MaterialConstant context)} {goal : Formula MaterialConstant context}
    (fuel : Nat) (code : NativeCode)
    (accepted : (decodeNative fuel context assumptions goal code).isSome = true)
    (model : HenkinModel.{0, 0, u} MaterialBase MaterialConstant)
    (valuation : HenkinModel.Valuation model context)
    (extensional : HenkinModel.FunctionsRespectEqv model)
    (admissible : HenkinModel.ValuationAdmissible model valuation)
    (premises : HOL.Soundness.SatisfiesHyps model valuation assumptions) :
    (HenkinModel.denote model goal valuation).down := by
  cases result : decodeNative fuel context assumptions goal code with
  | none => simp [result] at accepted
  | some retained =>
      exact HOL.Soundness.extDerivation_sound retained.erase extensional admissible premises

/-- Transport says that every consumer of this carrier respects the chosen
relation. It does not assert that the relation is inhabited or reflexive. -/
def RelationalTransport {Carrier : Type u} (relation : Carrier → Carrier → Prop) : Prop :=
  ∀ {first second}, relation first second →
    ∀ consumer : Carrier → Prop, consumer first → consumer second

theorem relationalTransport_iff_subidentity {Carrier : Type u}
    (relation : Carrier → Carrier → Prop) :
    RelationalTransport relation ↔ ∀ first second, relation first second → first = second := by
  constructor
  · intro transport first second related
    exact transport related (fun value => first = value) rfl
  · intro same first second related consumer holds
    exact same first second related ▸ holds

theorem transport_and_reflexivity_iff_identity {Carrier : Type u}
    (relation : Carrier → Carrier → Prop) :
    (RelationalTransport relation ∧ ∀ value, relation value value) ↔
      ∀ first second, relation first second ↔ first = second := by
  constructor
  · rintro ⟨transport, reflexive⟩ first second
    constructor
    · exact (relationalTransport_iff_subidentity relation).mp transport first second
    · rintro rfl
      exact reflexive first
  · intro same
    constructor
    · exact (relationalTransport_iff_subidentity relation).mpr
        (fun first second related => (same first second).mp related)
    · intro value
      exact (same value value).mpr rfl

theorem empty_relation_transports {Carrier : Type u} :
    RelationalTransport (fun (_ _ : Carrier) => False) := by
  intro first second impossible
  exact impossible.elim

theorem empty_relation_not_reflexive :
    ¬ ∀ value : Bool, (fun (_ _ : Bool) => False) value value := by
  intro reflexive
  exact reflexive false

/-- A presentation-sensitive observer may distinguish two points even when
an observational relation identifies them. Such a relation cannot license
arbitrary predicate transport. -/
theorem universal_relation_does_not_transport :
    ¬ RelationalTransport (fun (_ _ : Bool) => True) := by
  intro transport
  have impossible : false = true := transport (first := false) (second := true)
    True.intro (fun value => false = value) rfl
  cases impossible

/-- Types are explicit wherever the native reader needs an application or
lambda annotation. The only material constant is the existing `In` signature. -/
def renderObjectType : ObjectType → String
  | .prop => "prop"
  | .base .set => "set"
  | .arr domain codomain =>
      "(-> " ++ renderObjectType domain ++ " " ++ renderObjectType codomain ++ ")"

private def localName (depth : Nat) : String := "_ps_local_" ++ toString depth

private def renderVariable (depth index : Nat) : String :=
  if index < depth then localName (depth - 1 - index)
  else "(pf:var " ++ toString (index - depth) ++ ")"

/-- Term-lambda slots receive fresh names; proof-context slots keep their
de Bruijn indices. These are separate namespaces in the native reader. -/
def renderTerm {context : ObjectContext} {type : ObjectType}
    (depth : Nat) : Term MaterialConstant context type → String
  | .var slot => renderVariable depth (variableIndex slot)
  | .const .member => "In"
  | .app function argument => "(" ++ renderTerm depth function ++ " " ++ renderTerm depth argument ++ ")"
  | @Term.lam _ _ domain _ _ body =>
      "(lam (: " ++ localName depth ++ " " ++ renderObjectType domain ++ ") " ++
        renderTerm (depth+1) body ++ ")"
  | .top => "top"
  | .bot => "bottom"
  | .and left right => "(and " ++ renderTerm depth left ++ " " ++ renderTerm depth right ++ ")"
  | .or left right => "(or " ++ renderTerm depth left ++ " " ++ renderTerm depth right ++ ")"
  | .imp left right => "(imp " ++ renderTerm depth left ++ " " ++ renderTerm depth right ++ ")"
  | .not body => "(not " ++ renderTerm depth body ++ ")"
  | @Term.eq _ _ _ carrier left right =>
      "(eq " ++ renderObjectType carrier ++ " " ++ renderTerm depth left ++ " " ++ renderTerm depth right ++ ")"
  | @Term.all _ _ domain _ body =>
      "(all " ++ renderObjectType domain ++ " (lam (: " ++ localName depth ++ " " ++
        renderObjectType domain ++ ") " ++ renderTerm (depth+1) body ++ "))"
  | @Term.ex _ _ domain _ body =>
      "(exists " ++ renderObjectType domain ++ " (lam (: " ++ localName depth ++ " " ++
        renderObjectType domain ++ ") " ++ renderTerm (depth+1) body ++ "))"

/-- Printing raw data checks the expected type of lambda constructors.
Derived logical term constructors are printed here for inspectability;
the source compiler expands them before the admitted native target. -/
def renderRawTerm (depth : Nat) (type : ObjectType) : RawTerm → Option String
  | .variable index => some (renderVariable depth index)
  | .member => some "In"
  | .app domain function argument => do
      let function ← renderRawTerm depth (.arr domain type) function
      let argument ← renderRawTerm depth domain argument
      pure ("(" ++ function ++ " " ++ argument ++ ")")
  | .lam body => match type with
      | .arr domain codomain => do
          let body ← renderRawTerm (depth+1) codomain body
          pure ("(lam (: " ++ localName depth ++ " " ++ renderObjectType domain ++ ") " ++ body ++ ")")
      | _ => none
  | .top => some "top"
  | .bottom => some "bottom"
  | .both left right => do
      let left ← renderRawTerm depth .prop left
      let right ← renderRawTerm depth .prop right
      pure ("(and " ++ left ++ " " ++ right ++ ")")
  | .either left right => do
      let left ← renderRawTerm depth .prop left
      let right ← renderRawTerm depth .prop right
      pure ("(or " ++ left ++ " " ++ right ++ ")")
  | .imply left right => do
      let left ← renderRawTerm depth .prop left
      let right ← renderRawTerm depth .prop right
      pure ("(imp " ++ left ++ " " ++ right ++ ")")
  | .negative body => do
      let body ← renderRawTerm depth .prop body
      pure ("(not " ++ body ++ ")")
  | .equal carrier left right => do
      let left ← renderRawTerm depth carrier left
      let right ← renderRawTerm depth carrier right
      pure ("(eq " ++ renderObjectType carrier ++ " " ++ left ++ " " ++ right ++ ")")
  | .all domain body => do
      let body ← renderRawTerm (depth+1) .prop body
      pure ("(all " ++ renderObjectType domain ++ " (lam (: " ++ localName depth ++ " " ++
        renderObjectType domain ++ ") " ++ body ++ "))")
  | .exist domain body => do
      let body ← renderRawTerm (depth+1) .prop body
      pure ("(exists " ++ renderObjectType domain ++ " (lam (: " ++ localName depth ++ " " ++
        renderObjectType domain ++ ") " ++ body ++ "))")

theorem renderRawTerm_encode {context : ObjectContext} {type : ObjectType}
    (term : Term MaterialConstant context type) (depth : Nat) :
    renderRawTerm depth type (encodeTerm term) = some (renderTerm depth term) := by
  induction term generalizing depth with
  | const constant => cases constant; rfl
  | _ => simp_all [renderRawTerm, encodeTerm, renderTerm]

private def annotate (goal body : String) : String := "(pf:typed " ++ goal ++ " " ++ body ++ ")"

/-- The twelve authored target forms, each with its exact typed conclusion.
Printing alone neither checks the raw tree nor adopts a profile rule. -/
def renderNativeCode : NativeCode → Option String
  | .hypothesis goal occurrence => do
      let goal ← renderRawTerm 0 .prop goal
      pure (annotate goal ("(pf:hyp " ++ toString occurrence ++ ")"))
  | .implyIntro goal body => do
      let goal ← renderRawTerm 0 .prop goal
      let body ← renderNativeCode body
      pure (annotate goal ("(pf:imp-intro " ++ body ++ ")"))
  | .implyElim goal function argument => do
      let goal ← renderRawTerm 0 .prop goal
      let function ← renderNativeCode function
      let argument ← renderNativeCode argument
      pure (annotate goal ("(pf:imp-elim " ++ function ++ " " ++ argument ++ ")"))
  | .allIntro goal body => do
      let goal ← renderRawTerm 0 .prop goal
      let body ← renderNativeCode body
      pure (annotate goal ("(pf:all-intro " ++ body ++ ")"))
  | .allElim goal function argument => do
      let domain ← match function.goal with
        | .all domain _ => some domain
        | _ => none
      let goal ← renderRawTerm 0 .prop goal
      let function ← renderNativeCode function
      let argument ← renderRawTerm 0 domain argument
      pure (annotate goal ("(pf:all-elim " ++ function ++ " " ++ argument ++ ")"))
  | .equalRefl goal type term => do
      let goal ← renderRawTerm 0 .prop goal
      let term ← renderRawTerm 0 type term
      pure (annotate goal ("(pf:eq-refl " ++ renderObjectType type ++ " " ++ term ++ ")"))
  | .equalSymm goal body => do
      let goal ← renderRawTerm 0 .prop goal
      let body ← renderNativeCode body
      pure (annotate goal ("(pf:eq-symm " ++ body ++ ")"))
  | .equalTrans goal first second => do
      let goal ← renderRawTerm 0 .prop goal
      let first ← renderNativeCode first
      let second ← renderNativeCode second
      pure (annotate goal ("(pf:eq-trans " ++ first ++ " " ++ second ++ ")"))
  | .equalPropLeft goal body => do
      let goal ← renderRawTerm 0 .prop goal
      let body ← renderNativeCode body
      pure (annotate goal ("(pf:eq-prop-elim " ++ body ++ ")"))
  | .equalApp goal domain codomain body argument => do
      let goal ← renderRawTerm 0 .prop goal
      let body ← renderNativeCode body
      let argument ← renderRawTerm 0 domain argument
      pure (annotate goal ("(pf:eq-app " ++ renderObjectType domain ++ " " ++
        renderObjectType codomain ++ " " ++ body ++ " " ++ argument ++ ")"))
  | .equalAppArg goal domain codomain function body => do
      let goal ← renderRawTerm 0 .prop goal
      let function ← renderRawTerm 0 (.arr domain codomain) function
      let body ← renderNativeCode body
      pure (annotate goal ("(pf:eq-app-arg " ++ renderObjectType domain ++ " " ++
        renderObjectType codomain ++ " " ++ function ++ " " ++ body ++ ")"))
  | .beta goal domain codomain argument lambda => do
      let goal ← renderRawTerm 0 .prop goal
      let argument ← renderRawTerm 0 domain argument
      let lambda ← renderRawTerm 0 (.arr domain codomain) lambda
      pure (annotate goal ("(pf:beta " ++ renderObjectType domain ++ " " ++
        renderObjectType codomain ++ " " ++ argument ++ " " ++ lambda ++ ")"))

theorem renderNativeCode_defined {context : ObjectContext}
    {assumptions : List (Formula MaterialConstant context)} {goal : Formula MaterialConstant context}
    (proof : ProofSyntax MaterialConstant assumptions goal) (code : NativeCode)
    (encoded : encodeNative proof = some code) : ∃ text, renderNativeCode code = some text := by
  induction proof generalizing code with
  | hyp occurrence | eqRefl term | beta term body =>
      simp only [encodeNative, Option.some.injEq] at encoded
      rcases encoded with rfl
      simp [renderNativeCode, renderRawTerm_encode, renderRawTerm]
  | impE function argument firstIH secondIH | eqTrans function argument firstIH secondIH =>
      simp only [encodeNative, Option.bind_eq_some_iff, Option.map_eq_some_iff] at encoded
      rcases encoded with ⟨first, firstEncoded, second, secondEncoded, rfl⟩
      obtain ⟨firstText, firstPrinted⟩ := firstIH first firstEncoded
      obtain ⟨secondText, secondPrinted⟩ := secondIH second secondEncoded
      simp [renderNativeCode, firstPrinted, secondPrinted, renderRawTerm_encode]
  | impI body ih | allI body ih | allE arg body ih | eqSymm body ih | eqPropEL body ih | eqApp arg body ih | eqAppArg arg body ih =>
      simp only [encodeNative, Option.map_eq_some_iff] at encoded
      rcases encoded with ⟨bodyCode, bodyEncoded, rfl⟩
      have bodyGoal := encodedNative_goal _ bodyCode bodyEncoded
      try simp only [encodeTerm] at bodyGoal
      obtain ⟨bodyText, bodyPrinted⟩ := ih bodyCode bodyEncoded
      simp [renderNativeCode, bodyGoal, bodyPrinted, renderRawTerm_encode]
  | _ => simp only [encodeNative, reduceCtorEq] at encoded

theorem compiledSource_serializes {count : Nat} {context : ObjectContext}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {conclusion : ContextualMaterialLogic.Formula count}
    (deduction : GraphRealizedDeduction.Proof assumptions conclusion)
    (environment : Environment count context) :
    ∃ code text, encodeNative (coreProof deduction environment) = some code ∧
      renderNativeCode code = some text := by
  obtain ⟨code, encoded⟩ := (encodeNative_defined_iff _).mpr
    (compiledSource_nativeRules deduction environment)
  obtain ⟨text, printed⟩ := renderNativeCode_defined _ code encoded
  exact ⟨code, text, encoded, printed⟩

/-- Equality-rule requirements are inspectable dependencies of a receipt,
not automatic adoptions of a stronger profile. -/
def NativeCode.requiresLogicalEquality : NativeCode → Bool
  | .hypothesis _ _ => false
  | .implyIntro _ body | .allIntro _ body | .allElim _ body _ => body.requiresLogicalEquality
  | .implyElim _ first second => first.requiresLogicalEquality || second.requiresLogicalEquality
  | .equalRefl _ _ _ | .equalSymm _ _ | .equalTrans _ _ _ | .equalPropLeft _ _ |
      .equalApp _ _ _ _ _ | .equalAppArg _ _ _ _ _ | .beta _ _ _ _ _ => true

/-- This envelope retains the actual profile's typed adoptions and origins.
An arbitrary Type-valued primitive rule is not replaced by a string naming it.
The finite proof code is separate from the adoption data that authorizes its
source premises. -/
structure SerializedReceipt (profile : ProfileIndexedCalculus.Profile)
    (count : Nat) where
  declarations : List (ProfileIndexedCalculus.Declaration profile count)
  context : ObjectContext
  sourceEnvironment : List RawTerm
  premises : List RawTerm
  conclusion : RawTerm
  code : NativeCode

def serializeDerivation {profile : ProfileIndexedCalculus.Profile} {count : Nat}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {conclusion : ContextualMaterialLogic.Formula count} {context : ObjectContext}
    (derivation : ProfileIndexedCalculus.Derivation profile assumptions conclusion)
    (environment : Environment count context) : Option (SerializedReceipt profile count) :=
  (encodeNative (coreProof derivation.proof environment)).map fun code =>
    ⟨derivation.declarations, context, List.ofFn (fun index => encodeTerm (environment index)),
      ((hypotheses (ProfileIndexedCalculus.declarationFormulas derivation.declarations ++ assumptions)
        environment).map ImpredicativeConnectives.expand).map encodeTerm,
      encodeTerm (ImpredicativeConnectives.expand (formula conclusion environment)), code⟩

theorem serializeDerivation_defined {profile : ProfileIndexedCalculus.Profile} {count : Nat}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {conclusion : ContextualMaterialLogic.Formula count} {context : ObjectContext}
    (derivation : ProfileIndexedCalculus.Derivation profile assumptions conclusion)
    (environment : Environment count context) :
    ∃ receipt, serializeDerivation derivation environment = some receipt := by
  obtain ⟨code, encoded⟩ := (encodeNative_defined_iff _).mpr
    (compiledSource_nativeRules derivation.proof environment)
  simp [serializeDerivation, encoded]

theorem serializeDerivation_retains_declarations {profile : ProfileIndexedCalculus.Profile} {count : Nat}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {conclusion : ContextualMaterialLogic.Formula count} {context : ObjectContext}
    (derivation : ProfileIndexedCalculus.Derivation profile assumptions conclusion)
    (environment : Environment count context) (receipt : SerializedReceipt profile count)
    (serialized : serializeDerivation derivation environment = some receipt) :
    receipt.declarations = derivation.declarations := by
  simp only [serializeDerivation, Option.map_eq_some_iff] at serialized
  obtain ⟨code, _, rfl⟩ := serialized
  rfl

theorem serializeDerivation_retains_context {profile : ProfileIndexedCalculus.Profile} {count : Nat}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {conclusion : ContextualMaterialLogic.Formula count} {context : ObjectContext}
    (derivation : ProfileIndexedCalculus.Derivation profile assumptions conclusion)
    (environment : Environment count context) (receipt : SerializedReceipt profile count)
    (serialized : serializeDerivation derivation environment = some receipt) :
    receipt.context = context ∧
    receipt.sourceEnvironment = List.ofFn (fun index => encodeTerm (environment index)) ∧
    receipt.premises = ((hypotheses
      (ProfileIndexedCalculus.declarationFormulas derivation.declarations ++ assumptions)
      environment).map ImpredicativeConnectives.expand).map encodeTerm ∧
    receipt.conclusion = encodeTerm (ImpredicativeConnectives.expand (formula conclusion environment)) := by
  simp only [serializeDerivation, Option.map_eq_some_iff] at serialized
  obtain ⟨code, _, rfl⟩ := serialized
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem serializeDerivation_recovers_target {profile : ProfileIndexedCalculus.Profile} {count : Nat}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {conclusion : ContextualMaterialLogic.Formula count} {context : ObjectContext}
    (derivation : ProfileIndexedCalculus.Derivation profile assumptions conclusion)
    (environment : Environment count context) (receipt : SerializedReceipt profile count)
    (serialized : serializeDerivation derivation environment = some receipt) (fuel : Nat)
    (enough : (encodeProof (coreProof derivation.proof environment)).depth ≤ fuel) :
    decodeNative fuel context
      ((hypotheses (ProfileIndexedCalculus.declarationFormulas derivation.declarations ++ assumptions)
        environment).map ImpredicativeConnectives.expand)
      (ImpredicativeConnectives.expand (formula conclusion environment)) receipt.code =
        some (coreProof derivation.proof environment) := by
  simp only [serializeDerivation, Option.map_eq_some_iff] at serialized
  obtain ⟨code, encoded, rfl⟩ := serialized
  exact decodeNative_encode _ code encoded fuel enough

/-- Extract from the computed Option using its constructive existence proof,
without selecting an erased existential witness. -/
def sourceCode {count : Nat} {context : ObjectContext}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {conclusion : ContextualMaterialLogic.Formula count}
    (deduction : GraphRealizedDeduction.Proof assumptions conclusion)
    (environment : Environment count context) : NativeCode :=
  (encodeNative (coreProof deduction environment)).get (by
    obtain ⟨code, encoded⟩ := (encodeNative_defined_iff _).mpr
      (compiledSource_nativeRules deduction environment)
    simp [encoded])

theorem sourceCode_encoded {count : Nat} {context : ObjectContext}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {conclusion : ContextualMaterialLogic.Formula count}
    (deduction : GraphRealizedDeduction.Proof assumptions conclusion)
    (environment : Environment count context) :
    encodeNative (coreProof deduction environment) = some (sourceCode deduction environment) :=
  (Option.some_get _).symm

theorem sourceCode_printable {count : Nat} {context : ObjectContext}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {conclusion : ContextualMaterialLogic.Formula count}
    (deduction : GraphRealizedDeduction.Proof assumptions conclusion)
    (environment : Environment count context) :
    ∃ text, renderNativeCode (sourceCode deduction environment) = some text :=
  renderNativeCode_defined _ _ (sourceCode_encoded deduction environment)

namespace SourceControls

open ContextualMaterialLogic (Formula)
open GraphRealizedDeduction (Proof)

def bottomElimination : Proof (count := 0) [] (.all (.imply .bottom (.member 0 0))) :=
  .allIntro (.implyIntro (.bottomElim (.hypothesis 0)))

def conjunctionIntroduction : Proof (count := 0) []
    (.all (.imply (.member 0 0) (.both (.member 0 0) (.member 0 0)))) :=
  .allIntro (.implyIntro (.bothIntro (.hypothesis 0) (.hypothesis 0)))

def conjunctionLeft : Proof (count := 0) []
    (.all (.imply (.both (.member 0 0) (.equal 0 0)) (.member 0 0))) :=
  .allIntro (.implyIntro (.bothLeft (.hypothesis 0)))

def conjunctionRight : Proof (count := 0) []
    (.all (.imply (.both (.member 0 0) (.equal 0 0)) (.equal 0 0))) :=
  .allIntro (.implyIntro (.bothRight (.hypothesis 0)))

def disjunctionLeft : Proof (count := 0) []
    (.all (.imply (.member 0 0) (.either (.member 0 0) (.equal 0 0)))) :=
  .allIntro (.implyIntro (.eitherLeft (.hypothesis 0)))

def disjunctionRight : Proof (count := 0) []
    (.all (.imply (.member 0 0) (.either (.member 0 0) (.equal 0 0)))) :=
  .allIntro (.implyIntro (.eitherRight (.equalRefl 0)))

def disjunctionElimination : Proof (count := 0) []
    (.all (.imply (.either (.member 0 0) (.equal 0 0)) (.equal 0 0))) :=
  .allIntro (.implyIntro (.eitherElim (.hypothesis 0) (.equalRefl 0) (.hypothesis 0)))

def implicationElimination : Proof (count := 0) []
    (.all (.imply (.imply (.member 0 0) (.equal 0 0)) (.imply (.member 0 0) (.equal 0 0)))) :=
  .allIntro (.implyIntro (.implyIntro (.implyElim (.hypothesis 1) (.hypothesis 0))))

def universalElimination : Proof (count := 0) []
    (.all (.imply (.all (.member 0 0)) (.member 0 0))) :=
  .allIntro (.implyIntro (.allElim (body := .member 0 0) (.hypothesis 0) 0))

def existentialElimination : Proof (count := 0) []
    (.all (.imply (.exist (.member 0 1)) (.exist (.member 0 1)))) :=
  .allIntro (.implyIntro (.existElim (.hypothesis 0) (.existIntro 0 (.hypothesis 0))))

def equalityTransport : Proof (count := 0) []
    (.all (.all (.imply (.equal 1 0) (.imply (.member 1 1) (.member 0 1))))) :=
  .allIntro (.allIntro (.implyIntro (.implyIntro
    (.equalElim (body := .member 0 2) (.hypothesis 1) (.hypothesis 0)))))

def duplicateFirst : Proof (count := 0) []
    (.all (.imply (.member 0 0) (.imply (.member 0 0) (.member 0 0)))) :=
  .allIntro (.implyIntro (.implyIntro (.hypothesis 0)))

def duplicateSecond : Proof (count := 0) []
    (.all (.imply (.member 0 0) (.imply (.member 0 0) (.member 0 0)))) :=
  .allIntro (.implyIntro (.implyIntro (.hypothesis 1)))

def occurrenceWeakening : Proof (count := 0) []
    (.all (.imply (.member 0 0) (.imply (.equal 0 0) (.member 0 0)))) :=
  .allIntro (.implyIntro (.implyIntro
    (.weakening (.hypothesis (assumptions := [.member 0 0]) 0)
      (fun _ => 1) (fun index => by have same := Fin.eq_zero index; subst index; rfl))))

theorem missing_hypothesis_refused (goal : HOL.Formula MaterialConstant []) (fuel : Nat) :
    decodeNative (fuel+1) [] [] goal (.hypothesis (encodeTerm goal) 0) = none := by
  simp [decodeNative, NativeCode.toRaw, decodeProof]

theorem nonfunction_lambda_refused : renderRawTerm 0 .prop (.lam (.variable 0)) = none := rfl

end SourceControls

end Mettapedia.SetTheory.Profiles.ProfileNativeProofSerialization
