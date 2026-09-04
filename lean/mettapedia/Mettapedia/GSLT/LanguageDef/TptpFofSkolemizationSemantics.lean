import Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics

/-!
# Semantic Skolemization for canonical TPTP FOF NNF

This module defines the model-independent core of the Skolemization stage.
Original function symbols and generated Skolem symbols inhabit disjoint
constructors.  A generated symbol's arity is the number of universal binders
in scope at its existential, and its numeric identity is allocated from one
explicit preorder frontier.

The transformation is capture avoiding by construction.  Its environment maps
each source de Bruijn variable to a target term.  Universal binders extend both
the source and target depth; existential binders extend only the source depth
and are mapped to a fresh generated function applied to every current target
variable.

The first semantic theorem is the model-restriction direction: satisfaction of
the Skolem target in any extended model implies satisfaction of the source NNF
in the restricted model.  The converse requires constructing interpretations
for the generated symbols and is proved separately below rather than hidden in
the transformation definition.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics

open LO FirstOrder
open Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics

namespace Source

open Mettapedia.GSLT.LanguageDef.TptpFofNormalizationSemantics

abbrev Language := language
abbrev FunctionSymbol :=
  Mettapedia.GSLT.LanguageDef.TptpFofNormalizationSemantics.FunctionSymbol
abbrev RelationSymbol :=
  Mettapedia.GSLT.LanguageDef.TptpFofNormalizationSemantics.RelationSymbol
abbrev Term := Mettapedia.GSLT.LanguageDef.TptpFofNormalizationSemantics.Term
abbrev Formula (depth : Nat) :=
  LO.FirstOrder.Semiformula Language Empty depth
abbrev Model :=
  Mettapedia.GSLT.LanguageDef.TptpFofNormalizationSemantics.Model

end Source

/-! ## Signature extension -/

/-- A target function is either an original source function or a generated
Skolem function.  The generated identity is independent of source spellings;
external TPTP names are a later serialization concern. -/
inductive FunctionSymbol : Nat -> Type
  | original {arity : Nat} (symbol : Source.FunctionSymbol arity) :
      FunctionSymbol arity
  | generated {arity : Nat} (id : Nat) : FunctionSymbol arity
  deriving DecidableEq, Repr

/-- Skolemization adds functions but no predicates. -/
def language : LO.FirstOrder.Language where
  Func := FunctionSymbol
  Rel := Source.RelationSymbol

abbrev Term (depth : Nat) :=
  LO.FirstOrder.Semiterm language Empty depth

abbrev Formula (depth : Nat) :=
  LO.FirstOrder.Semiformula language Empty depth

/-- The literal embedding of the source signature into the Skolem signature. -/
@[reducible] def sourceEmbedding : Source.Language →ᵥ language where
  func := FunctionSymbol.original
  rel := id

/-- Restrict an extended structure to the original FOF signature. -/
@[reducible] def restrictStructure {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain) :
    LO.FirstOrder.Structure Source.Language Domain :=
  LO.FirstOrder.Structure.lMap sourceEmbedding target

/-! ## Typed environment translation -/

/-- Translate an original term through an explicit source-variable-to-target-
term environment. -/
def translateTerm {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth) :
    Source.Term sourceDepth -> Term targetDepth
  | .bvar index => environment index
  | .fvar impossible => nomatch impossible
  | .func symbol arguments =>
      .func (.original symbol) fun index =>
        translateTerm environment (arguments index)

/-- Shift every term in an environment under one new universal target binder,
and map the new source binder to target index zero. -/
def underUniversal {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth) :
    Fin (sourceDepth + 1) -> Term (targetDepth + 1) :=
  (.bvar 0 :> fun index => LO.FirstOrder.Rew.bShift (environment index))

/-- A fresh Skolem application receives every currently scoped universal
variable, in the target language's de Bruijn order. -/
def generatedApplication (targetDepth id : Nat) : Term targetDepth :=
  .func (.generated id) fun index => .bvar index

/-- Map a newly removed existential binder to its generated application. -/
def underExistential {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth) (id : Nat) :
    Fin (sourceDepth + 1) -> Term targetDepth :=
  (generatedApplication targetDepth id :> environment)

/-! ## Generated-symbol support -/

/-- Every generated function mentioned by a term has identity below `bound`. -/
def TermGeneratedBelow {depth : Nat} (bound : Nat) : Term depth -> Prop
  | .bvar _ => True
  | .fvar impossible => nomatch impossible
  | .func (.original _) arguments =>
      forall index, TermGeneratedBelow bound (arguments index)
  | .func (.generated id) arguments =>
      id < bound /\ forall index, TermGeneratedBelow bound (arguments index)

def EnvironmentGeneratedBelow {sourceDepth targetDepth : Nat}
    (bound : Nat) (environment : Fin sourceDepth -> Term targetDepth) : Prop :=
  forall index, TermGeneratedBelow bound (environment index)

def FormulaGeneratedBelow {depth : Nat} (bound : Nat) : Formula depth -> Prop
  | .verum | .falsum => True
  | .rel _ arguments | .nrel _ arguments =>
      forall index, TermGeneratedBelow bound (arguments index)
  | .and left right | .or left right =>
      FormulaGeneratedBelow bound left /\ FormulaGeneratedBelow bound right
  | .all body | .ex body => FormulaGeneratedBelow bound body

theorem TermGeneratedBelow.mono {depth first second : Nat}
    (included : first <= second) {term : Term depth}
    (bounded : TermGeneratedBelow first term) :
    TermGeneratedBelow second term := by
  induction term with
  | bvar => trivial
  | fvar impossible => exact nomatch impossible
  | func symbol arguments inductionHypothesis =>
      cases symbol with
      | original =>
          intro index
          exact inductionHypothesis index (bounded index)
      | generated id =>
          exact ⟨Nat.lt_of_lt_of_le bounded.1 included,
            fun index => inductionHypothesis index (bounded.2 index)⟩

theorem TermGeneratedBelow.bShift {depth bound : Nat}
    {term : Term depth} (bounded : TermGeneratedBelow bound term) :
    TermGeneratedBelow bound (LO.FirstOrder.Rew.bShift term) := by
  induction term with
  | bvar => trivial
  | fvar impossible => exact nomatch impossible
  | func symbol arguments inductionHypothesis =>
      rw [LO.FirstOrder.Rew.func]
      cases symbol with
      | original =>
          exact fun index => inductionHypothesis index (bounded index)
      | generated id =>
          exact ⟨bounded.1,
            fun index => inductionHypothesis index (bounded.2 index)⟩

theorem FormulaGeneratedBelow.mono {depth first second : Nat}
    (included : first <= second) {formula : Formula depth}
    (bounded : FormulaGeneratedBelow first formula) :
    FormulaGeneratedBelow second formula := by
  induction formula with
  | verum => trivial
  | falsum => trivial
  | rel relation arguments =>
      exact fun index => (bounded index).mono included
  | nrel relation arguments =>
      exact fun index => (bounded index).mono included
  | and left right leftHypothesis rightHypothesis =>
      exact ⟨leftHypothesis bounded.1, rightHypothesis bounded.2⟩
  | or left right leftHypothesis rightHypothesis =>
      exact ⟨leftHypothesis bounded.1, rightHypothesis bounded.2⟩
  | all body inductionHypothesis => exact inductionHypothesis bounded
  | ex body inductionHypothesis => exact inductionHypothesis bounded

theorem translateTerm_generatedBelow {sourceDepth targetDepth bound : Nat}
    {environment : Fin sourceDepth -> Term targetDepth}
    (bounded : EnvironmentGeneratedBelow bound environment)
    (source : Source.Term sourceDepth) :
    TermGeneratedBelow bound (translateTerm environment source) := by
  induction source with
  | bvar index => exact bounded index
  | fvar impossible => exact nomatch impossible
  | func symbol arguments inductionHypothesis =>
      exact fun index => inductionHypothesis index

theorem generatedApplication_generatedBelow {targetDepth id bound : Nat}
    (below : id < bound) :
    TermGeneratedBelow bound (generatedApplication targetDepth id) := by
  exact ⟨below, fun _ => trivial⟩

theorem underUniversal_generatedBelow
    {sourceDepth targetDepth bound : Nat}
    {environment : Fin sourceDepth -> Term targetDepth}
    (bounded : EnvironmentGeneratedBelow bound environment) :
    EnvironmentGeneratedBelow bound (underUniversal environment) := by
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · trivial
  · simpa [underUniversal] using (bounded prior).bShift

theorem underExistential_generatedBelow
    {sourceDepth targetDepth frontier : Nat}
    {environment : Fin sourceDepth -> Term targetDepth}
    (bounded : EnvironmentGeneratedBelow frontier environment) :
    EnvironmentGeneratedBelow (frontier + 1)
      (underExistential environment frontier) := by
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · exact generatedApplication_generatedBelow (Nat.lt_succ_self frontier)
  · exact (bounded prior).mono (Nat.le_succ frontier)

/-! ## Model interpretations and locality -/

/-- Interpret every generated symbol. -/
abbrev SkolemInterpretation (Domain : Type) :=
  forall arity : Nat, Nat -> (Fin arity -> Domain) -> Domain

/-- Interpret all arities at one numeric identity. -/
abbrev IdentityInterpretation (Domain : Type) :=
  forall arity : Nat, (Fin arity -> Domain) -> Domain

@[reducible] def extendStructure {Domain : Type}
    (source : LO.FirstOrder.Structure Source.Language Domain)
    (generated : SkolemInterpretation Domain) :
    LO.FirstOrder.Structure language Domain where
  func
    | _, .original symbol, arguments => source.func symbol arguments
    | arity, .generated id, arguments => generated arity id arguments
  rel := source.rel

/-- An extended model retains TPTP FOF's identity interpretation of equality. -/
structure Model (Domain : Type) where
  interpretation : LO.FirstOrder.Structure language Domain
  equality_exact : forall values : Fin 2 -> Domain,
    interpretation.rel
        Mettapedia.GSLT.LanguageDef.TptpFofNormalizationSemantics.RelationSymbol.equality
        values <->
      values 0 = values 1

def restrictModel {Domain : Type} (target : Model Domain) :
    Source.Model Domain where
  interpretation := restrictStructure target.interpretation
  equality_exact := target.equality_exact

def extendModel {Domain : Type} (source : Source.Model Domain)
    (generated : SkolemInterpretation Domain) : Model Domain where
  interpretation := extendStructure source.interpretation generated
  equality_exact := source.equality_exact

theorem restrict_extendModel_exact {Domain : Type}
    (source : Source.Model Domain) (generated : SkolemInterpretation Domain) :
    restrictModel (extendModel source generated) = source := by
  cases source
  rfl

theorem restrict_extend_exact {Domain : Type}
    (source : LO.FirstOrder.Structure Source.Language Domain)
    (generated : SkolemInterpretation Domain) :
    restrictStructure (extendStructure source generated) = source := by
  ext arity symbol arguments
  · rfl
  · rfl

/-- Override one globally fresh numeric identity while leaving every other
identity unchanged. -/
noncomputable def overrideIdentity {Domain : Type}
    (base : SkolemInterpretation Domain) (id : Nat)
    (replacement : IdentityInterpretation Domain) :
    SkolemInterpretation Domain :=
  fun arity queried arguments =>
    if queried = id then replacement arity arguments
    else base arity queried arguments

def AgreeBelow {Domain : Type} (bound : Nat)
    (left right : SkolemInterpretation Domain) : Prop :=
  forall arity id, id < bound -> left arity id = right arity id

theorem AgreeBelow.refl {Domain : Type} (bound : Nat)
    (interpretation : SkolemInterpretation Domain) :
    AgreeBelow bound interpretation interpretation := by
  intro _ _ _
  rfl

theorem AgreeBelow.symm {Domain : Type} {bound : Nat}
    {left right : SkolemInterpretation Domain}
    (agreement : AgreeBelow bound left right) :
    AgreeBelow bound right left := by
  intro arity id below
  exact (agreement arity id below).symm

theorem AgreeBelow.trans {Domain : Type} {bound : Nat}
    {first second third : SkolemInterpretation Domain}
    (firstSecond : AgreeBelow bound first second)
    (secondThird : AgreeBelow bound second third) :
    AgreeBelow bound first third := by
  intro arity id below
  exact (firstSecond arity id below).trans (secondThird arity id below)

theorem AgreeBelow.mono {Domain : Type} {firstBound secondBound : Nat}
    (included : firstBound <= secondBound)
    {left right : SkolemInterpretation Domain}
    (agreement : AgreeBelow secondBound left right) :
    AgreeBelow firstBound left right := by
  intro arity id below
  exact agreement arity id (Nat.lt_of_lt_of_le below included)

theorem overrideIdentity_agreesBelow {Domain : Type}
    (base : SkolemInterpretation Domain) (id : Nat)
    (replacement : IdentityInterpretation Domain) :
    AgreeBelow id (overrideIdentity base id replacement) base := by
  intro arity queried below
  funext arguments
  simp only [overrideIdentity, if_neg (Nat.ne_of_lt below)]

/-- Install one function at exactly one arity.  Other arities of the same
numeric identity receive an arbitrary value and are unreachable from the
well-formed generated formula. -/
noncomputable def identityAtArity {Domain : Type} [Nonempty Domain]
    (arity : Nat) (function : (Fin arity -> Domain) -> Domain) :
    IdentityInterpretation Domain :=
  fun queried arguments =>
    if equal : queried = arity then
      function (fun index => arguments (Fin.cast equal.symm index))
    else Classical.choice inferInstance

@[simp] theorem identityAtArity_exact {Domain : Type} [Nonempty Domain]
    (arity : Nat) (function : (Fin arity -> Domain) -> Domain)
    (arguments : Fin arity -> Domain) :
    identityAtArity arity function arity arguments = function arguments := by
  simp [identityAtArity]

@[simp] theorem generatedApplication_value_overrideIdentity_exact
    {Domain : Type} [Nonempty Domain]
    (source : LO.FirstOrder.Structure Source.Language Domain)
    (base : SkolemInterpretation Domain) (targetDepth id : Nat)
    (function : (Fin targetDepth -> Domain) -> Domain)
    (values : Fin targetDepth -> Domain) :
    LO.FirstOrder.Semiterm.val
        (extendStructure source
          (overrideIdentity base id (identityAtArity targetDepth function)))
        values Empty.elim (generatedApplication targetDepth id) =
      function values := by
  simp [generatedApplication, LO.FirstOrder.Semiterm.val_func,
    extendStructure, overrideIdentity]

theorem TermGeneratedBelow.value_eq_of_agreeBelow {Domain : Type}
    (source : LO.FirstOrder.Structure Source.Language Domain)
    {depth bound : Nat} {term : Term depth}
    {left right : SkolemInterpretation Domain}
    (bounded : TermGeneratedBelow bound term)
    (agreement : AgreeBelow bound left right)
    (values : Fin depth -> Domain) :
    LO.FirstOrder.Semiterm.val (extendStructure source left)
        values Empty.elim term =
      LO.FirstOrder.Semiterm.val (extendStructure source right)
        values Empty.elim term := by
  induction term with
  | bvar => rfl
  | fvar impossible => exact nomatch impossible
  | func symbol arguments inductionHypothesis =>
      cases symbol with
      | original =>
          simp only [LO.FirstOrder.Semiterm.val_func, extendStructure]
          congr 1
          funext index
          exact inductionHypothesis index (bounded index)
      | generated id =>
          simp only [LO.FirstOrder.Semiterm.val_func, extendStructure]
          rw [agreement _ id bounded.1]
          congr 1
          funext index
          exact inductionHypothesis index (bounded.2 index)

theorem EnvironmentGeneratedBelow.values_eq_of_agreeBelow {Domain : Type}
    (source : LO.FirstOrder.Structure Source.Language Domain)
    {sourceDepth targetDepth bound : Nat}
    {environment : Fin sourceDepth -> Term targetDepth}
    {left right : SkolemInterpretation Domain}
    (bounded : EnvironmentGeneratedBelow bound environment)
    (agreement : AgreeBelow bound left right)
    (values : Fin targetDepth -> Domain) :
    (fun index => LO.FirstOrder.Semiterm.val (extendStructure source left)
        values Empty.elim (environment index)) =
      (fun index => LO.FirstOrder.Semiterm.val (extendStructure source right)
        values Empty.elim (environment index)) := by
  funext index
  exact (bounded index).value_eq_of_agreeBelow source agreement values

theorem FormulaGeneratedBelow.eval_iff_of_agreeBelow {Domain : Type}
    (source : LO.FirstOrder.Structure Source.Language Domain)
    {depth bound : Nat} {formula : Formula depth}
    {left right : SkolemInterpretation Domain}
    (bounded : FormulaGeneratedBelow bound formula)
    (agreement : AgreeBelow bound left right)
    (values : Fin depth -> Domain) :
    LO.FirstOrder.Semiformula.EvalAux (extendStructure source left)
        Empty.elim values formula <->
      LO.FirstOrder.Semiformula.EvalAux (extendStructure source right)
        Empty.elim values formula := by
  induction formula with
  | verum => simp [LO.FirstOrder.Semiformula.EvalAux]
  | falsum => simp [LO.FirstOrder.Semiformula.EvalAux]
  | rel relation arguments =>
      simp only [LO.FirstOrder.Semiformula.EvalAux]
      have argumentsEqual :
          (fun index => LO.FirstOrder.Semiterm.val
            (extendStructure source left) values Empty.elim
              (arguments index)) =
          (fun index => LO.FirstOrder.Semiterm.val
            (extendStructure source right) values Empty.elim
              (arguments index)) := by
        funext index
        exact (bounded index).value_eq_of_agreeBelow source agreement values
      rw [argumentsEqual]
      exact Iff.rfl
  | nrel relation arguments =>
      simp only [LO.FirstOrder.Semiformula.EvalAux]
      have argumentsEqual :
          (fun index => LO.FirstOrder.Semiterm.val
            (extendStructure source left) values Empty.elim
              (arguments index)) =
          (fun index => LO.FirstOrder.Semiterm.val
            (extendStructure source right) values Empty.elim
              (arguments index)) := by
        funext index
        exact (bounded index).value_eq_of_agreeBelow source agreement values
      rw [argumentsEqual]
      exact Iff.rfl
  | and leftFormula rightFormula leftHypothesis rightHypothesis =>
      simpa [LO.FirstOrder.Semiformula.EvalAux] using
        and_congr (leftHypothesis bounded.1 values)
          (rightHypothesis bounded.2 values)
  | or leftFormula rightFormula leftHypothesis rightHypothesis =>
      simpa [LO.FirstOrder.Semiformula.EvalAux] using
        or_congr (leftHypothesis bounded.1 values)
          (rightHypothesis bounded.2 values)
  | all body inductionHypothesis =>
      simp only [LO.FirstOrder.Semiformula.EvalAux]
      constructor
      · intro satisfied value
        exact (inductionHypothesis bounded (value :> values)).mp
          (satisfied value)
      · intro satisfied value
        exact (inductionHypothesis bounded (value :> values)).mpr
          (satisfied value)
  | ex body inductionHypothesis =>
      simp only [LO.FirstOrder.Semiformula.EvalAux]
      constructor
      · rintro ⟨value, satisfied⟩
        exact ⟨value, (inductionHypothesis bounded (value :> values)).mp satisfied⟩
      · rintro ⟨value, satisfied⟩
        exact ⟨value, (inductionHypothesis bounded (value :> values)).mpr satisfied⟩

/-! ## Evidence-bearing output -/

/-- One freshly introduced symbol, with the arity forced by its universal
context. -/
structure IntroducedSymbol where
  id : Nat
  arity : Nat
  deriving DecidableEq, Repr

/-- The total output of one Skolemization traversal. -/
structure Output (targetDepth : Nat) where
  formula : Formula targetDepth
  next : Nat
  introduced : List IntroducedSymbol

/-- Number of existential binders in one canonical NNF formula. -/
def existentialCount {depth : Nat} : Source.Formula depth -> Nat
  | .verum | .falsum | .rel _ _ | .nrel _ _ => 0
  | .and left right | .or left right =>
      existentialCount left + existentialCount right
  | .all body => existentialCount body
  | .ex body => existentialCount body + 1

/-- Preorder Skolemization.  Conjunction and disjunction thread the frontier
left-to-right, making allocation independent of backend traversal order. -/
def skolemizeFrom {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (source : Source.Formula sourceDepth) (frontier : Nat) :
    Output targetDepth :=
  match source with
  | .verum => { formula := .verum, next := frontier, introduced := [] }
  | .falsum => { formula := .falsum, next := frontier, introduced := [] }
  | .rel relation arguments =>
      { formula := .rel relation fun index =>
          translateTerm environment (arguments index)
        next := frontier
        introduced := [] }
  | .nrel relation arguments =>
      { formula := .nrel relation fun index =>
          translateTerm environment (arguments index)
        next := frontier
        introduced := [] }
  | .and left right =>
      let leftOutput := skolemizeFrom environment left frontier
      let rightOutput := skolemizeFrom environment right leftOutput.next
      { formula := .and leftOutput.formula rightOutput.formula
        next := rightOutput.next
        introduced := leftOutput.introduced ++ rightOutput.introduced }
  | .or left right =>
      let leftOutput := skolemizeFrom environment left frontier
      let rightOutput := skolemizeFrom environment right leftOutput.next
      { formula := .or leftOutput.formula rightOutput.formula
        next := rightOutput.next
        introduced := leftOutput.introduced ++ rightOutput.introduced }
  | .all body =>
      let bodyOutput := skolemizeFrom (underUniversal environment) body frontier
      { formula := .all bodyOutput.formula
        next := bodyOutput.next
        introduced := bodyOutput.introduced }
  | .ex body =>
      let bodyOutput :=
        skolemizeFrom (underExistential environment frontier) body (frontier + 1)
      { formula := bodyOutput.formula
        next := bodyOutput.next
        introduced := ⟨frontier, targetDepth⟩ :: bodyOutput.introduced }
termination_by sizeOf source

/-- Closed NNF Skolemization begins with no source variables. -/
def skolemize (source : Source.Formula 0) : Output 0 :=
  skolemizeFrom Fin.elim0 source 0

/-! ## Exact allocation laws -/

theorem skolemizeFrom_next_exact {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (source : Source.Formula sourceDepth) (frontier : Nat) :
    (skolemizeFrom environment source frontier).next =
      frontier + existentialCount source := by
  induction source generalizing targetDepth frontier with
  | verum => simp [skolemizeFrom, existentialCount]
  | falsum => simp [skolemizeFrom, existentialCount]
  | rel => simp [skolemizeFrom, existentialCount]
  | nrel => simp [skolemizeFrom, existentialCount]
  | and left right leftHypothesis rightHypothesis =>
      simp only [skolemizeFrom, existentialCount]
      rw [rightHypothesis environment, leftHypothesis environment]
      omega
  | or left right leftHypothesis rightHypothesis =>
      simp only [skolemizeFrom, existentialCount]
      rw [rightHypothesis environment, leftHypothesis environment]
      omega
  | all body inductionHypothesis =>
      simpa [skolemizeFrom, existentialCount] using
        inductionHypothesis (targetDepth := targetDepth + 1)
          (underUniversal environment) frontier
  | ex body inductionHypothesis =>
      simp only [skolemizeFrom, existentialCount]
      rw [inductionHypothesis
        (underExistential environment frontier) (frontier + 1)]
      omega

theorem skolemize_next_exact (source : Source.Formula 0) :
    (skolemize source).next = existentialCount source := by
  simpa [skolemize] using
    skolemizeFrom_next_exact Fin.elim0 source 0

theorem skolemizeFrom_formulaGeneratedBelow
    {sourceDepth targetDepth : Nat}
    {environment : Fin sourceDepth -> Term targetDepth}
    (source : Source.Formula sourceDepth) (frontier : Nat)
    (environmentBounded : EnvironmentGeneratedBelow frontier environment) :
    FormulaGeneratedBelow (skolemizeFrom environment source frontier).next
      (skolemizeFrom environment source frontier).formula := by
  induction source generalizing targetDepth frontier with
  | verum => simp [skolemizeFrom, FormulaGeneratedBelow]
  | falsum => simp [skolemizeFrom, FormulaGeneratedBelow]
  | rel relation arguments =>
      simpa [skolemizeFrom, FormulaGeneratedBelow] using
        fun index => translateTerm_generatedBelow environmentBounded
          (arguments index)
  | nrel relation arguments =>
      simpa [skolemizeFrom, FormulaGeneratedBelow] using
        fun index => translateTerm_generatedBelow environmentBounded
          (arguments index)
  | and left right leftHypothesis rightHypothesis =>
      let leftOutput := skolemizeFrom environment left frontier
      let rightOutput := skolemizeFrom environment right leftOutput.next
      have frontierToLeft : frontier <= leftOutput.next := by
        dsimp [leftOutput]
        rw [skolemizeFrom_next_exact]
        omega
      have leftToRight : leftOutput.next <= rightOutput.next := by
        have rightNext : rightOutput.next =
            leftOutput.next + existentialCount right := by
          dsimp [rightOutput]
          exact skolemizeFrom_next_exact environment right leftOutput.next
        rw [rightNext]
        omega
      have environmentAtLeft :
          EnvironmentGeneratedBelow leftOutput.next environment :=
        fun index => (environmentBounded index).mono frontierToLeft
      have leftBounded :=
        leftHypothesis frontier environmentBounded
      have rightBounded :=
        rightHypothesis leftOutput.next environmentAtLeft
      simpa only [skolemizeFrom, FormulaGeneratedBelow] using
        And.intro (leftBounded.mono leftToRight) rightBounded
  | or left right leftHypothesis rightHypothesis =>
      let leftOutput := skolemizeFrom environment left frontier
      let rightOutput := skolemizeFrom environment right leftOutput.next
      have frontierToLeft : frontier <= leftOutput.next := by
        dsimp [leftOutput]
        rw [skolemizeFrom_next_exact]
        omega
      have leftToRight : leftOutput.next <= rightOutput.next := by
        have rightNext : rightOutput.next =
            leftOutput.next + existentialCount right := by
          dsimp [rightOutput]
          exact skolemizeFrom_next_exact environment right leftOutput.next
        rw [rightNext]
        omega
      have environmentAtLeft :
          EnvironmentGeneratedBelow leftOutput.next environment :=
        fun index => (environmentBounded index).mono frontierToLeft
      have leftBounded :=
        leftHypothesis frontier environmentBounded
      have rightBounded :=
        rightHypothesis leftOutput.next environmentAtLeft
      simpa only [skolemizeFrom, FormulaGeneratedBelow] using
        And.intro (leftBounded.mono leftToRight) rightBounded
  | all body inductionHypothesis =>
      simpa [skolemizeFrom, FormulaGeneratedBelow] using
        inductionHypothesis frontier
          (underUniversal_generatedBelow environmentBounded)
  | ex body inductionHypothesis =>
      simpa [skolemizeFrom] using
        inductionHypothesis (frontier + 1)
          (underExistential_generatedBelow environmentBounded)

theorem skolemize_formulaGeneratedBelow (source : Source.Formula 0) :
    FormulaGeneratedBelow (skolemize source).next (skolemize source).formula := by
  exact skolemizeFrom_formulaGeneratedBelow source 0 (fun index => Fin.elim0 index)

/-- Numeric identities of the generated symbols, in allocation order. -/
def introducedIds {targetDepth : Nat} (output : Output targetDepth) : List Nat :=
  output.introduced.map IntroducedSymbol.id

theorem skolemizeFrom_introducedIds_exact
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (source : Source.Formula sourceDepth) (frontier : Nat) :
    introducedIds (skolemizeFrom environment source frontier) =
      List.range' frontier (existentialCount source) := by
  induction source generalizing targetDepth frontier with
  | verum => simp [introducedIds, skolemizeFrom, existentialCount]
  | falsum => simp [introducedIds, skolemizeFrom, existentialCount]
  | rel => simp [introducedIds, skolemizeFrom, existentialCount]
  | nrel => simp [introducedIds, skolemizeFrom, existentialCount]
  | and left right leftHypothesis rightHypothesis =>
      simp only [introducedIds, skolemizeFrom, List.map_append,
        existentialCount]
      change introducedIds (skolemizeFrom environment left frontier) ++
          introducedIds (skolemizeFrom environment right
            (skolemizeFrom environment left frontier).next) =
        List.range' frontier
          (existentialCount left + existentialCount right)
      rw [leftHypothesis environment]
      rw [rightHypothesis environment]
      rw [skolemizeFrom_next_exact]
      have startExact : frontier + 1 * existentialCount left =
          frontier + existentialCount left := by
        omega
      rw [← startExact]
      exact List.range'_append
  | or left right leftHypothesis rightHypothesis =>
      simp only [introducedIds, skolemizeFrom, List.map_append,
        existentialCount]
      change introducedIds (skolemizeFrom environment left frontier) ++
          introducedIds (skolemizeFrom environment right
            (skolemizeFrom environment left frontier).next) =
        List.range' frontier
          (existentialCount left + existentialCount right)
      rw [leftHypothesis environment]
      rw [rightHypothesis environment]
      rw [skolemizeFrom_next_exact]
      have startExact : frontier + 1 * existentialCount left =
          frontier + existentialCount left := by
        omega
      rw [← startExact]
      exact List.range'_append
  | all body inductionHypothesis =>
      simpa [introducedIds, skolemizeFrom, existentialCount] using
        inductionHypothesis (targetDepth := targetDepth + 1)
          (underUniversal environment) frontier
  | ex body inductionHypothesis =>
      simp only [introducedIds, skolemizeFrom, List.map_cons,
        existentialCount]
      change frontier :: introducedIds
          (skolemizeFrom (underExistential environment frontier) body
            (frontier + 1)) =
        List.range' frontier (existentialCount body + 1)
      rw [inductionHypothesis
        (underExistential environment frontier) (frontier + 1)]
      simp [List.range'_succ]

theorem skolemizeFrom_introducedIds_nodup
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (source : Source.Formula sourceDepth) (frontier : Nat) :
    (introducedIds (skolemizeFrom environment source frontier)).Nodup := by
  rw [skolemizeFrom_introducedIds_exact]
  exact List.nodup_range'

theorem skolemize_introducedIds_exact (source : Source.Formula 0) :
    introducedIds (skolemize source) =
      List.range (existentialCount source) := by
  simpa [skolemize, List.range_eq_range'] using
    skolemizeFrom_introducedIds_exact Fin.elim0 source 0

theorem skolemize_introducedIds_nodup (source : Source.Formula 0) :
    (introducedIds (skolemize source)).Nodup := by
  rw [skolemize_introducedIds_exact]
  exact List.nodup_range

/-! ## Structural target invariant -/

/-- The target contains no existential binder. -/
def ExistentialFree {depth : Nat} : Formula depth -> Prop
  | .verum | .falsum | .rel _ _ | .nrel _ _ => True
  | .and left right | .or left right =>
      ExistentialFree left /\ ExistentialFree right
  | .all body => ExistentialFree body
  | .ex _ => False

theorem skolemizeFrom_existentialFree {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (source : Source.Formula sourceDepth) (frontier : Nat) :
    ExistentialFree (skolemizeFrom environment source frontier).formula := by
  induction source generalizing targetDepth frontier with
  | verum => simp [skolemizeFrom, ExistentialFree]
  | falsum => simp [skolemizeFrom, ExistentialFree]
  | rel => simp [skolemizeFrom, ExistentialFree]
  | nrel => simp [skolemizeFrom, ExistentialFree]
  | and left right leftHypothesis rightHypothesis =>
      simpa [skolemizeFrom, ExistentialFree] using
        And.intro
          (leftHypothesis environment frontier)
          (rightHypothesis environment
            (skolemizeFrom environment left frontier).next)
  | or left right leftHypothesis rightHypothesis =>
      simpa [skolemizeFrom, ExistentialFree] using
        And.intro
          (leftHypothesis environment frontier)
          (rightHypothesis environment
            (skolemizeFrom environment left frontier).next)
  | all body inductionHypothesis =>
      simpa [skolemizeFrom, ExistentialFree] using
        inductionHypothesis (targetDepth := targetDepth + 1)
          (underUniversal environment) frontier
  | ex body inductionHypothesis =>
      simpa [skolemizeFrom] using
        inductionHypothesis
          (underExistential environment frontier) (frontier + 1)

theorem skolemize_existentialFree (source : Source.Formula 0) :
    ExistentialFree (skolemize source).formula :=
  skolemizeFrom_existentialFree Fin.elim0 source 0

/-! ## Model restriction -/

theorem translateTerm_value_exact {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (targetValues : Fin targetDepth -> Domain)
    (source : Source.Term sourceDepth) :
    LO.FirstOrder.Semiterm.val target targetValues Empty.elim
        (translateTerm environment source) =
      LO.FirstOrder.Semiterm.val (restrictStructure target)
        (fun index => LO.FirstOrder.Semiterm.val target targetValues Empty.elim
          (environment index)) Empty.elim source := by
  induction source with
  | bvar index => rfl
  | fvar impossible => exact nomatch impossible
  | func symbol arguments inductionHypothesis =>
      simp only [translateTerm, LO.FirstOrder.Semiterm.val_func,
        restrictStructure, LO.FirstOrder.Structure.lMap_func, sourceEmbedding]
      congr 1
      funext index
      exact inductionHypothesis index

theorem eval_skolemizeFrom_iff_source_of_quantifierFree {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (source : Source.Formula sourceDepth) (frontier : Nat)
    (targetValues : Fin targetDepth -> Domain)
    (quantifierFree : QuantifierFree source) :
    LO.FirstOrder.Semiformula.EvalAux target Empty.elim targetValues
        (skolemizeFrom environment source frontier).formula <->
      LO.FirstOrder.Semiformula.EvalAux (restrictStructure target) Empty.elim
        (fun index => LO.FirstOrder.Semiterm.val target targetValues Empty.elim
          (environment index)) source := by
  induction source generalizing targetDepth frontier with
  | verum => simp [skolemizeFrom, LO.FirstOrder.Semiformula.EvalAux]
  | falsum => simp [skolemizeFrom, LO.FirstOrder.Semiformula.EvalAux]
  | rel relation arguments =>
      simp [skolemizeFrom, LO.FirstOrder.Semiformula.EvalAux,
        translateTerm_value_exact]
  | nrel relation arguments =>
      simp [skolemizeFrom, LO.FirstOrder.Semiformula.EvalAux,
        translateTerm_value_exact]
  | and left right leftHypothesis rightHypothesis =>
      simp only [QuantifierFree] at quantifierFree
      simp only [skolemizeFrom, LO.FirstOrder.Semiformula.EvalAux]
      exact and_congr
        (leftHypothesis environment frontier targetValues quantifierFree.1)
        (rightHypothesis environment
          (skolemizeFrom environment left frontier).next
          targetValues quantifierFree.2)
  | or left right leftHypothesis rightHypothesis =>
      simp only [QuantifierFree] at quantifierFree
      simp only [skolemizeFrom, LO.FirstOrder.Semiformula.EvalAux]
      exact or_congr
        (leftHypothesis environment frontier targetValues quantifierFree.1)
        (rightHypothesis environment
          (skolemizeFrom environment left frontier).next
          targetValues quantifierFree.2)
  | all body inductionHypothesis =>
      simp [QuantifierFree] at quantifierFree
  | ex body inductionHypothesis =>
      simp [QuantifierFree] at quantifierFree

private theorem underUniversal_value_exact {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (targetValues : Fin targetDepth -> Domain) (value : Domain) :
    (fun index => LO.FirstOrder.Semiterm.val target (value :> targetValues)
      Empty.elim (underUniversal environment index)) =
      (value :> fun index => LO.FirstOrder.Semiterm.val target targetValues
        Empty.elim (environment index)) := by
  funext index
  refine Fin.cases ?_ (fun prior => ?_) index
  · rfl
  · simp [underUniversal]

private theorem underExistential_value_exact {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (targetValues : Fin targetDepth -> Domain) (id : Nat) :
    (fun index => LO.FirstOrder.Semiterm.val target targetValues Empty.elim
      (underExistential environment id index)) =
      (LO.FirstOrder.Semiterm.val target targetValues Empty.elim
          (generatedApplication targetDepth id) :>
        fun index => LO.FirstOrder.Semiterm.val target targetValues Empty.elim
          (environment index)) := by
  funext index
  refine Fin.cases ?_ (fun _ => ?_) index <;> rfl

/-! ## Forward model extension for prenex input -/

/-- A satisfying source model extends to a satisfying Skolem model for prenex
NNF.  The theorem is predicate-indexed over target environments so universal
choices are uniform and existential witnesses become genuine functions of the
universals in scope. -/
theorem extendInterpretation_for_prenex
    {Domain : Type} [Nonempty Domain]
    (sourceStructure : LO.FirstOrder.Structure Source.Language Domain)
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (source : Source.Formula sourceDepth) (prenex : Prenex source)
    (frontier : Nat) (base : SkolemInterpretation Domain)
    (environmentBounded : EnvironmentGeneratedBelow frontier environment)
    (admissible : (Fin targetDepth -> Domain) -> Prop)
    (sourceSatisfied : forall values, admissible values ->
      LO.FirstOrder.Semiformula.EvalAux sourceStructure Empty.elim
        (fun index => LO.FirstOrder.Semiterm.val
          (extendStructure sourceStructure base) values Empty.elim
            (environment index)) source) :
    exists extended : SkolemInterpretation Domain,
      AgreeBelow frontier extended base /\
      forall values, admissible values ->
        LO.FirstOrder.Semiformula.EvalAux
          (extendStructure sourceStructure extended) Empty.elim values
          (skolemizeFrom environment source frontier).formula := by
  classical
  induction prenex generalizing targetDepth frontier base with
  | @matrix depth formula quantifierFree =>
      refine ⟨base, AgreeBelow.refl frontier base, ?_⟩
      intro values valuesAdmissible
      have exactSemantics :=
        eval_skolemizeFrom_iff_source_of_quantifierFree
          (extendStructure sourceStructure base) environment formula frontier
          values quantifierFree
      rw [restrict_extend_exact] at exactSemantics
      exact exactSemantics.mpr (sourceSatisfied values valuesAdmissible)
  | @all depth body bodyPrenex inductionHypothesis =>
      let bodyAdmissible : (Fin (targetDepth + 1) -> Domain) -> Prop :=
        fun extendedValues =>
          exists (values : Fin targetDepth -> Domain) (value : Domain),
            admissible values /\ extendedValues = (value :> values)
      have bodySatisfied : forall extendedValues,
          bodyAdmissible extendedValues ->
          LO.FirstOrder.Semiformula.EvalAux sourceStructure Empty.elim
            (fun index => LO.FirstOrder.Semiterm.val
                (extendStructure sourceStructure base) extendedValues Empty.elim
                (underUniversal environment index)) body := by
        intro extendedValues witness
        rcases witness with ⟨values, value, valuesAdmissible, rfl⟩
        have outerSatisfied := sourceSatisfied values valuesAdmissible
        have innerSatisfied := outerSatisfied value
        simpa only [underUniversal_value_exact
          (extendStructure sourceStructure base) environment values value]
          using innerSatisfied
      rcases inductionHypothesis
          (targetDepth := targetDepth + 1)
          (underUniversal environment) frontier base
          (underUniversal_generatedBelow environmentBounded)
          bodyAdmissible bodySatisfied with
        ⟨extended, agreement, targetSatisfied⟩
      refine ⟨extended, agreement, ?_⟩
      intro values valuesAdmissible
      simp only [skolemizeFrom, LO.FirstOrder.Semiformula.EvalAux]
      intro value
      exact targetSatisfied (value :> values)
        ⟨values, value, valuesAdmissible, rfl⟩
  | @ex depth body bodyPrenex inductionHypothesis =>
      have sourceWitness : forall values, admissible values ->
          exists value : Domain,
            LO.FirstOrder.Semiformula.EvalAux sourceStructure Empty.elim
              (value :> fun index => LO.FirstOrder.Semiterm.val
                (extendStructure sourceStructure base) values Empty.elim
                  (environment index)) body := by
        intro values valuesAdmissible
        exact sourceSatisfied values valuesAdmissible
      let witness : (Fin targetDepth -> Domain) -> Domain :=
        fun values =>
          if valuesAdmissible : admissible values then
            Classical.choose (sourceWitness values valuesAdmissible)
          else Classical.choice inferInstance
      have witnessSatisfied : forall values (valuesAdmissible : admissible values),
          LO.FirstOrder.Semiformula.EvalAux sourceStructure Empty.elim
            (witness values :> fun index => LO.FirstOrder.Semiterm.val
              (extendStructure sourceStructure base) values Empty.elim
                (environment index)) body := by
        intro values valuesAdmissible
        simpa [witness, valuesAdmissible] using
          Classical.choose_spec (sourceWitness values valuesAdmissible)
      let current := overrideIdentity base frontier
        (identityAtArity targetDepth witness)
      have currentAgrees : AgreeBelow frontier current base := by
        exact overrideIdentity_agreesBelow base frontier
          (identityAtArity targetDepth witness)
      have bodyEnvironmentBounded :
          EnvironmentGeneratedBelow (frontier + 1)
            (underExistential environment frontier) :=
        underExistential_generatedBelow environmentBounded
      have bodySatisfied : forall values, admissible values ->
          LO.FirstOrder.Semiformula.EvalAux sourceStructure Empty.elim
            (fun index => LO.FirstOrder.Semiterm.val
              (extendStructure sourceStructure current) values Empty.elim
                (underExistential environment frontier index)) body := by
        intro values valuesAdmissible
        have oldValuesEqual :=
          environmentBounded.values_eq_of_agreeBelow sourceStructure
            currentAgrees values
        have environmentExact :
            (fun index => LO.FirstOrder.Semiterm.val
              (extendStructure sourceStructure current) values Empty.elim
                (underExistential environment frontier index)) =
              (witness values :> fun index => LO.FirstOrder.Semiterm.val
                (extendStructure sourceStructure base) values Empty.elim
                  (environment index)) := by
          funext index
          refine Fin.cases ?_ (fun prior => ?_) index
          · simp [underExistential, current]
          · exact congrFun oldValuesEqual prior
        rw [environmentExact]
        exact witnessSatisfied values valuesAdmissible
      rcases inductionHypothesis
          (underExistential environment frontier) (frontier + 1) current
          bodyEnvironmentBounded admissible bodySatisfied with
        ⟨extended, extendedAgrees, targetSatisfied⟩
      refine ⟨extended, ?_, ?_⟩
      · exact (extendedAgrees.mono (Nat.le_succ frontier)).trans currentAgrees
      · simpa only [skolemizeFrom] using targetSatisfied

/-- Any model of the generated target restricts to a model of the source NNF.
This is the nontrivial, calculus-independent backward half of Skolem
equisatisfiability. -/
theorem eval_skolemizeFrom_implies_source {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth -> Term targetDepth)
    (source : Source.Formula sourceDepth) (frontier : Nat)
    (targetValues : Fin targetDepth -> Domain) :
    LO.FirstOrder.Semiformula.EvalAux target Empty.elim targetValues
        (skolemizeFrom environment source frontier).formula ->
      LO.FirstOrder.Semiformula.EvalAux (restrictStructure target) Empty.elim
        (fun index => LO.FirstOrder.Semiterm.val target targetValues Empty.elim
          (environment index)) source := by
  induction source generalizing targetDepth frontier with
  | verum => simp [skolemizeFrom, LO.FirstOrder.Semiformula.EvalAux]
  | falsum => simp [skolemizeFrom, LO.FirstOrder.Semiformula.EvalAux]
  | rel relation arguments =>
      simp [skolemizeFrom, LO.FirstOrder.Semiformula.EvalAux,
        translateTerm_value_exact]
  | nrel relation arguments =>
      simp [skolemizeFrom, LO.FirstOrder.Semiformula.EvalAux,
        translateTerm_value_exact]
  | and left right leftHypothesis rightHypothesis =>
      simp only [skolemizeFrom, LO.FirstOrder.Semiformula.EvalAux]
      intro satisfied
      exact ⟨leftHypothesis environment frontier targetValues satisfied.1,
        rightHypothesis environment
          (skolemizeFrom environment left frontier).next
          targetValues satisfied.2⟩
  | or left right leftHypothesis rightHypothesis =>
      simp only [skolemizeFrom, LO.FirstOrder.Semiformula.EvalAux]
      intro satisfied
      rcases satisfied with leftSatisfied | rightSatisfied
      · exact Or.inl
          (leftHypothesis environment frontier targetValues leftSatisfied)
      · exact Or.inr
          (rightHypothesis environment
            (skolemizeFrom environment left frontier).next
            targetValues rightSatisfied)
  | all body inductionHypothesis =>
      simp only [skolemizeFrom, LO.FirstOrder.Semiformula.EvalAux]
      intro satisfied value
      have bodySatisfied := satisfied value
      have reflected := inductionHypothesis
        (underUniversal environment) frontier
        (value :> targetValues) bodySatisfied
      simpa only [underUniversal_value_exact target environment targetValues value]
        using reflected
  | ex body inductionHypothesis =>
      simp only [skolemizeFrom, LO.FirstOrder.Semiformula.EvalAux]
      intro satisfied
      let witness := LO.FirstOrder.Semiterm.val target targetValues Empty.elim
        (generatedApplication targetDepth frontier)
      refine ⟨witness, ?_⟩
      have reflected := inductionHypothesis
        (underExistential environment frontier) (frontier + 1)
        targetValues satisfied
      simpa only [underExistential_value_exact target environment targetValues frontier]
        using reflected

theorem eval_skolemize_implies_source {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    (source : Source.Formula 0) :
    LO.FirstOrder.Semiformula.EvalAux target Empty.elim ![]
        (skolemize source).formula ->
      LO.FirstOrder.Semiformula.EvalAux (restrictStructure target) Empty.elim
        ![] source := by
  have reflected :=
    eval_skolemizeFrom_implies_source target Fin.elim0 source 0 ![]
  simpa only [skolemize, Subsingleton.elim
    (fun index : Fin 0 =>
      LO.FirstOrder.Semiterm.val target ![] Empty.elim (Fin.elim0 index)) ![]]
    using reflected

/-! ## Model-level equisatisfiability -/

def SourceSatisfiable (source : Source.Formula 0) : Prop :=
  exists (Domain : Type) (_ : Nonempty Domain) (model : Source.Model Domain),
    LO.FirstOrder.Semiformula.EvalAux model.interpretation Empty.elim ![] source

def Satisfiable (target : Formula 0) : Prop :=
  exists (Domain : Type) (_ : Nonempty Domain) (model : Model Domain),
    LO.FirstOrder.Semiformula.EvalAux model.interpretation Empty.elim ![] target

theorem sourceSatisfiable_iff_skolemSatisfiable_of_prenex
    (source : Source.Formula 0) (prenex : Prenex source) :
    SourceSatisfiable source <-> Satisfiable (skolemize source).formula := by
  constructor
  · rintro ⟨Domain, domainNonempty, sourceModel, sourceSatisfied⟩
    letI : Nonempty Domain := domainNonempty
    let base : SkolemInterpretation Domain :=
      fun _ _ _ => Classical.choice domainNonempty
    have environmentBounded : EnvironmentGeneratedBelow 0
        (Fin.elim0 : Fin 0 -> Term 0) := by
      intro index
      exact Fin.elim0 index
    have sourceSatisfiedForEmpty :
        forall values : Fin 0 -> Domain, True ->
          LO.FirstOrder.Semiformula.EvalAux sourceModel.interpretation
            Empty.elim
            (fun index => LO.FirstOrder.Semiterm.val
              (extendStructure sourceModel.interpretation base)
              values Empty.elim (Fin.elim0 index)) source := by
      intro values _
      simpa only [Subsingleton.elim
        (fun index : Fin 0 => LO.FirstOrder.Semiterm.val
          (extendStructure sourceModel.interpretation base)
          values Empty.elim (Fin.elim0 index)) ![]] using sourceSatisfied
    rcases extendInterpretation_for_prenex sourceModel.interpretation
        (Fin.elim0 : Fin 0 -> Term 0) source prenex 0 base
        environmentBounded (fun _ => True) sourceSatisfiedForEmpty with
      ⟨extended, _agreement, targetSatisfied⟩
    refine ⟨Domain, domainNonempty, extendModel sourceModel extended, ?_⟩
    simpa only [skolemize, extendModel] using targetSatisfied ![] trivial
  · rintro ⟨Domain, domainNonempty, targetModel, targetSatisfied⟩
    refine ⟨Domain, domainNonempty, restrictModel targetModel, ?_⟩
    exact eval_skolemize_implies_source targetModel.interpretation source
      targetSatisfied

/-! ## Total NNF-to-prenex-to-Skolem composition -/

/-- The public semantic core first performs the proved equivalence-preserving
prenex transformation and only then performs the equisatisfiable signature
extension.  This is not yet CNF conversion. -/
def prenexSkolemize (source : Source.Formula 0) : Output 0 :=
  skolemize
    (Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.normalize source)

theorem sourceSatisfiable_iff_prenexNormalizedSatisfiable
    (source : Source.Formula 0) :
    SourceSatisfiable source <->
      SourceSatisfiable
        (Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.normalize source) := by
  constructor
  · rintro ⟨Domain, domainNonempty, model, sourceSatisfied⟩
    letI : Nonempty Domain := domainNonempty
    refine ⟨Domain, domainNonempty, model, ?_⟩
    exact
      (Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.normalize_eval_exact
        model.interpretation ![] source).mpr sourceSatisfied
  · rintro ⟨Domain, domainNonempty, model, normalizedSatisfied⟩
    letI : Nonempty Domain := domainNonempty
    refine ⟨Domain, domainNonempty, model, ?_⟩
    exact
      (Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.normalize_eval_exact
        model.interpretation ![] source).mp normalizedSatisfied

theorem sourceSatisfiable_iff_prenexSkolemSatisfiable
    (source : Source.Formula 0) :
    SourceSatisfiable source <->
      Satisfiable (prenexSkolemize source).formula := by
  exact
    (sourceSatisfiable_iff_prenexNormalizedSatisfiable source).trans <| by
      simpa only [prenexSkolemize] using
        sourceSatisfiable_iff_skolemSatisfiable_of_prenex
          (Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.normalize source)
          (Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.normalize_prenex
            source)

theorem prenexSkolemize_existentialFree (source : Source.Formula 0) :
    ExistentialFree (prenexSkolemize source).formula := by
  exact skolemize_existentialFree
    (Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.normalize source)

theorem prenexSkolemize_introducedIds_exact (source : Source.Formula 0) :
    introducedIds (prenexSkolemize source) =
      List.range
        (existentialCount
          (Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.normalize source)) := by
  exact skolemize_introducedIds_exact
    (Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.normalize source)

/-! ## Canaries -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.TptpFofNormalizationSemantics

def p : PredicateSymbol 2 := ⟨"p", .plain⟩

/-- `forall x, exists y, p(x,y)` introduces one unary Skolem function. -/
def source : Source.Formula 0 :=
  .all (.ex (.rel (.predicate p) ![.bvar 1, .bvar 0]))

def expected : Formula 0 :=
  .all (.rel (.predicate p)
    ![.bvar 0, generatedApplication 1 0])

theorem source_skolemizes_exactly :
    (skolemize source).formula = expected := by
  simp [skolemize, source, expected, skolemizeFrom, underUniversal,
    underExistential, generatedApplication]
  funext index
  fin_cases index <;> rfl

theorem source_introduces_exact_symbol :
    (skolemize source).introduced = [⟨0, 1⟩] := by
  simp [skolemize, source, skolemizeFrom]

theorem source_frontier_exact :
    (skolemize source).next = 1 := by
  simp [skolemize, source, skolemizeFrom]

theorem source_is_prenex : Prenex source := by
  exact .all (.ex (.matrix (by simp [QuantifierFree])))

theorem source_is_equisatisfiable_with_target :
    SourceSatisfiable source <-> Satisfiable (skolemize source).formula :=
  sourceSatisfiable_iff_skolemSatisfiable_of_prenex source source_is_prenex

/-- Nested shadowing is represented by indices, so the existential depends on
both universal binders even if a concrete source reused their spellings. -/
def nestedSource : Source.Formula 0 :=
  .all (.all (.ex (.rel (.predicate p) ![.bvar 2, .bvar 0])))

theorem nested_source_introduces_binary_symbol :
    (skolemize nestedSource).introduced = [⟨0, 2⟩] := by
  simp [skolemize, nestedSource, skolemizeFrom]

/-- Quantifiers below a Boolean connective are NNF but not prenex.  They must
pass through the preceding equivalence-preserving prenex transformation before
the forward model-extension theorem is invoked. -/
def nonPrenexSource : Source.Formula 0 :=
  .or (.ex .verum) .verum

theorem non_prenex_source_is_rejected : Not (Prenex nonPrenexSource) := by
  intro accepted
  cases accepted with
  | matrix quantifierFree =>
      simp [nonPrenexSource, QuantifierFree] at quantifierFree

/-- A Skolem target containing an existential cannot be produced. -/
theorem target_existential_is_rejected :
    Not (ExistentialFree (.ex (.verum : Formula 1))) := by
  simp [ExistentialFree]

namespace Composed

abbrev source : Source.Formula 0 :=
  Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.Canary.source

def expected : Formula 0 :=
  .all
    (.or
      (.rel
        (.predicate
          Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.Canary.p)
        ![.func (.generated 0) ![]])
      (.rel
        (.predicate
          Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.Canary.q)
        ![.bvar 0]))

theorem source_was_not_prenex : Not (Prenex source) :=
  Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.Canary.source_not_prenex

theorem source_prenex_skolemizes_exactly :
    (prenexSkolemize source).formula = expected := by
  change
    (skolemize
      (Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.normalize source)).formula =
      expected
  rw [Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.Canary.source_normalizes_exactly]
  simp [skolemize, skolemizeFrom, expected, underUniversal,
    underExistential, generatedApplication, translateTerm,
    Matrix.constant_eq_singleton]

theorem source_introduces_exact_constant :
    (prenexSkolemize source).introduced = [⟨0, 0⟩] := by
  change
    (skolemize
      (Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.normalize source)).introduced =
      [⟨0, 0⟩]
  rw [Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.Canary.source_normalizes_exactly]
  simp [skolemize, skolemizeFrom]

theorem source_target_is_existentialFree :
    ExistentialFree (prenexSkolemize source).formula :=
  prenexSkolemize_existentialFree source

theorem source_is_equisatisfiable_with_target :
    SourceSatisfiable source <->
      Satisfiable (prenexSkolemize source).formula :=
  sourceSatisfiable_iff_prenexSkolemSatisfiable source

end Composed

end Canary

#print axioms skolemizeFrom_next_exact
#print axioms skolemize_next_exact
#print axioms skolemizeFrom_formulaGeneratedBelow
#print axioms skolemize_formulaGeneratedBelow
#print axioms skolemizeFrom_introducedIds_exact
#print axioms skolemizeFrom_introducedIds_nodup
#print axioms skolemize_introducedIds_exact
#print axioms skolemize_introducedIds_nodup
#print axioms skolemizeFrom_existentialFree
#print axioms skolemize_existentialFree
#print axioms restrict_extendModel_exact
#print axioms FormulaGeneratedBelow.eval_iff_of_agreeBelow
#print axioms translateTerm_value_exact
#print axioms eval_skolemizeFrom_iff_source_of_quantifierFree
#print axioms extendInterpretation_for_prenex
#print axioms eval_skolemizeFrom_implies_source
#print axioms eval_skolemize_implies_source
#print axioms sourceSatisfiable_iff_skolemSatisfiable_of_prenex
#print axioms sourceSatisfiable_iff_prenexNormalizedSatisfiable
#print axioms sourceSatisfiable_iff_prenexSkolemSatisfiable
#print axioms Canary.source_skolemizes_exactly
#print axioms Canary.source_introduces_exact_symbol
#print axioms Canary.source_is_equisatisfiable_with_target
#print axioms Canary.Composed.source_prenex_skolemizes_exactly
#print axioms Canary.Composed.source_is_equisatisfiable_with_target
#print axioms Canary.nested_source_introduces_binary_symbol
#print axioms Canary.non_prenex_source_is_rejected
#print axioms Canary.target_existential_is_rejected

end Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics
