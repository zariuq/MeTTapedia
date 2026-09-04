import Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics

/-!
# Evidence-bearing definitional naming for Skolem FOF matrices

This module defines the semantic authority for the structure-preserving naming
stage that follows Skolemization.  It is deliberately independent of TPTP
concrete syntax and of proof search.

The input is a quantifier-free Skolem matrix at an arbitrary universal depth.
Every Boolean connective is named by one fresh predicate applied to the complete
enclosing universal environment.  Children are named before their parent, so
the definition list is already in topological order.  Each record retains its
source subformula and the two generated child references.  That redundancy is
intentional evidence: it supports both model-extension and independently
checked clause generation.

The first authority uses full equivalences.  A later polarity-sensitive
Plaisted--Greenbaum pass may remove directions, but must be proved as an
optimization of this stronger object rather than replacing its semantics.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingSemantics

open LO FirstOrder
open scoped LO.FirstOrder

namespace Source

abbrev Language : LO.FirstOrder.Language :=
  Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.language
abbrev FunctionSymbol (arity : Nat) :=
  Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.FunctionSymbol arity
abbrev RelationSymbol (arity : Nat) :=
  Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.Source.RelationSymbol
    arity
abbrev Term (depth : Nat) :=
  Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.Term depth
abbrev Formula (depth : Nat) :=
  Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.Formula depth
abbrev Model (Domain : Type) :=
  Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.Model Domain

end Source

/-- The Skolem matrix contains no remaining quantifier.  This is deliberately
stated over the extended Skolem signature rather than reusing the preceding
source-signature predicate. -/
def QuantifierFree {depth : Nat} : Source.Formula depth -> Prop
  | .verum | .falsum | .rel _ _ | .nrel _ _ => True
  | .and left right | .or left right =>
      QuantifierFree left /\ QuantifierFree right
  | .all _ | .ex _ => False

theorem QuantifierFree.existentialFree {depth : Nat}
    {source : Source.Formula depth} (quantifierFree : QuantifierFree source) :
    Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.ExistentialFree
      source := by
  induction source with
  | verum | falsum | rel | nrel => trivial
  | and left right leftHypothesis rightHypothesis =>
      exact ⟨leftHypothesis quantifierFree.1,
        rightHypothesis quantifierFree.2⟩
  | or left right leftHypothesis rightHypothesis =>
      exact ⟨leftHypothesis quantifierFree.1,
        rightHypothesis quantifierFree.2⟩
  | all body inductionHypothesis => contradiction
  | ex body inductionHypothesis => contradiction

/-! ## Explicit universal-prefix boundary -/

/-- A Skolem formula accepted for clausification consists only of universal
binders followed by a quantifier-free matrix. -/
inductive UniversalPrefix : {depth : Nat} -> Source.Formula depth -> Type
  | matrix {depth : Nat} {source : Source.Formula depth} :
      QuantifierFree source -> UniversalPrefix source
  | all {depth : Nat} {body : Source.Formula (depth + 1)} :
      UniversalPrefix body -> UniversalPrefix (.all body)

structure OpenedMatrix where
  depth : Nat
  formula : Source.Formula depth
  quantifierFree : QuantifierFree formula

theorem UniversalPrefix.existentialFree {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source) :
    Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.ExistentialFree
      source := by
  induction evidence with
  | matrix quantifierFree => exact quantifierFree.existentialFree
  | all bodyPrefix inductionHypothesis => exact inductionHypothesis

def UniversalPrefix.opened {depth : Nat} {source : Source.Formula depth} :
    UniversalPrefix source → OpenedMatrix
  | .matrix quantifierFree => ⟨depth, source, quantifierFree⟩
  | .all bodyPrefix => bodyPrefix.opened

/-- Computational evidence that the first non-universal formula is a matrix. -/
def quantifierFreeWitness? {depth : Nat} :
    (source : Source.Formula depth) -> Option (PLift (QuantifierFree source))
  | .verum => some ⟨trivial⟩
  | .falsum => some ⟨trivial⟩
  | .rel _ _ => some ⟨trivial⟩
  | .nrel _ _ => some ⟨trivial⟩
  | .and left right =>
      match quantifierFreeWitness? left, quantifierFreeWitness? right with
      | some leftWitness, some rightWitness =>
          some ⟨leftWitness.down, rightWitness.down⟩
      | _, _ => none
  | .or left right =>
      match quantifierFreeWitness? left, quantifierFreeWitness? right with
      | some leftWitness, some rightWitness =>
          some ⟨leftWitness.down, rightWitness.down⟩
      | _, _ => none
  | .all _ => none
  | .ex _ => none

theorem quantifierFreeWitness?_complete {depth : Nat}
    (source : Source.Formula depth) (quantifierFree : QuantifierFree source) :
    exists witness, quantifierFreeWitness? source = some witness := by
  induction source with
  | verum => exact ⟨⟨trivial⟩, rfl⟩
  | falsum => exact ⟨⟨trivial⟩, rfl⟩
  | rel => exact ⟨⟨trivial⟩, rfl⟩
  | nrel => exact ⟨⟨trivial⟩, rfl⟩
  | and left right leftHypothesis rightHypothesis =>
      rcases leftHypothesis quantifierFree.1 with ⟨leftWitness, leftExact⟩
      rcases rightHypothesis quantifierFree.2 with ⟨rightWitness, rightExact⟩
      exact ⟨⟨leftWitness.down, rightWitness.down⟩, by
        simp [quantifierFreeWitness?, leftExact, rightExact]⟩
  | or left right leftHypothesis rightHypothesis =>
      rcases leftHypothesis quantifierFree.1 with ⟨leftWitness, leftExact⟩
      rcases rightHypothesis quantifierFree.2 with ⟨rightWitness, rightExact⟩
      exact ⟨⟨leftWitness.down, rightWitness.down⟩, by
        simp [quantifierFreeWitness?, leftExact, rightExact]⟩
  | all body inductionHypothesis => contradiction
  | ex body inductionHypothesis => contradiction

/-- Remove only a leading universal prefix.  A quantifier below a Boolean
connective or any existential makes the operation fail closed. -/
def openUniversals? {depth : Nat} :
    (source : Source.Formula depth) -> Option OpenedMatrix
  | .all body => openUniversals? body
  | source =>
      match quantifierFreeWitness? source with
      | some witness => some ⟨depth, source, witness.down⟩
      | none => none

theorem openUniversals?_eq_some_of_quantifierFree
    {depth : Nat} (source : Source.Formula depth)
    (quantifierFree : QuantifierFree source) :
    exists opened, openUniversals? source = some opened := by
  cases source with
  | verum | falsum | rel | nrel | and | or =>
      rcases quantifierFreeWitness?_complete _ quantifierFree with
        ⟨witness, witnessExact⟩
      exact ⟨⟨depth, _, witness.down⟩, by
        simp [openUniversals?, witnessExact]⟩
  | all body => contradiction
  | ex body => contradiction

theorem UniversalPrefix.openUniversals?_exact {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source) :
    openUniversals? source = some evidence.opened := by
  induction evidence with
  | @matrix depth source quantifierFree =>
      cases source with
      | verum => simp [openUniversals?, quantifierFreeWitness?, UniversalPrefix.opened]
      | falsum => simp [openUniversals?, quantifierFreeWitness?, UniversalPrefix.opened]
      | rel => simp [openUniversals?, quantifierFreeWitness?, UniversalPrefix.opened]
      | nrel => simp [openUniversals?, quantifierFreeWitness?, UniversalPrefix.opened]
      | and left right =>
          change QuantifierFree left ∧ QuantifierFree right at quantifierFree
          rcases quantifierFreeWitness?_complete left quantifierFree.1 with
            ⟨leftWitness, leftExact⟩
          rcases quantifierFreeWitness?_complete right quantifierFree.2 with
            ⟨rightWitness, rightExact⟩
          simp [openUniversals?, quantifierFreeWitness?, leftExact, rightExact,
            UniversalPrefix.opened]
      | or left right =>
          change QuantifierFree left ∧ QuantifierFree right at quantifierFree
          rcases quantifierFreeWitness?_complete left quantifierFree.1 with
            ⟨leftWitness, leftExact⟩
          rcases quantifierFreeWitness?_complete right quantifierFree.2 with
            ⟨rightWitness, rightExact⟩
          simp [openUniversals?, quantifierFreeWitness?, leftExact, rightExact,
            UniversalPrefix.opened]
      | all body => contradiction
      | ex body => contradiction
  | all bodyPrefix inductionHypothesis =>
      simpa [openUniversals?, UniversalPrefix.opened] using inductionHypothesis

/-- Universally quantifying every remaining free variable is exactly the
meaning of removing an explicit all-only prefix. -/
theorem openUniversals?_eval_iff {Domain : Type}
    (interpretation : LO.FirstOrder.Structure Source.Language Domain)
    {depth : Nat} {source : Source.Formula depth}
    (opened : OpenedMatrix)
    (openedExact : openUniversals? source = some opened) :
    (forall values : Fin depth -> Domain,
      LO.FirstOrder.Semiformula.EvalAux interpretation Empty.elim values
        source) <->
    (forall values : Fin opened.depth -> Domain,
      LO.FirstOrder.Semiformula.EvalAux interpretation Empty.elim values
        opened.formula) := by
  induction source generalizing opened with
  | verum => simp [openUniversals?, quantifierFreeWitness?] at openedExact; subst opened; rfl
  | falsum => simp [openUniversals?, quantifierFreeWitness?] at openedExact; subst opened; rfl
  | rel => simp [openUniversals?, quantifierFreeWitness?] at openedExact; subst opened; rfl
  | nrel => simp [openUniversals?, quantifierFreeWitness?] at openedExact; subst opened; rfl
  | and left right leftHypothesis rightHypothesis =>
      cases leftExact : quantifierFreeWitness? left <;>
        cases rightExact : quantifierFreeWitness? right <;>
        simp [openUniversals?, quantifierFreeWitness?, leftExact,
          rightExact] at openedExact
      subst opened
      rfl
  | or left right leftHypothesis rightHypothesis =>
      cases leftExact : quantifierFreeWitness? left <;>
        cases rightExact : quantifierFreeWitness? right <;>
        simp [openUniversals?, quantifierFreeWitness?, leftExact,
          rightExact] at openedExact
      subst opened
      rfl
  | @all depth body inductionHypothesis =>
      simp only [openUniversals?] at openedExact
      have swap :
          (forall (values : Fin depth -> Domain) (value : Domain),
            LO.FirstOrder.Semiformula.EvalAux interpretation Empty.elim
              (value :> values) body) <->
          (forall (value : Domain) (values : Fin depth -> Domain),
            LO.FirstOrder.Semiformula.EvalAux interpretation Empty.elim
              (value :> values) body) := by
        constructor <;> intro hypothesis first second
        · exact hypothesis second first
        · exact hypothesis second first
      simpa only [LO.FirstOrder.Semiformula.EvalAux] using
        (swap.trans (Fin.forall_vec_iff_forall_forall_vec.symm.trans
          (inductionHypothesis opened openedExact)))
  | ex body inductionHypothesis =>
      simp [openUniversals?, quantifierFreeWitness?] at openedExact

/-- Skolemizing a quantifier-free source matrix produces a quantifier-free
target matrix. -/
theorem skolemizeFrom_quantifierFree
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth ->
      Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.Term
        targetDepth)
    (source :
      Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.Source.Formula
        sourceDepth)
    (quantifierFree :
      Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.QuantifierFree source)
    (frontier : Nat) :
    QuantifierFree
      (Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.skolemizeFrom
        environment source frontier).formula := by
  induction source generalizing targetDepth frontier with
  | verum =>
      simp [Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.skolemizeFrom,
        QuantifierFree]
  | falsum =>
      simp [Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.skolemizeFrom,
        QuantifierFree]
  | rel =>
      simp [Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.skolemizeFrom,
        QuantifierFree]
  | nrel =>
      simp [Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.skolemizeFrom,
        QuantifierFree]
  | and left right leftHypothesis rightHypothesis =>
      simpa [Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.skolemizeFrom,
        QuantifierFree] using
          And.intro
            (leftHypothesis environment quantifierFree.1 frontier)
            (rightHypothesis environment quantifierFree.2
              (Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.skolemizeFrom
                environment left frontier).next)
  | or left right leftHypothesis rightHypothesis =>
      simpa [Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.skolemizeFrom,
        QuantifierFree] using
          And.intro
            (leftHypothesis environment quantifierFree.1 frontier)
            (rightHypothesis environment quantifierFree.2
              (Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.skolemizeFrom
                environment left frontier).next)
  | all body inductionHypothesis => contradiction
  | ex body inductionHypothesis => contradiction

/-- Skolemizing a computational prenex object always exposes an all-only
prefix followed by a matrix. -/
theorem skolemizeFrom_opens_prenexForm
    {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth ->
      Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.Term
        targetDepth)
    (prenex : Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.PrenexForm
      sourceDepth)
    (frontier : Nat) :
    exists opened,
      openUniversals?
        (Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.skolemizeFrom
          environment prenex.toFormula frontier).formula = some opened := by
  induction prenex generalizing targetDepth frontier with
  | matrix source quantifierFree =>
      exact openUniversals?_eq_some_of_quantifierFree _
        (skolemizeFrom_quantifierFree environment source quantifierFree frontier)
  | all body inductionHypothesis =>
      simpa [Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.PrenexForm.toFormula,
        Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.skolemizeFrom,
        openUniversals?]
        using (inductionHypothesis
          (Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.underUniversal
            environment) frontier)
  | ex body inductionHypothesis =>
      simpa [Mettapedia.GSLT.LanguageDef.TptpFofPrenexSemantics.PrenexForm.toFormula,
        Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.skolemizeFrom]
        using inductionHypothesis
          (Mettapedia.GSLT.LanguageDef.TptpFofSkolemizationSemantics.underExistential
            environment frontier) (frontier + 1)

/-! ## Signature extension and compact naming evidence -/

/-- The target predicate signature is the disjoint union of original
predicates and fresh definition predicates. -/
inductive RelationSymbol : Nat -> Type
  | original {arity : Nat} (symbol : Source.RelationSymbol arity) :
      RelationSymbol arity
  | defined {arity : Nat} (id : Nat) : RelationSymbol arity
  deriving DecidableEq, Repr

/-- Definitional naming adds predicates but no functions. -/
def language : LO.FirstOrder.Language where
  Func := Source.FunctionSymbol
  Rel := RelationSymbol

abbrev Term (depth : Nat) :=
  LO.FirstOrder.Semiterm language Empty depth

/-- A generated reference is either a truth constant or a signed atom. -/
inductive Reference (depth : Nat)
  | verum
  | falsum
  | positive {arity : Nat} (relation : RelationSymbol arity)
      (arguments : Fin arity -> Term depth)
  | negative {arity : Nat} (relation : RelationSymbol arity)
      (arguments : Fin arity -> Term depth)

inductive Connective
  | and
  | or
  deriving DecidableEq, Repr

def Connective.holds : Connective -> Prop -> Prop -> Prop
  | .and => And
  | .or => Or

/-- One full-equivalence definition.  `source` is semantic evidence, while
`left` and `right` are the independently clausifiable body. -/
structure Definition (depth : Nat) where
  id : Nat
  source : Source.Formula depth
  connective : Connective
  left : Reference depth
  right : Reference depth

structure IntroducedPredicate where
  id : Nat
  arity : Nat
  deriving DecidableEq, Repr

/-- The naming result is topologically ordered and carries its exact fresh
predicate ledger. -/
structure Output (depth : Nat) where
  root : Reference depth
  next : Nat
  definitions : List (Definition depth)
  introduced : List IntroducedPredicate

def leafOutput {depth : Nat} (root : Reference depth)
    (frontier : Nat) : Output depth := {
  root
  next := frontier
  definitions := []
  introduced := []
}

/-- Translate a source term across the identity function-signature map. -/
def translateTerm {depth : Nat} : Source.Term depth -> Term depth
  | .bvar index => .bvar index
  | .fvar impossible => nomatch impossible
  | .func function arguments =>
      .func function fun index => translateTerm (arguments index)

def sourceReference {depth : Nat} : Source.Formula depth -> Reference depth
  | .verum => .verum
  | .falsum => .falsum
  | .rel relation arguments =>
      .positive (.original relation) fun index =>
        translateTerm (arguments index)
  | .nrel relation arguments =>
      .negative (.original relation) fun index =>
        translateTerm (arguments index)
  | .and _ _ | .or _ _ | .all _ | .ex _ => .falsum

/-- Every definition predicate receives the complete enclosing universal
environment.  This is semantically canonical; support minimization is a later
proved optimization. -/
def definedReference (depth id : Nat) : Reference depth :=
  .positive (.defined id) fun index => .bvar index

/-- Number of fresh definition predicates required by a matrix. -/
def connectiveCount {depth : Nat} : Source.Formula depth -> Nat
  | .verum | .falsum | .rel _ _ | .nrel _ _ => 0
  | .and left right | .or left right =>
      connectiveCount left + connectiveCount right + 1
  | .all _ | .ex _ => 0

/-- Postorder naming.  The proof argument makes the transformation total only
on the intended quantifier-free source type. -/
def nameFrom {depth : Nat} (source : Source.Formula depth)
    (quantifierFree : QuantifierFree source) (frontier : Nat) : Output depth :=
  match source with
  | .verum => leafOutput .verum frontier
  | .falsum => leafOutput .falsum frontier
  | .rel relation arguments =>
      leafOutput
        (.positive (.original relation) fun index =>
          translateTerm (arguments index)) frontier
  | .nrel relation arguments =>
      leafOutput
        (.negative (.original relation) fun index =>
          translateTerm (arguments index)) frontier
  | .and left right =>
      let leftOutput := nameFrom left quantifierFree.1 frontier
      let rightOutput := nameFrom right quantifierFree.2 leftOutput.next
      let id := rightOutput.next
      let current : Definition depth := {
        id
        source := .and left right
        connective := .and
        left := leftOutput.root
        right := rightOutput.root
      }
      {
        root := definedReference depth id
        next := id + 1
        definitions := leftOutput.definitions ++
          rightOutput.definitions ++ [current]
        introduced := leftOutput.introduced ++ rightOutput.introduced ++
          [{ id, arity := depth }]
      }
  | .or left right =>
      let leftOutput := nameFrom left quantifierFree.1 frontier
      let rightOutput := nameFrom right quantifierFree.2 leftOutput.next
      let id := rightOutput.next
      let current : Definition depth := {
        id
        source := .or left right
        connective := .or
        left := leftOutput.root
        right := rightOutput.root
      }
      {
        root := definedReference depth id
        next := id + 1
        definitions := leftOutput.definitions ++
          rightOutput.definitions ++ [current]
        introduced := leftOutput.introduced ++ rightOutput.introduced ++
          [{ id, arity := depth }]
      }
  | .all _ => False.elim quantifierFree
  | .ex _ => False.elim quantifierFree
termination_by sizeOf source

/-! ## Linear accumulator realization -/

/-- The state threaded by the authored naming LanguageDef.  Definition and
predicate rows are accumulated in reverse postorder, making every update a
constant-time cons. -/
structure AccumulatedOutput (depth : Nat) where
  root : Reference depth
  next : Nat
  reverseDefinitions : List (Definition depth)
  reverseIntroduced : List IntroducedPredicate

def nameAccumulate? {depth : Nat} (source : Source.Formula depth)
    (frontier : Nat)
    (reverseDefinitions : List (Definition depth))
    (reverseIntroduced : List IntroducedPredicate) :
    Option (AccumulatedOutput depth) :=
  match source with
  | .verum => some ⟨.verum, frontier, reverseDefinitions, reverseIntroduced⟩
  | .falsum => some ⟨.falsum, frontier, reverseDefinitions, reverseIntroduced⟩
  | .rel relation arguments =>
      some ⟨.positive (.original relation) (fun index =>
          translateTerm (arguments index)),
        frontier, reverseDefinitions, reverseIntroduced⟩
  | .nrel relation arguments =>
      some ⟨.negative (.original relation) (fun index =>
          translateTerm (arguments index)),
        frontier, reverseDefinitions, reverseIntroduced⟩
  | .and left right =>
      match nameAccumulate? left frontier reverseDefinitions
          reverseIntroduced with
      | none => none
      | some leftOutput =>
          match nameAccumulate? right leftOutput.next
              leftOutput.reverseDefinitions leftOutput.reverseIntroduced with
          | none => none
          | some rightOutput =>
              let current : Definition depth := {
                id := rightOutput.next
                source := .and left right
                connective := .and
                left := leftOutput.root
                right := rightOutput.root
              }
              some {
                root := definedReference depth rightOutput.next
                next := rightOutput.next + 1
                reverseDefinitions := current :: rightOutput.reverseDefinitions
                reverseIntroduced :=
                  { id := rightOutput.next, arity := depth } ::
                    rightOutput.reverseIntroduced }
  | .or left right =>
      match nameAccumulate? left frontier reverseDefinitions
          reverseIntroduced with
      | none => none
      | some leftOutput =>
          match nameAccumulate? right leftOutput.next
              leftOutput.reverseDefinitions leftOutput.reverseIntroduced with
          | none => none
          | some rightOutput =>
              let current : Definition depth := {
                id := rightOutput.next
                source := .or left right
                connective := .or
                left := leftOutput.root
                right := rightOutput.root
              }
              some {
                root := definedReference depth rightOutput.next
                next := rightOutput.next + 1
                reverseDefinitions := current :: rightOutput.reverseDefinitions
                reverseIntroduced :=
                  { id := rightOutput.next, arity := depth } ::
                    rightOutput.reverseIntroduced }
  | .all _ | .ex _ => none
termination_by sizeOf source

/-- The linear accumulator computes exactly the independent postorder naming
semantics.  Reversing its ledgers once yields the canonical output. -/
theorem nameAccumulate?_exact {depth : Nat} (source : Source.Formula depth)
    (quantifierFree : QuantifierFree source) (frontier : Nat)
    (reverseDefinitions : List (Definition depth))
    (reverseIntroduced : List IntroducedPredicate) :
    nameAccumulate? source frontier reverseDefinitions reverseIntroduced =
      some (let output := nameFrom source quantifierFree frontier
        { root := output.root
          next := output.next
          reverseDefinitions := output.definitions.reverse ++ reverseDefinitions
          reverseIntroduced := output.introduced.reverse ++ reverseIntroduced }) := by
  revert frontier reverseDefinitions reverseIntroduced
  induction source with
  | verum | falsum | rel | nrel =>
      intro frontier reverseDefinitions reverseIntroduced
      simp [nameAccumulate?, nameFrom, leafOutput]
  | and left right leftHypothesis rightHypothesis =>
      intro frontier reverseDefinitions reverseIntroduced
      change QuantifierFree left ∧ QuantifierFree right at quantifierFree
      simp only [nameAccumulate?]
      rw [leftHypothesis quantifierFree.1 frontier reverseDefinitions
        reverseIntroduced]
      simp only
      rw [rightHypothesis quantifierFree.2]
      simp [nameFrom, List.reverse_append, List.append_assoc]
  | or left right leftHypothesis rightHypothesis =>
      intro frontier reverseDefinitions reverseIntroduced
      change QuantifierFree left ∧ QuantifierFree right at quantifierFree
      simp only [nameAccumulate?]
      rw [leftHypothesis quantifierFree.1 frontier reverseDefinitions
        reverseIntroduced]
      simp only
      rw [rightHypothesis quantifierFree.2]
      simp [nameFrom, List.reverse_append, List.append_assoc]
  | all body inductionHypothesis =>
      intro frontier reverseDefinitions reverseIntroduced
      contradiction
  | ex body inductionHypothesis =>
      intro frontier reverseDefinitions reverseIntroduced
      contradiction

theorem nameAccumulate?_empty_exact {depth : Nat}
    (source : Source.Formula depth) (quantifierFree : QuantifierFree source)
    (frontier : Nat) :
    nameAccumulate? source frontier [] [] = some
      { root := (nameFrom source quantifierFree frontier).root
        next := (nameFrom source quantifierFree frontier).next
        reverseDefinitions :=
          (nameFrom source quantifierFree frontier).definitions.reverse
        reverseIntroduced :=
          (nameFrom source quantifierFree frontier).introduced.reverse } := by
  simpa using nameAccumulate?_exact source quantifierFree frontier [] []

def definitionIds {depth : Nat} (output : Output depth) : List Nat :=
  output.definitions.map Definition.id

def introducedIds {depth : Nat} (output : Output depth) : List Nat :=
  output.introduced.map IntroducedPredicate.id

/-! ## Exact allocation and ordering -/

private theorem range'_append_singleton (start first second : Nat) :
    List.range' start first ++ List.range' (start + first) second ++
        [start + first + second] =
      List.range' start (first + second + 1) := by
  rw [show start + first = start + 1 * first by omega]
  rw [List.range'_append]
  rw [← List.range'_append (s := start) (m := first + second)
    (n := 1) (step := 1)]
  simp

theorem nameFrom_next_exact {depth : Nat} (source : Source.Formula depth)
    (quantifierFree : QuantifierFree source) (frontier : Nat) :
    (nameFrom source quantifierFree frontier).next =
      frontier + connectiveCount source := by
  induction source generalizing frontier with
  | verum => simp [nameFrom, leafOutput, connectiveCount]
  | falsum => simp [nameFrom, leafOutput, connectiveCount]
  | rel => simp [nameFrom, leafOutput, connectiveCount]
  | nrel => simp [nameFrom, leafOutput, connectiveCount]
  | and left right leftHypothesis rightHypothesis =>
      simp only [nameFrom, connectiveCount]
      rw [rightHypothesis quantifierFree.2,
        leftHypothesis quantifierFree.1]
      omega
  | or left right leftHypothesis rightHypothesis =>
      simp only [nameFrom, connectiveCount]
      rw [rightHypothesis quantifierFree.2,
        leftHypothesis quantifierFree.1]
      omega
  | all body inductionHypothesis => contradiction
  | ex body inductionHypothesis => contradiction

theorem nameFrom_definitionIds_exact {depth : Nat}
    (source : Source.Formula depth)
    (quantifierFree : QuantifierFree source) (frontier : Nat) :
    definitionIds (nameFrom source quantifierFree frontier) =
      List.range' frontier (connectiveCount source) := by
  induction source generalizing frontier with
  | verum => simp [nameFrom, leafOutput, definitionIds, connectiveCount]
  | falsum => simp [nameFrom, leafOutput, definitionIds, connectiveCount]
  | rel => simp [nameFrom, leafOutput, definitionIds, connectiveCount]
  | nrel => simp [nameFrom, leafOutput, definitionIds, connectiveCount]
  | and left right leftHypothesis rightHypothesis =>
      simp only [nameFrom, definitionIds, List.map_append, List.map_cons,
        List.map_nil, connectiveCount]
      rw [show List.map Definition.id
            (nameFrom left quantifierFree.1 frontier).definitions =
          List.range' frontier (connectiveCount left) by
        simpa [definitionIds] using
          leftHypothesis quantifierFree.1 frontier]
      rw [show List.map Definition.id
            (nameFrom right quantifierFree.2
              (nameFrom left quantifierFree.1 frontier).next).definitions =
          List.range' (nameFrom left quantifierFree.1 frontier).next
            (connectiveCount right) by
        simpa [definitionIds] using rightHypothesis quantifierFree.2
          (nameFrom left quantifierFree.1 frontier).next]
      rw [nameFrom_next_exact left quantifierFree.1]
      rw [nameFrom_next_exact right quantifierFree.2]
      exact range'_append_singleton frontier
        (connectiveCount left) (connectiveCount right)
  | or left right leftHypothesis rightHypothesis =>
      simp only [nameFrom, definitionIds, List.map_append, List.map_cons,
        List.map_nil, connectiveCount]
      rw [show List.map Definition.id
            (nameFrom left quantifierFree.1 frontier).definitions =
          List.range' frontier (connectiveCount left) by
        simpa [definitionIds] using
          leftHypothesis quantifierFree.1 frontier]
      rw [show List.map Definition.id
            (nameFrom right quantifierFree.2
              (nameFrom left quantifierFree.1 frontier).next).definitions =
          List.range' (nameFrom left quantifierFree.1 frontier).next
            (connectiveCount right) by
        simpa [definitionIds] using rightHypothesis quantifierFree.2
          (nameFrom left quantifierFree.1 frontier).next]
      rw [nameFrom_next_exact left quantifierFree.1]
      rw [nameFrom_next_exact right quantifierFree.2]
      exact range'_append_singleton frontier
        (connectiveCount left) (connectiveCount right)
  | all body inductionHypothesis => contradiction
  | ex body inductionHypothesis => contradiction

theorem nameFrom_introducedIds_exact {depth : Nat}
    (source : Source.Formula depth)
    (quantifierFree : QuantifierFree source) (frontier : Nat) :
    introducedIds (nameFrom source quantifierFree frontier) =
      List.range' frontier (connectiveCount source) := by
  induction source generalizing frontier with
  | verum => simp [nameFrom, leafOutput, introducedIds, connectiveCount]
  | falsum => simp [nameFrom, leafOutput, introducedIds, connectiveCount]
  | rel => simp [nameFrom, leafOutput, introducedIds, connectiveCount]
  | nrel => simp [nameFrom, leafOutput, introducedIds, connectiveCount]
  | and left right leftHypothesis rightHypothesis =>
      simp only [nameFrom, introducedIds, List.map_append, List.map_cons,
        List.map_nil, connectiveCount]
      rw [show List.map IntroducedPredicate.id
            (nameFrom left quantifierFree.1 frontier).introduced =
          List.range' frontier (connectiveCount left) by
        simpa [introducedIds] using
          leftHypothesis quantifierFree.1 frontier]
      rw [show List.map IntroducedPredicate.id
            (nameFrom right quantifierFree.2
              (nameFrom left quantifierFree.1 frontier).next).introduced =
          List.range' (nameFrom left quantifierFree.1 frontier).next
            (connectiveCount right) by
        simpa [introducedIds] using rightHypothesis quantifierFree.2
          (nameFrom left quantifierFree.1 frontier).next]
      rw [nameFrom_next_exact left quantifierFree.1]
      rw [nameFrom_next_exact right quantifierFree.2]
      exact range'_append_singleton frontier
        (connectiveCount left) (connectiveCount right)
  | or left right leftHypothesis rightHypothesis =>
      simp only [nameFrom, introducedIds, List.map_append, List.map_cons,
        List.map_nil, connectiveCount]
      rw [show List.map IntroducedPredicate.id
            (nameFrom left quantifierFree.1 frontier).introduced =
          List.range' frontier (connectiveCount left) by
        simpa [introducedIds] using
          leftHypothesis quantifierFree.1 frontier]
      rw [show List.map IntroducedPredicate.id
            (nameFrom right quantifierFree.2
              (nameFrom left quantifierFree.1 frontier).next).introduced =
          List.range' (nameFrom left quantifierFree.1 frontier).next
            (connectiveCount right) by
        simpa [introducedIds] using rightHypothesis quantifierFree.2
          (nameFrom left quantifierFree.1 frontier).next]
      rw [nameFrom_next_exact left quantifierFree.1]
      rw [nameFrom_next_exact right quantifierFree.2]
      exact range'_append_singleton frontier
        (connectiveCount left) (connectiveCount right)
  | all body inductionHypothesis => contradiction
  | ex body inductionHypothesis => contradiction

theorem nameFrom_definitionIds_nodup {depth : Nat}
    (source : Source.Formula depth)
    (quantifierFree : QuantifierFree source) (frontier : Nat) :
    (definitionIds (nameFrom source quantifierFree frontier)).Nodup := by
  rw [nameFrom_definitionIds_exact]
  exact List.nodup_range'

theorem nameFrom_introducedIds_nodup {depth : Nat}
    (source : Source.Formula depth)
    (quantifierFree : QuantifierFree source) (frontier : Nat) :
    (introducedIds (nameFrom source quantifierFree frontier)).Nodup := by
  rw [nameFrom_introducedIds_exact]
  exact List.nodup_range'

theorem nameFrom_ledgers_agree {depth : Nat}
    (source : Source.Formula depth)
    (quantifierFree : QuantifierFree source) (frontier : Nat) :
    definitionIds (nameFrom source quantifierFree frontier) =
      introducedIds (nameFrom source quantifierFree frontier) := by
  rw [nameFrom_definitionIds_exact, nameFrom_introducedIds_exact]

/-- Every retained source row is itself quantifier-free.  This makes the
evidence field admissible in the inert Skolem carrier without a partial
encoder or a hidden fallback constructor. -/
theorem nameFrom_definition_sources_quantifierFree {depth : Nat}
    (source : Source.Formula depth)
    (quantifierFree : QuantifierFree source) (frontier : Nat)
    (definition : Definition depth)
    (membership : definition ∈
      (nameFrom source quantifierFree frontier).definitions) :
    QuantifierFree definition.source := by
  induction source generalizing frontier with
  | verum => simp [nameFrom, leafOutput] at membership
  | falsum => simp [nameFrom, leafOutput] at membership
  | rel => simp [nameFrom, leafOutput] at membership
  | nrel => simp [nameFrom, leafOutput] at membership
  | and left right leftHypothesis rightHypothesis =>
      let leftOutput := nameFrom left quantifierFree.1 frontier
      let rightOutput := nameFrom right quantifierFree.2 leftOutput.next
      let current : Definition _ := {
        id := rightOutput.next
        source := .and left right
        connective := .and
        left := leftOutput.root
        right := rightOutput.root
      }
      simp only [nameFrom, List.mem_append, List.mem_singleton] at membership
      rcases membership with (leftMember | rightMember) | rfl
      · exact leftHypothesis quantifierFree.1 frontier definition leftMember
      · exact rightHypothesis quantifierFree.2 leftOutput.next definition
          rightMember
      · exact quantifierFree
  | or left right leftHypothesis rightHypothesis =>
      let leftOutput := nameFrom left quantifierFree.1 frontier
      let rightOutput := nameFrom right quantifierFree.2 leftOutput.next
      let current : Definition _ := {
        id := rightOutput.next
        source := .or left right
        connective := .or
        left := leftOutput.root
        right := rightOutput.root
      }
      simp only [nameFrom, List.mem_append, List.mem_singleton] at membership
      rcases membership with (leftMember | rightMember) | rfl
      · exact leftHypothesis quantifierFree.1 frontier definition leftMember
      · exact rightHypothesis quantifierFree.2 leftOutput.next definition
          rightMember
      · exact quantifierFree
  | all body inductionHypothesis => contradiction
  | ex body inductionHypothesis => contradiction

/-! ## Model semantics -/

@[reducible] def sourceEmbedding : Source.Language →ᵥ language where
  func := fun function => function
  rel := RelationSymbol.original

@[reducible] def restrictStructure {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain) :
    LO.FirstOrder.Structure Source.Language Domain :=
  LO.FirstOrder.Structure.lMap sourceEmbedding target

def evalReference {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (values : Fin depth -> Domain) : Reference depth -> Prop
  | .verum => True
  | .falsum => False
  | .positive relation arguments =>
      target.rel relation fun index =>
        LO.FirstOrder.Semiterm.val target values Empty.elim (arguments index)
  | .negative relation arguments =>
      ¬target.rel relation fun index =>
        LO.FirstOrder.Semiterm.val target values Empty.elim (arguments index)

def Definition.Satisfied {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (values : Fin depth -> Domain)
    (definition : Definition depth) : Prop :=
  evalReference target values (definedReference depth definition.id) <->
    definition.connective.holds
      (evalReference target values definition.left)
      (evalReference target values definition.right)

def Output.Satisfied {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (output : Output depth) : Prop :=
  forall values : Fin depth -> Domain,
    (forall definition, definition ∈ output.definitions ->
      definition.Satisfied target values) /\
    evalReference target values output.root

theorem translateTerm_value_exact {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (values : Fin depth -> Domain)
    (source : Source.Term depth) :
    LO.FirstOrder.Semiterm.val target values Empty.elim
        (translateTerm source) =
      LO.FirstOrder.Semiterm.val (restrictStructure target) values
        Empty.elim source := by
  induction source with
  | bvar => rfl
  | fvar impossible => exact nomatch impossible
  | func function arguments inductionHypothesis =>
      simp only [translateTerm, LO.FirstOrder.Semiterm.val_func,
        restrictStructure, LO.FirstOrder.Structure.lMap_func,
        sourceEmbedding]
      congr 1
      funext index
      exact inductionHypothesis index

theorem eval_sourceReference_exact {Domain : Type}
    (target : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (values : Fin depth -> Domain)
    (source : Source.Formula depth)
    (quantifierFreeAtom :
      source = .verum \/ source = .falsum \/
      (exists arity relation arguments,
        source = .rel (arity := arity) relation arguments) \/
      (exists arity relation arguments,
        source = .nrel (arity := arity) relation arguments)) :
    evalReference target values (sourceReference source) <->
      LO.FirstOrder.Semiformula.EvalAux (restrictStructure target)
        Empty.elim values source := by
  rcases quantifierFreeAtom with rfl | rfl | relationCase | relationCase
  · simp [sourceReference, evalReference,
      LO.FirstOrder.Semiformula.EvalAux]
  · simp [sourceReference, evalReference,
      LO.FirstOrder.Semiformula.EvalAux]
  · rcases relationCase with ⟨arity, relation, arguments, rfl⟩
    simp only [sourceReference, evalReference,
      LO.FirstOrder.Semiformula.EvalAux, restrictStructure,
      LO.FirstOrder.Structure.lMap_rel, sourceEmbedding]
    have argumentsExact :
        (fun index => LO.FirstOrder.Semiterm.val target values Empty.elim
          (translateTerm (arguments index))) =
        (fun index => LO.FirstOrder.Semiterm.val (restrictStructure target)
          values Empty.elim (arguments index)) := by
      funext index
      exact translateTerm_value_exact target values (arguments index)
    rw [argumentsExact]
  · rcases relationCase with ⟨arity, relation, arguments, rfl⟩
    simp only [sourceReference, evalReference,
      LO.FirstOrder.Semiformula.EvalAux, restrictStructure,
      LO.FirstOrder.Structure.lMap_rel, sourceEmbedding]
    have argumentsExact :
        (fun index => LO.FirstOrder.Semiterm.val target values Empty.elim
          (translateTerm (arguments index))) =
        (fun index => LO.FirstOrder.Semiterm.val (restrictStructure target)
          values Empty.elim (arguments index)) := by
      funext index
      exact translateTerm_value_exact target values (arguments index)
    rw [argumentsExact]

/-! ## Backward semantic reflection -/

/-- In any target model satisfying all generated equivalences, the generated
root has exactly the meaning of the source matrix in the restricted model. -/
theorem eval_nameFrom_root_iff_source_of_definitions
    {Domain : Type} (target : LO.FirstOrder.Structure language Domain)
    {depth : Nat} (source : Source.Formula depth)
    (quantifierFree : QuantifierFree source) (frontier : Nat)
    (values : Fin depth -> Domain)
    (definitionsSatisfied : forall definition,
      definition ∈ (nameFrom source quantifierFree frontier).definitions ->
        definition.Satisfied target values) :
    evalReference target values
        (nameFrom source quantifierFree frontier).root <->
      LO.FirstOrder.Semiformula.EvalAux (restrictStructure target)
        Empty.elim values source := by
  induction source generalizing frontier with
  | verum =>
      simp [nameFrom, leafOutput, evalReference,
        LO.FirstOrder.Semiformula.EvalAux]
  | falsum =>
      simp [nameFrom, leafOutput, evalReference,
        LO.FirstOrder.Semiformula.EvalAux]
  | rel relation arguments =>
      simpa only [nameFrom, leafOutput, sourceReference] using
        eval_sourceReference_exact target values (.rel relation arguments)
          (Or.inr (Or.inr (Or.inl ⟨_, relation, arguments, rfl⟩)))
  | nrel relation arguments =>
      simpa only [nameFrom, leafOutput, sourceReference] using
        eval_sourceReference_exact target values (.nrel relation arguments)
          (Or.inr (Or.inr (Or.inr ⟨_, relation, arguments, rfl⟩)))
  | and left right leftHypothesis rightHypothesis =>
      let leftOutput := nameFrom left quantifierFree.1 frontier
      let rightOutput := nameFrom right quantifierFree.2 leftOutput.next
      let current : Definition _ := {
        id := rightOutput.next
        source := .and left right
        connective := .and
        left := leftOutput.root
        right := rightOutput.root
      }
      have leftDefinitionsSatisfied : forall definition,
          definition ∈ leftOutput.definitions ->
            definition.Satisfied target values := by
        intro definition membership
        apply definitionsSatisfied definition
        simp [nameFrom, leftOutput, membership]
      have rightDefinitionsSatisfied : forall definition,
          definition ∈ rightOutput.definitions ->
            definition.Satisfied target values := by
        intro definition membership
        apply definitionsSatisfied definition
        simp [nameFrom, leftOutput, rightOutput, membership]
      have currentSatisfied : current.Satisfied target values := by
        apply definitionsSatisfied current
        simp [nameFrom, leftOutput, rightOutput, current]
      have leftExact := leftHypothesis quantifierFree.1 frontier values
        leftDefinitionsSatisfied
      have rightExact := rightHypothesis quantifierFree.2 leftOutput.next values
        rightDefinitionsSatisfied
      simpa [nameFrom, leftOutput, rightOutput, current,
        Definition.Satisfied, Connective.holds,
        LO.FirstOrder.Semiformula.EvalAux, leftExact, rightExact]
        using currentSatisfied
  | or left right leftHypothesis rightHypothesis =>
      let leftOutput := nameFrom left quantifierFree.1 frontier
      let rightOutput := nameFrom right quantifierFree.2 leftOutput.next
      let current : Definition _ := {
        id := rightOutput.next
        source := .or left right
        connective := .or
        left := leftOutput.root
        right := rightOutput.root
      }
      have leftDefinitionsSatisfied : forall definition,
          definition ∈ leftOutput.definitions ->
            definition.Satisfied target values := by
        intro definition membership
        apply definitionsSatisfied definition
        simp [nameFrom, leftOutput, membership]
      have rightDefinitionsSatisfied : forall definition,
          definition ∈ rightOutput.definitions ->
            definition.Satisfied target values := by
        intro definition membership
        apply definitionsSatisfied definition
        simp [nameFrom, leftOutput, rightOutput, membership]
      have currentSatisfied : current.Satisfied target values := by
        apply definitionsSatisfied current
        simp [nameFrom, leftOutput, rightOutput, current]
      have leftExact := leftHypothesis quantifierFree.1 frontier values
        leftDefinitionsSatisfied
      have rightExact := rightHypothesis quantifierFree.2 leftOutput.next values
        rightDefinitionsSatisfied
      simpa [nameFrom, leftOutput, rightOutput, current,
        Definition.Satisfied, Connective.holds,
        LO.FirstOrder.Semiformula.EvalAux, leftExact, rightExact]
        using currentSatisfied
  | all body inductionHypothesis => contradiction
  | ex body inductionHypothesis => contradiction

/-! ## Canonical model extension -/

/-- Interpret a fresh predicate by the source subformula recorded at its unique
definition row.  The arity equality makes accidental cross-depth use false
rather than assigning it an arbitrary meaning. -/
@[reducible] noncomputable def extendStructure {Domain : Type} {depth : Nat}
    (source : LO.FirstOrder.Structure Source.Language Domain)
    (output : Output depth) : LO.FirstOrder.Structure language Domain where
  func := source.func
  rel := fun {arity} relation arguments =>
    match relation with
    | .original original => source.rel original arguments
    | .defined id =>
        exists definition,
          definition ∈ output.definitions /\
          definition.id = id /\
          exists exactArity : arity = depth,
            LO.FirstOrder.Semiformula.EvalAux source Empty.elim
              (fun index => arguments (Fin.cast exactArity.symm index))
              definition.source

theorem restrict_extendStructure_exact {Domain : Type} {depth : Nat}
    (source : LO.FirstOrder.Structure Source.Language Domain)
    (output : Output depth) :
    restrictStructure (extendStructure source output) = source := by
  ext arity symbol arguments
  · rfl
  · rfl

/-- Target models retain the source identity interpretation of equality. -/
structure Model (Domain : Type) where
  interpretation : LO.FirstOrder.Structure language Domain
  equality_exact : forall values : Fin 2 -> Domain,
    interpretation.rel
        (.original
          Mettapedia.GSLT.LanguageDef.TptpFofNormalizationSemantics.RelationSymbol.equality)
        values <->
      values 0 = values 1

def restrictModel {Domain : Type} (target : Model Domain) :
    Source.Model Domain where
  interpretation := restrictStructure target.interpretation
  equality_exact := target.equality_exact

noncomputable def extendModel {Domain : Type} {depth : Nat}
    (source : Source.Model Domain) (output : Output depth) : Model Domain where
  interpretation := extendStructure source.interpretation output
  equality_exact := source.equality_exact

theorem restrict_extendModel_exact {Domain : Type} {depth : Nat}
    (source : Source.Model Domain) (output : Output depth) :
    restrictModel (extendModel source output) = source := by
  cases source
  rfl

private theorem definition_eq_of_same_id
    {depth : Nat} {definitions : List (Definition depth)}
    (idsNodup : (definitions.map Definition.id).Nodup)
    {first second : Definition depth}
    (firstMember : first ∈ definitions)
    (secondMember : second ∈ definitions)
    (sameId : first.id = second.id) : first = second :=
  List.inj_on_of_nodup_map idsNodup firstMember secondMember sameId

/-- A generated predicate in the canonical extension denotes exactly the
source subformula carried by its unique definition row. -/
theorem eval_definedReference_extend_exact
    {Domain : Type} {depth : Nat}
    (source : LO.FirstOrder.Structure Source.Language Domain)
    (output : Output depth)
    (idsNodup : (output.definitions.map Definition.id).Nodup)
    (definition : Definition depth)
    (definitionMember : definition ∈ output.definitions)
    (values : Fin depth -> Domain) :
    evalReference (extendStructure source output) values
        (definedReference depth definition.id) <->
      LO.FirstOrder.Semiformula.EvalAux source Empty.elim values
        definition.source := by
  constructor
  · rintro ⟨other, otherMember, sameId, exactArity, satisfied⟩
    have otherEq : other = definition :=
      definition_eq_of_same_id idsNodup otherMember definitionMember sameId
    subst other
    have arityProofEq : exactArity = rfl := Subsingleton.elim _ _
    subst arityProofEq
    simpa [evalReference, definedReference, extendStructure] using satisfied
  · intro satisfied
    change exists other,
      other ∈ output.definitions /\ other.id = definition.id /\
        exists exactArity : depth = depth,
          LO.FirstOrder.Semiformula.EvalAux source Empty.elim
            (fun index => values (Fin.cast exactArity.symm index)) other.source
    exact ⟨definition, definitionMember, rfl, rfl, by simpa using satisfied⟩

/-- The canonical extension simultaneously satisfies every generated
equivalence and makes the root exactly denote the source matrix.  The theorem
is generalized over a larger definition ledger so recursive subtrees are
checked in the same target model. -/
theorem nameFrom_extension_exact
    {Domain : Type} (sourceStructure :
      LO.FirstOrder.Structure Source.Language Domain)
    {depth : Nat} (source : Source.Formula depth)
    (quantifierFree : QuantifierFree source) (frontier : Nat)
    (super : Output depth)
    (superIdsNodup : (super.definitions.map Definition.id).Nodup)
    (contained : forall definition,
      definition ∈ (nameFrom source quantifierFree frontier).definitions ->
        definition ∈ super.definitions)
    (values : Fin depth -> Domain) :
    (forall definition,
      definition ∈ (nameFrom source quantifierFree frontier).definitions ->
        definition.Satisfied (extendStructure sourceStructure super) values) /\
    (evalReference (extendStructure sourceStructure super) values
        (nameFrom source quantifierFree frontier).root <->
      LO.FirstOrder.Semiformula.EvalAux sourceStructure Empty.elim values
        source) := by
  induction source generalizing frontier with
  | verum =>
      constructor
      · intro definition membership
        simp [nameFrom, leafOutput] at membership
      · simp [nameFrom, leafOutput, evalReference,
          LO.FirstOrder.Semiformula.EvalAux]
  | falsum =>
      constructor
      · intro definition membership
        simp [nameFrom, leafOutput] at membership
      · simp [nameFrom, leafOutput, evalReference,
          LO.FirstOrder.Semiformula.EvalAux]
  | rel relation arguments =>
      constructor
      · intro definition membership
        simp [nameFrom, leafOutput] at membership
      · have restricted :
            restrictStructure (extendStructure sourceStructure super) =
              sourceStructure :=
          restrict_extendStructure_exact sourceStructure super
        have exactReference := eval_sourceReference_exact
          (extendStructure sourceStructure super) values
          (.rel relation arguments)
          (Or.inr (Or.inr (Or.inl ⟨_, relation, arguments, rfl⟩)))
        rw [restricted] at exactReference
        simpa [nameFrom, leafOutput, sourceReference] using exactReference
  | nrel relation arguments =>
      constructor
      · intro definition membership
        simp [nameFrom, leafOutput] at membership
      · have restricted :
            restrictStructure (extendStructure sourceStructure super) =
              sourceStructure :=
          restrict_extendStructure_exact sourceStructure super
        have exactReference := eval_sourceReference_exact
          (extendStructure sourceStructure super) values
          (.nrel relation arguments)
          (Or.inr (Or.inr (Or.inr ⟨_, relation, arguments, rfl⟩)))
        rw [restricted] at exactReference
        simpa [nameFrom, leafOutput, sourceReference] using exactReference
  | and left right leftHypothesis rightHypothesis =>
      let leftOutput := nameFrom left quantifierFree.1 frontier
      let rightOutput := nameFrom right quantifierFree.2 leftOutput.next
      let current : Definition _ := {
        id := rightOutput.next
        source := .and left right
        connective := .and
        left := leftOutput.root
        right := rightOutput.root
      }
      have leftContained : forall definition,
          definition ∈ leftOutput.definitions ->
            definition ∈ super.definitions := by
        intro definition membership
        apply contained definition
        simp [nameFrom, leftOutput, membership]
      have rightContained : forall definition,
          definition ∈ rightOutput.definitions ->
            definition ∈ super.definitions := by
        intro definition membership
        apply contained definition
        simp [nameFrom, leftOutput, rightOutput, membership]
      have currentContained : current ∈ super.definitions := by
        apply contained current
        simp [nameFrom, leftOutput, rightOutput, current]
      rcases leftHypothesis quantifierFree.1 frontier super superIdsNodup
          leftContained values with ⟨leftDefinitions, leftExact⟩
      rcases rightHypothesis quantifierFree.2 leftOutput.next super
          superIdsNodup rightContained values with
        ⟨rightDefinitions, rightExact⟩
      have currentExact : current.Satisfied
          (extendStructure sourceStructure super) values := by
        have namedExact := eval_definedReference_extend_exact sourceStructure
          super superIdsNodup current currentContained values
        exact namedExact.trans <| by
          simpa [current, Connective.holds,
            LO.FirstOrder.Semiformula.EvalAux] using
              (and_congr leftExact rightExact).symm
      constructor
      · intro definition membership
        simp only [nameFrom, List.mem_append, List.mem_singleton] at membership
        rcases membership with (leftMember | rightMember) | rfl
        · exact leftDefinitions definition leftMember
        · exact rightDefinitions definition rightMember
        · exact currentExact
      · simpa [nameFrom, leftOutput, rightOutput, current] using
          (eval_definedReference_extend_exact sourceStructure super
            superIdsNodup current currentContained values)
  | or left right leftHypothesis rightHypothesis =>
      let leftOutput := nameFrom left quantifierFree.1 frontier
      let rightOutput := nameFrom right quantifierFree.2 leftOutput.next
      let current : Definition _ := {
        id := rightOutput.next
        source := .or left right
        connective := .or
        left := leftOutput.root
        right := rightOutput.root
      }
      have leftContained : forall definition,
          definition ∈ leftOutput.definitions ->
            definition ∈ super.definitions := by
        intro definition membership
        apply contained definition
        simp [nameFrom, leftOutput, membership]
      have rightContained : forall definition,
          definition ∈ rightOutput.definitions ->
            definition ∈ super.definitions := by
        intro definition membership
        apply contained definition
        simp [nameFrom, leftOutput, rightOutput, membership]
      have currentContained : current ∈ super.definitions := by
        apply contained current
        simp [nameFrom, leftOutput, rightOutput, current]
      rcases leftHypothesis quantifierFree.1 frontier super superIdsNodup
          leftContained values with ⟨leftDefinitions, leftExact⟩
      rcases rightHypothesis quantifierFree.2 leftOutput.next super
          superIdsNodup rightContained values with
        ⟨rightDefinitions, rightExact⟩
      have currentExact : current.Satisfied
          (extendStructure sourceStructure super) values := by
        have namedExact := eval_definedReference_extend_exact sourceStructure
          super superIdsNodup current currentContained values
        exact namedExact.trans <| by
          simpa [current, Connective.holds,
            LO.FirstOrder.Semiformula.EvalAux] using
              (or_congr leftExact rightExact).symm
      constructor
      · intro definition membership
        simp only [nameFrom, List.mem_append, List.mem_singleton] at membership
        rcases membership with (leftMember | rightMember) | rfl
        · exact leftDefinitions definition leftMember
        · exact rightDefinitions definition rightMember
        · exact currentExact
      · simpa [nameFrom, leftOutput, rightOutput, current] using
          (eval_definedReference_extend_exact sourceStructure super
            superIdsNodup current currentContained values)
  | all body inductionHypothesis => contradiction
  | ex body inductionHypothesis => contradiction

theorem nameFrom_canonical_extension_exact
    {Domain : Type} (sourceStructure :
      LO.FirstOrder.Structure Source.Language Domain)
    {depth : Nat} (source : Source.Formula depth)
    (quantifierFree : QuantifierFree source) (frontier : Nat)
    (values : Fin depth -> Domain) :
    (forall definition,
      definition ∈ (nameFrom source quantifierFree frontier).definitions ->
        definition.Satisfied
          (extendStructure sourceStructure
            (nameFrom source quantifierFree frontier)) values) /\
    (evalReference
        (extendStructure sourceStructure
          (nameFrom source quantifierFree frontier)) values
        (nameFrom source quantifierFree frontier).root <->
      LO.FirstOrder.Semiformula.EvalAux sourceStructure Empty.elim values
        source) := by
  apply nameFrom_extension_exact sourceStructure source quantifierFree frontier
    (nameFrom source quantifierFree frontier)
  · exact nameFrom_definitionIds_nodup source quantifierFree frontier
  · exact fun _ membership => membership

def SourceSatisfiable {depth : Nat} (source : Source.Formula depth) : Prop :=
  exists (Domain : Type) (_ : Nonempty Domain) (model : Source.Model Domain),
    forall values : Fin depth -> Domain,
      LO.FirstOrder.Semiformula.EvalAux model.interpretation Empty.elim values
        source

def Satisfiable {depth : Nat} (output : Output depth) : Prop :=
  exists (Domain : Type) (_ : Nonempty Domain) (model : Model Domain),
    output.Satisfied model.interpretation

theorem sourceSatisfiable_iff_openedSourceSatisfiable
    {depth : Nat} (source : Source.Formula depth)
    (opened : OpenedMatrix)
    (openedExact : openUniversals? source = some opened) :
    SourceSatisfiable source <-> SourceSatisfiable opened.formula := by
  constructor
  · rintro ⟨Domain, domainNonempty, model, satisfied⟩
    exact ⟨Domain, domainNonempty, model,
      (openUniversals?_eval_iff model.interpretation opened openedExact).mp
        satisfied⟩
  · rintro ⟨Domain, domainNonempty, model, satisfied⟩
    exact ⟨Domain, domainNonempty, model,
      (openUniversals?_eval_iff model.interpretation opened openedExact).mpr
        satisfied⟩

/-- Full-equivalence naming is a conservative signature extension and hence
equisatisfiable with the universally closed source matrix. -/
theorem sourceSatisfiable_iff_namedSatisfiable
    {depth : Nat} (source : Source.Formula depth)
    (quantifierFree : QuantifierFree source) (frontier : Nat) :
    SourceSatisfiable source <->
      Satisfiable (nameFrom source quantifierFree frontier) := by
  constructor
  · rintro ⟨Domain, domainNonempty, sourceModel, sourceSatisfied⟩
    let targetModel := extendModel sourceModel
      (nameFrom source quantifierFree frontier)
    refine ⟨Domain, domainNonempty, targetModel, ?_⟩
    intro values
    rcases nameFrom_canonical_extension_exact sourceModel.interpretation
      source quantifierFree frontier values with
      ⟨definitionsExact, rootExact⟩
    exact ⟨definitionsExact, rootExact.mpr (sourceSatisfied values)⟩
  · rintro ⟨Domain, domainNonempty, targetModel, targetSatisfied⟩
    refine ⟨Domain, domainNonempty, restrictModel targetModel, ?_⟩
    intro values
    have satisfiedAt := targetSatisfied values
    exact (eval_nameFrom_root_iff_source_of_definitions
      targetModel.interpretation source quantifierFree frontier values
      satisfiedAt.1).mp satisfiedAt.2

/-- Full all-prefix removal followed by naming is equisatisfiable with the
closed Skolem source. -/
theorem sourceSatisfiable_iff_openedNamedSatisfiable
    {depth : Nat} (source : Source.Formula depth)
    (opened : OpenedMatrix)
    (openedExact : openUniversals? source = some opened)
    (frontier : Nat) :
    SourceSatisfiable source <->
      Satisfiable
        (nameFrom opened.formula opened.quantifierFree frontier) := by
  exact (sourceSatisfiable_iff_openedSourceSatisfiable source opened
    openedExact).trans
      (sourceSatisfiable_iff_namedSatisfiable opened.formula
        opened.quantifierFree frontier)

/-! ## Allocation and boundary canaries -/

namespace Canary

/-- A nested matrix exercises child-before-parent allocation. -/
def source : Source.Formula 0 :=
  .or (.and .verum .falsum) .verum

theorem source_quantifierFree : QuantifierFree source := by
  simp [source, QuantifierFree]

theorem source_definition_ids_are_topological :
    definitionIds (nameFrom source source_quantifierFree 7) = [7, 8] := by
  rw [nameFrom_definitionIds_exact]
  decide

theorem source_introduced_ledger_is_exact :
    (nameFrom source source_quantifierFree 7).introduced =
      [⟨7, 0⟩, ⟨8, 0⟩] := by
  simp [source, nameFrom, leafOutput]

theorem source_is_equisatisfiable_with_named_output :
    SourceSatisfiable source <->
      Satisfiable (nameFrom source source_quantifierFree 7) :=
  sourceSatisfiable_iff_namedSatisfiable source source_quantifierFree 7

/-- A literal matrix introduces no artificial predicate. -/
def literal : Source.Formula 0 := .verum

theorem literal_introduces_nothing :
    (nameFrom literal (by simp [literal, QuantifierFree]) 7).introduced = [] := by
  simp [literal, nameFrom, leafOutput]

/-- Quantified input is rejected at this stage rather than silently named. -/
theorem quantified_input_is_rejected :
    Not (QuantifierFree (.all (.verum : Source.Formula 1))) := by
  simp [QuantifierFree]

end Canary

#print axioms nameFrom_next_exact
#print axioms nameFrom_definitionIds_exact
#print axioms nameFrom_introducedIds_exact
#print axioms nameFrom_ledgers_agree
#print axioms nameFrom_definition_sources_quantifierFree
#print axioms eval_nameFrom_root_iff_source_of_definitions
#print axioms nameFrom_canonical_extension_exact
#print axioms sourceSatisfiable_iff_namedSatisfiable
#print axioms UniversalPrefix.existentialFree
#print axioms UniversalPrefix.openUniversals?_exact
#print axioms openUniversals?_eval_iff
#print axioms skolemizeFrom_opens_prenexForm
#print axioms sourceSatisfiable_iff_openedNamedSatisfiable
#print axioms Canary.source_definition_ids_are_topological
#print axioms Canary.quantified_input_is_rejected

end Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingSemantics
