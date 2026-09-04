import Foundation.FirstOrder.Basic
import Mettapedia.GSLT.LanguageDef.TptpOfficialPrincipalSymbols
import Mettapedia.GSLT.LanguageDef.TptpFofSymbolIdentity

/-!
# Binder-resolved FOF normalization semantics

TPTP's parsed first-order document deliberately retains source variable
spellings.  Capture-avoiding transformations cannot operate on those names
directly because a nested quantifier may reuse a spelling.  This module gives
the semantic refinement used by the clausification pipeline:

* bound variables are de Bruijn indices supplied by Foundation's
  `LO.FirstOrder.Semiterm`;
* function and predicate symbols retain their arity in the type;
* equality has the identity interpretation required by FOF; and
* every FOF connective normalizes to Foundation's negation-normal first-order
  syntax with an exact semantic and principal-signature theorem.

The module does not parse names and does not choose fresh binder identities.
Those are obligations of the preceding document-to-resolved-formula
refinement.  It also performs no Skolemization: NNF is signature-preserving,
whereas Skolemization is the following evidence-carrying signature-extension
stage.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofNormalizationSemantics

open LO FirstOrder
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationSyntax
open Mettapedia.GSLT.LanguageDef.TptpOfficialPrincipalSymbols
open Mettapedia.GSLT.LanguageDef.TptpFofSymbolIdentity

/-! ## Arity-indexed first-order signature -/

/-- A user function symbol at one fixed arity. -/
structure FunctionSymbol (arity : Nat) where
  name : String
  kind : FunctionKind := .plain
  deriving DecidableEq, Repr

/-- A user predicate symbol at one fixed arity.  Equality is deliberately not
a user predicate: it has its own source constructor and fixed semantics. -/
structure PredicateSymbol (arity : Nat) where
  name : String
  kind : PredicateKind := .plain
  deriving DecidableEq, Repr

/-- A user predicate at one fixed arity, together with FOF equality. -/
inductive RelationSymbol : Nat -> Type
  | predicate {arity : Nat} (symbol : PredicateSymbol arity) :
      RelationSymbol arity
  | equality : RelationSymbol 2
  deriving DecidableEq, Repr

/-- The dynamic FOF language.  Arity remains an index rather than untrusted
metadata attached to an untyped symbol. -/
def language : LO.FirstOrder.Language where
  Func := FunctionSymbol
  Rel := RelationSymbol

abbrev Term (depth : Nat) :=
  LO.FirstOrder.Semiterm language Empty depth

/-- The principal-symbol identity used by official `new_symbols` metadata.
Arity remains available in `FunctionSymbol`; the official metadata identity
itself consists of kind and name. -/
def FunctionSymbol.principalId? {arity : Nat}
    (symbol : FunctionSymbol arity) : Option PrincipalSymbolId :=
  match symbol.kind with
  | .plain => some { kind := .functor, name := symbol.name }
  | _ => none

def RelationSymbol.principalId? {arity : Nat} :
    RelationSymbol arity -> Option PrincipalSymbolId
  | .predicate symbol =>
      match symbol.kind with
      | .plain => some { kind := .functor, name := symbol.name }
      | _ => none
  | .equality => none

/-! ## Binder-resolved source formulas -/

/-- FOF after binder resolution but before connective normalization.

Every constructor preserves one explicit binder depth.  TPTP's derived
connectives remain distinct here so normalization is a real transformation,
not a parser convention. -/
inductive Formula : Nat -> Type
  | verum {depth : Nat} : Formula depth
  | falsum {depth : Nat} : Formula depth
  | predicate {depth arity : Nat} :
      PredicateSymbol arity -> (Fin arity -> Term depth) -> Formula depth
  | equal {depth : Nat} : Term depth -> Term depth -> Formula depth
  | not {depth : Nat} : Formula depth -> Formula depth
  | and {depth : Nat} : Formula depth -> Formula depth -> Formula depth
  | or {depth : Nat} : Formula depth -> Formula depth -> Formula depth
  | iff {depth : Nat} : Formula depth -> Formula depth -> Formula depth
  | implies {depth : Nat} : Formula depth -> Formula depth -> Formula depth
  | reverseImplies {depth : Nat} :
      Formula depth -> Formula depth -> Formula depth
  | xor {depth : Nat} : Formula depth -> Formula depth -> Formula depth
  | nor {depth : Nat} : Formula depth -> Formula depth -> Formula depth
  | nand {depth : Nat} : Formula depth -> Formula depth -> Formula depth
  | all {depth : Nat} : Formula (depth + 1) -> Formula depth
  | ex {depth : Nat} : Formula (depth + 1) -> Formula depth

/-! ## Identity-respecting model semantics -/

/-- A first-order structure whose distinguished equality relation is actual
identity.  User predicates and functions remain otherwise arbitrary. -/
structure Model (Domain : Type) where
  interpretation : LO.FirstOrder.Structure language Domain
  equality_exact : forall values : Fin 2 -> Domain,
    interpretation.rel RelationSymbol.equality values <-> values 0 = values 1

def eval {Domain : Type} (model : Model Domain) {depth : Nat}
    (environment : Fin depth -> Domain) : Formula depth -> Prop
  | .verum => True
  | .falsum => False
  | .predicate predicate arguments =>
      model.interpretation.rel (.predicate predicate)
        (fun index => LO.FirstOrder.Semiterm.val model.interpretation
          environment Empty.elim (arguments index))
  | .equal left right =>
      LO.FirstOrder.Semiterm.val model.interpretation environment Empty.elim left =
        LO.FirstOrder.Semiterm.val model.interpretation environment Empty.elim right
  | .not body => Not (eval model environment body)
  | .and left right => eval model environment left /\ eval model environment right
  | .or left right => eval model environment left \/ eval model environment right
  | .iff left right => eval model environment left <-> eval model environment right
  | .implies left right => eval model environment left -> eval model environment right
  | .reverseImplies left right =>
      eval model environment right -> eval model environment left
  | .xor left right =>
      (eval model environment left /\ Not (eval model environment right)) \/
        (Not (eval model environment left) /\ eval model environment right)
  | .nor left right =>
      Not (eval model environment left \/ eval model environment right)
  | .nand left right =>
      Not (eval model environment left /\ eval model environment right)
  | .all body => forall value : Domain, eval model (value :> environment) body
  | .ex body => Exists fun value : Domain => eval model (value :> environment) body

/-! ## Total normalization to Foundation NNF -/

/-- Normalize under positive (`true`) or negative (`false`) polarity.
Foundation's first-order formula has only positive/negative atoms,
conjunction, disjunction, and quantifiers, so the result is NNF by type. -/
def normalize {depth : Nat} (polarity : Bool) : Formula depth ->
    LO.FirstOrder.Semiformula language Empty depth
  | .verum => if polarity then .verum else .falsum
  | .falsum => if polarity then .falsum else .verum
  | .predicate predicate arguments =>
      if polarity then .rel (.predicate predicate) arguments
      else .nrel (.predicate predicate) arguments
  | .equal left right =>
      let arguments : Fin 2 -> Term depth := ![left, right]
      if polarity then
        .rel RelationSymbol.equality arguments
      else
        .nrel RelationSymbol.equality arguments
  | .not body => normalize (!polarity) body
  | .and left right =>
      if polarity then
        .and (normalize true left) (normalize true right)
      else
        .or (normalize false left) (normalize false right)
  | .or left right =>
      if polarity then
        .or (normalize true left) (normalize true right)
      else
        .and (normalize false left) (normalize false right)
  | .iff left right =>
      if polarity then
        .and
          (.or (normalize false left) (normalize true right))
          (.or (normalize false right) (normalize true left))
      else
        .or
          (.and (normalize true left) (normalize false right))
          (.and (normalize true right) (normalize false left))
  | .implies left right =>
      if polarity then
        .or (normalize false left) (normalize true right)
      else
        .and (normalize true left) (normalize false right)
  | .reverseImplies left right =>
      if polarity then
        .or (normalize false right) (normalize true left)
      else
        .and (normalize true right) (normalize false left)
  | .xor left right =>
      if polarity then
        .or
          (.and (normalize true left) (normalize false right))
          (.and (normalize false left) (normalize true right))
      else
        .and
          (.or (normalize false left) (normalize true right))
          (.or (normalize false right) (normalize true left))
  | .nor left right =>
      if polarity then
        .and (normalize false left) (normalize false right)
      else
        .or (normalize true left) (normalize true right)
  | .nand left right =>
      if polarity then
        .or (normalize false left) (normalize false right)
      else
        .and (normalize true left) (normalize true right)
  | .all body =>
      if polarity then .all (normalize true body)
      else .ex (normalize false body)
  | .ex body =>
      if polarity then .ex (normalize true body)
      else .all (normalize false body)

abbrev normalizePositive {depth : Nat} (formula : Formula depth) :=
  normalize true formula

theorem eval_normalize_iff {Domain : Type} (model : Model Domain)
    {depth : Nat} (environment : Fin depth -> Domain)
    (polarity : Bool) (formula : Formula depth) :
    LO.FirstOrder.Semiformula.EvalAux model.interpretation Empty.elim
        environment (normalize polarity formula) <->
      if polarity then eval model environment formula
      else Not (eval model environment formula) := by
  induction formula generalizing polarity with
  | verum =>
      cases polarity <;>
        simp [normalize, eval, LO.FirstOrder.Semiformula.EvalAux]
  | falsum =>
      cases polarity <;>
        simp [normalize, eval, LO.FirstOrder.Semiformula.EvalAux]
  | predicate relation arguments =>
      cases polarity <;>
        simp [normalize, eval, LO.FirstOrder.Semiformula.EvalAux]
  | equal left right =>
      cases polarity <;>
        simp [normalize, eval, LO.FirstOrder.Semiformula.EvalAux,
          model.equality_exact]
  | not body inductionHypothesis =>
      cases polarity <;>
        simp [normalize, eval, inductionHypothesis]
  | and left right leftHypothesis rightHypothesis =>
      cases polarity <;>
        (simp [normalize, eval, LO.FirstOrder.Semiformula.EvalAux,
          leftHypothesis, rightHypothesis]; try tauto)
  | or left right leftHypothesis rightHypothesis =>
      cases polarity <;>
        simp [normalize, eval, LO.FirstOrder.Semiformula.EvalAux,
          leftHypothesis, rightHypothesis]
  | iff left right leftHypothesis rightHypothesis =>
      cases polarity <;>
        (simp [normalize, eval, LO.FirstOrder.Semiformula.EvalAux,
          leftHypothesis, rightHypothesis]; try tauto)
  | implies left right leftHypothesis rightHypothesis =>
      cases polarity <;>
        (simp [normalize, eval, LO.FirstOrder.Semiformula.EvalAux,
          leftHypothesis, rightHypothesis]; try tauto)
  | reverseImplies left right leftHypothesis rightHypothesis =>
      cases polarity <;>
        (simp [normalize, eval, LO.FirstOrder.Semiformula.EvalAux,
          leftHypothesis, rightHypothesis]; try tauto)
  | xor left right leftHypothesis rightHypothesis =>
      cases polarity <;>
        (simp [normalize, eval, LO.FirstOrder.Semiformula.EvalAux,
          leftHypothesis, rightHypothesis]; try tauto)
  | nor left right leftHypothesis rightHypothesis =>
      cases polarity <;>
        (simp [normalize, eval, LO.FirstOrder.Semiformula.EvalAux,
          leftHypothesis, rightHypothesis]; try tauto)
  | nand left right leftHypothesis rightHypothesis =>
      cases polarity <;>
        (simp [normalize, eval, LO.FirstOrder.Semiformula.EvalAux,
          leftHypothesis, rightHypothesis]; try tauto)
  | all body inductionHypothesis =>
      cases polarity <;>
        simp [normalize, eval, LO.FirstOrder.Semiformula.EvalAux,
          inductionHypothesis]
  | ex body inductionHypothesis =>
      cases polarity <;>
        simp [normalize, eval, LO.FirstOrder.Semiformula.EvalAux,
          inductionHypothesis]

theorem eval_normalizePositive_iff {Domain : Type} (model : Model Domain)
    {depth : Nat} (environment : Fin depth -> Domain)
    (formula : Formula depth) :
    LO.FirstOrder.Semiformula.EvalAux model.interpretation Empty.elim
        environment (normalizePositive formula) <->
      eval model environment formula := by
  simpa using eval_normalize_iff model environment true formula

/-! ## Exact principal-signature preservation -/

def termPrincipalSymbols {depth : Nat} : Term depth -> Finset PrincipalSymbolId
  | .bvar _ => ∅
  | .fvar impossible => nomatch impossible
  | .func symbol arguments =>
      let argumentsSymbols := Finset.univ.biUnion fun index =>
        termPrincipalSymbols (arguments index)
      match symbol.principalId? with
      | some principal => insert principal argumentsSymbols
      | none => argumentsSymbols

def formulaPrincipalSymbols {depth : Nat} :
    Formula depth -> Finset PrincipalSymbolId
  | .verum | .falsum => ∅
  | .predicate predicate arguments =>
      let argumentsSymbols := Finset.univ.biUnion fun index =>
        termPrincipalSymbols (arguments index)
      match (RelationSymbol.predicate predicate).principalId? with
      | some principal => insert principal argumentsSymbols
      | none => argumentsSymbols
  | .equal left right =>
      termPrincipalSymbols left ∪ termPrincipalSymbols right
  | .not body => formulaPrincipalSymbols body
  | .and left right | .or left right | .iff left right |
      .implies left right | .reverseImplies left right |
      .xor left right | .nor left right | .nand left right =>
      formulaPrincipalSymbols left ∪ formulaPrincipalSymbols right
  | .all body | .ex body => formulaPrincipalSymbols body

def nnfPrincipalSymbols {depth : Nat} :
    LO.FirstOrder.Semiformula language Empty depth ->
      Finset PrincipalSymbolId
  | .verum | .falsum => ∅
  | .rel relation arguments | .nrel relation arguments =>
      let argumentsSymbols := Finset.univ.biUnion fun index =>
        termPrincipalSymbols (arguments index)
      match relation.principalId? with
      | some symbol => insert symbol argumentsSymbols
      | none => argumentsSymbols
  | .and left right | .or left right =>
      nnfPrincipalSymbols left ∪ nnfPrincipalSymbols right
  | .all body | .ex body => nnfPrincipalSymbols body

private theorem biUnion_fin_two {alpha : Type} [DecidableEq alpha]
    (items : Fin 2 -> Finset alpha) :
    Finset.univ.biUnion items = items 0 ∪ items 1 := by
  ext element
  simp [Fin.exists_fin_two]

theorem normalize_principalSymbols_exact {depth : Nat}
    (polarity : Bool) (formula : Formula depth) :
    nnfPrincipalSymbols (normalize polarity formula) =
      formulaPrincipalSymbols formula := by
  induction formula generalizing polarity with
  | verum => cases polarity <;> rfl
  | falsum => cases polarity <;> rfl
  | predicate relation arguments => cases polarity <;> rfl
  | equal left right =>
      cases polarity <;>
        simp [normalize, nnfPrincipalSymbols, formulaPrincipalSymbols,
          RelationSymbol.principalId?, biUnion_fin_two]
  | not body inductionHypothesis =>
      simp [normalize, formulaPrincipalSymbols, inductionHypothesis]
  | and left right leftHypothesis rightHypothesis =>
      cases polarity <;>
        simp [normalize, formulaPrincipalSymbols, nnfPrincipalSymbols,
          leftHypothesis, rightHypothesis]
  | or left right leftHypothesis rightHypothesis =>
      cases polarity <;>
        simp [normalize, formulaPrincipalSymbols, nnfPrincipalSymbols,
          leftHypothesis, rightHypothesis]
  | iff left right leftHypothesis rightHypothesis =>
      cases polarity <;>
        simp [normalize, formulaPrincipalSymbols, nnfPrincipalSymbols,
          leftHypothesis, rightHypothesis, Finset.union_comm]
  | implies left right leftHypothesis rightHypothesis =>
      cases polarity <;>
        simp [normalize, formulaPrincipalSymbols, nnfPrincipalSymbols,
          leftHypothesis, rightHypothesis]
  | reverseImplies left right leftHypothesis rightHypothesis =>
      cases polarity <;>
        simp [normalize, formulaPrincipalSymbols, nnfPrincipalSymbols,
          leftHypothesis, rightHypothesis, Finset.union_comm]
  | xor left right leftHypothesis rightHypothesis =>
      cases polarity <;>
        simp [normalize, formulaPrincipalSymbols, nnfPrincipalSymbols,
          leftHypothesis, rightHypothesis, Finset.union_comm]
  | nor left right leftHypothesis rightHypothesis =>
      cases polarity <;>
        simp [normalize, formulaPrincipalSymbols, nnfPrincipalSymbols,
          leftHypothesis, rightHypothesis]
  | nand left right leftHypothesis rightHypothesis =>
      cases polarity <;>
        simp [normalize, formulaPrincipalSymbols, nnfPrincipalSymbols,
          leftHypothesis, rightHypothesis]
  | all body inductionHypothesis =>
      cases polarity <;>
        simp [normalize, formulaPrincipalSymbols, nnfPrincipalSymbols,
          inductionHypothesis]
  | ex body inductionHypothesis =>
      cases polarity <;>
        simp [normalize, formulaPrincipalSymbols, nnfPrincipalSymbols,
          inductionHypothesis]

/-! ## Evidence-carrying normalization result -/

/-- A normalization result retains the source, exact computed target, semantic
equivalence in every identity-respecting model, and exact principal-signature
preservation. -/
structure NormalizationResult {depth : Nat} (source : Formula depth) where
  target : LO.FirstOrder.Semiformula language Empty depth
  target_exact : target = normalizePositive source
  semantics_exact : forall {Domain : Type} (model : Model Domain)
      (environment : Fin depth -> Domain),
    LO.FirstOrder.Semiformula.EvalAux model.interpretation Empty.elim
        environment target <->
      eval model environment source
  principalSymbols_exact :
    nnfPrincipalSymbols target = formulaPrincipalSymbols source

def normalizeWithEvidence {depth : Nat} (source : Formula depth) :
    NormalizationResult source where
  target := normalizePositive source
  target_exact := rfl
  semantics_exact := by
    intro Domain model environment
    exact eval_normalizePositive_iff model environment source
  principalSymbols_exact := normalize_principalSymbols_exact true source

/-! ## Positive and negative canaries -/

namespace Canary

def p : PredicateSymbol 0 := ⟨"p", .plain⟩
def q : PredicateSymbol 0 := ⟨"q", .plain⟩

def atom (predicate : PredicateSymbol 0) : Formula 0 :=
  .predicate predicate ![]

/-- Negated implication normalizes to `p and not q`, rather than retaining a
derived connective or a negation above a compound formula. -/
def source : Formula 0 := .not (.implies (atom p) (atom q))

theorem source_normalizes_exactly :
    normalizePositive source =
      LO.FirstOrder.Semiformula.and
        (.rel (RelationSymbol.predicate p) ![])
        (.nrel (RelationSymbol.predicate q) ![]) := by
  rfl

theorem source_signature_exact :
    nnfPrincipalSymbols (normalizePositive source) =
      [{ kind := .functor, name := "p" },
       { kind := .functor, name := "q" }].toFinset := by
  simp [source, atom, p, q, normalizePositive, normalize,
    nnfPrincipalSymbols, RelationSymbol.principalId?]

/-- Equality is not admitted as a user principal symbol. -/
def reflexiveEquality : Formula 1 :=
  .equal (.bvar 0) (.bvar 0)

theorem equality_does_not_invent_principal_symbol :
    formulaPrincipalSymbols reflexiveEquality = ∅ := by
  rfl

theorem negative_polarity_is_semantic_negation
    {Domain : Type} (model : Model Domain) :
    LO.FirstOrder.Semiformula.EvalAux model.interpretation Empty.elim ![]
        (normalize false source) <->
      Not (eval model ![] source) := by
  exact eval_normalize_iff model ![] false source

end Canary

#print axioms eval_normalize_iff
#print axioms eval_normalizePositive_iff
#print axioms normalize_principalSymbols_exact
#print axioms normalizeWithEvidence
#print axioms Canary.source_normalizes_exactly
#print axioms Canary.source_signature_exact
#print axioms Canary.equality_does_not_invent_principal_symbol
#print axioms Canary.negative_polarity_is_semantic_negation

end Mettapedia.GSLT.LanguageDef.TptpFofNormalizationSemantics
