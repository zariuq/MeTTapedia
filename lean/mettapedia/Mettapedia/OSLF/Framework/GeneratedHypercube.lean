import Mettapedia.OSLF.Framework.RedexPosition
import Mettapedia.OSLF.Framework.ModalHypercube

/-!
# Slot families and a partial sort-constraint analyzer

`ModalHypercube` supplies the target: a `ModalPresentation n` is `n` sort slots
together with a decidable admissibility predicate, and its `equationalCenter`
is the set of admissible assignments.  What it did not supply is the function
from a presentation to that data — every instance there names its slot count in
prose and types its admissibility by hand.

This module computes slot data and a candidate admissibility filter from the
authored language. For a rewrite rule and a choice of position:

* the slots are one per rely parameter plus one output, so the slot family is
  `RedexPosition.slotCount`, a function of the rule; and
* admissibility is decided by evaluating the language's own equations at the
  sort level under the slot assignment, together with the modality's output
  agreement.

The sort-level interpretation of constructors is a parameter, not a derivation:
it belongs to the target-logic specification, exactly as the choice of which
connectives to admit does.  What must not be hand-written, and here is not, is
which slots a rule has and which assignments its equations leave standing.

Equation variables are assigned to rely slots by enumerating name maps. This is
not yet a sort-correct instantiation theorem. Uninterpreted terms are skipped,
collection rest variables are ignored by evaluation, and only the selected
right-hand side is checked for output agreement. Other base rewrite laws and
context closure are not checked. Thus `derivedCenter` is a candidate filter,
not a certified implementation of the source's equational center. Soundness,
completeness and renaming invariance remain mathematical obligations.
-/

namespace Mettapedia.OSLF.Framework.GeneratedHypercube

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ModalHypercube
open Mettapedia.OSLF.Framework.RedexPosition

/-! ## Sort-level evaluation -/

/-- A sort-level interpretation of the signature: each constructor sends the
sorts of its arguments to the sort of its result.  `none` marks a constructor
the specification leaves uninterpreted; the current analyzer skips that
obligation rather than establishing it. -/
abbrev SortAlgebra := String → List HSort → Option HSort

/-- The interpretation used in the worked examples: a constructor takes the
sort of its first argument, and a nullary constructor is uninterpreted.  This
is the first-projection reading under which a commutative binary operation
forces its two argument slots to agree. -/
def firstProjection : SortAlgebra := fun _ args => args.head?

/-- The label under which a collection node is interpreted. -/
def collectionLabel : CollType → String
  | .vec => "‹vec›"
  | .hashBag => "‹bag›"
  | .hashSet => "‹set›"

/-- The slot a rely parameter occupies. -/
def relyIndex (relies : List String) (x : String) :
    Option (Fin (relies.length + 1)) :=
  if h : relies.idxOf x < relies.length then
    some ⟨relies.idxOf x, by omega⟩
  else
    none

/-- The output slot, always the last. -/
def outputIndex (relies : List String) : Fin (relies.length + 1) :=
  ⟨relies.length, by omega⟩

mutual

/-- Evaluate a pattern at the sort level under an assignment of sorts to
variables.  A variable reads its sort; a constructor applies the interpretation;
anything the specification does not interpret — a bound variable, a binder, an
explicit substitution, a variable with no sort — evaluates to `none`. The
current filter skips such obligations; this is not evidence of coherence.

Written by structural recursion on the constructor fields, so that a generated
center reduces in the kernel rather than only under `#eval`. -/
def evalSortWith (alg : SortAlgebra) (lookup : String → Option HSort) :
    Pattern → Option HSort
  | .fvar x => lookup x
  | .apply f args => (evalSortListWith alg lookup args).bind (alg f)
  | .collection tag elements _ =>
      (evalSortListWith alg lookup elements).bind (alg (collectionLabel tag))
  | .bvar _ => none
  | .lambda _ _ => none
  | .multiLambda _ _ _ => none
  | .subst _ _ => none

/-- Evaluate every argument, failing if any is uninterpreted. -/
def evalSortListWith (alg : SortAlgebra) (lookup : String → Option HSort) :
    List Pattern → Option (List HSort)
  | [] => some []
  | p :: ps =>
      match evalSortWith alg lookup p, evalSortListWith alg lookup ps with
      | some a, some rest => some (a :: rest)
      | _, _ => none

end

/-- The assignment that reads a rely parameter's own slot. -/
def slotLookup (relies : List String)
    (σ : Fin (relies.length + 1) → HSort) : String → Option HSort :=
  fun x => (relyIndex relies x).map σ

/-- Evaluate a pattern at the sort level under a slot assignment. -/
def evalSort (alg : SortAlgebra) (relies : List String)
    (σ : Fin (relies.length + 1) → HSort) (p : Pattern) : Option HSort :=
  evalSortWith alg (slotLookup relies σ) p

/-! ## Instantiating an equation at the slots -/

/-- The variables of an equation. -/
def equationVars (eq : Equation) : List String :=
  (fvarNames eq.left ++ fvarNames eq.right).eraseDups

/-- Every map from a list of variables to the rely parameters. -/
def allInstantiations (vars relies : List String) :
    List (List (String × String)) :=
  match vars with
  | [] => [[]]
  | x :: rest =>
      (allInstantiations rest relies).flatMap fun tail =>
        relies.map fun r => (x, r) :: tail

/-- The sort assignment an instantiation induces: each equation variable reads
the slot of the rely parameter it was sent to. -/
def instantiationLookup (relies : List String)
    (σ : Fin (relies.length + 1) → HSort)
    (inst : List (String × String)) : String → Option HSort :=
  fun x =>
    match inst.find? (fun entry => entry.1 == x) with
    | some entry => (relyIndex relies entry.2).map σ
    | none => none

/-- Compare an equation under every enumerated name map to rely slots.
Uninterpreted comparisons are skipped; this does not certify the equation. -/
def equationRespected (alg : SortAlgebra) (relies : List String)
    (σ : Fin (relies.length + 1) → HSort) (eq : Equation) : Bool :=
  (allInstantiations (equationVars eq) relies).all fun inst =>
    let lookup := instantiationLookup relies σ inst
    match evalSortWith alg lookup eq.left, evalSortWith alg lookup eq.right with
    | some a, some b => a == b
    | _, _ => true

/-! ## The derived presentation -/

/-- Candidate filter from interpreted equations and selected output agreement.
It does not check all base rewrite laws or their context closures. -/
def derivedAdmissible (alg : SortAlgebra) (lang : LanguageDef)
    (rule : RewriteRule) (pos : Position)
    (σ : Fin ((relyVars rule.left pos).length + 1) → HSort) : Bool :=
  let relies := relyVars rule.left pos
  lang.equations.all (equationRespected alg relies σ) &&
    (match evalSort alg relies σ rule.right with
     | some a => a == σ (outputIndex relies)
     | none => true)

/-- The modal presentation generated by a rule at a redex position: slot count
from the rely parameters, admissibility from the equations. -/
def derivedPresentation (alg : SortAlgebra) (lang : LanguageDef)
    (rule : RewriteRule) (pos : Position) :
    ModalPresentation (slotCount rule.left pos) where
  admissible := derivedAdmissible alg lang rule pos

/-- The finite candidate filter produced by the partial analyzer. -/
def derivedCenter (alg : SortAlgebra) (lang : LanguageDef)
    (rule : RewriteRule) (pos : Position) :
    Finset (Fin (slotCount rule.left pos) → HSort) :=
  equationalCenter (derivedPresentation alg lang rule pos)

/-- Whether an assignment sends a named rely parameter's slot to a given sort.

A name the position does not have as a rely parameter fails, rather than
imposing no condition.  Failing open would make a face named by a misspelt
parameter silently equal to the whole cube, which is the quietest possible way
to report a wrong answer. -/
def fixSlot (relies : List String) (name : String) (s : HSort)
    (σ : Fin (relies.length + 1) → HSort) : Bool :=
  match relyIndex relies name with
  | some i => σ i == s
  | none => false

/-! ## Rely parameters the rule does not declare

A free metavariable of a left-hand side that the rule's own type context does
not declare still becomes a rely parameter, and so mints a sort slot.  That is
usually a defect of the authored rule rather than of the generator, so it is
worth being able to say which rules have one. -/

/-- Every rely parameter of this position is declared in the rule's type
context. -/
def RelyVarsDeclared (rule : RewriteRule) (pos : Position) : Bool :=
  (relyVars rule.left pos).all fun x =>
    rule.typeContext.any fun entry => entry.1 == x

end Mettapedia.OSLF.Framework.GeneratedHypercube
