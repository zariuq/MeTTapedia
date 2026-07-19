import Mathlib.Data.Finset.Union
import Mettapedia.Languages.OpenTheory.Syntax

/-!
# OpenTheory sequents and theorem carriers

This module models the alpha-set and theorem-state boundary of OpenTheory
revision `f555adbf6f3ca52ef6a9c5ca35d0316e53a289c1`, following
`src/TypeOp.sml`, `src/Type.sml`, `src/Const.sml`, `src/Term.sml`,
`src/Sequent.sml`, and `src/Thm.sml`.

Every term in a sequent is individually checked and alpha-canonical.  A raw
sequent is not intrinsically Boolean: the source exposes a separate Booleanity
test, and raw theorem substitution can produce a typed non-Boolean current
sequent.  Tagged axiom sequents remain Boolean, while `VerifiedTheorem` adds the
Boolean current-sequent invariant used by the verified profile.

Primitive Boolean and equality heads include their undefined provenance.
Matching only the printed names `bool` or `=` is deliberately insufficient.
-/

namespace Mettapedia.Languages.OpenTheory

/-! ## Primitive heads -/

namespace TypeOp

/-- The exact undefined global Boolean type operator from OpenTheory. -/
def bool : TypeOp := .mk (Name.global "bool") .undefined

end TypeOp

namespace Ty

/-- The exact nullary OpenTheory Boolean type. -/
def bool : Ty := .op TypeOp.bool []

/-- Executable recognition of the exact primitive Boolean type. -/
def isBool : Ty → Bool
  | .op operator [] => TypeOp.same operator TypeOp.bool
  | _ => false

@[simp] theorem isBool_eq_true_iff (ty : Ty) :
    ty.isBool = true ↔ ty = Ty.bool := by
  cases ty with
  | var name => simp [isBool, bool]
  | op operator arguments =>
      cases arguments with
      | nil => simp [isBool, bool]
      | cons head tail => simp [isBool, bool]

/-- The polymorphic equality-constant type at one operand type. -/
def equality (operand : Ty) : Ty :=
  .function operand (.function operand Ty.bool)

end Ty

namespace Const

/-- The exact undefined global equality constant from OpenTheory. -/
def equality : Const := .mk (Name.global "=") .undefined

end Const

/-! ## Executable equality on checked canonical terms -/

namespace CanonicalTerm

/-- A closed checked term's type is uniquely determined by its canonical term. -/
@[ext] theorem ext_term {left right : CanonicalTerm}
    (hterm : left.term = right.term) : left = right := by
  cases left with
  | mk leftTerm leftTy leftChecked =>
      cases right with
      | mk rightTerm rightTy rightChecked =>
          dsimp at hterm
          subst rightTerm
          have hty : leftTy = rightTy :=
            Option.some.inj (leftChecked.symm.trans rightChecked)
          subst rightTy
          rfl

/-- Structural equality of checked alpha-canonical terms. -/
def same (left right : CanonicalTerm) : Bool :=
  DBTerm.same left.term right.term

@[simp] theorem same_eq_true_iff (left right : CanonicalTerm) :
    left.same right = true ↔ left = right := by
  constructor
  · intro hsame
    apply ext_term
    exact (DBTerm.same_eq_true_iff left.term right.term).mp hsame
  · intro heq
    subst right
    exact (DBTerm.same_eq_true_iff left.term left.term).mpr rfl

/-- The structural equality above is executable and proof-field independent. -/
instance instDecidableEq : DecidableEq CanonicalTerm := fun left right =>
  if hsame : left.same right = true then
    isTrue ((same_eq_true_iff left right).mp hsame)
  else
    isFalse fun heq => hsame ((same_eq_true_iff left right).mpr heq)

/-- A checked term has the exact primitive Boolean type. -/
def IsBool (term : CanonicalTerm) : Prop := term.ty = Ty.bool

/-- Executable Booleanity test for a checked term. -/
def isBoolB (term : CanonicalTerm) : Bool := term.ty.isBool

@[simp] theorem isBoolB_eq_true_iff (term : CanonicalTerm) :
    term.isBoolB = true ↔ term.IsBool := by
  simp [isBoolB, IsBool]

end CanonicalTerm

/-! ## Alpha-canonical finite hypothesis sets

`Finset` represents the extensional hypothesis set used by the inference
rules.  It intentionally does not retain source order or a named-term
representative for article replay; a later reader boundary must retain that
separate source evidence and reject duplicates before conversion.
-/

/-- A typed OpenTheory sequent.  Booleanity is intentionally separate. -/
structure Sequent where
  hyp : Finset CanonicalTerm
  concl : CanonicalTerm
deriving DecidableEq

namespace Sequent

/-- Sequents are determined by their canonical hypothesis set and conclusion. -/
@[ext] theorem ext {left right : Sequent}
    (hhyp : left.hyp = right.hyp) (hconcl : left.concl = right.concl) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Every hypothesis and the conclusion has exact primitive Boolean type. -/
def IsBool (sequent : Sequent) : Prop :=
  sequent.concl.IsBool ∧
    ∀ hypothesis ∈ sequent.hyp, hypothesis.IsBool

/-- Executable form of `IsBool`. -/
def isBoolB (sequent : Sequent) : Bool :=
  sequent.concl.isBoolB &&
    decide ((sequent.hyp.filter fun term => term.isBoolB = false) = ∅)

@[simp] theorem isBoolB_eq_true_iff (sequent : Sequent) :
    sequent.isBoolB = true ↔ sequent.IsBool := by
  simp [isBoolB, IsBool]

/-- Article ingress rejects duplicate hypotheses modulo alpha equivalence. -/
def ofObjectTerms? (hypotheses : List CanonicalTerm)
    (conclusion : CanonicalTerm) : Option Sequent :=
  if hypotheses.Nodup then
    some ⟨hypotheses.toFinset, conclusion⟩
  else
    none

/-- Exact characterization of alpha-duplicate-rejecting article ingress. -/
theorem ofObjectTerms?_eq_some_iff
    (hypotheses : List CanonicalTerm) (conclusion : CanonicalTerm)
    (sequent : Sequent) :
    ofObjectTerms? hypotheses conclusion = some sequent ↔
      hypotheses.Nodup ∧
        sequent.hyp = hypotheses.toFinset ∧
        sequent.concl = conclusion := by
  constructor
  · intro hresult
    by_cases hnodup : hypotheses.Nodup
    · simp [ofObjectTerms?, hnodup] at hresult
      subst sequent
      exact ⟨hnodup, rfl, rfl⟩
    · simp [ofObjectTerms?, hnodup] at hresult
  · rintro ⟨hnodup, hhyp, hconcl⟩
    simp only [ofObjectTerms?, if_pos hnodup, Option.some.injEq]
    cases sequent
    simp_all

/-- Hypothesis-set construction is invariant under input permutation. -/
theorem ofObjectTerms?_eq_of_perm
    {left right : List CanonicalTerm} (permutation : left.Perm right)
    (conclusion : CanonicalTerm) :
    ofObjectTerms? left conclusion = ofObjectTerms? right conclusion := by
  have hsets : left.toFinset = right.toFinset := by
    ext term
    simp only [List.mem_toFinset]
    exact permutation.mem_iff
  by_cases hleft : left.Nodup
  · have hright : right.Nodup := permutation.nodup_iff.mp hleft
    simp [ofObjectTerms?, hleft, hright, hsets]
  · have hright : ¬ right.Nodup := by
      simpa [permutation.nodup_iff] using hleft
    simp [ofObjectTerms?, hleft, hright]

/-- Finite-set deletion removes exactly one canonical alpha class. -/
theorem mem_erase_iff (hypotheses : Finset CanonicalTerm)
    (removed candidate : CanonicalTerm) :
    candidate ∈ hypotheses.erase removed ↔
      candidate ∈ hypotheses ∧ candidate ≠ removed := by
  simp [and_comm]

end Sequent

/-! ## Raw and verified theorem carriers -/

/-- Raw source theorem state.  Axiom tags are Boolean; the current sequent may
become non-Boolean under source-compatible raw substitution. -/
structure Theorem where
  axioms : Finset Sequent
  axiomsBoolean : ∀ taggedSequent ∈ axioms, taggedSequent.IsBool
  sequent : Sequent

namespace Theorem

/-- Proof irrelevance leaves theorem structure determined by its data fields. -/
@[ext] theorem ext {left right : Theorem}
    (haxioms : left.axioms = right.axioms)
    (hsequent : left.sequent = right.sequent) : left = right := by
  cases left
  cases right
  simp_all

/-- Source theorem equality intentionally ignores axiom provenance. -/
def SourceEq (left right : Theorem) : Prop :=
  left.sequent = right.sequent

/-- Executable source theorem equality. -/
def sourceEqB (left right : Theorem) : Bool :=
  decide (left.sequent = right.sequent)

@[simp] theorem sourceEqB_eq_true_iff (left right : Theorem) :
    sourceEqB left right = true ↔ left.SourceEq right := by
  simp [sourceEqB, SourceEq]

/-- Union of theorem axiom sets preserves the Boolean-tag invariant. -/
theorem axiomsBoolean_union (left right : Theorem) :
    ∀ taggedSequent ∈ left.axioms ∪ right.axioms,
      taggedSequent.IsBool := by
  intro taggedSequent hmember
  rw [Finset.mem_union] at hmember
  rcases hmember with hleft | hright
  · exact left.axiomsBoolean taggedSequent hleft
  · exact right.axiomsBoolean taggedSequent hright

end Theorem

/-- Verified theorem state adds Booleanity of the current sequent. -/
structure VerifiedTheorem where
  raw : Theorem
  currentBool : raw.sequent.IsBool

/-! ## Calibration examples -/

namespace SequentExamples

def boolVariable (component : String) : CanonicalTerm :=
  ⟨.free ⟨Name.global component, Ty.bool⟩, Ty.bool, by simp [Ty.bool]⟩

def individualVariable (component : String) : CanonicalTerm :=
  ⟨.free ⟨Name.global component, Examples.individual⟩,
    Examples.individual, by simp⟩

example : (boolVariable "p").isBoolB = true := by
  simp [boolVariable, CanonicalTerm.IsBool]

/-- A type variable printed `bool` is not the primitive Boolean type. -/
example : Ty.isBool (.var (Name.global "bool")) = false := by
  rfl

private def definedBoolOperator : TypeOp :=
  .mk (Name.global "bool")
    (.defined (.var (Name.global "witness") Ty.bool) [])

/-- Same printed name and arity do not erase type-operator provenance. -/
example : Ty.isBool (.op definedBoolOperator []) = false := by
  simp [Ty.isBool, definedBoolOperator, TypeOp.bool,
    TypeOp.same, TypeOpProvenance.same]

/-- The primitive Boolean operator at the wrong arity is not Boolean. -/
example : Ty.isBool (.op TypeOp.bool [Ty.bool]) = false := by
  rfl

example :
    Sequent.ofObjectTerms? [boolVariable "p", boolVariable "q"]
        (boolVariable "r") =
      Sequent.ofObjectTerms? [boolVariable "q", boolVariable "p"]
        (boolVariable "r") := by
  apply Sequent.ofObjectTerms?_eq_of_perm
  exact List.Perm.swap _ _ []

/-- Duplicate alpha classes reject at article-list ingress. -/
example :
    Sequent.ofObjectTerms? [boolVariable "p", boolVariable "p"]
      (boolVariable "q") = none := by
  simp [Sequent.ofObjectTerms?, boolVariable]

def canonicalIdentityX : CanonicalTerm :=
  ⟨Examples.identityX.toDB [],
    .function Examples.individual Examples.individual, by
      calc
        DBTerm.inferType [] (Examples.identityX.toDB []) =
            Examples.identityX.inferType := by
              simpa using DBTerm.inferType_toDB [] Examples.identityX
        _ = some (.function Examples.individual Examples.individual) := by
          simp [Examples.identityX]⟩

def canonicalIdentityY : CanonicalTerm :=
  ⟨Examples.identityY.toDB [],
    .function Examples.individual Examples.individual, by
      calc
        DBTerm.inferType [] (Examples.identityY.toDB []) =
            Examples.identityY.inferType := by
              simpa using DBTerm.inferType_toDB [] Examples.identityY
        _ = some (.function Examples.individual Examples.individual) := by
          simp [Examples.identityY]⟩

/-- Binder-renamed source terms occupy one canonical alpha class. -/
theorem canonicalIdentityX_eq_canonicalIdentityY :
    canonicalIdentityX = canonicalIdentityY := by
  apply CanonicalTerm.ext_term
  simp [canonicalIdentityX, canonicalIdentityY, Examples.identityX,
    Examples.identityY, SourceTerm.toDB, boundIndex, sourceVarSame]

/-- Source-list duplicate rejection therefore catches binder-renamed copies. -/
example :
    Sequent.ofObjectTerms? [canonicalIdentityX, canonicalIdentityY]
      (boolVariable "q") = none := by
  rw [canonicalIdentityX_eq_canonicalIdentityY]
  simp [Sequent.ofObjectTerms?]

/-- A typed but non-Boolean current sequent remains representable raw data. -/
def nonBooleanSequent : Sequent :=
  ⟨{individualVariable "x"}, individualVariable "x"⟩

example : nonBooleanSequent.isBoolB = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hbool
  have hcurrent :=
    (Sequent.isBoolB_eq_true_iff nonBooleanSequent).mp hbool
  have hconclusion := hcurrent.1
  simp [nonBooleanSequent, individualVariable, CanonicalTerm.IsBool,
    Ty.bool, Examples.individual, TypeOp.bool, Name.global] at hconclusion

end SequentExamples

end Mettapedia.Languages.OpenTheory
