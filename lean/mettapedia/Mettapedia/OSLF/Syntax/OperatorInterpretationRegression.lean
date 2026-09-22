import Mettapedia.OSLF.Syntax.SignatureMorphism
import Mettapedia.OSLF.Syntax.PatternAsBindingSignature

/-!
# Ordinary substitution naturality does not suffice for operator composition

This control uses the existing pattern signature throughout. A local operation
on one binding argument inspects whether that argument is precisely `k` applied
to the newly bound variable. It returns one of two constants. Ordinary
substitution acts only on the enclosing free variables, so the inspection
commutes with every such substitution.

A strict signature morphism merges the unary labels `k` and `l`, retaining the
two result constants. The inspected bodies then have the same image, although
the inspection results do not. No operation on the translated bodies can
factor this composite, even without imposing any law on that operation.

Thus ordinary-substitution compatibility is a valid local law but does not by
itself license composition of arbitrary binding-argument interpretations.
No new signature, interpretation record, or recursive translation is defined.
-/

namespace Mettapedia.OSLF.Binding.OperatorInterpretationRegression

open PatternPresentation

set_option autoImplicit false

/-- A nullary application in the existing pattern signature. -/
def atom {Γ : Ctx patSig} (label : String) : Term patSig Γ .pat :=
  .op (.applyOp label 0) .nil

/-- An ordinary unary application, binding no variables of its own. -/
def unary {Γ : Ctx patSig} (label : String) (body : Term patSig Γ .pat) :
    Term patSig Γ .pat :=
  .op (.applyOp label 1) (.cons body .nil)

/-- Recognize the surrounding binding argument's newly bound variable. -/
def isBoundZero {Γ : Ctx patSig} : Term patSig (.pat :: Γ) .pat → Bool
  | .var .zero => true
  | _ => false

/-- Recognize exactly `k(bound-zero)`, not an arbitrary body headed by `k`. -/
def isKBound {Γ : Ctx patSig} : Term patSig (.pat :: Γ) .pat → Bool
  | .op (.applyOp label 1) (.cons body .nil) =>
      if label = "k" then isBoundZero body else false
  | _ => false

theorem isBoundZero_weaken {Γ : Ctx patSig} (body : Term patSig Γ .pat) :
    isBoundZero (weaken body) = false := by
  cases body <;> rfl

theorem isBoundZero_bind_liftSub {Γ Δ : Ctx patSig} (τ : Sub patSig Γ Δ)
    (body : Term patSig (.pat :: Γ) .pat) :
    isBoundZero (bind (liftSub τ [.pat]) body) = isBoundZero body := by
  cases body with
  | var token =>
      cases token with
      | zero => rfl
      | succ token => exact isBoundZero_weaken (τ _ token)
  | op operation arguments => rfl

/-- Substituting an enclosing variable cannot manufacture the new bound
variable: its replacement is weakened past that binder. -/
theorem isKBound_weaken {Γ : Ctx patSig} (body : Term patSig Γ .pat) :
    isKBound (weaken body) = false := by
  cases body with
  | var token => rfl
  | op operation arguments =>
      cases operation with
      | applyOp label arity =>
          cases arity with
          | zero => rfl
          | succ arity =>
              cases arity with
              | zero =>
                  change Args patSig [([], .pat)] Γ at arguments
                  cases arguments with
                  | cons head tail =>
                      change Args patSig [] Γ at tail
                      cases tail
                      change (if label = "k" then isBoundZero (weaken head)
                        else false) = false
                      rw [isBoundZero_weaken]
                      split <;> rfl
              | succ arity => rfl
      | _ => rfl

theorem isKBound_bind_liftSub {Γ Δ : Ctx patSig} (τ : Sub patSig Γ Δ)
    (body : Term patSig (.pat :: Γ) .pat) :
    isKBound (bind (liftSub τ [.pat]) body) = isKBound body := by
  cases body with
  | var token =>
      cases token with
      | zero => rfl
      | succ token => exact isKBound_weaken (τ _ token)
  | op operation arguments =>
      cases operation with
      | applyOp label arity =>
          cases arity with
          | zero => rfl
          | succ arity =>
              cases arity with
              | zero =>
                  change Args patSig [([], .pat)] (.pat :: Γ) at arguments
                  cases arguments with
                  | cons head tail =>
                      change Args patSig [] (.pat :: Γ) at tail
                      cases tail
                      change (if label = "k" then
                        isBoundZero (bind (liftSub τ [.pat]) head) else false) =
                        (if label = "k" then isBoundZero head else false)
                      rw [isBoundZero_bind_liftSub]
              | succ arity => rfl
      | _ => rfl

/-- A local operation of binding arity `([pat], pat) -> pat`. Its dependence
on the argument is intensional, despite commuting with ordinary substitution. -/
def inspect {Γ : Ctx patSig} (body : Term patSig (.pat :: Γ) .pat) :
    Term patSig Γ .pat :=
  if isKBound body then atom "a" else atom "b"

/-- Positive control: the local operation commutes with every substitution
between arbitrary enclosing contexts, with the argument binder lifted. -/
theorem inspect_bind {Γ Δ : Ctx patSig} (τ : Sub patSig Γ Δ)
    (body : Term patSig (.pat :: Γ) .pat) :
    bind τ (inspect body) = inspect (bind (liftSub τ [.pat]) body) := by
  unfold inspect
  rw [isKBound_bind_liftSub τ body]
  split <;> rfl

def mergeLabel (label : String) : String :=
  if label = "k" ∨ label = "l" then "m" else label

def mergeOp : {s : PatSrt} → PatOp s → PatOp s
  | _, .applyOp label arity => .applyOp (mergeLabel label) arity
  | _, operation => operation

/-- A strict existing-signature morphism. Labels `k` and `l` are identified
at every arity; arities and binder annotations themselves are unchanged. -/
def merge : SigMor patSig patSig where
  sortMap := id
  opMap := mergeOp
  carriesArity := by
    intro sort operation
    cases operation <;> exact (mapArities_id _).symm

def kBody : Term patSig [.pat] .pat := unary "k" (.var .zero)

def lBody : Term patSig [.pat] .pat := unary "l" (.var .zero)

def mBody : Term patSig [.pat] .pat := unary "m" (.var .zero)

theorem inspect_kBody : inspect kBody = (atom "a" : Term patSig [] .pat) := rfl

theorem inspect_lBody : inspect lBody = (atom "b" : Term patSig [] .pat) := rfl

theorem merge_kBody : merge.onTerm kBody = mBody := rfl

theorem merge_lBody : merge.onTerm lBody = mBody := rfl

theorem merge_atom_a :
    merge.onTerm (atom "a" : Term patSig [] .pat) = atom "a" := rfl

theorem merge_atom_b :
    merge.onTerm (atom "b" : Term patSig [] .pat) = atom "b" := rfl

private def outerLabel {Γ : Ctx patSig} : Term patSig Γ .pat → Option String
  | .op (.applyOp label _) _ => some label
  | _ => none

theorem atom_a_ne_b : (atom "a" : Term patSig [] .pat) ≠ atom "b" := by
  intro equal
  have labels := congrArg outerLabel equal
  exact (by decide : (some "a" : Option String) ≠ some "b") labels

/-- Negative control: even an arbitrary function on the translated binding
arguments cannot make inspection commute with this strict signature morphism.
Consequently adding ordinary-substitution naturality to that function could
not repair the failure. -/
theorem no_postcomposition_operation :
    ¬ ∃ operation : Term patSig [.pat] .pat → Term patSig [] .pat,
      ∀ body : Term patSig [.pat] .pat,
        merge.onTerm (inspect body) = operation (merge.onTerm body) := by
  rintro ⟨operation, factors⟩
  have first := factors kBody
  have second := factors lBody
  rw [inspect_kBody, merge_atom_a, merge_kBody] at first
  rw [inspect_lBody, merge_atom_b, merge_lBody] at second
  exact atom_a_ne_b (first.trans second.symm)

#print axioms inspect_bind
#print axioms merge
#print axioms merge_kBody
#print axioms merge_lBody
#print axioms atom_a_ne_b
#print axioms no_postcomposition_operation

end Mettapedia.OSLF.Binding.OperatorInterpretationRegression
