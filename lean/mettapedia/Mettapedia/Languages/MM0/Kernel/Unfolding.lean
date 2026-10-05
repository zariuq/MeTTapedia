import Mettapedia.Languages.MM0.Kernel.FreshDummies

/-!
# MM0 definition unfolding with explicit fresh images

An unfolding request supplies a definition identifier, parameter images and
fresh dummy images. The body is obtained from the definition environment and
substituted by computation. The independent relation checks the same request;
it does not accept an unrelated conversion with the same end result.

Definition admission is separate: the typing theorem below consumes the
actual body's typing judgment in its declared parameter-and-dummy context.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel
namespace Definition

structure Body where
  dummies : List Nat
  expression : Preterm

abbrev Signature := Nat → Option Body

def substitutionValues (arguments : List Preterm) (images : List Nat) : List Preterm :=
  arguments ++ images.map Preterm.var

inductive Unfolds (signature : TermSignature) (definitions : Signature) (target : Context)
    (symbol : Nat) (arguments : List Preterm) (images : List Nat) : Preterm → Prop where
  | intro {declaration : TermDecl} {body : Body} {result : Preterm} :
    signature symbol = some declaration → definitions symbol = some body →
    List.Forall₂ (Preterm.FitsBinder signature target) arguments declaration.arguments →
    FreshDummies target arguments body.dummies images →
    Preterm.Substitutes (Substitution.ofList (substitutionValues arguments images))
      body.expression result →
    Unfolds signature definitions target symbol arguments images result

def unfold? (signature : TermSignature) (definitions : Signature) (target : Context)
    (symbol : Nat) (arguments : List Preterm) (images : List Nat) : Option Preterm := do
  let declaration ← signature symbol
  let body ← definitions symbol
  if Substitution.checkArguments signature target arguments declaration.arguments &&
      checkDummies target arguments body.dummies images then
    body.expression.substitute (Substitution.ofList (substitutionValues arguments images))
  else none

theorem unfold_eq_some_iff (signature : TermSignature) (definitions : Signature) (target : Context)
    (symbol : Nat) (arguments : List Preterm) (images : List Nat) (result : Preterm) :
    unfold? signature definitions target symbol arguments images = some result ↔
      Unfolds signature definitions target symbol arguments images result := by
  constructor
  · intro accepted
    cases termLookup : signature symbol with
    | none => simp [unfold?, termLookup] at accepted
    | some declaration =>
        cases bodyLookup : definitions symbol with
        | none => simp [unfold?, termLookup, bodyLookup] at accepted
        | some body =>
            simp only [unfold?, termLookup, bodyLookup] at accepted
            change (if Substitution.checkArguments signature target arguments declaration.arguments &&
              checkDummies target arguments body.dummies images then
              body.expression.substitute (Substitution.ofList (substitutionValues arguments images))
              else none) = some result at accepted
            split at accepted
            next guards =>
              have conditions := Bool.and_eq_true_iff.mp guards
              exact .intro termLookup bodyLookup
                ((Substitution.checkArguments_iff _ _ _ _).mp conditions.1)
                ((checkDummies_iff _ _ _ _).mp conditions.2)
                (Preterm.substitute_sound accepted)
            next => simp at accepted
  · intro unfolded
    cases unfolded with
    | intro termLookup bodyLookup typed fresh substituted =>
        simp [unfold?, termLookup, bodyLookup,
          (Substitution.checkArguments_iff _ _ _ _).mpr typed,
          (checkDummies_iff _ _ _ _).mpr fresh, substituted.eval]

theorem unfold_none_iff (signature : TermSignature) (definitions : Signature) (target : Context)
    (symbol : Nat) (arguments : List Preterm) (images : List Nat) :
    unfold? signature definitions target symbol arguments images = none ↔
      ¬ ∃ result, Unfolds signature definitions target symbol arguments images result := by
  constructor
  · intro refused ⟨result, unfolded⟩
    have accepted := (unfold_eq_some_iff _ _ _ _ _ _ _).mpr unfolded
    rw [refused] at accepted
    contradiction
  · intro impossible
    cases result : unfold? signature definitions target symbol arguments images with
    | none => rfl
    | some value => exact False.elim (impossible ⟨value,
        (unfold_eq_some_iff _ _ _ _ _ _ _).mp result⟩)

theorem Unfolds.deterministic {signature : TermSignature} {definitions : Signature}
    {target : Context} {symbol : Nat} {arguments : List Preterm} {images : List Nat}
    {left right : Preterm}
    (first : Unfolds signature definitions target symbol arguments images left)
    (second : Unfolds signature definitions target symbol arguments images right) : left = right :=
  Option.some.inj (((unfold_eq_some_iff _ _ _ _ _ _ _).mpr first).symm.trans
    ((unfold_eq_some_iff _ _ _ _ _ _ _).mpr second))

theorem FreshDummies.typed_substitution {signature : TermSignature} {target : Context}
    {arguments : List Preterm} {formal : Context} {sorts images : List Nat}
    (fresh : FreshDummies target arguments sorts images)
    (typed : List.Forall₂ (Preterm.FitsBinder signature target) arguments formal) :
    List.Forall₂ (Preterm.FitsBinder signature target) (substitutionValues arguments images)
      (formal ++ sorts.map Binder.bound) :=
  List.rel_append typed (fresh.typed signature)

theorem unfold_typed_total {signature : TermSignature} {definitions : Signature} {target : Context}
    {symbol : Nat} {declaration : TermDecl} {body : Body}
    (termLookup : signature symbol = some declaration) (bodyLookup : definitions symbol = some body)
    {arguments : List Preterm} {images : List Nat}
    (typed : List.Forall₂ (Preterm.FitsBinder signature target) arguments declaration.arguments)
    (fresh : FreshDummies target arguments body.dummies images)
    (bodyTyped : Preterm.HasType signature
      (declaration.arguments ++ body.dummies.map Binder.bound) body.expression [] declaration.resultSort) :
    ∃ result, unfold? signature definitions target symbol arguments images = some result ∧
      Preterm.HasType signature target result [] declaration.resultSort := by
  have typedValues := fresh.typed_substitution typed
  obtain ⟨support, supported⟩ := bodyTyped.support_exists
  have defined : ∃ result,
      body.expression.substitute (Substitution.ofList (substitutionValues arguments images)) =
        some result := by
    apply (Preterm.substitute_ofList_defined_iff _ _).mpr
    intro index occurs
    obtain ⟨binder, lookup⟩ := supported.lookup_exists index occurs
    rw [typedValues.length_eq]
    exact (List.getElem?_eq_some_iff.mp lookup).1
  obtain ⟨result, computed⟩ := defined
  have substituted := Preterm.substitute_sound computed
  exact ⟨result, (unfold_eq_some_iff _ _ _ _ _ _ _).mpr
    (.intro termLookup bodyLookup typed fresh substituted),
    bodyTyped.substitute typedValues substituted⟩

end Definition
end Mettapedia.Languages.MM0.Kernel
