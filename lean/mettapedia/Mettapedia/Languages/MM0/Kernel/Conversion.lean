import Mettapedia.Languages.MM0.Kernel.Unfolding
import Mettapedia.Languages.MM0.Kernel.FreeVariables

/-!
# Typed MM0 conversion and submitted conversion witnesses

The independent conversion rules use saturated expression typing, ordered
same-head congruence and actual definition unfolding. Congruence retains the
bound-slot restrictions on both sides. An unfolding supplies fresh dummy
images and computes the direct substitution of the stored body.

The witness checker synthesizes both endpoints and their sort. Transitivity
checks its actual intermediate expression; congruence checks every child in
declaration order. This is validation of finite supplied evidence, without
proof search or a fixed recursion bound. Definition admission is separate;
the result typing guard also refuses malformed bodies in an unadmitted
definition environment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

open Preterm

mutual

inductive Converts (signature : TermSignature) (definitions : Definition.Signature)
    (context : Context) : Preterm → Preterm → Nat → Prop where
  | refl {expression : Preterm} {sort : Nat} : HasType signature context expression [] sort →
      Converts signature definitions context expression expression sort
  | symm {left right : Preterm} {sort : Nat} :
      Converts signature definitions context left right sort →
      Converts signature definitions context right left sort
  | trans {left middle right : Preterm} {sort : Nat} :
      Converts signature definitions context left middle sort →
      Converts signature definitions context middle right sort →
      Converts signature definitions context left right sort
  | congruence {symbol : Nat} {declaration : TermDecl} {left right : List Preterm} :
      signature symbol = some declaration →
      ConvertsArgs signature definitions context left right declaration.arguments →
      Converts signature definitions context (applyArgs (.term symbol) left)
        (applyArgs (.term symbol) right) declaration.resultSort
  | unfold {symbol : Nat} {declaration : TermDecl} {arguments : List Preterm}
      {images : List Nat} {result : Preterm} :
      signature symbol = some declaration →
      Definition.Unfolds signature definitions context symbol arguments images result →
      HasType signature context result [] declaration.resultSort →
      Converts signature definitions context (applyArgs (.term symbol) arguments)
        result declaration.resultSort

inductive ConvertsArgs (signature : TermSignature) (definitions : Definition.Signature)
    (context : Context) : List Preterm → List Preterm → Context → Prop where
  | nil : ConvertsArgs signature definitions context [] [] []
  | cons {left right : Preterm} {lefts rights : List Preterm} {binder : Binder}
      {binders : Context} :
      FitsBinder signature context left binder → FitsBinder signature context right binder →
      Converts signature definitions context left right binder.sort →
      ConvertsArgs signature definitions context lefts rights binders →
      ConvertsArgs signature definitions context (left :: lefts) (right :: rights) (binder :: binders)

end

/-- Finite conversion evidence. Substitution's internal steps are not supplied. -/
inductive ConvWitness where
  | refl (expression : Preterm)
  | symm (child : ConvWitness)
  | trans (first second : ConvWitness)
  | congruence (symbol : Nat) (children : List ConvWitness)
  | unfold (symbol : Nat) (arguments : List Preterm) (images : List Nat)
  deriving Repr

structure ConversionResult where
  left : Preterm
  right : Preterm
  sort : Nat
  deriving DecidableEq, Repr

namespace ConvWitness

mutual

def conversion? (signature : TermSignature) (definitions : Definition.Signature)
    (context : Context) : ConvWitness → Option ConversionResult
  | .refl expression => do
      let (remaining, sort) ← infer signature context expression
      if remaining = [] then some ⟨expression, expression, sort⟩ else none
  | .symm child => do
      let result ← conversion? signature definitions context child
      pure ⟨result.right, result.left, result.sort⟩
  | .trans first second => do
      let left ← conversion? signature definitions context first
      let right ← conversion? signature definitions context second
      if left.right = right.left ∧ left.sort = right.sort then
        some ⟨left.left, right.right, left.sort⟩
      else none
  | .congruence symbol children => do
      let declaration ← signature symbol
      let (left, right) ← arguments? signature definitions context children declaration.arguments
      pure ⟨applyArgs (.term symbol) left, applyArgs (.term symbol) right, declaration.resultSort⟩
  | .unfold symbol arguments images => do
      let declaration ← signature symbol
      let result ← Definition.unfold? signature definitions context symbol arguments images
      if infer signature context result = some ([], declaration.resultSort) then
        some ⟨applyArgs (.term symbol) arguments, result, declaration.resultSort⟩
      else none
termination_by witness => sizeOf witness

def arguments? (signature : TermSignature) (definitions : Definition.Signature)
    (context : Context) : List ConvWitness → Context → Option (List Preterm × List Preterm)
  | [], [] => some ([], [])
  | child :: children, binder :: binders => do
      let result ← conversion? signature definitions context child
      if result.sort = binder.sort ∧ checkBinder signature context result.left binder = true ∧
          checkBinder signature context result.right binder = true then
        let (left, right) ← arguments? signature definitions context children binders
        some (result.left :: left, result.right :: right)
      else none
  | _, _ => none
termination_by children _ => sizeOf children

end

mutual

/-- The meaning of this particular submitted witness and its claimed endpoints. -/
inductive Checks (signature : TermSignature) (definitions : Definition.Signature)
    (context : Context) : ConvWitness → Preterm → Preterm → Nat → Prop where
  | refl {expression : Preterm} {sort : Nat} : HasType signature context expression [] sort →
      Checks signature definitions context (.refl expression) expression expression sort
  | symm {child : ConvWitness} {left right : Preterm} {sort : Nat} :
      Checks signature definitions context child left right sort →
      Checks signature definitions context (.symm child) right left sort
  | trans {first second : ConvWitness} {left middle right : Preterm} {sort : Nat} :
      Checks signature definitions context first left middle sort →
      Checks signature definitions context second middle right sort →
      Checks signature definitions context (.trans first second) left right sort
  | congruence {symbol : Nat} {declaration : TermDecl} {children : List ConvWitness}
      {left right : List Preterm} :
      signature symbol = some declaration →
      ChecksArgs signature definitions context children left right declaration.arguments →
      Checks signature definitions context (.congruence symbol children)
        (applyArgs (.term symbol) left) (applyArgs (.term symbol) right) declaration.resultSort
  | unfold {symbol : Nat} {declaration : TermDecl} {arguments : List Preterm}
      {images : List Nat} {result : Preterm} :
      signature symbol = some declaration →
      Definition.Unfolds signature definitions context symbol arguments images result →
      HasType signature context result [] declaration.resultSort →
      Checks signature definitions context (.unfold symbol arguments images)
        (applyArgs (.term symbol) arguments) result declaration.resultSort

inductive ChecksArgs (signature : TermSignature) (definitions : Definition.Signature)
    (context : Context) : List ConvWitness → List Preterm → List Preterm → Context → Prop where
  | nil : ChecksArgs signature definitions context [] [] [] []
  | cons {child : ConvWitness} {children : List ConvWitness} {left right : Preterm}
      {lefts rights : List Preterm} {binder : Binder} {binders : Context} :
      FitsBinder signature context left binder → FitsBinder signature context right binder →
      Checks signature definitions context child left right binder.sort →
      ChecksArgs signature definitions context children lefts rights binders →
      ChecksArgs signature definitions context (child :: children)
        (left :: lefts) (right :: rights) (binder :: binders)

end

theorem Checks.eval {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {witness : ConvWitness} {left right : Preterm} {sort : Nat}
    (checked : Checks signature definitions context witness left right sort) :
    conversion? signature definitions context witness = some ⟨left, right, sort⟩ := by
  induction checked using Checks.rec
      (motive_2 := fun children left right binders _ =>
        arguments? signature definitions context children binders = some (left, right)) with
  | refl typed => simp [conversion?, typed.eval]
  | symm _ ih => simp [conversion?, ih]
  | trans _ _ ihFirst ihSecond => simp [conversion?, ihFirst, ihSecond]
  | congruence lookup _ ih => simp [conversion?, lookup, ih]
  | unfold lookup unfolded typed =>
      simp [conversion?, lookup, (Definition.unfold_eq_some_iff _ _ _ _ _ _ _).mpr unfolded, typed.eval]
  | nil => simp [arguments?]
  | cons leftFits rightFits _ _ ihChild ihTail =>
      simp [arguments?, ihChild, ihTail,
        (checkBinder_iff _ _ _ _).mpr leftFits, (checkBinder_iff _ _ _ _).mpr rightFits]

theorem ChecksArgs.eval {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {children : List ConvWitness} {left right : List Preterm} {binders : Context}
    (checked : ChecksArgs signature definitions context children left right binders) :
    arguments? signature definitions context children binders = some (left, right) := by
  induction checked using ChecksArgs.rec
      (motive_1 := fun witness left right sort _ =>
        conversion? signature definitions context witness = some ⟨left, right, sort⟩) with
  | refl typed => simp [conversion?, typed.eval]
  | symm _ ih => simp [conversion?, ih]
  | trans _ _ ihFirst ihSecond => simp [conversion?, ihFirst, ihSecond]
  | congruence lookup _ ih => simp [conversion?, lookup, ih]
  | unfold lookup unfolded typed =>
      simp [conversion?, lookup, (Definition.unfold_eq_some_iff _ _ _ _ _ _ _).mpr unfolded, typed.eval]
  | nil => simp [arguments?]
  | cons leftFits rightFits _ _ ihChild ihTail =>
      simp [arguments?, ihChild, ihTail,
        (checkBinder_iff _ _ _ _).mpr leftFits, (checkBinder_iff _ _ _ _).mpr rightFits]

mutual

theorem conversion_sound {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {witness : ConvWitness} {result : ConversionResult}
    (accepted : conversion? signature definitions context witness = some result) :
    Checks signature definitions context witness result.left result.right result.sort := by
  cases witness with
  | refl expression =>
      cases inferred : infer signature context expression with
      | none => simp [conversion?, inferred] at accepted
      | some type =>
          rcases type with ⟨remaining, sort⟩
          by_cases saturated : remaining = []
          · subst remaining
            have same : (⟨expression, expression, sort⟩ : ConversionResult) = result := by
              simpa [conversion?, inferred] using accepted
            subst result
            exact .refl (infer_sound inferred)
          · simp [conversion?, inferred, saturated] at accepted
  | symm child =>
      cases childResult : conversion? signature definitions context child with
      | none => simp [conversion?, childResult] at accepted
      | some value =>
          have same : (⟨value.right, value.left, value.sort⟩ : ConversionResult) = result := by
            simpa [conversion?, childResult] using accepted
          subst result
          exact .symm (conversion_sound childResult)
  | trans first second =>
      cases firstResult : conversion? signature definitions context first with
      | none => simp [conversion?, firstResult] at accepted
      | some firstValue =>
          cases secondResult : conversion? signature definitions context second with
          | none => simp [conversion?, firstResult, secondResult] at accepted
          | some secondValue =>
              by_cases matching : firstValue.right = secondValue.left ∧
                  firstValue.sort = secondValue.sort
              · have same : (⟨firstValue.left, secondValue.right, firstValue.sort⟩ : ConversionResult) =
                    result := by simpa [conversion?, firstResult, secondResult, matching] using accepted
                subst result
                have firstChecked := conversion_sound firstResult
                have secondChecked := conversion_sound secondResult
                rw [← matching.1, ← matching.2] at secondChecked
                exact .trans (middle := firstValue.right) firstChecked secondChecked
              · simp [conversion?, firstResult, secondResult, matching] at accepted
  | congruence symbol children =>
      cases lookup : signature symbol with
      | none => simp [conversion?, lookup] at accepted
      | some declaration =>
          cases childrenResult : arguments? signature definitions context children declaration.arguments with
          | none => simp [conversion?, lookup, childrenResult] at accepted
          | some value =>
              rcases value with ⟨left, right⟩
              have same : (⟨applyArgs (.term symbol) left, applyArgs (.term symbol) right,
                  declaration.resultSort⟩ : ConversionResult) = result := by
                simpa [conversion?, lookup, childrenResult] using accepted
              subst result
              exact .congruence lookup (arguments_sound childrenResult)
  | unfold symbol arguments images =>
      cases lookup : signature symbol with
      | none => simp [conversion?, lookup] at accepted
      | some declaration =>
          cases unfolded : Definition.unfold? signature definitions context symbol arguments images with
          | none => simp [conversion?, lookup, unfolded] at accepted
          | some expression =>
              by_cases typed : infer signature context expression = some ([], declaration.resultSort)
              · have same : (⟨applyArgs (.term symbol) arguments, expression,
                    declaration.resultSort⟩ : ConversionResult) = result := by
                  simpa [conversion?, lookup, unfolded, typed] using accepted
                subst result
                exact .unfold lookup ((Definition.unfold_eq_some_iff _ _ _ _ _ _ _).mp unfolded)
                  (infer_sound typed)
              · simp [conversion?, lookup, unfolded, typed] at accepted
termination_by structural witness

theorem arguments_sound {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {children : List ConvWitness} {binders : Context} {left right : List Preterm}
    (accepted : arguments? signature definitions context children binders = some (left, right)) :
    ChecksArgs signature definitions context children left right binders := by
  cases children with
  | nil =>
      cases binders with
      | nil =>
          have same : ([], []) = (left, right) := by simpa [arguments?] using accepted
          rcases Prod.mk.inj same with ⟨rfl, rfl⟩
          exact .nil
      | cons => simp [arguments?] at accepted
  | cons child children =>
      cases binders with
      | nil => simp [arguments?] at accepted
      | cons binder binders =>
          cases head : conversion? signature definitions context child with
          | none => simp [arguments?, head] at accepted
          | some value =>
              by_cases fits : value.sort = binder.sort ∧
                  checkBinder signature context value.left binder = true ∧
                  checkBinder signature context value.right binder = true
              · cases tail : arguments? signature definitions context children binders with
                | none => simp [arguments?, head, tail] at accepted
                | some valueTail =>
                    rcases valueTail with ⟨lefts, rights⟩
                    have same : (value.left :: lefts, value.right :: rights) = (left, right) := by
                      simpa [arguments?, head, fits, tail] using accepted
                    rcases Prod.mk.inj same with ⟨rfl, rfl⟩
                    have childChecked := conversion_sound head
                    rw [fits.1] at childChecked
                    exact .cons ((checkBinder_iff _ _ _ _).mp fits.2.1)
                      ((checkBinder_iff _ _ _ _).mp fits.2.2) childChecked (arguments_sound tail)
              · simp [arguments?, head, fits] at accepted
termination_by structural children

end

theorem conversion_eq_some_iff (signature : TermSignature) (definitions : Definition.Signature)
    (context : Context) (witness : ConvWitness) (left right : Preterm) (sort : Nat) :
    conversion? signature definitions context witness = some ⟨left, right, sort⟩ ↔
      Checks signature definitions context witness left right sort :=
  ⟨conversion_sound, Checks.eval⟩

theorem arguments_eq_some_iff (signature : TermSignature) (definitions : Definition.Signature)
    (context : Context) (children : List ConvWitness) (left right : List Preterm) (binders : Context) :
    arguments? signature definitions context children binders = some (left, right) ↔
      ChecksArgs signature definitions context children left right binders :=
  ⟨arguments_sound, ChecksArgs.eval⟩

theorem Checks.derives {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {witness : ConvWitness} {left right : Preterm} {sort : Nat}
    (checked : Checks signature definitions context witness left right sort) :
    Converts signature definitions context left right sort := by
  induction checked using Checks.rec
      (motive_2 := fun _ left right binders _ =>
        ConvertsArgs signature definitions context left right binders) with
  | refl typed => exact .refl typed
  | symm _ ih => exact .symm ih
  | trans _ _ ihFirst ihSecond => exact .trans ihFirst ihSecond
  | congruence lookup _ ih => exact .congruence lookup ih
  | unfold lookup unfolded typed => exact .unfold lookup unfolded typed
  | nil => exact .nil
  | cons leftFits rightFits _ _ ihChild ihTail => exact .cons leftFits rightFits ihChild ihTail

theorem ChecksArgs.derives {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {children : List ConvWitness} {left right : List Preterm} {binders : Context}
    (checked : ChecksArgs signature definitions context children left right binders) :
    ConvertsArgs signature definitions context left right binders := by
  induction checked using ChecksArgs.rec
      (motive_1 := fun _ left right sort _ => Converts signature definitions context left right sort) with
  | refl typed => exact .refl typed
  | symm _ ih => exact .symm ih
  | trans _ _ ihFirst ihSecond => exact .trans ihFirst ihSecond
  | congruence lookup _ ih => exact .congruence lookup ih
  | unfold lookup unfolded typed => exact .unfold lookup unfolded typed
  | nil => exact .nil
  | cons leftFits rightFits _ _ ihChild ihTail => exact .cons leftFits rightFits ihChild ihTail

def check (signature : TermSignature) (definitions : Definition.Signature) (context : Context)
    (witness : ConvWitness) (left right : Preterm) (sort : Nat) : Bool :=
  decide (conversion? signature definitions context witness = some ⟨left, right, sort⟩)

theorem check_iff (signature : TermSignature) (definitions : Definition.Signature) (context : Context)
    (witness : ConvWitness) (left right : Preterm) (sort : Nat) :
    check signature definitions context witness left right sort = true ↔
      Checks signature definitions context witness left right sort := by
  simp only [check, decide_eq_true_eq, conversion_eq_some_iff]

theorem conversion_none_iff (signature : TermSignature) (definitions : Definition.Signature)
    (context : Context) (witness : ConvWitness) :
    conversion? signature definitions context witness = none ↔
      ¬ ∃ left right sort, Checks signature definitions context witness left right sort := by
  constructor
  · intro refused ⟨left, right, sort, checked⟩
    have success := checked.eval
    rw [refused] at success
    contradiction
  · intro impossible
    cases result : conversion? signature definitions context witness with
    | none => rfl
    | some value => exact False.elim (impossible ⟨_, _, _, conversion_sound result⟩)

theorem check_sound {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {witness : ConvWitness} {left right : Preterm} {sort : Nat}
    (accepted : check signature definitions context witness left right sort = true) :
    Converts signature definitions context left right sort :=
  ((check_iff _ _ _ _ _ _ _).mp accepted).derives

end ConvWitness

theorem Converts.certificate_exists {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {left right : Preterm} {sort : Nat}
    (conversion : Converts signature definitions context left right sort) :
    ∃ witness, ConvWitness.Checks signature definitions context witness left right sort := by
  induction conversion using Converts.rec
      (motive_2 := fun left right binders _ =>
        ∃ children, ConvWitness.ChecksArgs signature definitions context children left right binders) with
  | refl typed => exact ⟨.refl _, .refl typed⟩
  | symm _ ih =>
      obtain ⟨witness, checked⟩ := ih
      exact ⟨.symm witness, .symm checked⟩
  | trans _ _ ihFirst ihSecond =>
      obtain ⟨firstWitness, firstChecked⟩ := ihFirst
      obtain ⟨secondWitness, secondChecked⟩ := ihSecond
      exact ⟨.trans firstWitness secondWitness, .trans firstChecked secondChecked⟩
  | congruence lookup _ ih =>
      obtain ⟨witnesses, checked⟩ := ih
      exact ⟨.congruence _ witnesses, .congruence lookup checked⟩
  | unfold lookup unfolded typed => exact ⟨.unfold _ _ _, .unfold lookup unfolded typed⟩
  | nil => exact ⟨[], .nil⟩
  | cons leftFits rightFits _ _ ihChild ihTail =>
      obtain ⟨witness, checked⟩ := ihChild
      obtain ⟨witnesses, children⟩ := ihTail
      exact ⟨witness :: witnesses, .cons leftFits rightFits checked children⟩

theorem ConvertsArgs.certificate_exists {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {left right : List Preterm} {binders : Context}
    (conversion : ConvertsArgs signature definitions context left right binders) :
    ∃ children, ConvWitness.ChecksArgs signature definitions context children left right binders := by
  induction conversion using ConvertsArgs.rec
      (motive_1 := fun left right sort _ =>
        ∃ witness, ConvWitness.Checks signature definitions context witness left right sort) with
  | refl typed => exact ⟨.refl _, .refl typed⟩
  | symm _ ih =>
      obtain ⟨witness, checked⟩ := ih
      exact ⟨.symm witness, .symm checked⟩
  | trans _ _ ihFirst ihSecond =>
      obtain ⟨firstWitness, firstChecked⟩ := ihFirst
      obtain ⟨secondWitness, secondChecked⟩ := ihSecond
      exact ⟨.trans firstWitness secondWitness, .trans firstChecked secondChecked⟩
  | congruence lookup _ ih =>
      obtain ⟨witnesses, checked⟩ := ih
      exact ⟨.congruence _ witnesses, .congruence lookup checked⟩
  | unfold lookup unfolded typed => exact ⟨.unfold _ _ _, .unfold lookup unfolded typed⟩
  | nil => exact ⟨[], .nil⟩
  | cons leftFits rightFits _ _ ihChild ihTail =>
      obtain ⟨witness, checked⟩ := ihChild
      obtain ⟨witnesses, children⟩ := ihTail
      exact ⟨witness :: witnesses, .cons leftFits rightFits checked children⟩

theorem converts_iff_checked (signature : TermSignature) (definitions : Definition.Signature)
    (context : Context) (left right : Preterm) (sort : Nat) :
    Converts signature definitions context left right sort ↔
      ∃ witness, ConvWitness.check signature definitions context witness left right sort = true := by
  constructor
  · intro conversion
    obtain ⟨witness, checked⟩ := conversion.certificate_exists
    exact ⟨witness, (ConvWitness.check_iff _ _ _ _ _ _ _).mpr checked⟩
  · rintro ⟨witness, accepted⟩
    exact ConvWitness.check_sound accepted

/-- Conversion changes neither endpoint's sort and never accepts an unsaturated side. -/
theorem Converts.typed {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {left right : Preterm} {sort : Nat}
    (conversion : Converts signature definitions context left right sort) :
    HasType signature context left [] sort ∧ HasType signature context right [] sort := by
  induction conversion using Converts.rec
      (motive_2 := fun left right binders _ =>
        List.Forall₂ (FitsBinder signature context) left binders ∧
          List.Forall₂ (FitsBinder signature context) right binders) with
  | refl typed => exact ⟨typed, typed⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ihFirst ihSecond => exact ⟨ihFirst.1, ihSecond.2⟩
  | congruence lookup _ ih =>
      exact ⟨(HasType.term lookup).applyArgs ih.1, (HasType.term lookup).applyArgs ih.2⟩
  | unfold lookup unfolded typed =>
      cases unfolded with
      | intro knownTerm _ argumentsTyped _ _ =>
          have same := Option.some.inj (lookup.symm.trans knownTerm)
          subst same
          exact ⟨(HasType.term lookup).applyArgs argumentsTyped, typed⟩
  | nil => exact ⟨.nil, .nil⟩
  | cons leftFits rightFits _ _ _ ih => exact ⟨.cons leftFits ih.1, .cons rightFits ih.2⟩

theorem ConvWitness.Checks.typed {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {witness : ConvWitness} {left right : Preterm} {sort : Nat}
    (checked : ConvWitness.Checks signature definitions context witness left right sort) :
    HasType signature context left [] sort ∧ HasType signature context right [] sort :=
  checked.derives.typed

theorem ConvWitness.Checks.deterministic {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {witness : ConvWitness} {left right otherLeft otherRight : Preterm}
    {sort otherSort : Nat}
    (first : ConvWitness.Checks signature definitions context witness left right sort)
    (second : ConvWitness.Checks signature definitions context witness otherLeft otherRight otherSort) :
    left = otherLeft ∧ right = otherRight ∧ sort = otherSort := by
  have same := Option.some.inj (first.eval.symm.trans second.eval)
  exact ConversionResult.mk.inj same

end Mettapedia.Languages.MM0.Kernel
