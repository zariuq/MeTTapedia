import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-!
# Goal-directed replay of raw certificates

A raw NIK certificate is a finite tree of rule instances.  It records no
conclusions: replay computes each node's ordered premises and its conclusion
from the rule instance alone, compares that conclusion with the requested
goal, and continues into the children against the computed premises.

This module isolates that replay discipline from the representation of
judgments.  A `ReplaySignature` supplies only a type of goals with decidable
equality and the local rule-application map.

* `replay` is structural recursion over the certificate.
* `Deriv` is the proof-relevant family of trees that replay accepts, and
  `Deriv.erase` forgets everything except the rule instances.
* `replay_iff` is the exact correspondence: a certificate is accepted for a
  goal exactly when it is the erasure of a derivation of that goal.
* Accepted certificates determine their goal (`replay_goal_unique`) and their
  derivation (`Deriv.eq_of_erase_eq`).
* Every derivation is sound in every interpretation closed under the local
  rule map (`Deriv.sound`).

None of these uses `Classical.choice`.  The generic inference checker is the
instance whose goals are patterns and whose local map is rule instantiation
in a validated calculus (`nikSignature`): `checkRaw_eq_replay` identifies the
two checkers and `derivationEquiv` identifies the two derivation families.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BootstrapCell

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

universe u

/-- Goals with decidable equality, and the local rule-application map that
reads a rule instance as its ordered premises and its conclusion. -/
structure ReplaySignature where
  Goal : Type u
  decEq : DecidableEq Goal
  step : RuleInstance → Option (List Goal × Goal)

attribute [instance] ReplaySignature.decEq

namespace ReplaySignature

variable (σ : ReplaySignature.{u})

mutual

/-- Goal-directed replay of one raw certificate. -/
def replay : σ.Goal → RawProof → Bool
  | goal, .node label children =>
      match σ.step label with
      | none => false
      | some (premises, conclusion) =>
          decide (conclusion = goal) && replayAll premises children
termination_by structural _ certificate => certificate

/-- Replay of ordered children against ordered premises; a length mismatch
rejects. -/
def replayAll : List σ.Goal → List RawProof → Bool
  | [], [] => true
  | goal :: goals, child :: children => replay goal child && replayAll goals children
  | _, _ => false
termination_by structural _ children => children

end

@[simp] theorem replay_node (goal : σ.Goal) (label : RuleInstance)
    (children : List RawProof) :
    σ.replay goal (.node label children) =
      match σ.step label with
      | none => false
      | some (premises, conclusion) =>
          decide (conclusion = goal) && σ.replayAll premises children := rfl

@[simp] theorem replayAll_nil_nil : σ.replayAll [] [] = true := rfl

@[simp] theorem replayAll_cons_cons (goal : σ.Goal) (goals : List σ.Goal)
    (child : RawProof) (children : List RawProof) :
    σ.replayAll (goal :: goals) (child :: children) =
      (σ.replay goal child && σ.replayAll goals children) := rfl

@[simp] theorem replayAll_nil_cons (child : RawProof) (children : List RawProof) :
    σ.replayAll [] (child :: children) = false := rfl

@[simp] theorem replayAll_cons_nil (goal : σ.Goal) (goals : List σ.Goal) :
    σ.replayAll (goal :: goals) [] = false := rfl

mutual

/-- Derivations accepted by replay: each node is a rule instance whose local
map returns its conclusion and the premises of its ordered children. -/
inductive Deriv (σ : ReplaySignature.{u}) : σ.Goal → Type u where
  | byStep (label : RuleInstance) {premises : List σ.Goal} {conclusion : σ.Goal}
      (step : σ.step label = some (premises, conclusion))
      (children : DerivList σ premises) : Deriv σ conclusion

/-- Ordered derivations of an ordered premise list. -/
inductive DerivList (σ : ReplaySignature.{u}) : List σ.Goal → Type u where
  | nil : DerivList σ []
  | cons {goal : σ.Goal} {goals : List σ.Goal}
      (head : Deriv σ goal) (tail : DerivList σ goals) :
      DerivList σ (goal :: goals)

end

variable {σ}

mutual

/-- Forget a derivation down to its raw certificate. -/
def Deriv.erase {goal : σ.Goal} : Deriv σ goal → RawProof
  | .byStep label _ children => .node label children.erase

/-- Pointwise erasure of ordered children. -/
def DerivList.erase {goals : List σ.Goal} : DerivList σ goals → List RawProof
  | .nil => []
  | .cons head tail => head.erase :: tail.erase

end

@[simp] theorem Deriv.erase_byStep (label : RuleInstance) {premises : List σ.Goal}
    {conclusion : σ.Goal} (step : σ.step label = some (premises, conclusion))
    (children : DerivList σ premises) :
    (Deriv.byStep label step children).erase = .node label children.erase := by
  rw [Deriv.erase]

@[simp] theorem DerivList.erase_nil : (DerivList.nil : DerivList σ []).erase = [] := by
  rw [DerivList.erase]

@[simp] theorem DerivList.erase_cons {goal : σ.Goal} {goals : List σ.Goal}
    (head : Deriv σ goal) (tail : DerivList σ goals) :
    (DerivList.cons head tail).erase = head.erase :: tail.erase := by
  rw [DerivList.erase]

/-! ## Replay is exact for derivations -/

mutual

/-- Every derivation's erasure replays against its goal. -/
theorem Deriv.replay_erase : {goal : σ.Goal} → (derivation : Deriv σ goal) →
    σ.replay goal derivation.erase = true
  | _, .byStep label step children => by
      rw [Deriv.erase_byStep, replay_node, step]
      simp only [decide_true, Bool.true_and]
      exact DerivList.replayAll_erase children

/-- Every derivation list's erasure replays against its premises. -/
theorem DerivList.replayAll_erase : {goals : List σ.Goal} →
    (derivations : DerivList σ goals) → σ.replayAll goals derivations.erase = true
  | _, .nil => by rw [DerivList.erase_nil, replayAll_nil_nil]
  | _, .cons head tail => by
      rw [DerivList.erase_cons, replayAll_cons_cons, Deriv.replay_erase head,
        DerivList.replayAll_erase tail]
      rfl

end

mutual

/-- An accepted certificate is the erasure of a derivation of its goal. -/
theorem exists_deriv_of_replay : (goal : σ.Goal) → (certificate : RawProof) →
    σ.replay goal certificate = true →
      ∃ derivation : Deriv σ goal, derivation.erase = certificate
  | goal, .node label children, accepted => by
      rw [replay_node] at accepted
      cases stepEq : σ.step label with
      | none => rw [stepEq] at accepted; exact absurd accepted Bool.false_ne_true
      | some result =>
          obtain ⟨premises, conclusion⟩ := result
          rw [stepEq] at accepted
          simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
          obtain ⟨rfl, childrenAccepted⟩ := accepted
          obtain ⟨derivations, erased⟩ :=
            exists_derivList_of_replayAll premises children childrenAccepted
          exact ⟨.byStep label stepEq derivations, by
            rw [Deriv.erase_byStep, erased]⟩

/-- Accepted ordered children are the erasure of ordered derivations. -/
theorem exists_derivList_of_replayAll : (goals : List σ.Goal) →
    (children : List RawProof) → σ.replayAll goals children = true →
      ∃ derivations : DerivList σ goals, derivations.erase = children
  | [], [], _ => ⟨.nil, by rw [DerivList.erase_nil]⟩
  | [], _ :: _, accepted => by
      rw [replayAll_nil_cons] at accepted; exact absurd accepted Bool.false_ne_true
  | _ :: _, [], accepted => by
      rw [replayAll_cons_nil] at accepted; exact absurd accepted Bool.false_ne_true
  | goal :: goals, child :: children, accepted => by
      rw [replayAll_cons_cons, Bool.and_eq_true] at accepted
      obtain ⟨head, headErased⟩ := exists_deriv_of_replay goal child accepted.1
      obtain ⟨tail, tailErased⟩ :=
        exists_derivList_of_replayAll goals children accepted.2
      exact ⟨.cons head tail, by rw [DerivList.erase_cons, headErased, tailErased]⟩

end

/-- **Exact replay.**  A raw certificate is accepted for a goal exactly when
it is the erasure of a derivation of that goal. -/
theorem replay_iff (goal : σ.Goal) (certificate : RawProof) :
    σ.replay goal certificate = true ↔
      ∃ derivation : Deriv σ goal, derivation.erase = certificate := by
  constructor
  · exact exists_deriv_of_replay goal certificate
  · rintro ⟨derivation, rfl⟩
    exact derivation.replay_erase

/-- An accepted certificate determines its goal. -/
theorem replay_goal_unique {first second : σ.Goal} {certificate : RawProof}
    (firstAccepted : σ.replay first certificate = true)
    (secondAccepted : σ.replay second certificate = true) : first = second := by
  cases certificate with
  | node label children =>
      rw [replay_node] at firstAccepted secondAccepted
      cases stepEq : σ.step label with
      | none =>
          rw [stepEq] at firstAccepted
          exact absurd firstAccepted Bool.false_ne_true
      | some result =>
          obtain ⟨premises, conclusion⟩ := result
          rw [stepEq] at firstAccepted secondAccepted
          simp only [Bool.and_eq_true, decide_eq_true_eq] at firstAccepted secondAccepted
          exact firstAccepted.1.symm.trans secondAccepted.1

mutual

/-- A derivation is determined by its erasure: replay is proof-irrelevant
once the certificate is fixed. -/
theorem Deriv.eq_of_erase_eq : {goal : σ.Goal} → (first second : Deriv σ goal) →
    first.erase = second.erase → first = second
  | _, .byStep label step children, .byStep label' step' children', erased => by
      rw [Deriv.erase_byStep, Deriv.erase_byStep] at erased
      injection erased with labelEq childrenErased
      subst labelEq
      rw [step] at step'
      injection step' with pairEq
      injection pairEq with premisesEq _conclusionEq
      subst premisesEq
      rw [DerivList.eq_of_erase_eq children children' childrenErased]

/-- Ordered derivation lists are determined by their erasure. -/
theorem DerivList.eq_of_erase_eq : {goals : List σ.Goal} →
    (first second : DerivList σ goals) → first.erase = second.erase → first = second
  | _, .nil, .nil, _ => rfl
  | _, .cons head tail, .cons head' tail', erased => by
      rw [DerivList.erase_cons, DerivList.erase_cons] at erased
      injection erased with headErased tailErased
      rw [Deriv.eq_of_erase_eq head head' headErased,
        DerivList.eq_of_erase_eq tail tail' tailErased]

end

/-- The derivations with a fixed erasure form a subsingleton. -/
instance (goal : σ.Goal) (certificate : RawProof) :
    Subsingleton { derivation : Deriv σ goal // derivation.erase = certificate } :=
  ⟨fun first second =>
    Subtype.ext (Deriv.eq_of_erase_eq first.1 second.1 (first.2.trans second.2.symm))⟩

/-! ## Soundness in every interpretation closed under the local rule map -/

mutual

/-- Any predicate closed under every local rule application holds of every
derived goal. -/
theorem Deriv.sound (meaning : σ.Goal → Prop)
    (closed : ∀ label premises conclusion, σ.step label = some (premises, conclusion) →
      (∀ premise ∈ premises, meaning premise) → meaning conclusion) :
    {goal : σ.Goal} → Deriv σ goal → meaning goal
  | _, .byStep label step children =>
      closed label _ _ step (DerivList.sound meaning closed children)

/-- Pointwise soundness for ordered derivation lists. -/
theorem DerivList.sound (meaning : σ.Goal → Prop)
    (closed : ∀ label premises conclusion, σ.step label = some (premises, conclusion) →
      (∀ premise ∈ premises, meaning premise) → meaning conclusion) :
    {goals : List σ.Goal} → DerivList σ goals → ∀ premise ∈ goals, meaning premise
  | _, .nil => fun _ member => nomatch member
  | _, .cons head tail => fun _ member =>
      match member with
      | .head _ => Deriv.sound meaning closed head
      | .tail _ member => DerivList.sound meaning closed tail _ member

end

/-- Accepted certificates prove goals true in every interpretation closed
under the local rule map. -/
theorem replay_sound (meaning : σ.Goal → Prop)
    (closed : ∀ label premises conclusion, σ.step label = some (premises, conclusion) →
      (∀ premise ∈ premises, meaning premise) → meaning conclusion)
    {goal : σ.Goal} {certificate : RawProof}
    (accepted : σ.replay goal certificate = true) : meaning goal :=
  let ⟨derivation, _⟩ := exists_deriv_of_replay goal certificate accepted
  Deriv.sound meaning closed derivation

end ReplaySignature

/-! ## The generic inference checker as a replay signature -/

/-- Replay for a validated calculus: goals are patterns and the local map is
rule instantiation. -/
abbrev nikSignature (definition : ValidatedCalculusLanguageDef) : ReplaySignature.{0} where
  Goal := Pattern
  decEq := inferInstance
  step := instantiateRule? definition

@[simp] theorem nikSignature_step (definition : ValidatedCalculusLanguageDef) :
    (nikSignature definition).step = instantiateRule? definition := rfl

mutual

/-- The generic inference checker is replay in the calculus's signature. -/
theorem checkRaw_eq_replay (definition : ValidatedCalculusLanguageDef) :
    (goal : Pattern) → (certificate : RawProof) →
      checkRaw definition goal certificate =
        (nikSignature definition).replay goal certificate
  | goal, .node label children => by
      rw [ReplaySignature.replay_node, checkRaw, nikSignature_step]
      cases instantiateRule? definition label with
      | none => rfl
      | some result =>
          obtain ⟨premises, conclusion⟩ := result
          simp only
          rw [checkRawChildren_eq_replayAll definition premises children]

/-- The same identification for ordered children. -/
theorem checkRawChildren_eq_replayAll (definition : ValidatedCalculusLanguageDef) :
    (goals : List Pattern) → (children : List RawProof) →
      checkRawChildren definition goals children =
        (nikSignature definition).replayAll goals children
  | [], [] => by rw [checkRawChildren, ReplaySignature.replayAll_nil_nil]
  | [], _ :: _ => by rw [ReplaySignature.replayAll_nil_cons]; simp [checkRawChildren]
  | _ :: _, [] => by rw [ReplaySignature.replayAll_cons_nil]; simp [checkRawChildren]
  | goal :: goals, child :: children => by
      rw [checkRawChildren, ReplaySignature.replayAll_cons_cons,
        checkRaw_eq_replay definition goal child,
        checkRawChildren_eq_replayAll definition goals children]

end

mutual

/-- Read a derivation of the generic checker as a replay derivation. -/
def toDeriv {definition : ValidatedCalculusLanguageDef} :
    {goal : Pattern} → Derivation definition goal →
      (nikSignature definition).Deriv goal
  | _, .byRule label application children =>
      .byStep label (instantiateRule?_eq_some_iff_application.mpr application)
        (toDerivList children)

/-- Pointwise reading for ordered children. -/
def toDerivList {definition : ValidatedCalculusLanguageDef} :
    {goals : List Pattern} → DerivationList definition goals →
      (nikSignature definition).DerivList goals
  | _, .nil => .nil
  | _, .cons head tail => .cons (toDeriv head) (toDerivList tail)

end

mutual

/-- Read a replay derivation as a derivation of the generic checker. -/
def ofDeriv {definition : ValidatedCalculusLanguageDef} :
    {goal : Pattern} → (nikSignature definition).Deriv goal →
      Derivation definition goal
  | _, .byStep label step children =>
      .byRule label (instantiateRule?_eq_some_iff_application.mp step)
        (ofDerivList children)

/-- Pointwise reading for ordered children. -/
def ofDerivList {definition : ValidatedCalculusLanguageDef} :
    {goals : List Pattern} → (nikSignature definition).DerivList goals →
      DerivationList definition goals
  | _, .nil => .nil
  | _, .cons head tail => .cons (ofDeriv head) (ofDerivList tail)

end

mutual

theorem ofDeriv_toDeriv {definition : ValidatedCalculusLanguageDef} :
    {goal : Pattern} → (derivation : Derivation definition goal) →
      ofDeriv (toDeriv derivation) = derivation
  | _, .byRule label application children => by
      rw [toDeriv, ofDeriv, ofDerivList_toDerivList children]

theorem ofDerivList_toDerivList {definition : ValidatedCalculusLanguageDef} :
    {goals : List Pattern} → (derivations : DerivationList definition goals) →
      ofDerivList (toDerivList derivations) = derivations
  | _, .nil => by rw [toDerivList, ofDerivList]
  | _, .cons head tail => by
      rw [toDerivList, ofDerivList, ofDeriv_toDeriv head, ofDerivList_toDerivList tail]

end

mutual

theorem toDeriv_ofDeriv {definition : ValidatedCalculusLanguageDef} :
    {goal : Pattern} → (derivation : (nikSignature definition).Deriv goal) →
      toDeriv (ofDeriv derivation) = derivation
  | _, .byStep label step children => by
      rw [ofDeriv, toDeriv, toDerivList_ofDerivList children]

theorem toDerivList_ofDerivList {definition : ValidatedCalculusLanguageDef} :
    {goals : List Pattern} → (derivations : (nikSignature definition).DerivList goals) →
      toDerivList (ofDerivList derivations) = derivations
  | _, .nil => by rw [ofDerivList, toDerivList]
  | _, .cons head tail => by
      rw [ofDerivList, toDerivList, toDeriv_ofDeriv head, toDerivList_ofDerivList tail]

end

/-- The derivations of the generic checker and the replay derivations of its
signature are the same family. -/
def derivationEquiv (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    Derivation definition goal ≃ (nikSignature definition).Deriv goal where
  toFun := toDeriv
  invFun := ofDeriv
  left_inv := ofDeriv_toDeriv
  right_inv := toDeriv_ofDeriv

mutual

/-- The identification preserves raw certificates exactly. -/
theorem toDeriv_erase {definition : ValidatedCalculusLanguageDef} :
    {goal : Pattern} → (derivation : Derivation definition goal) →
      (toDeriv derivation).erase = derivation.erase
  | _, .byRule label application children => by
      rw [toDeriv, ReplaySignature.Deriv.erase_byStep, Derivation.erase,
        toDerivList_erase children]

theorem toDerivList_erase {definition : ValidatedCalculusLanguageDef} :
    {goals : List Pattern} → (derivations : DerivationList definition goals) →
      (toDerivList derivations).erase = derivations.erase
  | _, .nil => by rw [toDerivList, ReplaySignature.DerivList.erase_nil, DerivationList.erase]
  | _, .cons head tail => by
      rw [toDerivList, ReplaySignature.DerivList.erase_cons, DerivationList.erase,
        toDeriv_erase head, toDerivList_erase tail]

end

end Mettapedia.GSLT.LanguageDef.BootstrapCell
