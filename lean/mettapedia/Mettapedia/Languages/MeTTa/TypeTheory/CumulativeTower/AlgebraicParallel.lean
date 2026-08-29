import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AlgebraicSchema

/-!
# Algebraic parallel reduction over open rewrite schemas

An algebraic root equation is represented by an open left/right pair.  A
parallel occurrence substitutes one source/target pair for each open
variable.  Repeated occurrences of a variable therefore share one target;
this is the coherence needed by rules such as dependent eliminator iota,
where a parameter occurs both in the family and in its constructor.

This module is independent of any particular datatype or universe tower.
It supplies the reusable parallel relation and its binding laws.  A concrete
presentation must still prove that its root computation is exactly covered
by selected schemas and that its schemas have a complete development (or an
equivalent diamond proof).
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace AlgebraicParallel

open ConversionCoherence
open AlgebraicSchema

variable {Head : Type}
variable (headEq : Head → Head → Prop) (schema : SchemaFamily Head)

mutual

/-- Parallel beta/sigma/head/algebraic reduction.  The algebraic constructor
uses one coherent target substitution for the whole right-hand side. -/
inductive ParRed :
    {n : Nat} → Tm Head n → Tm Head n → Prop where
  | var (index : Fin n) : ParRed (.var index) (.var index)
  | const (name : DeclName) :
      ParRed (.const name : Tm Head n) (.const name)
  | head (value : Head) :
      ParRed (.head value : Tm Head n) (.head value)
  | headRel {left right : Head} :
      headEq left right →
        ParRed (.head left : Tm Head n) (.head right)
  | pi {domain domain' : Tm Head n}
      {codomain codomain' : Tm Head (n + 1)} :
      ParRed domain domain' →
      ParRed codomain codomain' →
        ParRed (.pi domain codomain)
          (.pi domain' codomain')
  | sigma {domain domain' : Tm Head n}
      {codomain codomain' : Tm Head (n + 1)} :
      ParRed domain domain' →
      ParRed codomain codomain' →
        ParRed (.sigma domain codomain)
          (.sigma domain' codomain')
  | id {type type' left left' right right' : Tm Head n} :
      ParRed type type' →
      ParRed left left' →
      ParRed right right' →
        ParRed (.id type left right)
          (.id type' left' right')
  | lam {body body' : Tm Head (n + 1)} :
      ParRed body body' →
        ParRed (.lam body) (.lam body')
  | app {function function' argument argument' : Tm Head n} :
      ParRed function function' →
      ParRed argument argument' →
        ParRed (.app function argument)
          (.app function' argument')
  | pair {first first' second second' : Tm Head n} :
      ParRed first first' →
      ParRed second second' →
        ParRed (.pair first second)
          (.pair first' second')
  | fst {pair pair' : Tm Head n} :
      ParRed pair pair' →
        ParRed (.fst pair) (.fst pair')
  | snd {pair pair' : Tm Head n} :
      ParRed pair pair' →
        ParRed (.snd pair) (.snd pair')
  | refl {term term' : Tm Head n} :
      ParRed term term' →
        ParRed (.refl term) (.refl term')
  | betaPi {body body' : Tm Head (n + 1)}
      {argument argument' : Tm Head n} :
      ParRed body body' →
      ParRed argument argument' →
        ParRed (.app (.lam body) argument)
          (inst0 argument' body')
  | betaSigmaFst {first first' second second' : Tm Head n} :
      ParRed first first' →
      ParRed second second' →
        ParRed (.fst (.pair first second)) first'
  | betaSigmaSnd {first first' second second' : Tm Head n} :
      ParRed first first' →
      ParRed second second' →
        ParRed (.snd (.pair first second)) second'
  | algebraic {arity n : Nat} {left right : Tm Head arity}
      (rule : schema left right)
      (source target : Sub Head arity n)
      (arguments : ParSub source target) :
      ParRed (subst source left) (subst target right)

/-- A proof-relevant parallel substitution telescope.  Unlike a bare
pointwise proposition, this is an inductive spine and therefore exposes the
arity and each metavariable development structurally. -/
inductive ParSub :
    {arity ambient : Nat} →
      Sub Head arity ambient → Sub Head arity ambient → Prop where
  | nil {ambient : Nat} :
      ParSub
        (fun index : Fin 0 => (Fin.elim0 index : Tm Head ambient))
        (fun index : Fin 0 => (Fin.elim0 index : Tm Head ambient))
  | cons {arity ambient : Nat}
      {sourceHead targetHead : Tm Head ambient}
      {sourceTail targetTail : Sub Head arity ambient} :
      ParRed sourceHead targetHead →
      ParSub sourceTail targetTail →
      ParSub
        (Fin.cases sourceHead sourceTail)
        (Fin.cases targetHead targetTail)

end

/-- Parallel reduction includes the identity development of every term. -/
theorem par_refl
    {headEq : Head → Head → Prop} {schema : SchemaFamily Head} :
    ∀ {n : Nat} (term : Tm Head n), ParRed headEq schema term term := by
  intro n term
  induction term with
  | var index => exact .var index
  | const name => exact .const name
  | head value => exact .head value
  | pi domain codomain domainIH codomainIH =>
      exact .pi domainIH codomainIH
  | sigma domain codomain domainIH codomainIH =>
      exact .sigma domainIH codomainIH
  | id type left right typeIH leftIH rightIH =>
      exact .id typeIH leftIH rightIH
  | lam body bodyIH => exact .lam bodyIH
  | app function argument functionIH argumentIH =>
      exact .app functionIH argumentIH
  | pair first second firstIH secondIH => exact .pair firstIH secondIH
  | fst pair pairIH => exact .fst pairIH
  | snd pair pairIH => exact .snd pairIH
  | refl term termIH => exact .refl termIH

/-- Identity development of every metavariable in a substitution. -/
theorem parSub_refl
    {headEq : Head → Head → Prop} {schema : SchemaFamily Head} :
    ∀ {arity ambient : Nat} (substitution : Sub Head arity ambient),
      ParSub headEq schema substitution substitution := by
  intro arity
  induction arity with
  | zero =>
      intro ambient substitution
      have empty : substitution =
          (fun index : Fin 0 => (Fin.elim0 index : Tm Head ambient)) := by
        funext index
        exact Fin.elim0 index
      subst substitution
      exact .nil
  | succ arity inductionHypothesis =>
      intro ambient substitution
      let tail : Sub Head arity ambient := fun index => substitution index.succ
      have decomposition :
          substitution = Fin.cases (substitution 0) tail := by
        funext index
        refine Fin.cases ?_ ?_ index
        · rfl
        · intro prior
          rfl
      rw [decomposition]
      exact .cons (par_refl _) (inductionHypothesis tail)

/-- A selected schema presentation is sound for, and extensionally covers,
the root computation of a rule package.  Coverage is an actual decomposition
into an open schema and one substitution, not endpoint classification. -/
structure SchemaPresentation (rules : Rules Head) where
  schema : SchemaFamily Head
  sound {arity ambient : Nat} {left right : Tm Head arity}
      (rule : schema left right) (substitution : Sub Head arity ambient) :
    rules.computation.step (subst substitution left)
      (subst substitution right)
  cover {n : Nat} {source target : Tm Head n} :
    rules.computation.step source target →
      ∃ (arity : Nat) (left right : Tm Head arity)
          (substitution : Sub Head arity n),
        schema left right ∧
        subst substitution left = source ∧
        subst substitution right = target

/-- Parallel reduction generated by the schemas selected for a
presentation. -/
abbrev SchemaPresentation.Par
    {rules : Rules Head} (presentation : SchemaPresentation rules)
    {n : Nat} : Tm Head n → Tm Head n → Prop :=
  ParRed rules.headEq presentation.schema

private theorem stepStar_single
    {rules : Rules Head} {source target : Tm Head n}
    (step : Step rules.headEq source target rules.computation) :
    StepStar rules source target :=
  Relation.ReflTransGen.tail Relation.ReflTransGen.refl step

private theorem stepStar_map
    {rules : Rules Head} (transform : Tm Head n → Tm Head m)
    (preserves : ∀ {source target : Tm Head n},
      Step rules.headEq source target rules.computation →
        Step rules.headEq (transform source) (transform target)
          rules.computation)
    {source target : Tm Head n} (steps : StepStar rules source target) :
    StepStar rules (transform source) (transform target) := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail priorSteps finalStep inductionHypothesis =>
      exact Relation.ReflTransGen.tail inductionHypothesis
        (preserves finalStep)

private theorem stepStar_rename
    {rules : Rules Head} (renameMap : Ren n m)
    {source target : Tm Head n} (steps : StepStar rules source target) :
    StepStar rules (rename renameMap source) (rename renameMap target) :=
  stepStar_map (rename renameMap)
    (fun step => step.renameTerms renameMap) steps

private theorem stepStar_pi
    {rules : Rules Head}
    {domain domain' : Tm Head n}
    {codomain codomain' : Tm Head (n + 1)}
    (domainSteps : StepStar rules domain domain')
    (codomainSteps : StepStar rules codomain codomain') :
    StepStar rules (.pi domain codomain) (.pi domain' codomain') :=
  Relation.ReflTransGen.trans
    (stepStar_map (fun nextDomain => .pi nextDomain codomain)
      (fun step => Step.congPiDom step) domainSteps)
    (stepStar_map (fun nextCodomain => .pi domain' nextCodomain)
      (fun step => Step.congPiCod step) codomainSteps)

private theorem stepStar_sigma
    {rules : Rules Head}
    {domain domain' : Tm Head n}
    {codomain codomain' : Tm Head (n + 1)}
    (domainSteps : StepStar rules domain domain')
    (codomainSteps : StepStar rules codomain codomain') :
    StepStar rules (.sigma domain codomain) (.sigma domain' codomain') :=
  Relation.ReflTransGen.trans
    (stepStar_map (fun nextDomain => .sigma nextDomain codomain)
      (fun step => Step.congSigmaDom step) domainSteps)
    (stepStar_map (fun nextCodomain => .sigma domain' nextCodomain)
      (fun step => Step.congSigmaCod step) codomainSteps)

private theorem stepStar_id
    {rules : Rules Head}
    {type type' left left' right right' : Tm Head n}
    (typeSteps : StepStar rules type type')
    (leftSteps : StepStar rules left left')
    (rightSteps : StepStar rules right right') :
    StepStar rules (.id type left right) (.id type' left' right') :=
  Relation.ReflTransGen.trans
    (Relation.ReflTransGen.trans
      (stepStar_map (fun nextType => .id nextType left right)
        (fun step => Step.congIdTy step) typeSteps)
      (stepStar_map (fun nextLeft => .id type' nextLeft right)
        (fun step => Step.congIdLeft step) leftSteps))
    (stepStar_map (fun nextRight => .id type' left' nextRight)
      (fun step => Step.congIdRight step) rightSteps)

private theorem stepStar_lam
    {rules : Rules Head} {body body' : Tm Head (n + 1)}
    (steps : StepStar rules body body') :
    StepStar rules (.lam body) (.lam body') :=
  stepStar_map Tm.lam (fun step => Step.congLam step) steps

private theorem stepStar_app
    {rules : Rules Head}
    {function function' argument argument' : Tm Head n}
    (functionSteps : StepStar rules function function')
    (argumentSteps : StepStar rules argument argument') :
    StepStar rules (.app function argument) (.app function' argument') :=
  Relation.ReflTransGen.trans
    (stepStar_map (fun nextFunction => .app nextFunction argument)
      (fun step => Step.congAppFun step) functionSteps)
    (stepStar_map (fun nextArgument => .app function' nextArgument)
      (fun step => Step.congAppArg step) argumentSteps)

private theorem stepStar_pair
    {rules : Rules Head}
    {first first' second second' : Tm Head n}
    (firstSteps : StepStar rules first first')
    (secondSteps : StepStar rules second second') :
    StepStar rules (.pair first second) (.pair first' second') :=
  Relation.ReflTransGen.trans
    (stepStar_map (fun nextFirst => .pair nextFirst second)
      (fun step => Step.congPairFst step) firstSteps)
    (stepStar_map (fun nextSecond => .pair first' nextSecond)
      (fun step => Step.congPairSnd step) secondSteps)

private theorem stepStar_fst
    {rules : Rules Head} {pair pair' : Tm Head n}
    (steps : StepStar rules pair pair') :
    StepStar rules (.fst pair) (.fst pair') :=
  stepStar_map Tm.fst (fun step => Step.congFst step) steps

private theorem stepStar_snd
    {rules : Rules Head} {pair pair' : Tm Head n}
    (steps : StepStar rules pair pair') :
    StepStar rules (.snd pair) (.snd pair') :=
  stepStar_map Tm.snd (fun step => Step.congSnd step) steps

private theorem stepStar_refl
    {rules : Rules Head} {term term' : Tm Head n}
    (steps : StepStar rules term term') :
    StepStar rules (.refl term) (.refl term') :=
  stepStar_map Tm.refl (fun step => Step.congRefl step) steps

private theorem liftSub_stepStar
    {rules : Rules Head} {source target : Sub Head n m}
    (pointwise : ∀ index, StepStar rules (source index) (target index)) :
    ∀ index,
      StepStar rules (liftSub source index) (liftSub target index) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · exact Relation.ReflTransGen.refl
  · intro prior
    exact stepStar_rename wk (pointwise prior)

/-- Pointwise multi-step computation of a substitution lifts through every
open term.  This is the binding theorem used to realize an algebraic schema
step operationally. -/
theorem stepStar_substitute
    {rules : Rules Head} {source target : Sub Head n m}
    (pointwise : ∀ index, StepStar rules (source index) (target index)) :
    ∀ term : Tm Head n,
      StepStar rules (subst source term) (subst target term) := by
  intro term
  induction term generalizing m with
  | var index => exact pointwise index
  | const name => exact Relation.ReflTransGen.refl
  | head value => exact Relation.ReflTransGen.refl
  | pi domain codomain domainIH codomainIH =>
      exact stepStar_pi (domainIH pointwise)
        (codomainIH (liftSub_stepStar pointwise))
  | sigma domain codomain domainIH codomainIH =>
      exact stepStar_sigma (domainIH pointwise)
        (codomainIH (liftSub_stepStar pointwise))
  | id type left right typeIH leftIH rightIH =>
      exact stepStar_id (typeIH pointwise) (leftIH pointwise)
        (rightIH pointwise)
  | lam body bodyIH =>
      exact stepStar_lam (bodyIH (liftSub_stepStar pointwise))
  | app function argument functionIH argumentIH =>
      exact stepStar_app (functionIH pointwise) (argumentIH pointwise)
  | pair first second firstIH secondIH =>
      exact stepStar_pair (firstIH pointwise) (secondIH pointwise)
  | fst pair pairIH => exact stepStar_fst (pairIH pointwise)
  | snd pair pairIH => exact stepStar_snd (pairIH pointwise)
  | refl term termIH => exact stepStar_refl (termIH pointwise)

/-- Every ordinary presentation step is one algebraic parallel step.  The
root case uses exact schema coverage and the identity development of its
metavariable telescope. -/
theorem SchemaPresentation.step_to_par
    {rules : Rules Head} (presentation : SchemaPresentation rules)
    {source target : Tm Head n}
    (step : Step rules.headEq source target rules.computation) :
    presentation.Par source target := by
  induction step with
  | betaPi body argument =>
      exact .betaPi (par_refl body) (par_refl argument)
  | betaSigmaFst first second =>
      exact .betaSigmaFst (par_refl first) (par_refl second)
  | betaSigmaSnd first second =>
      exact .betaSigmaSnd (par_refl first) (par_refl second)
  | head equality => exact .headRel equality
  | root rootStep =>
      rcases presentation.cover rootStep with
        ⟨arity, left, right, substitution, schema,
          sourceEquation, targetEquation⟩
      rw [← sourceEquation, ← targetEquation]
      exact .algebraic schema substitution substitution
        (parSub_refl substitution)
  | congPiDom _ inductionHypothesis =>
      exact .pi inductionHypothesis (par_refl _)
  | congPiCod _ inductionHypothesis =>
      exact .pi (par_refl _) inductionHypothesis
  | congSigmaDom _ inductionHypothesis =>
      exact .sigma inductionHypothesis (par_refl _)
  | congSigmaCod _ inductionHypothesis =>
      exact .sigma (par_refl _) inductionHypothesis
  | congIdTy _ inductionHypothesis =>
      exact .id inductionHypothesis (par_refl _) (par_refl _)
  | congIdLeft _ inductionHypothesis =>
      exact .id (par_refl _) inductionHypothesis (par_refl _)
  | congIdRight _ inductionHypothesis =>
      exact .id (par_refl _) (par_refl _) inductionHypothesis
  | congLam _ inductionHypothesis => exact .lam inductionHypothesis
  | congAppFun _ inductionHypothesis =>
      exact .app inductionHypothesis (par_refl _)
  | congAppArg _ inductionHypothesis =>
      exact .app (par_refl _) inductionHypothesis
  | congPairFst _ inductionHypothesis =>
      exact .pair inductionHypothesis (par_refl _)
  | congPairSnd _ inductionHypothesis =>
      exact .pair (par_refl _) inductionHypothesis
  | congFst _ inductionHypothesis => exact .fst inductionHypothesis
  | congSnd _ inductionHypothesis => exact .snd inductionHypothesis
  | congRefl _ inductionHypothesis => exact .refl inductionHypothesis

/-- Realization says that an algebraic parallel move is operationally honest:
it expands to a finite path in the presentation's actual computation. -/
abbrev Realization {rules : Rules Head}
    (presentation : SchemaPresentation rules) : Prop :=
  ∀ {n : Nat} {source target : Tm Head n},
    presentation.Par source target →
      ConversionCoherence.StepStar rules source target

mutual

private def parRealizes
    {rules : Rules Head} (presentation : SchemaPresentation rules)
    {n : Nat} {source target : Tm Head n} :
    presentation.Par source target → StepStar rules source target
  | .var _ => Relation.ReflTransGen.refl
  | .const _ => Relation.ReflTransGen.refl
  | .head _ => Relation.ReflTransGen.refl
  | .headRel equality => stepStar_single (.head equality)
  | .pi domain codomain =>
      stepStar_pi (parRealizes presentation domain)
        (parRealizes presentation codomain)
  | .sigma domain codomain =>
      stepStar_sigma (parRealizes presentation domain)
        (parRealizes presentation codomain)
  | .id type left right =>
      stepStar_id (parRealizes presentation type)
        (parRealizes presentation left) (parRealizes presentation right)
  | .lam body => stepStar_lam (parRealizes presentation body)
  | .app function argument =>
      stepStar_app (parRealizes presentation function)
        (parRealizes presentation argument)
  | .pair first second =>
      stepStar_pair (parRealizes presentation first)
        (parRealizes presentation second)
  | .fst pair => stepStar_fst (parRealizes presentation pair)
  | .snd pair => stepStar_snd (parRealizes presentation pair)
  | .refl term => stepStar_refl (parRealizes presentation term)
  | .betaPi body argument =>
      Relation.ReflTransGen.trans
        (stepStar_app
          (stepStar_lam (parRealizes presentation body))
          (parRealizes presentation argument))
        (stepStar_single (.betaPi _ _))
  | .betaSigmaFst first second =>
      Relation.ReflTransGen.trans
        (stepStar_fst
          (stepStar_pair (parRealizes presentation first)
            (parRealizes presentation second)))
        (stepStar_single (.betaSigmaFst _ _))
  | .betaSigmaSnd first second =>
      Relation.ReflTransGen.trans
        (stepStar_snd
          (stepStar_pair (parRealizes presentation first)
            (parRealizes presentation second)))
        (stepStar_single (.betaSigmaSnd _ _))
  | .algebraic rule sourceSubstitution targetSubstitution arguments =>
      Relation.ReflTransGen.trans
        (stepStar_substitute
          (parSubRealizes presentation arguments) _)
        (stepStar_single
          (.root (presentation.sound rule targetSubstitution)))

private def parSubRealizes
    {rules : Rules Head} (presentation : SchemaPresentation rules)
    {arity ambient : Nat}
    {source target : Sub Head arity ambient} :
    ParSub rules.headEq presentation.schema source target →
      ∀ index, StepStar rules (source index) (target index)
  | .nil, index => Fin.elim0 index
  | .cons head tail, index =>
      Fin.cases (parRealizes presentation head)
        (fun prior => parSubRealizes presentation tail prior) index

end

/-- Algebraic parallel reduction is operationally realized by the root
computation selected in its exact schema presentation. -/
def SchemaPresentation.realization
    {rules : Rules Head} (presentation : SchemaPresentation rules) :
    Realization presentation := by
  intro n source target reduction
  exact parRealizes presentation reduction

/-- A complete development is a common one-step target for every parallel
development out of a term.  It is data separate from schema coverage and
operational realization, so none of the three obligations can masquerade as
another. -/
structure CompleteDevelopment {rules : Rules Head}
    (presentation : SchemaPresentation rules) where
  develop : {n : Nat} → Tm Head n → Tm Head n
  reaches {n : Nat} {source target : Tm Head n} :
    presentation.Par source target →
      presentation.Par target (develop source)

/-- Complete development gives the one-step parallel diamond. -/
theorem CompleteDevelopment.diamond
    {rules : Rules Head} {presentation : SchemaPresentation rules}
    (complete : CompleteDevelopment presentation)
    {source left right : Tm Head n}
    (first : presentation.Par source left)
    (second : presentation.Par source right) :
    ∃ common,
      presentation.Par left common ∧
      presentation.Par right common :=
  ⟨complete.develop source, complete.reaches first, complete.reaches second⟩

/-- Exact schema coverage, operational realization, and complete development
jointly imply Church--Rosser for the original presentation. -/
theorem churchRosserOfCompleteDevelopment
    {rules : Rules Head} (presentation : SchemaPresentation rules)
    (complete : CompleteDevelopment presentation) :
    ConversionCoherence.ChurchRosser rules :=
  ConversionCoherence.churchRosserOfParallelDiamond
    { parallel := presentation.Par
      ofStep := presentation.step_to_par
      realizes := presentation.realization }
    complete.diamond

/-! ## Axiom audit -/

#print axioms par_refl
#print axioms parSub_refl
#print axioms SchemaPresentation.step_to_par
#print axioms stepStar_substitute
#print axioms SchemaPresentation.realization
#print axioms CompleteDevelopment.diamond
#print axioms churchRosserOfCompleteDevelopment

end AlgebraicParallel
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
