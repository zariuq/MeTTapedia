import Mettapedia.Logic.HOL.PredicateFixedPoint
import Mettapedia.Logic.HOL.ContextualTrinity
import Mettapedia.Logic.HOL.TermInterpretationLaws

/-!
# Retained monotonicity proofs for positive predicate formulas

A distinguished predicate occurs through explicit membership nodes. Other
formulas are fixed parameters. Conjunction, disjunction, guarded implication
and both quantifiers preserve positivity. The compiler transports an actual
retained proof along a predicate inclusion, including beneath binders.
This is truth-valued reasoning; occurrence multiplicities remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.PositivePredicate

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {source : Ty Base}

inductive Code (Const : Ty Base → Type v) (source : Ty Base) : Ctx Base → Type (max u v) where
  | atom {context} : Formula Const context → Code Const source context
  | member {context} : Term Const context source → Code Const source context
  | conj {context} : Code Const source context → Code Const source context → Code Const source context
  | disj {context} : Code Const source context → Code Const source context → Code Const source context
  | guard {context} : Formula Const context → Code Const source context → Code Const source context
  | all {context domain} : Code Const source (domain :: context) → Code Const source context
  | ex {context domain} : Code Const source (domain :: context) → Code Const source context

namespace Code

universe u' v'
variable {Target : Type u'} {Symbols : Ty Target → Type v'}

/-- Retype a positive program and read its fixed atoms by closed terms. -/
def read (reading : TermInterpretation Base Const Target Symbols) :
    {context : Ctx Base} → Code Const source context →
      Code Symbols (Ty.substitute reading.types source) (context.map (Ty.substitute reading.types))
  | _, .atom formula => .atom (reading.term formula)
  | _, .member point => .member (reading.term point)
  | _, .conj left right => .conj (read reading left) (read reading right)
  | _, .disj left right => .disj (read reading left) (read reading right)
  | _, .guard premise body => .guard (reading.term premise) (read reading body)
  | _, .all body => .all (read reading body)
  | _, .ex body => .ex (read reading body)

def interpret : {context : Ctx Base} → Code Const source context →
    Term Const context (source ⇒ .prop) → Formula Const context
  | _, .atom formula, _ => formula
  | _, .member point, predicate => .app predicate point
  | _, .conj left right, predicate => .and (interpret left predicate) (interpret right predicate)
  | _, .disj left right, predicate => .or (interpret left predicate) (interpret right predicate)
  | _, .guard premise body, predicate => .imp premise (interpret body predicate)
  | _, .all body, predicate => .all (interpret body (weaken predicate))
  | _, .ex body, predicate => .ex (interpret body (weaken predicate))

theorem interpret_read (reading : TermInterpretation Base Const Target Symbols) :
    ∀ {context : Ctx Base} (code : Code Const source context)
      (predicate : Term Const context (source ⇒ .prop)),
      reading.term (code.interpret predicate) = (code.read reading).interpret (reading.term predicate)
  | _, .atom _, _ => rfl
  | _, .member _, _ => rfl
  | _, .conj left right, predicate => by
    simp only [interpret, read, TermInterpretation.term_and,
      interpret_read reading left predicate, interpret_read reading right predicate]
    rfl
  | _, .disj left right, predicate => by
    simp only [interpret, read, TermInterpretation.term_or,
      interpret_read reading left predicate, interpret_read reading right predicate]
    rfl
  | _, .guard premise body, predicate => by
    simp only [interpret, read, TermInterpretation.term_imp, interpret_read reading body predicate]
    rfl
  | _, .all body, predicate => by
    simp only [interpret, read, TermInterpretation.term_all]
    rw [interpret_read, TermInterpretation.term_weaken]
    rfl
  | _, .ex body, predicate => by
    simp only [interpret, read, TermInterpretation.term_ex]
    rw [interpret_read, TermInterpretation.term_weaken]
    rfl

def rename {context target : Ctx Base} (mapping : Rename Base context target) :
    Code Const source context → Code Const source target
  | .atom formula => .atom (HOL.rename mapping formula)
  | .member point => .member (HOL.rename mapping point)
  | .conj left right => .conj (rename mapping left) (rename mapping right)
  | .disj left right => .disj (rename mapping left) (rename mapping right)
  | .guard premise body => .guard (HOL.rename mapping premise) (rename mapping body)
  | .all body => .all (rename (Rename.lift mapping) body)
  | .ex body => .ex (rename (Rename.lift mapping) body)

def subst {context target : Ctx Base} (mapping : Subst Const context target) :
    Code Const source context → Code Const source target
  | .atom formula => .atom (HOL.subst mapping formula)
  | .member point => .member (HOL.subst mapping point)
  | .conj left right => .conj (subst mapping left) (subst mapping right)
  | .disj left right => .disj (subst mapping left) (subst mapping right)
  | .guard premise body => .guard (HOL.subst mapping premise) (subst mapping body)
  | .all body => .all (subst (Subst.lift mapping) body)
  | .ex body => .ex (subst (Subst.lift mapping) body)

private theorem reading_lift_compatible (reading : TermInterpretation Base Const Target Symbols)
    {context target : Ctx Base} (rho : Rename Base context target)
    (mapped : Rename Target (context.map (Ty.substitute reading.types)) (target.map (Ty.substitute reading.types)))
    (compatible : ∀ {type} (index : Var context type),
      (rho index).mapTypes reading.types = mapped (index.mapTypes reading.types))
    {domain type : Ty Base} (index : Var (domain :: context) type) :
    ((Rename.lift rho) index).mapTypes reading.types = (Rename.lift mapped) (index.mapTypes reading.types) := by
  cases index with
  | vz => rfl
  | vs index => exact congrArg Var.vs (compatible index)

theorem read_rename (reading : TermInterpretation Base Const Target Symbols)
    {context target : Ctx Base} (rho : Rename Base context target)
    (mapped : Rename Target (context.map (Ty.substitute reading.types)) (target.map (Ty.substitute reading.types)))
    (compatible : ∀ {type} (index : Var context type),
      (rho index).mapTypes reading.types = mapped (index.mapTypes reading.types))
    (code : Code Const source context) :
    (code.rename rho).read reading = (code.read reading).rename mapped := by
  induction code generalizing target with
  | atom formula => exact congrArg Code.atom (reading.term_rename rho mapped compatible formula)
  | member point => exact congrArg Code.member (reading.term_rename rho mapped compatible point)
  | conj _ _ first second => simp only [read, rename, first rho mapped compatible, second rho mapped compatible]
  | disj _ _ first second => simp only [read, rename, first rho mapped compatible, second rho mapped compatible]
  | guard premise _ body =>
    exact congrArg₂ Code.guard (reading.term_rename rho mapped compatible premise) (body rho mapped compatible)
  | all body hypothesis =>
    simp only [read, rename]
    exact congrArg Code.all (hypothesis (Rename.lift rho) (Rename.lift mapped)
      (reading_lift_compatible reading rho mapped compatible))
  | ex body hypothesis =>
    simp only [read, rename]
    exact congrArg Code.ex (hypothesis (Rename.lift rho) (Rename.lift mapped)
      (reading_lift_compatible reading rho mapped compatible))

theorem rename_comp {context middle target : Ctx Base}
    (first : Rename Base middle target) (second : Rename Base context middle)
    (code : Code Const source context) :
    (code.rename second).rename first = code.rename (fun index => first (second index)) := by
  induction code generalizing middle target with
  | atom _ => simp [rename,HOL.rename_comp]
  | member _ => simp [rename,HOL.rename_comp]
  | conj _ _ left right => simp [rename,left,right]
  | disj _ _ left right => simp [rename,left,right]
  | guard _ _ ih => simp [rename,HOL.rename_comp,ih]
  | all body ih =>
    simp only [rename,ih]
    congr 2
    funext type index
    cases index <;> rfl
  | ex body ih =>
    simp only [rename,ih]
    congr 2
    funext type index
    cases index <;> rfl

theorem subst_rename {context middle target : Ctx Base}
    (substitution : Subst Const middle target) (relabel : Rename Base context middle)
    (code : Code Const source context) :
    (code.rename relabel).subst substitution = code.subst (fun index => substitution (relabel index)) := by
  induction code generalizing middle target with
  | atom _ => simp [rename,subst,HOL.subst_rename]
  | member _ => simp [rename,subst,HOL.subst_rename]
  | conj _ _ left right => simp [rename,subst,left,right]
  | disj _ _ left right => simp [rename,subst,left,right]
  | guard _ _ ih => simp [rename,subst,HOL.subst_rename,ih]
  | all body ih =>
    simp only [rename,subst,ih]
    congr 2
    funext type index
    cases index <;> rfl
  | ex body ih =>
    simp only [rename,subst,ih]
    congr 2
    funext type index
    cases index <;> rfl

theorem rename_subst {context middle target : Ctx Base}
    (rho : Rename Base middle target) (substitution : Subst Const context middle)
    (code : Code Const source context) :
    (code.subst substitution).rename rho = code.subst (fun index => HOL.rename rho (substitution index)) := by
  induction code generalizing middle target with
  | atom _ => simp [rename, subst, HOL.rename_subst]
  | member _ => simp [rename, subst, HOL.rename_subst]
  | conj _ _ first second => simp [rename, subst, first, second]
  | disj _ _ first second => simp [rename, subst, first, second]
  | guard _ _ ih => simp [rename, subst, HOL.rename_subst, ih]
  | all body ih =>
      simp only [rename, subst, ih]
      congr 2
      funext type index
      cases index <;> simp [Subst.lift, HOL.rename_comp, Rename.lift, Rename.weaken]
  | ex body ih =>
      simp only [rename, subst, ih]
      congr 2
      funext type index
      cases index <;> simp [Subst.lift, HOL.rename_comp, Rename.lift, Rename.weaken]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem subst_id {context : Ctx Base} (code : Code Const source context) :
    code.subst (fun index => Term.var index) = code := by
  induction code with
  | atom formula => exact congrArg Code.atom (HOL.subst_id formula)
  | member point => exact congrArg Code.member (HOL.subst_id point)
  | conj _ _ left right => simp [subst,left,right]
  | disj _ _ left right => simp [subst,left,right]
  | guard premise _ ih => exact congrArg₂ Code.guard (HOL.subst_id premise) ih
  | @all context domain body ih =>
    have lifted : (Subst.lift (fun index => Term.var index) : Subst Const (domain :: context) (domain :: context)) = (fun {type} (index : Var (domain :: context) type) => Term.var index) := by
      funext type index
      cases index <;> rfl
    simpa only [subst,lifted] using congrArg Code.all ih
  | @ex context domain body ih =>
    have lifted : (Subst.lift (fun index => Term.var index) : Subst Const (domain :: context) (domain :: context)) = (fun {type} (index : Var (domain :: context) type) => Term.var index) := by
      funext type index
      cases index <;> rfl
    simpa only [subst,lifted] using congrArg Code.ex ih

@[simp] theorem interpret_rename {context target : Ctx Base} (mapping : Rename Base context target)
    (code : Code Const source context) (predicate : Term Const context (source ⇒ .prop)) :
    (code.rename mapping).interpret (HOL.rename mapping predicate) = HOL.rename mapping (code.interpret predicate) := by
  induction code generalizing target with
  | atom _ => rfl
  | member _ => rfl
  | conj _ _ first second => simp [rename,interpret,HOL.rename,first,second]
  | disj _ _ first second => simp [rename,interpret,HOL.rename,first,second]
  | guard _ _ ih => simp [rename,interpret,HOL.rename,ih]
  | all body ih =>
    simp only [rename,interpret,HOL.rename]
    congr 1
    rw [← ih]
    congr 1
    simp [weaken,HOL.rename_comp, Rename.lift, Rename.weaken]
  | ex body ih =>
    simp only [rename,interpret,HOL.rename]
    congr 1
    rw [← ih]
    congr 1
    simp [weaken,HOL.rename_comp, Rename.lift, Rename.weaken]

@[simp] theorem interpret_subst {context target : Ctx Base} (mapping : Subst Const context target)
    (code : Code Const source context) (predicate : Term Const context (source ⇒ .prop)) :
    (code.subst mapping).interpret (HOL.subst mapping predicate) = HOL.subst mapping (code.interpret predicate) := by
  induction code generalizing target with
  | atom _ => rfl
  | member _ => rfl
  | conj _ _ first second => simp [subst,interpret,HOL.subst,first,second]
  | disj _ _ first second => simp [subst,interpret,HOL.subst,first,second]
  | guard _ _ ih => simp [subst,interpret,HOL.subst,ih]
  | all body ih =>
    simp only [subst,interpret,HOL.subst]
    congr 1
    rw [← ih]
    congr 1
    simp [weaken,HOL.subst_rename,HOL.rename_subst,Subst.lift,Rename.weaken]
  | ex body ih =>
    simp only [subst,interpret,HOL.subst]
    congr 1
    rw [← ih]
    congr 1
    simp [weaken,HOL.subst_rename,HOL.rename_subst,Subst.lift,Rename.weaken]

private def weakenInclusion {context : Ctx Base} {domain : Ty Base}
    {assumptions : List (Formula Const context)}
    (first second : Term Const context (source ⇒ .prop))
    (inclusion : ProofSyntax Const assumptions (PredicateFixedPoint.included first second)) :
    ProofSyntax Const (weakenHyps (σ := domain) assumptions)
      (PredicateFixedPoint.included (weaken first) (weaken second)) :=
  ProofSyntax.castIndices rfl (PredicateFixedPoint.rename_included Rename.weaken first second)
    (PredicateFixedPoint.weakenProof inclusion)

private def freshAll {context : Ctx Base} {domain : Ty Base}
    {assumptions : List (Formula Const context)} {body : Formula Const (domain :: context)}
    (proof : ProofSyntax Const assumptions (.all body)) :
    ProofSyntax Const (weakenHyps (σ := domain) assumptions) body :=
  ProofSyntax.castIndices rfl (ContextualTrinity.instantiate_vz_rename_lift_weaken body)
    (ProofSyntax.allE (.var .vz) (PredicateFixedPoint.weakenProof proof))

private def freshExists {context : Ctx Base} {domain : Ty Base}
    {assumptions : List (Formula Const (domain :: context))} {body : Formula Const (domain :: context)}
    (proof : ProofSyntax Const assumptions body) :
    ProofSyntax Const assumptions (weaken (σ := domain) (.ex body)) :=
  ProofSyntax.exI (.var .vz)
    (ProofSyntax.castIndices rfl (ContextualTrinity.instantiate_vz_rename_lift_weaken body).symm proof)

/-- Structural proof compilation along predicate inclusion. Guard premises
and atom formulas are held fixed while the distinguished predicate varies. -/
def transport : ∀ {context : Ctx Base} (code : Code Const source context)
    (first second : Term Const context (source ⇒ .prop)) {assumptions : List (Formula Const context)},
    ProofSyntax Const assumptions (PredicateFixedPoint.included first second) →
    ProofSyntax Const assumptions (code.interpret first) →
    ProofSyntax Const assumptions (code.interpret second)
  | _, .atom _, _, _, _, _, present => present
  | _, .member point, first, second, _, inclusion, present =>
      PredicateFixedPoint.inclusion_elim first second point inclusion present
  | _, .conj left right, first, second, _, inclusion, present =>
      .andI (transport left first second inclusion (.andEL present))
        (transport right first second inclusion (.andER present))
  | _, .disj left right, first, second, _, inclusion, present =>
      .orE present
        (.orIL (transport left first second (inclusion.prepend (left.interpret first)) (.hyp 0)))
        (.orIR (transport right first second (inclusion.prepend (right.interpret first)) (.hyp 0)))
  | _, .guard premise body, first, second, _, inclusion, present =>
      .impI (transport body first second (inclusion.prepend premise) (.impE (present.prepend premise) (.hyp 0)))
  | _, .all body, first, second, _, inclusion, present =>
      .allI (transport body (weaken first) (weaken second)
        (weakenInclusion first second inclusion) (freshAll present))
  | _, .ex body, first, second, _, inclusion, present =>
      .exE present (freshExists (transport body (weaken first) (weaken second)
        ((weakenInclusion first second inclusion).prepend (body.interpret (weaken first))) (.hyp 0)))

set_option backward.isDefEq.respectTransparency false in
theorem transport_functionExtensionalityFree {context : Ctx Base}
    (code : Code Const source context) (first second : Term Const context (source ⇒ .prop))
    {assumptions : List (Formula Const context)}
    (inclusion : ProofSyntax Const assumptions (PredicateFixedPoint.included first second))
    (present : ProofSyntax Const assumptions (code.interpret first))
    (inclusionFree : ProofSyntax.FunctionExtensionalityFree inclusion)
    (presentFree : ProofSyntax.FunctionExtensionalityFree present) :
    ProofSyntax.FunctionExtensionalityFree (code.transport first second inclusion present) := by
  induction code with
  | atom _ => exact presentFree
  | member _ =>
    simpa [transport,PredicateFixedPoint.inclusion_elim,ProofSyntax.FunctionExtensionalityFree]
      using And.intro inclusionFree presentFree
  | conj _ _ left right =>
    simp only [transport,ProofSyntax.FunctionExtensionalityFree]
    exact ⟨left _ _ inclusion (.andEL present) inclusionFree presentFree,
      right _ _ inclusion (.andER present) inclusionFree presentFree⟩
  | disj _ _ left right =>
    simp [transport,ProofSyntax.FunctionExtensionalityFree,ProofSyntax.prepend,
      left,right,inclusionFree,presentFree]
  | guard _ _ ih =>
    simp [transport,ProofSyntax.FunctionExtensionalityFree,ProofSyntax.prepend,
      ih,inclusionFree,presentFree]
  | all _ ih =>
    simp [transport,ProofSyntax.FunctionExtensionalityFree,weakenInclusion,freshAll,
      PredicateFixedPoint.weakenProof,ih,inclusionFree,presentFree]
  | ex _ ih =>
    simp [transport,ProofSyntax.FunctionExtensionalityFree,weakenInclusion,freshExists,
      PredicateFixedPoint.weakenProof,ProofSyntax.prepend,ih,inclusionFree,presentFree]

#print axioms transport
#print axioms transport_functionExtensionalityFree

def operator {context : Ctx Base} (code : Code Const source (source :: context)) :
    Term Const context (PredicateFixedPoint.Operator source) :=
  .lam (.lam ((code.rename (Rename.lift Rename.weaken)).interpret (.var (.vs .vz))))

theorem operator_read (reading : TermInterpretation Base Const Target Symbols)
    {context : Ctx Base} (code : Code Const source (source :: context)) :
    reading.term code.operator = (code.read reading).operator := by
  simp only [operator, TermInterpretation.term_lam]
  rw [interpret_read, read_rename reading (Rename.lift Rename.weaken) (Rename.lift Rename.weaken)
    (by intro type index; cases index <;> rfl)]
  rfl

def body {context : Ctx Base} (code : Code Const source (source :: context))
    (predicate : Term Const context (source ⇒ .prop)) (point : Term Const context source) : Formula Const context :=
  (code.subst (Subst.single point)).interpret predicate

set_option backward.isDefEq.respectTransparency false in
theorem operator_first_beta {context : Ctx Base} (code : Code Const source (source :: context))
    (predicate : Term Const context (source ⇒ .prop)) :
    instantiate predicate (.lam ((code.rename (Rename.lift Rename.weaken)).interpret (.var (.vs .vz)))) =
      .lam (code.interpret (weaken predicate)) := by
  simp only [instantiate,HOL.subst,← interpret_subst]
  rw [subst_rename]
  have identity : (fun {type} (index : Var (source :: context) type) =>
      Subst.lift (Subst.single predicate) (Rename.lift Rename.weaken index)) =
      (fun {type} (index : Var (source :: context) type) => Term.var index) := by
    funext type index
    cases index <;> rfl
  rw [identity]
  have fixed := subst_id code
  rw [fixed]
  rfl

def operator_beta {context : Ctx Base} (code : Code Const source (source :: context))
    (predicate : Term Const context (source ⇒ .prop)) (point : Term Const context source)
    {assumptions : List (Formula Const context)} :
    ProofSyntax Const assumptions (.eq (.app (.app code.operator predicate) point) (code.body predicate point)) := by
  have first := ProofSyntax.eqApp point (ProofSyntax.beta (Δ := assumptions) predicate
    (.lam ((code.rename (Rename.lift Rename.weaken)).interpret (.var (.vs .vz)))))
  have second := ProofSyntax.beta (Δ := assumptions) point (code.interpret (weaken predicate))
  have firstEq : instantiate predicate
      (.lam ((code.rename (Rename.lift Rename.weaken)).interpret (.var (.vs .vz)))) =
      .lam (code.interpret (weaken predicate)) := operator_first_beta code predicate
  have secondEq : instantiate point (code.interpret (weaken predicate)) = code.body predicate point := by
    rw [instantiate,← interpret_subst]
    simp only [body,PredicateFixedPoint.subst_single_weaken]
  exact .eqTrans (ProofSyntax.castIndices rfl (congrArg (fun function => Term.eq
    (.app (.app code.operator predicate) point) (.app function point)) firstEq) first)
    (ProofSyntax.castIndices rfl (congrArg (Term.eq (.app (.lam (code.interpret (weaken predicate))) point)) secondEq) second)

@[simp] theorem operator_rename {context target : Ctx Base} (mapping : Rename Base context target)
    (code : Code Const source (source :: context)) :
    (code.rename (Rename.lift mapping)).operator = HOL.rename mapping code.operator := by
  simp only [operator,HOL.rename,← interpret_rename,rename_comp]
  congr 3
  congr 1
  funext type index
  cases index <;> rfl

@[simp] theorem operator_subst {context target : Ctx Base} (mapping : Subst Const context target)
    (code : Code Const source (source :: context)) :
    (code.subst (Subst.lift mapping)).operator = HOL.subst mapping code.operator := by
  simp only [operator, HOL.subst, ← interpret_subst, rename_subst, subst_rename]
  congr 3
  congr 1
  funext type index
  cases index <;> simp [Subst.lift, HOL.rename_comp, Rename.lift, Rename.weaken]

def operator_monotone {context : Ctx Base} (code : Code Const source (source :: context))
    {assumptions : List (Formula Const context)} :
    ProofSyntax Const assumptions (PredicateFixedPoint.monotone code.operator) := by
  refine .allI (.allI (.impI (.allI (.impI ?_))))
  let mapping : Rename Base context (source :: (source ⇒ .prop) :: (source ⇒ .prop) :: context) :=
    fun index => .vs (.vs (.vs index))
  let raised := code.rename (Rename.lift mapping)
  let first : Term Const (source :: (source ⇒ .prop) :: (source ⇒ .prop) :: context) (source ⇒ .prop) :=
    .var (.vs (.vs .vz))
  let second : Term Const (source :: (source ⇒ .prop) :: (source ⇒ .prop) :: context) (source ⇒ .prop) :=
    .var (.vs .vz)
  let point : Term Const (source :: (source ⇒ .prop) :: (source ⇒ .prop) :: context) source := .var .vz
  let hypotheses := .app (.app raised.operator first) point ::
    PredicateFixedPoint.included first second ::
      weakenHyps (σ := source) (weakenHyps (σ := source ⇒ .prop)
        (weakenHyps (σ := source ⇒ .prop) assumptions))
  have inclusion : ProofSyntax Const hypotheses (PredicateFixedPoint.included first second) := .hyp 1
  have present : ProofSyntax Const hypotheses (.app (.app raised.operator first) point) := .hyp 0
  have mapped := (raised.subst (Subst.single point)).transport first second inclusion
    (.impE (.eqPropEL (raised.operator_beta first point)) present)
  have result := ProofSyntax.impE (.eqPropER (raised.operator_beta second point)) mapped
  apply ProofSyntax.castIndices ?_ ?_ result
  · simp [hypotheses,PredicateFixedPoint.included,raised,mapping,first,second,point,
      weakenHyps,weaken,operator_rename,HOL.rename,HOL.rename_comp,Rename.lift,Rename.weaken]
  · simp [raised,mapping,second,point,weaken,operator_rename,HOL.rename,HOL.rename_comp,Rename.weaken]

set_option backward.isDefEq.respectTransparency false in
theorem operator_monotone_functionExtensionalityFree {context : Ctx Base}
    (code : Code Const source (source :: context)) {assumptions : List (Formula Const context)} :
    ProofSyntax.FunctionExtensionalityFree (code.operator_monotone (assumptions := assumptions)) := by
  simp [operator_monotone,transport_functionExtensionalityFree,operator_beta,
    ProofSyntax.FunctionExtensionalityFree]

/-- The retained least-predicate theorem receives the generated monotonicity
proof. No monotonicity premise is added to the resulting fixed-point formula. -/
def fixed_point {context : Ctx Base} (code : Code Const source (source :: context))
    {assumptions : List (Formula Const context)} :
    ProofSyntax Const assumptions (PredicateFixedPoint.equation code.operator) :=
  PredicateFixedPoint.fixed_point code.operator code.operator_monotone

set_option backward.isDefEq.respectTransparency false in
theorem fixed_point_functionExtensionalityFree {context : Ctx Base}
    (code : Code Const source (source :: context)) {assumptions : List (Formula Const context)} :
    ProofSyntax.FunctionExtensionalityFree (code.fixed_point (assumptions := assumptions)) := by
  simp [fixed_point,PredicateFixedPoint.fixed_point,PredicateFixedPoint.least_postfixed,
    PredicateFixedPoint.least_prefixed,PredicateFixedPoint.closure_at,PredicateFixedPoint.least_intro,
    PredicateFixedPoint.monotonicity_elim,PredicateFixedPoint.minimality,PredicateFixedPoint.least_elim,
    PredicateFixedPoint.least_beta,PredicateFixedPoint.inclusion_elim,PredicateFixedPoint.weakenProof,
    ProofSyntax.prepend,ProofSyntax.FunctionExtensionalityFree,operator_monotone_functionExtensionalityFree]

#print axioms operator_beta
#print axioms operator_monotone

end Code
end Mettapedia.Logic.HOL.PositivePredicate
