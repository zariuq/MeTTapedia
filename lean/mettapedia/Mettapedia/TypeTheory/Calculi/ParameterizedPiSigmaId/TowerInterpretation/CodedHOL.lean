import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedCodedReading
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.Soundness
import Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation

/-!
# Coded HOL terms with the actual annotated set meaning

The target signature reuses material-set operations and names the existing
trace product, graph abstraction, trace application and ordered-pair operations.
An independently defined standard HOL model interprets them by the actual set
operations. The entire source term grammar commutes with that interpretation.
This is semantic correspondence of generated HOL syntax; retained derivations
of its theory laws and native implementation qualification remain separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL
open Mettapedia.Logic Mettapedia.Logic.HOL
open Presentation TypedEquality.Annotated
open HOL.Embedding ZFSetDependentProducts ZFSetTraceProducts ZFSetTraceProofDecoding
open Mettapedia.SetTheory
universe u

abbrev object : Ty Unit := .base ()

inductive Symbol (Head : Type) : Ty Unit → Type where
  | core {type : Ty Unit} (symbol : ZFSetHenkinInterpretation.Symbol type) : Symbol Head type
  | head (head : Head) : Symbol Head object
  | constant (name : DeclName) : Symbol Head object
  | product : Symbol Head (object ⇒ (object ⇒ object) ⇒ object)
  | sum : Symbol Head (object ⇒ (object ⇒ object) ⇒ object)
  | abstraction : Symbol Head (object ⇒ (object ⇒ object) ⇒ object)
  | application : Symbol Head (object ⇒ object ⇒ object)
  | pair : Symbol Head (object ⇒ object ⇒ object)
  | first : Symbol Head (object ⇒ object)
  | second : Symbol Head (object ⇒ object)
  | truth : Symbol Head (.prop ⇒ object)

variable {Head : Type}

def operations : AnnotatedCodedReading.Operations Head (Symbol Head) object where
  head h := .const (.head h)
  constant c := .const (.constant c)
  product := .const .product
  sum := .const .sum
  abstraction := .const .abstraction
  application := .const .application
  pair := .const .pair
  first := .const .first
  second := .const .second
  truth := .const .truth
  empty := .const (.core .empty)

noncomputable def denoteSymbol (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    {type : Ty Unit} → Symbol Head type → Ty.denote.{0,u+1} ZFSetHenkinInterpretation.carrier.{u} type
  | _, .core c => ZFSetHenkinInterpretation.denoteSymbol c
  | _, .head h => heads h
  | _, .constant c => constants c
  | _, .product => tracePiSet
  | _, .sum => sigmaSet
  | _, .abstraction => fun domain body => traceLam (graph domain body)
  | _, .application => traceApp
  | _, .pair => ZFSet.pair
  | _, .first => ZFSetOrderedPair.first
  | _, .second => ZFSetOrderedPair.second
  | _, .truth => fun p => truthCode p.down

noncomputable abbrev model (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    HenkinModel.{0,0,u+1} Unit (Symbol Head) :=
  HenkinModel.standard ZFSetHenkinInterpretation.carrier (denoteSymbol heads constants)

variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})

private theorem denote_lift {n : Nat} {Γ : Ctx Unit}
    (bound : Fin n → Term (Symbol Head) Γ object) (rho : (model heads constants).Valuation Γ)
    (point : ZFSet.{u}) :
    (fun i => (model heads constants).denote (AnnotatedCodedReading.lift bound i)
      ((model heads constants).toPreModel.extend (σ := object) rho point)) =
      TowerInterpretation.extend (fun i => (model heads constants).denote (bound i) rho) point := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact HOL.Soundness.denote_weaken (σ := object) (model heads constants) (bound j) rho point

theorem denote_readAt {n : Nat} {Γ : Ctx Unit} (source : CTm Head n)
    (bound : Fin n → Term (Symbol Head) Γ object) (rho : (model heads constants).Valuation Γ) :
    (model heads constants).denote (AnnotatedCodedReading.readAt operations bound source) rho =
      ev heads constants source (fun i => (model heads constants).denote (bound i) rho) := by
  induction source generalizing Γ with
  | var i => rfl
  | head h | const h =>
    simp only [AnnotatedCodedReading.readAt,operations,HOL.weakenCtx_const]
    rfl
  | pi A B ihA ihB =>
    simp only [AnnotatedCodedReading.readAt,operations,HOL.weakenCtx_const]
    change tracePiSet ((model heads constants).denote (AnnotatedCodedReading.readAt operations bound A) rho)
      (fun x => (model heads constants).denote (AnnotatedCodedReading.readAt operations (AnnotatedCodedReading.lift bound) B)
        ((model heads constants).toPreModel.extend (σ := object) rho x)) = _
    rw [ihA]
    congr 1
    funext point
    rw [ihB,denote_lift]
  | sigma A B ihA ihB =>
    simp only [AnnotatedCodedReading.readAt,operations,HOL.weakenCtx_const]
    change sigmaSet ((model heads constants).denote (AnnotatedCodedReading.readAt operations bound A) rho)
      (fun x => (model heads constants).denote (AnnotatedCodedReading.readAt operations (AnnotatedCodedReading.lift bound) B)
        ((model heads constants).toPreModel.extend (σ := object) rho x)) = _
    rw [ihA]
    congr 1
    funext point
    rw [ihB,denote_lift]
  | lam A B ihA ihB =>
    simp only [AnnotatedCodedReading.readAt,operations,HOL.weakenCtx_const]
    change traceLam (graph ((model heads constants).denote (AnnotatedCodedReading.readAt operations bound A) rho)
      (fun x => (model heads constants).denote (AnnotatedCodedReading.readAt operations (AnnotatedCodedReading.lift bound) B)
        ((model heads constants).toPreModel.extend (σ := object) rho x))) = _
    rw [ihA]
    congr 2
    funext point
    rw [ihB,denote_lift]
  | app f a ihf iha | pair f a ihf iha =>
    simp only [AnnotatedCodedReading.readAt,operations,HOL.weakenCtx_const]
    first
    | exact congrArg₂ traceApp (ihf bound rho) (iha bound rho)
    | exact congrArg₂ ZFSet.pair (ihf bound rho) (iha bound rho)
  | fst p ih | snd p ih =>
    simp only [AnnotatedCodedReading.readAt,operations,HOL.weakenCtx_const]
    first
    | exact congrArg ZFSetOrderedPair.first (ih bound rho)
    | exact congrArg ZFSetOrderedPair.second (ih bound rho)
  | id A a b _ iha ihb =>
    simp only [AnnotatedCodedReading.readAt,operations,HOL.weakenCtx_const]
    change truthCode ((model heads constants).denote (AnnotatedCodedReading.readAt operations bound a) rho =
      (model heads constants).denote (AnnotatedCodedReading.readAt operations bound b) rho) = _
    rw [iha,ihb]
    rfl
  | refl _ _ =>
    simp only [AnnotatedCodedReading.readAt,operations,HOL.weakenCtx_const]
    rfl

def memberAt {Γ : Ctx Unit} (value type : Term (Symbol Head) Γ object) : Formula (Symbol Head) Γ :=
  .app (.app (.const (.core .member)) value) type

def contextAt : {n : Nat} → {Γ : Ctx Unit} → CCtx Head n →
    (Fin n → Term (Symbol Head) Γ object) → Formula (Symbol Head) Γ
  | _, _, .nil, _ => .top
  | _, _, .snoc earlier type, bound =>
      .and (contextAt earlier (fun i => bound i.succ))
        (memberAt (bound 0) (AnnotatedCodedReading.readAt operations (fun i => bound i.succ) type))

private theorem environment_eta {n : Nat} (rho : Env.{u} (n+1)) :
    rho = TowerInterpretation.extend (fun i => rho i.succ) (rho 0) := by
  funext i
  refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

private def setMember (value type : ZFSet.{u}) : Prop := value ∈ type

theorem denote_contextAt {n : Nat} {Γ : Ctx Unit} (context : CCtx Head n)
    (bound : Fin n → Term (Symbol Head) Γ object) (rho : (model heads constants).Valuation Γ) :
    ((model heads constants).denote (contextAt context bound) rho).down ↔
      Sat heads constants context (fun i => (model heads constants).denote (bound i) rho) := by
  induction context generalizing Γ with
  | nil => exact ⟨fun _ => sat_nil _ _ _, fun _ => True.intro⟩
  | snoc earlier type ih =>
    change (((model heads constants).denote (contextAt earlier (fun i => bound i.succ)) rho).down ∧
      setMember ((model heads constants).denote (bound 0) rho)
        ((model heads constants).denote (AnnotatedCodedReading.readAt operations (fun i => bound i.succ) type) rho)) ↔ _
    rw [ih,denote_readAt]
    conv_rhs => rw [environment_eta (fun i => (model heads constants).denote (bound i) rho)]
    exact (sat_snoc heads constants).symm

abbrev statementArity : CStatement Head → Nat
  | .typing (n := n) _ _ _ | .equality (n := n) _ _ _ _ | .sub (n := n) _ _ _ => n

def statementContext : (statement : CStatement Head) → CCtx Head (statementArity statement)
  | .typing context _ _ | .equality context _ _ _ | .sub context _ _ => context

def statementAt : (statement : CStatement Head) → {Γ : Ctx Unit} →
    (Fin (statementArity statement) → Term (Symbol Head) Γ object) → Formula (Symbol Head) Γ
  | .typing _ value type, _, bound => memberAt (AnnotatedCodedReading.readAt operations bound value)
      (AnnotatedCodedReading.readAt operations bound type)
  | .equality _ first second type, _, bound =>
      .and (.eq (AnnotatedCodedReading.readAt operations bound first) (AnnotatedCodedReading.readAt operations bound second))
        (memberAt (AnnotatedCodedReading.readAt operations bound first) (AnnotatedCodedReading.readAt operations bound type))
  | .sub _ first second, _, bound =>
      .all (.imp (memberAt (.var .vz) (weaken (AnnotatedCodedReading.readAt operations bound first)))
        (memberAt (.var .vz) (weaken (AnnotatedCodedReading.readAt operations bound second))))

theorem denote_statementAt (statement : CStatement Head) {Γ : Ctx Unit}
    (bound : Fin (statementArity statement) → Term (Symbol Head) Γ object)
    (rho : (model heads constants).Valuation Γ) :
    ((model heads constants).denote (statementAt statement bound) rho).down ↔
      (match statement with
      | .typing _ value type => ev heads constants value (fun i => (model heads constants).denote (bound i) rho) ∈
          ev heads constants type (fun i => (model heads constants).denote (bound i) rho)
      | .equality _ first second type =>
          ev heads constants first (fun i => (model heads constants).denote (bound i) rho) =
            ev heads constants second (fun i => (model heads constants).denote (bound i) rho) ∧
          ev heads constants first (fun i => (model heads constants).denote (bound i) rho) ∈
            ev heads constants type (fun i => (model heads constants).denote (bound i) rho)
      | .sub _ first second => ev heads constants first (fun i => (model heads constants).denote (bound i) rho) ⊆
          ev heads constants second (fun i => (model heads constants).denote (bound i) rho)) := by
  cases statement with
  | typing context value type =>
    change setMember ((model heads constants).denote (AnnotatedCodedReading.readAt operations bound value) rho)
      ((model heads constants).denote (AnnotatedCodedReading.readAt operations bound type) rho) ↔ _
    rw [denote_readAt,denote_readAt]
    rfl
  | equality context first second type =>
    change ((model heads constants).denote (AnnotatedCodedReading.readAt operations bound first) rho =
      (model heads constants).denote (AnnotatedCodedReading.readAt operations bound second) rho ∧
      setMember ((model heads constants).denote (AnnotatedCodedReading.readAt operations bound first) rho)
      ((model heads constants).denote (AnnotatedCodedReading.readAt operations bound type) rho)) ↔ _
    simp only [denote_readAt]
    rfl
  | sub context first second =>
    change (∀ point : ZFSet.{u}, True →
      setMember point ((model heads constants).denote (weaken (σ := object) (AnnotatedCodedReading.readAt operations bound first))
        ((model heads constants).toPreModel.extend (σ := object) rho point)) →
      setMember point ((model heads constants).denote (weaken (σ := object) (AnnotatedCodedReading.readAt operations bound second))
        ((model heads constants).toPreModel.extend (σ := object) rho point))) ↔ _
    simp only [HOL.Soundness.denote_weaken,denote_readAt,true_implies]
    rfl

def judgmentAt (statement : CStatement Head) {Γ : Ctx Unit}
    (bound : Fin (statementArity statement) → Term (Symbol Head) Γ object) : Formula (Symbol Head) Γ :=
  .imp (contextAt (statementContext statement) bound) (statementAt statement bound)

/-- All source rules use the existing semantic theorem. This establishes
truth of the generated HOL formula in the stated model; it constructs no
retained HOL proof and assumes no completeness of that proof calculus. -/
theorem judgmentAt_holds {R : Rules Head} {P : ChurchRules R}
    (interpretation : SetModel heads constants P) {statement : CStatement Head}
    (derivation : CDerivable P statement) {Γ : Ctx Unit}
    (bound : Fin (statementArity statement) → Term (Symbol Head) Γ object)
    (rho : (model heads constants).Valuation Γ) :
    ((model heads constants).denote (judgmentAt statement bound) rho).down := by
  change ((model heads constants).denote (contextAt (statementContext statement) bound) rho).down →
    ((model heads constants).denote (statementAt statement bound) rho).down
  intro admitted
  have sat := (denote_contextAt heads constants (statementContext statement) bound rho).mp admitted
  apply (denote_statementAt heads constants statement bound rho).mpr
  have sound := TowerInterpretation.CDerivable.sound interpretation derivation
  cases statement <;> exact sound _ sat

#print axioms denote_readAt
#print axioms judgmentAt_holds
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL
