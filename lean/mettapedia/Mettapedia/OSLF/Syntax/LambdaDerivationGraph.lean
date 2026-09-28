import Mettapedia.OSLF.Syntax.LambdaCategoricalModel
import Mettapedia.OSLF.Syntax.FreePresheafEventExtension
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Proof-relevant events for the four-rule lambda presentation

An event is a derivation tree, retaining whether beta, application congruence,
or binder congruence generated it. Source and target are computed from that
tree. Substitution transports complete events, not only their endpoint
relation; its identity, composition, and endpoint laws are proved below.
The event object and its endpoint image are distinct semantic data.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaDerivationGraph

open CategoryTheory
open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaCategoricalModel
open Mettapedia.OSLF.Binding.LambdaReductionSubobject
open Mettapedia.OSLF.Binding.BinderLocalPremise
open Mettapedia.OSLF.Binding.FreePresheafEventExtension

/-- A derivation ticket, with its rule and premises retained as data. -/
inductive Event : Ctx sig → Type where
  | beta {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term)
      (arg : Term sig Γ .term) : Event Γ
  | appCongL {Γ : Ctx sig} (arg : Term sig Γ .term)
      (premise : Event Γ) : Event Γ
  | appCongR {Γ : Ctx sig} (funTerm : Term sig Γ .term)
      (premise : Event Γ) : Event Γ
  | lamCong {Γ : Ctx sig} (premise : Event (.term :: Γ)) : Event Γ

/-- The left endpoint of a derivation. -/
def source : {Γ : Ctx sig} → Event Γ → Term sig Γ .term
  | _, .beta body arg => appT (lamT body) arg
  | _, .appCongL arg premise => appT (source premise) arg
  | _, .appCongR funTerm premise => appT funTerm (source premise)
  | _, .lamCong premise => lamT (source premise)

/-- The right endpoint of a derivation. -/
def target : {Γ : Ctx sig} → Event Γ → Term sig Γ .term
  | _, .beta body arg => inst body arg
  | _, .appCongL arg premise => appT (target premise) arg
  | _, .appCongR funTerm premise => appT funTerm (target premise)
  | _, .lamCong premise => lamT (target premise)

/-- Forgetting the derivation ticket yields exactly a source reduction. -/
theorem denotes : ∀ {Γ : Ctx sig} (event : Event Γ),
    LambdaContextualRung.Step Γ (source event) (target event)
  | _, .beta body arg => .beta body arg
  | _, .appCongL arg premise => .appCongL arg (denotes premise)
  | _, .appCongR funTerm premise => .appCongR funTerm (denotes premise)
  | _, .lamCong premise => .lamCong (denotes premise)

/-- A simultaneous substitution transports a complete derivation tree. -/
def map {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ) : Event Γ → Event Δ
  | .beta body arg =>
      .beta (bind (liftSub sigma [.term]) body) (bind sigma arg)
  | .appCongL arg premise =>
      .appCongL (bind sigma arg) (map sigma premise)
  | .appCongR funTerm premise =>
      .appCongR (bind sigma funTerm) (map sigma premise)
  | .lamCong premise =>
      .lamCong (map (liftSub sigma [.term]) premise)

/-- The source endpoint commutes with substitution of events. -/
theorem source_map {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ) :
    ∀ event : Event Γ, source (map sigma event) = bind sigma (source event)
  | .beta body arg => by
      simp only [map, source, bind_appT, bind_lamT]
  | .appCongL arg premise => by
      simp only [map, source, bind_appT, source_map sigma premise]
  | .appCongR funTerm premise => by
      simp only [map, source, bind_appT, source_map sigma premise]
  | .lamCong premise => by
      simp only [map, source, bind_lamT,
        source_map (liftSub sigma [.term]) premise]

/-- The target endpoint commutes with substitution, including beta plugging. -/
theorem target_map {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ) :
    ∀ event : Event Γ, target (map sigma event) = bind sigma (target event)
  | .beta body arg => by
      simp only [map, target]
      exact (ContextualLinearSubstitution.bind_inst sigma body arg).symm
  | .appCongL arg premise => by
      simp only [map, target, bind_appT, target_map sigma premise]
  | .appCongR funTerm premise => by
      simp only [map, target, bind_appT, target_map sigma premise]
  | .lamCong premise => by
      simp only [map, target, bind_lamT,
        target_map (liftSub sigma [.term]) premise]

/-- Substituting variables leaves every derivation ticket unchanged. -/
theorem map_id : ∀ {Γ : Ctx sig} (event : Event Γ),
    map (fun _ v => Term.var v) event = event
  | _, .beta body arg => by
      simp only [map, liftSub_var]
      exact congrArg₂ Event.beta (bind_id body) (bind_id arg)
  | _, .appCongL arg premise => by
      simp only [map, map_id premise]
      exact congrArg (fun term => Event.appCongL term premise) (bind_id arg)
  | _, .appCongR funTerm premise => by
      simp only [map, map_id premise]
      exact congrArg (fun term => Event.appCongR term premise) (bind_id funTerm)
  | _, .lamCong premise => by
      simp only [map, liftSub_var]
      exact congrArg Event.lamCong (map_id premise)

/-- Transporting a derivation by two substitutions equals transport by
their composite, including the lifted substitution below a binder. -/
theorem map_comp {Γ Δ Θ : Ctx sig}
    (sigma : Sub sig Γ Δ) (tau : Sub sig Δ Θ) :
    ∀ event : Event Γ,
      map tau (map sigma event) =
        map (fun sort v => bind tau (sigma sort v)) event
  | .beta body arg => by
      simp only [map]
      apply congrArg₂ Event.beta
      · rw [bind_comp (liftSub sigma [.term]) (liftSub tau [.term]) body]
        rw [liftSub_comp sigma tau [.term]]
      · exact bind_comp sigma tau arg
  | .appCongL arg premise => by
      simp only [map, map_comp sigma tau premise]
      exact congrArg (fun term => Event.appCongL term _) (bind_comp sigma tau arg)
  | .appCongR funTerm premise => by
      simp only [map, map_comp sigma tau premise]
      exact congrArg (fun term => Event.appCongR term _) (bind_comp sigma tau funTerm)
  | .lamCong premise => by
      simp only [map, map_comp (liftSub sigma [.term])
        (liftSub tau [.term]) premise]
      rw [liftSub_comp sigma tau [.term]]

/-- A substitution-indexed presheaf of retained derivation tickets. -/
def eventPresheaf : Base ⥤ Type where
  obj X := Event X.unop.vars
  map f := TypeCat.ofHom (map f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro event
    exact map_id event
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro event
    exact (map_comp f.unop g.unop event).symm

/-- Source endpoints vary naturally over context substitution. -/
def sourceNatural : eventPresheaf ⟶ Programs where
  app X := TypeCat.ofHom source
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro event
    exact source_map f.unop event

/-- Target endpoints vary naturally, including below binders. -/
def targetNatural : eventPresheaf ⟶ Programs where
  app X := TypeCat.ofHom target
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro event
    exact target_map f.unop event

/-- The proof-relevant source presentation is an internal graph over its
program presheaf. -/
def graph : Graph Programs where
  edge := eventPresheaf
  source := sourceNatural
  target := targetNatural

/-- Forget an event's rule tree while retaining its endpoint pair and its
proof of membership in the least reduction subfunctor. -/
def incidence : eventPresheaf ⟶ reduction.toFunctor where
  app X := TypeCat.ofHom (fun event =>
    ⟨(⟨Srt.term, source event, target event⟩ : rootPairs sig X.unop.vars),
      denotes event⟩)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro event
    apply Subtype.ext
    change (⟨Srt.term, source (map f.unop event),
        target (map f.unop event)⟩ : rootPairs sig Y.unop.vars) =
      ⟨Srt.term, bind f.unop (source event), bind f.unop (target event)⟩
    exact congrArg
      (fun p : Term sig Y.unop.vars .term × Term sig Y.unop.vars .term =>
        (⟨Srt.term, p⟩ : rootPairs sig Y.unop.vars))
      (Prod.ext (source_map f.unop event) (target_map f.unop event))

/-- Every source derivation has a retained event ticket. The induction is
into an existence proposition; it does not eliminate a proof into `Type`. -/
theorem event_exists_of_step : ∀ {Γ : Ctx sig}
    {left right : Term sig Γ .term},
    LambdaContextualRung.Step Γ left right →
      ∃ event : Event Γ, source event = left ∧ target event = right
  | _, _, _, .beta body arg => ⟨.beta body arg, rfl, rfl⟩
  | _, _, _, .appCongL arg premise => by
      obtain ⟨event, leftEq, rightEq⟩ := event_exists_of_step premise
      exact ⟨.appCongL arg event,
        congrArg (fun term => appT term arg) leftEq,
        congrArg (fun term => appT term arg) rightEq⟩
  | _, _, _, .appCongR funTerm premise => by
      obtain ⟨event, leftEq, rightEq⟩ := event_exists_of_step premise
      exact ⟨.appCongR funTerm event,
        congrArg (appT funTerm) leftEq,
        congrArg (appT funTerm) rightEq⟩
  | _, _, _, .lamCong premise => by
      obtain ⟨event, leftEq, rightEq⟩ := event_exists_of_step premise
      exact ⟨.lamCong event, congrArg lamT leftEq, congrArg lamT rightEq⟩

/-- The endpoint image of retained derivations is exactly the least
four-rule reduction subobject at every context. -/
theorem incidence_surjective (X : Base) :
    Function.Surjective (incidence.app X) := by
  rintro ⟨⟨sort, sourceTerm, targetTerm⟩, step⟩
  cases sort
  obtain ⟨event, sourceEq, targetEq⟩ := event_exists_of_step step
  refine ⟨event, ?_⟩
  apply Subtype.ext
  change (⟨Srt.term, source event, target event⟩ : rootPairs sig X.unop.vars) =
    ⟨Srt.term, sourceTerm, targetTerm⟩
  rw [sourceEq, targetEq]

/-- The event-to-relation factor is pointwise surjective and therefore an
epimorphism in the presheaf category. -/
theorem incidence_epi : Epi incidence := by
  apply (NatTrans.epi_iff_epi_app incidence).2
  intro X
  exact (epi_iff_surjective (incidence.app X)).2 (incidence_surjective X)

/-- The natural paired source/target map before taking its image. -/
def endpoints : eventPresheaf ⟶ rootPairsPresheaf sig where
  app X := TypeCat.ofHom (fun event =>
    (⟨Srt.term, source event, target event⟩ : rootPairs sig X.unop.vars))
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro event
    change (⟨Srt.term, source (map f.unop event),
        target (map f.unop event)⟩ : rootPairs sig Y.unop.vars) =
      ⟨Srt.term, bind f.unop (source event), bind f.unop (target event)⟩
    exact congrArg
      (fun p : Term sig Y.unop.vars .term × Term sig Y.unop.vars .term =>
        (⟨Srt.term, p⟩ : rootPairs sig Y.unop.vars))
      (Prod.ext (source_map f.unop event) (target_map f.unop event))

/-- The paired endpoint map factors through the reduction inclusion. -/
theorem endpoints_factorization :
    incidence ≫ reduction.ι = endpoints := by
  ext X event
  rfl

/-- The image of the proof-relevant event presheaf is exactly the least
four-rule reduction subfunctor. No event identity is identified before this
image operation. -/
theorem range_endpoints_eq_reduction :
    Subfunctor.range endpoints = reduction := by
  ext X pair
  constructor
  · rintro ⟨event, rfl⟩
    exact (incidence.app X event).property
  · intro membership
    obtain ⟨event, equality⟩ := incidence_surjective X ⟨pair, membership⟩
    exact ⟨event, congrArg Subtype.val equality⟩

/-- A beta event whose argument is the surrounding binder's variable. -/
def openBetaEvent : Event [.term] :=
  .beta (.var .zero) (.var .zero)

/-- The binder-congruence event retains that open beta as its premise. -/
def closedLamEvent : Event [] := .lamCong openBetaEvent

theorem closedLamEvent_endpoints :
    source closedLamEvent =
      lamT (appT (lamT (.var .zero)) (.var .zero)) ∧
    target closedLamEvent = lamT (.var .zero) := by
  constructor <;> rfl

/-- The negative control holds at the event level as well as at the image:
a bare variable cannot be the source of a derivation ticket. -/
theorem no_event_from_variable {Γ : Ctx sig} (v : Var Γ .term) :
    ¬ ∃ event : Event Γ, source event = .var v := by
  rintro ⟨event, equality⟩
  have step := denotes event
  rw [equality] at step
  exact variable_has_no_step v step

/-- The untyped self-application body and its closed abstraction. -/
def duplicateBody : Term sig [.term] .term :=
  appT (.var .zero) (.var .zero)

def omegaFunction : Term sig [] .term := lamT duplicateBody

/-- Ω contracts to itself in one beta step. -/
def omega : Term sig [] .term := appT omegaFunction omegaFunction

def omegaEvent : Event [] := .beta duplicateBody omegaFunction

theorem omegaEvent_loop :
    source omegaEvent = omega ∧ target omegaEvent = omega := by
  constructor <;> rfl

/-- Two different subterm occurrences of the Ω self-loop. -/
def leftOmegaEvent : Event [] := .appCongL omega omegaEvent
def rightOmegaEvent : Event [] := .appCongR omega omegaEvent

theorem omega_events_distinct : leftOmegaEvent ≠ rightOmegaEvent := by
  intro equality
  cases equality

/-- Both retained tickets connect exactly the same source and target term. -/
theorem omega_events_same_endpoints :
    source leftOmegaEvent = source rightOmegaEvent ∧
    target leftOmegaEvent = target rightOmegaEvent := by
  rcases omegaEvent_loop with ⟨sourceEq, targetEq⟩
  constructor
  · simp only [leftOmegaEvent, rightOmegaEvent, source, sourceEq]
  · simp only [leftOmegaEvent, rightOmegaEvent, target, targetEq]

/-- The paired endpoint map is not injective even without duplicated rules:
it forgets which side of the application performed the Ω self-loop. -/
theorem endpoints_not_injective :
    ¬ Function.Injective
      (endpoints.app (Opposite.op (Syntactic.Ctxt.mk ([] : Ctx sig)))) := by
  intro injective
  have same : endpoints.app (Opposite.op (Syntactic.Ctxt.mk ([] : Ctx sig)))
      leftOmegaEvent =
      endpoints.app (Opposite.op (Syntactic.Ctxt.mk ([] : Ctx sig)))
        rightOmegaEvent := by
    rcases omega_events_same_endpoints with ⟨sourceEq, targetEq⟩
    change (⟨Srt.term, source leftOmegaEvent, target leftOmegaEvent⟩ :
        rootPairs sig []) =
      ⟨Srt.term, source rightOmegaEvent, target rightOmegaEvent⟩
    exact congrArg
      (fun p : Term sig [] .term × Term sig [] .term =>
        (⟨Srt.term, p⟩ : rootPairs sig []))
      (Prod.ext sourceEq targetEq)
  exact omega_events_distinct (injective same)

end Mettapedia.OSLF.Binding.LambdaDerivationGraph
