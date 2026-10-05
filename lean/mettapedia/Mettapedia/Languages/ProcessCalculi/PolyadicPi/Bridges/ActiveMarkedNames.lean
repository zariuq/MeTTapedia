import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking

/-!
# Actual channel and payload keys for traced active prefixes

A private binder supplies its own recorded key, while ambient keys are read
from the supplied name environment. The observation records the actual
channel and ordered payload fields of each active prefix. All static
transports preserve target observation inclusion, including private-name
exchange and extrusion. This constrains the names of recovered origins;
constructor marks alone would not establish channel ownership.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarkedNames

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveHeaderInvariant
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking

universe u v

abbrev Environment (Key : Type v) (Γ : Ctx sig) := Var Γ Srt.nm → Key

def extend {Key : Type v} {Γ : Ctx sig} (fresh : Key)
    (environment : Environment Key Γ) : Environment Key (.nm :: Γ)
  | .zero => fresh
  | .succ old => environment old

def nameKey {Key : Type v} {Γ : Ctx sig} (environment : Environment Key Γ) : Name Γ → Key
  | .var name => environment name
  | .op operator _ => nomatch operator

theorem nameKey_rename {Key : Type v} {Γ Δ : Ctx sig} (reindex : Ren sig Γ Δ)
    (source : Environment Key Γ) (target : Environment Key Δ)
    (consistent : ∀ name, target (reindex _ name) = source name) (name : Name Γ) :
    nameKey target (rename reindex name) = nameKey source name := by
  cases name with
  | var name => exact consistent name
  | op operator _ => cases operator

theorem extend_consistent {Key : Type v} {Γ Δ : Ctx sig} (reindex : Ren sig Γ Δ)
    (source : Environment Key Γ) (target : Environment Key Δ)
    (consistent : ∀ name, target (reindex _ name) = source name) (fresh : Key) :
    ∀ name : Var (Srt.nm :: Γ) Srt.nm,
      extend fresh target (liftRen reindex [.nm] _ name) = extend fresh source name := by
  intro name
  cases name with
  | zero => rfl
  | succ old => exact consistent old

structure Observation (Label : Type u) (Key : Type v) where
  header : Header
  origin : Label
  channel : Key
  fields : List Key
  deriving DecidableEq

/-- Active observations use the actual subject and ordered output fields.
Input bodies remain opaque until communication opens them. -/
def observe {Label : Type u} {Key : Type v} (binderKey : Label → Key) :
    {Γ : Ctx sig} → ActiveMarking.Tree Label → Proc Γ → Environment Key Γ → Set (Observation Label Key)
  | _, _, .var _, _ => ∅
  | _, _, .op .nil .nil, _ => ∅
  | _, marked, .op .par (.cons p (.cons q .nil)), environment => match marked with
      | .par first second => observe binderKey first p environment ∪ observe binderKey second q environment
      | _ => ∅
  | _, marked, .op .inp1 (.cons channel (.cons _ .nil)), environment => match marked with
      | .inp1 origin _ => {⟨.input1, origin, nameKey environment channel, []⟩}
      | _ => ∅
  | _, marked, .op .inp2 (.cons channel (.cons _ .nil)), environment => match marked with
      | .inp2 origin _ => {⟨.input2, origin, nameKey environment channel, []⟩}
      | _ => ∅
  | _, marked, .op .out1 (.cons channel (.cons datum .nil)), environment => match marked with
      | .out1 origin => {⟨.output1, origin, nameKey environment channel, [nameKey environment datum]⟩}
      | _ => ∅
  | _, marked, .op .out2 (.cons channel (.cons first (.cons second .nil))), environment => match marked with
      | .out2 origin =>
          {⟨.output2, origin, nameKey environment channel, [nameKey environment first, nameKey environment second]⟩}
      | _ => ∅
  | _, marked, .op .nu (.cons body .nil), environment => match marked with
      | .nu origin inner => observe binderKey inner body (extend (binderKey origin) environment)
      | _ => ∅
  | _, marked, .op .rep (.cons body .nil), environment => match marked with
      | .rep inner => observe binderKey inner body environment
      | _ => ∅
termination_by _ _marked process _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

/-- Coherent ambient reindexing preserves the complete active observation,
including channel identity and the order of binary fields. -/
theorem observe_rename {Label : Type u} {Key : Type v} (binderKey : Label → Key) :
    ∀ {Γ Δ : Ctx sig} (reindex : Ren sig Γ Δ) (process : Proc Γ) (marked : ActiveMarking.Tree Label)
      (source : Environment Key Γ) (target : Environment Key Δ)
      (_consistent : ∀ name, target (reindex _ name) = source name),
      observe binderKey marked (rename reindex process) target = observe binderKey marked process source
  | _, _, _, .var _, marked, _, _, _ => by simp only [rename, observe]
  | _, _, _, .op .nil .nil, marked, _, _, _ => by simp only [rename, renameArgs, observe]
  | _, _, reindex, .op .par (.cons p (.cons q .nil)), marked, source, target, consistent => by
      cases marked <;> simp only [rename, renameArgs, liftRen, observe]
      rename_i first second
      rw [observe_rename binderKey reindex p first source target consistent,
        observe_rename binderKey reindex q second source target consistent]
  | _, _, reindex, .op .inp1 (.cons channel (.cons body .nil)), marked, source, target, consistent => by
      cases marked <;> simp only [rename, renameArgs, liftRen, observe]
      simp only [nameKey_rename reindex source target consistent]
  | _, _, reindex, .op .inp2 (.cons channel (.cons body .nil)), marked, source, target, consistent => by
      cases marked <;> simp only [rename, renameArgs, liftRen, observe]
      simp only [nameKey_rename reindex source target consistent]
  | _, _, reindex, .op .out1 (.cons channel (.cons datum .nil)), marked, source, target, consistent => by
      cases marked <;> simp only [rename, renameArgs, liftRen, observe]
      simp only [nameKey_rename reindex source target consistent]
  | _, _, reindex, .op .out2 (.cons channel (.cons first (.cons second .nil))), marked, source, target, consistent => by
      cases marked <;> simp only [rename, renameArgs, liftRen, observe]
      simp only [nameKey_rename reindex source target consistent]
  | _, _, reindex, .op .nu (.cons body .nil), marked, source, target, consistent => by
      cases marked <;> simp only [rename, renameArgs, observe]
      rename_i origin inner
      exact observe_rename binderKey (liftRen reindex [.nm]) body inner _ _
        (extend_consistent reindex source target consistent (binderKey origin))
  | _, _, reindex, .op .rep (.cons body .nil), marked, source, target, consistent => by
      cases marked <;> simp only [rename, renameArgs, liftRen, observe]
      rename_i inner
      exact observe_rename binderKey reindex body inner source target consistent
termination_by _ _ _ process _ _ _ _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

/-- The private-binder marks follow the actual binder swap; therefore names
of selected offers are stable, rather than merely their arities. -/
theorem Transport.observations_back {Label : Type u} {Key : Type v}
    (binderKey : Label → Key) {Γ : Ctx sig} {m n : ActiveMarking.Tree Label} {p q : Proc Γ}
    (tracked : Transport m p n q) :
    ∀ environment : Environment Key Γ,
      observe binderKey n q environment ⊆ observe binderKey m p environment := by
  induction tracked with
  | refl => intro environment; exact Set.Subset.refl _
  | trans _ _ firstIH secondIH => intro environment; exact (secondIH environment).trans (firstIH environment)
  | parComm => intro environment; simp only [par, observe, Set.union_comm, Set.Subset.refl]
  | parAssoc => intro environment; simp only [par, observe, Set.union_assoc, Set.Subset.refl]
  | parAssocBack => intro environment; simp only [par, observe, Set.union_assoc, Set.Subset.refl]
  | parUnit => intro environment; simp only [par, nil, observe, Set.union_empty, Set.Subset.refl]
  | parUnitBack => intro environment; simp only [par, nil, observe, Set.union_empty, Set.Subset.refl]
  | nuUnused origin marked process =>
      intro environment
      simp only [nu, observe, weaken]
      rw [observe_rename binderKey _ process marked environment (extend (binderKey origin) environment) (fun _ => rfl)]
  | nuUnusedBack origin marked process =>
      intro environment
      simp only [nu, observe, weaken]
      rw [observe_rename binderKey _ process marked environment (extend (binderKey origin) environment) (fun _ => rfl)]
  | nuPar origin first second process frame =>
      intro environment
      simp only [nu, par, observe, weaken]
      rw [observe_rename binderKey _ frame second environment (extend (binderKey origin) environment) (fun _ => rfl)]
  | nuParBack origin first second process frame =>
      intro environment
      simp only [nu, par, observe, weaken]
      rw [observe_rename binderKey _ frame second environment (extend (binderKey origin) environment) (fun _ => rfl)]
  | nuSwap outer inner marked process =>
      intro environment
      simp only [nu, observe]
      rw [observe_rename binderKey swapRen process marked
        (extend (binderKey inner) (extend (binderKey outer) environment))
        (extend (binderKey outer) (extend (binderKey inner) environment)) (by
          intro name; cases name with
          | zero => rfl
          | succ name => cases name <;> rfl)]
  | nuSwapBack outer inner marked process =>
      intro environment
      simp only [nu, observe]
      rw [observe_rename binderKey swapRen process marked
        (extend (binderKey inner) (extend (binderKey outer) environment))
        (extend (binderKey outer) (extend (binderKey inner) environment)) (by
          intro name; cases name with
          | zero => rfl
          | succ name => cases name <;> rfl)]
  | repUnfold => intro environment; simp only [rep, par, observe, Set.union_self, Set.Subset.refl]
  | repFold => intro environment; simp only [rep, par, observe]; exact Set.subset_union_right
  | par _ _ firstIH secondIH =>
      intro environment
      simp only [par, observe]
      exact Set.union_subset_union (firstIH environment) (secondIH environment)
  | nu origin _ ih => intro environment; simp only [nu, observe]; exact ih (extend (binderKey origin) environment)
  | inp1 => intro environment; simp only [inp1, observe]; exact Set.Subset.refl _
  | inp2 => intro environment; simp only [inp2, observe]; exact Set.Subset.refl _
  | rep _ ih => intro environment; simp only [rep, observe]; exact ih environment

/-- The actual marked telescope extends the ambient key environment in the
same order as its private restrictions. -/
def scopeEnvironment {Label : Type u} {Key : Type v} (binderKey : Label → Key) :
    {Γ Δ : Ctx sig} → {scope : ScopedActiveFrontier.Scope Γ Δ} →
    ScopeMarks Label scope → Environment Key Γ → Environment Key Δ
  | _, _, _, .nil, environment => environment
  | _, _, _, .bind origin rest, environment =>
      scopeEnvironment binderKey rest (extend (binderKey origin) environment)

theorem observe_scope {Label : Type u} {Key : Type v} (binderKey : Label → Key) :
    ∀ {Γ Δ : Ctx sig} {scope : ScopedActiveFrontier.Scope Γ Δ}
      (binders : ScopeMarks Label scope) (marked : ActiveMarking.Tree Label)
      (body : Proc Δ) (environment : Environment Key Γ),
      observe binderKey (binders.close marked) (scope.close body) environment =
        observe binderKey marked body (scopeEnvironment binderKey binders environment)
  | _, _, _, .nil, _, _, _ => rfl
  | _, _, _, .bind origin rest, marked, body, environment => by
      simp only [ScopeMarks.close, ScopedActiveFrontier.Scope.close, nu, observe, scopeEnvironment]
      exact observe_scope binderKey rest marked body (extend (binderKey origin) environment)

def inputObservation {Label : Type u} {Key : Type v} : {Γ : Ctx sig} →
    {redex reduct : Proc Γ} → {selected : ScopedCommunicationInversion.Communication redex reduct} →
    {marked : ActiveMarking.Tree Label} → MarkedCommunication selected marked →
      Environment Key Γ → Observation Label Key
  | _, _, _, _, _, .unary channel _ _ _ input _ _, environment =>
      ⟨.input1, input, nameKey environment channel, []⟩
  | _, _, _, _, _, .binary channel _ _ _ _ input _ _, environment =>
      ⟨.input2, input, nameKey environment channel, []⟩

def outputObservation {Label : Type u} {Key : Type v} : {Γ : Ctx sig} →
    {redex reduct : Proc Γ} → {selected : ScopedCommunicationInversion.Communication redex reduct} →
    {marked : ActiveMarking.Tree Label} → MarkedCommunication selected marked →
      Environment Key Γ → Observation Label Key
  | _, _, _, _, _, .unary channel datum _ output _ _ _, environment =>
      ⟨.output1, output, nameKey environment channel, [nameKey environment datum]⟩
  | _, _, _, _, _, .binary channel first second _ output _ _ _, environment =>
      ⟨.output2, output, nameKey environment channel, [nameKey environment first, nameKey environment second]⟩

theorem communication_subjects_agree {Label : Type u} {Key : Type v} {Γ : Ctx sig}
    {redex reduct : Proc Γ} {selected : ScopedCommunicationInversion.Communication redex reduct}
    {marked : ActiveMarking.Tree Label} (comm : MarkedCommunication selected marked)
    (environment : Environment Key Γ) :
    (inputObservation comm environment).channel = (outputObservation comm environment).channel := by
  cases comm <;> rfl

theorem communication_input_observed {Label : Type u} {Key : Type v} (binderKey : Label → Key)
    {Γ : Ctx sig} {redex reduct : Proc Γ}
    {selected : ScopedCommunicationInversion.Communication redex reduct}
    {marked : ActiveMarking.Tree Label} (comm : MarkedCommunication selected marked)
    (environment : Environment Key Γ) :
    inputObservation comm environment ∈ observe binderKey marked redex environment := by
  cases comm <;> simp only [inputObservation, par, inp1, inp2, out1, out2, observe, Set.mem_union, Set.mem_singleton_iff]
  all_goals exact Or.inr True.intro

theorem communication_output_observed {Label : Type u} {Key : Type v} (binderKey : Label → Key)
    {Γ : Ctx sig} {redex reduct : Proc Γ}
    {selected : ScopedCommunicationInversion.Communication redex reduct}
    {marked : ActiveMarking.Tree Label} (comm : MarkedCommunication selected marked)
    (environment : Environment Key Γ) :
    outputObservation comm environment ∈ observe binderKey marked redex environment := by
  cases comm <;> simp only [outputObservation, par, inp1, inp2, out1, out2, observe, Set.mem_union, Set.mem_singleton_iff]
  all_goals exact Or.inl True.intro

/-- The receiver's actual channel key and origin occur in the original
pre-equation syntax, with its own ambient key assignment. -/
theorem traced_input_observed {Label : Type u} {Key : Type v} (binderKey : Label → Key)
    {Γ : Ctx sig} {original : ActiveMarking.Tree Label} {source target : Proc Γ}
    {exposure : ScopedCommunicationInversion.Exposure source target}
    (traced : TracedExposure original exposure) (environment : Environment Key Γ) :
    inputObservation traced.continuation (scopeEnvironment binderKey traced.binders environment) ∈
      observe binderKey original source environment := by
  apply Transport.observations_back binderKey traced.transport environment
  rw [observe_scope]
  simp only [par, observe, Set.mem_union]
  exact Or.inl (communication_input_observed binderKey traced.continuation _)

/-- The sender's actual channel key and ordered payload keys occur in the
original syntax. The selected rendezvous therefore keeps both sides of its
name comparison, not just the existence of a matching arity. -/
theorem traced_output_observed {Label : Type u} {Key : Type v} (binderKey : Label → Key)
    {Γ : Ctx sig} {original : ActiveMarking.Tree Label} {source target : Proc Γ}
    {exposure : ScopedCommunicationInversion.Exposure source target}
    (traced : TracedExposure original exposure) (environment : Environment Key Γ) :
    outputObservation traced.continuation (scopeEnvironment binderKey traced.binders environment) ∈
      observe binderKey original source environment := by
  apply Transport.observations_back binderKey traced.transport environment
  rw [observe_scope]
  simp only [par, observe, Set.mem_union]
  exact Or.inl (communication_output_observed binderKey traced.continuation _)

/-- The two headers belong to the actual same-arity primitive rule. -/
theorem communication_arities {Label : Type u} {Key : Type v} {Γ : Ctx sig}
    {redex reduct : Proc Γ} {selected : ScopedCommunicationInversion.Communication redex reduct}
    {marked : ActiveMarking.Tree Label} (comm : MarkedCommunication selected marked)
    (environment : Environment Key Γ) :
    ((inputObservation comm environment).header = .input1 ∧
      (outputObservation comm environment).header = .output1) ∨
    ((inputObservation comm environment).header = .input2 ∧
      (outputObservation comm environment).header = .output2) := by
  cases comm
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- Every arbitrary actual class step requires two original active offers on
the same evaluated channel, with their actual primitive arities. -/
theorem step_has_observed_pair {Label : Type u} {Key : Type v} (binderKey : Label → Key)
    (fresh : Label) {Γ : Ctx sig} {original : ActiveMarking.Tree Label} {source target : Proc Γ}
    (fitted : Fits original source) (environment : Environment Key Γ)
    (firing : StepModulo source target) :
    ∃ (input output : Observation Label Key),
      input ∈ observe binderKey original source environment ∧
      output ∈ observe binderKey original source environment ∧
      input.channel = output.channel ∧
      ((input.header = .input1 ∧ output.header = .output1) ∨
       (input.header = .input2 ∧ output.header = .output2)) := by
  rcases modulo_step_has_traced_origins fresh fitted firing with ⟨exposure, ⟨traced⟩⟩
  exact ⟨inputObservation traced.continuation (scopeEnvironment binderKey traced.binders environment),
    outputObservation traced.continuation (scopeEnvironment binderKey traced.binders environment),
    traced_input_observed binderKey traced environment,
    traced_output_observed binderKey traced environment,
    communication_subjects_agree traced.continuation _, communication_arities traced.continuation _⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarkedNames
