import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetModel

/-!
# Soundness of the set interpretation for the annotated judgment

A statement of the annotated judgment (`Annotated.CStatement`) *holds* in the set
interpretation (`Holds`) when, at every environment satisfying its context,

* a typing: the term's value lies in the type's value;
* an equality: the two values are equal and lie in the type's value;
* a subtyping: the lower type's value is a subset of the upper type's value.

A *set model* of an annotated package (`SetModel`) interprets the universe
rules of its rule package by closed universes of sets — the existing closure
package `ZFSetReplayInterpretation.UniverseModel`, reused unchanged — together
with equal values for equal heads, declared constants inside the values of
their declared types, and root steps that preserve values wherever the
premises their package requires of them hold.

**Soundness** (`CDerivable.sound`): in a set model every derivable annotated
statement holds. The proof is one induction over all forty rules of
`Annotated.CDerivable`; no rule needs a coherence argument, because the value
of an annotated term is determined by the term. The rule for root steps uses the
induction hypotheses of its premises: a step of a constant that computes holds
where the arguments of its redex are typed, and those typings are premises of
the rule. In `lamCong` the two domains
are equal types, so they denote one set, and the two abstractions denote traces
of graphs over it with equal values (`Holds.lamCong`).

Consequences recorded here:

* typed equality is valid set equality, so the model validates equality
  reflection and `UIP` (`CDerivable.sound_equality`, and the controls module);
* closed types of derivable closed terms are inhabited
  (`CDerivable.inhabited`), so a closed type whose value is empty in a set
  model has no derivable closed inhabitant (`CDerivable.no_closed_inhabitant`).

**The annotated fragment of the candidate judgment** (`InAnnotatedImage`): the
candidate statements that are erasures of annotated derivations. Every
annotated derivation erases to a candidate derivation (`Annotated.CDerivable.erase`),
so the candidate judgment contains the fragment (`inAnnotatedImage_derivable`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (graph sigmaSet mem_sigmaSet sigmaSet_congr)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta tracePiSet_congr)
open ZFSetTraceProofDecoding (truthCode)
open ZFSetReplayInterpretation (UniverseModel)
open Mettapedia.SetTheory

universe u

variable {Head : Type}

section Semantics

variable (heads : Head → ZFSet.{u}) (consts : DeclName → ZFSet.{u})

/-- The meaning of an annotated statement in the set interpretation. -/
def Holds : CStatement Head → Prop
  | .typing Γ t A => ∀ ρ : Env.{u} _, Sat heads consts Γ ρ →
      ev heads consts t ρ ∈ ev heads consts A ρ
  | .equality Γ a b A => ∀ ρ : Env.{u} _, Sat heads consts Γ ρ →
      ev heads consts a ρ = ev heads consts b ρ ∧ ev heads consts a ρ ∈ ev heads consts A ρ
  | .sub Γ A B => ∀ ρ : Env.{u} _, Sat heads consts Γ ρ →
      ev heads consts A ρ ⊆ ev heads consts B ρ

/-- A set model of an annotated package: closed universes for the universe
rules of its rule package, equal values for equal heads, declared constants in
their declared types, and root steps that preserve values where their premises
hold: at every environment satisfying a context in which the premises required
of the step hold. -/
structure SetModel {R : Rules Head} (P : ChurchRules R) : Prop where
  universes : UniverseModel R heads
  headEq : ∀ {h h' : Head}, R.headEq h h' → heads h = heads h'
  constants : ∀ {c : DeclName} {T : CTm Head 0}, P.constantType c = some T →
    consts c ∈ ev heads consts T Fin.elim0
  steps : ∀ {n : Nat} {Γ : CCtx Head n} {l r : CTm Head n} {premises : List (CPremise Head n)},
    P.computation.step l r → P.computation.requires l r premises →
    (∀ premise ∈ premises, Holds heads consts (premise.statement Γ)) →
    ∀ ρ : Env.{u} n, Sat heads consts Γ ρ → ev heads consts l ρ = ev heads consts r ρ

end Semantics

variable {R : Rules Head} {P : ChurchRules R} {heads : Head → ZFSet.{u}}
  {consts : DeclName → ZFSet.{u}}

/-- **Abstractions with equal domains and equal bodies have one value**: equal
domains denote one set, and the two abstractions denote traces of graphs over
it with equal values. -/
theorem Holds.lamCong {n : Nat} {Γ : CCtx Head n} {A A' : CTm Head n}
    {body body' B : CTm Head (n + 1)} {w : Head}
    (domains : Holds heads consts (.equality Γ A A' (.head w)))
    (bodies : Holds heads consts (.equality (.snoc Γ A) body body' B)) :
    Holds heads consts (.equality Γ (.lam A body) (.lam A' body') (.pi A B)) := by
  intro ρ sat
  obtain ⟨eA, -⟩ := domains ρ sat
  have body := fun x (hx : x ∈ ev heads consts A ρ) =>
    bodies (extend ρ x) ((sat_snoc heads consts).mpr ⟨sat, hx⟩)
  refine ⟨?_, traceLam_graph_mem (fun x hx => (body x hx).2)⟩
  change traceLam (graph _ _) = traceLam (graph _ _)
  rw [← eA, graph_congr (fun x hx => (body x hx).1)]

/-- **Soundness.** Every derivable annotated statement holds in every set
model of its package. -/
theorem CDerivable.sound (model : SetModel heads consts P) {s : CStatement Head}
    (d : CDerivable P s) : Holds heads consts s := by
  induction d with
  | headType typed => exact fun _ _ => model.universes.headTyping_mem typed
  | var i => exact fun _ sat => sat i
  | const known _ _ _ =>
      intro ρ _
      change consts _ ∈ ev heads consts (CTm.liftClosed _) ρ
      rw [ev_liftClosed]
      exact model.constants known
  | piForm _ _ _ _ joined ihA ihB =>
      intro ρ sat
      exact model.universes.pi_mem joined (ihA ρ sat) _
        (fun x hx => ihB (extend ρ x) ((sat_snoc heads consts).mpr ⟨sat, hx⟩))
  | sigmaForm _ _ _ _ joined ihA ihB =>
      intro ρ sat
      exact model.universes.sigma_mem joined (ihA ρ sat) _
        (fun x hx => ihB (extend ρ x) ((sat_snoc heads consts).mpr ⟨sat, hx⟩))
  | lamIntro _ _ _ _ _ _ _ ihBody =>
      intro ρ sat
      exact traceLam_graph_mem
        (fun x hx => ihBody (extend ρ x) ((sat_snoc heads consts).mpr ⟨sat, hx⟩))
  | appElim _ _ ihg iha =>
      intro ρ sat
      change traceApp _ _ ∈ ev heads consts (CTm.inst0 _ _) ρ
      rw [ev_inst0]
      exact traceApp_mem_fibre (ihg ρ sat) (iha ρ sat)
  | pairIntro _ _ _ _ _ iha ihb =>
      intro ρ sat
      have hb := ihb ρ sat
      rw [ev_inst0] at hb
      exact mem_sigmaSet.mpr ⟨_, iha ρ sat, _, hb, rfl⟩
  | fstElim _ ih =>
      intro ρ sat
      exact first_mem_sigmaSet (ih ρ sat)
  | sndElim _ ih =>
      intro ρ sat
      change ZFSetOrderedPair.second _ ∈ ev heads consts (CTm.inst0 _ _) ρ
      rw [ev_inst0]
      exact second_mem_sigmaSet (ih ρ sat)
  | idForm _ hu _ _ _ _ _ =>
      intro ρ _
      exact model.universes.identity_mem hu _
  | reflIntro _ _ =>
      intro ρ _
      exact empty_mem_truthCode_eq _
  | sub _ _ iht ihs => exact fun ρ sat => ihs ρ sat (iht ρ sat)
  | conv _ _ _ iht ihe =>
      intro ρ sat
      exact (ihe ρ sat).1 ▸ iht ρ sat
  | refl _ ih => exact fun ρ sat => ⟨rfl, ih ρ sat⟩
  | symm _ ih =>
      intro ρ sat
      obtain ⟨e, m⟩ := ih ρ sat
      exact ⟨e.symm, e ▸ m⟩
  | trans _ _ ih ih' =>
      intro ρ sat
      exact ⟨(ih ρ sat).1.trans (ih' ρ sat).1, (ih ρ sat).2⟩
  | convEq _ _ _ ih ihe =>
      intro ρ sat
      exact ⟨(ih ρ sat).1, (ihe ρ sat).1 ▸ (ih ρ sat).2⟩
  | subEq _ _ ih ihs =>
      intro ρ sat
      exact ⟨(ih ρ sat).1, ihs ρ sat (ih ρ sat).2⟩
  | headEq same _ _ ih _ =>
      intro ρ sat
      exact ⟨model.headEq same, ih ρ sat⟩
  | piCong _ _ _ _ joined ihA ihB =>
      intro ρ sat
      obtain ⟨eA, mA⟩ := ihA ρ sat
      have fibres := fun x (hx : x ∈ ev heads consts _ ρ) =>
        ihB (extend ρ x) ((sat_snoc heads consts).mpr ⟨sat, hx⟩)
      refine ⟨?_, model.universes.pi_mem joined mA _ (fun x hx => (fibres x hx).2)⟩
      change tracePiSet _ _ = tracePiSet _ _
      rw [← eA]
      exact tracePiSet_congr (fun x hx => (fibres x hx).1)
  | sigmaCong _ _ _ _ joined ihA ihB =>
      intro ρ sat
      obtain ⟨eA, mA⟩ := ihA ρ sat
      have fibres := fun x (hx : x ∈ ev heads consts _ ρ) =>
        ihB (extend ρ x) ((sat_snoc heads consts).mpr ⟨sat, hx⟩)
      refine ⟨?_, model.universes.sigma_mem joined mA _ (fun x hx => (fibres x hx).2)⟩
      change sigmaSet _ _ = sigmaSet _ _
      rw [← eA]
      exact sigmaSet_congr (fun x hx => (fibres x hx).1)
  | idCong _ hu _ _ _ iha ihb =>
      intro ρ sat
      refine ⟨?_, model.universes.identity_mem hu _⟩
      change truthCode _ = truthCode _
      rw [(iha ρ sat).1, (ihb ρ sat).1]
  | lamCong _ _ _ _ _ ihA _ ihBody => exact Holds.lamCong ihA ihBody
  | appCong _ _ ihf iha =>
      intro ρ sat
      obtain ⟨ef, mf⟩ := ihf ρ sat
      obtain ⟨ea, ma⟩ := iha ρ sat
      refine ⟨?_, ?_⟩
      · change traceApp _ _ = traceApp _ _
        rw [ef, ea]
      · change traceApp _ _ ∈ ev heads consts (CTm.inst0 _ _) ρ
        rw [ev_inst0]
        exact traceApp_mem_fibre mf ma
  | pairCong _ _ _ _ _ iha ihb =>
      intro ρ sat
      obtain ⟨ea, ma⟩ := iha ρ sat
      obtain ⟨eb, mb⟩ := ihb ρ sat
      rw [ev_inst0] at mb
      refine ⟨?_, mem_sigmaSet.mpr ⟨_, ma, _, mb, rfl⟩⟩
      change ZFSet.pair _ _ = ZFSet.pair _ _
      rw [ea, eb]
  | fstCong _ ih =>
      intro ρ sat
      obtain ⟨e, m⟩ := ih ρ sat
      exact ⟨congrArg ZFSetOrderedPair.first e, first_mem_sigmaSet m⟩
  | sndCong _ ih =>
      intro ρ sat
      obtain ⟨e, m⟩ := ih ρ sat
      refine ⟨congrArg ZFSetOrderedPair.second e, ?_⟩
      change ZFSetOrderedPair.second _ ∈ ev heads consts (CTm.inst0 _ _) ρ
      rw [ev_inst0]
      exact second_mem_sigmaSet m
  | reflCong _ _ =>
      intro ρ _
      exact ⟨rfl, empty_mem_truthCode_eq _⟩
  | betaPi _ _ _ _ _ ihBody iha =>
      intro ρ sat
      have ha := iha ρ sat
      have hb := ihBody (extend ρ _) ((sat_snoc heads consts).mpr ⟨sat, ha⟩)
      change traceApp (traceLam (graph _ _)) _ = ev heads consts (CTm.inst0 _ _) ρ ∧
        traceApp (traceLam (graph _ _)) _ ∈ ev heads consts (CTm.inst0 _ _) ρ
      rw [traceApp_graph_beta _ ha, ev_inst0, ev_inst0]
      exact ⟨rfl, hb⟩
  | betaFst _ _ _ _ _ iha _ =>
      intro ρ sat
      change ZFSetOrderedPair.first (ZFSet.pair _ _) = _ ∧
        ZFSetOrderedPair.first (ZFSet.pair _ _) ∈ _
      rw [ZFSetOrderedPair.first_pair]
      exact ⟨rfl, iha ρ sat⟩
  | betaSnd _ _ _ _ _ _ ihb =>
      intro ρ sat
      change ZFSetOrderedPair.second (ZFSet.pair _ _) = _ ∧
        ZFSetOrderedPair.second (ZFSet.pair _ _) ∈ _
      rw [ZFSetOrderedPair.second_pair]
      exact ⟨rfl, ihb ρ sat⟩
  | root step requires _ _ _ ihPremises ihl _ =>
      intro ρ sat
      exact ⟨model.steps step requires ihPremises ρ sat, ihl ρ sat⟩
  | etaPi _ _ _ ihf ihg ihApp =>
      intro ρ sat
      refine ⟨tracePiSet_ext (ihf ρ sat) (ihg ρ sat) (fun x hx => ?_), ihf ρ sat⟩
      have same := (ihApp (extend ρ x) ((sat_snoc heads consts).mpr ⟨sat, hx⟩)).1
      change traceApp (ev heads consts (CTm.rename wk _) (extend ρ x)) x =
        traceApp (ev heads consts (CTm.rename wk _) (extend ρ x)) x at same
      rwa [ev_rename_wk, ev_rename_wk] at same
  | etaSigma _ _ _ _ ihp ihq ihFst ihSnd =>
      intro ρ sat
      exact ⟨sigmaSet_ext (ihp ρ sat) (ihq ρ sat) (ihFst ρ sat).1 (ihSnd ρ sat).1, ihp ρ sat⟩
  | subEqual _ _ ih =>
      intro ρ sat z hz
      exact (ih ρ sat).1 ▸ hz
  | subUniv below => exact fun _ _ => model.universes.cumulative_subset below
  | subPi _ _ _ _ _ _ _ _ _ ihDom ihCod =>
      intro ρ sat
      change tracePiSet _ _ ⊆ tracePiSet _ _
      rw [← (ihDom ρ sat).1]
      exact tracePiSet_mono
        (fun x hx => ihCod (extend ρ x) ((sat_snoc heads consts).mpr ⟨sat, hx⟩))
  | subSigma _ _ _ _ _ _ _ _ ihDom ihCod =>
      intro ρ sat
      exact sigmaSet_mono (ihDom ρ sat)
        (fun x hx => ihCod (extend ρ x) ((sat_snoc heads consts).mpr ⟨sat, hx⟩))
  | subTrans _ _ ih ih' => exact fun ρ sat z hz => ih' ρ sat (ih ρ sat hz)

/-- Typed equality is set equality. -/
theorem CDerivable.sound_equality (model : SetModel heads consts P) {n : Nat} {Γ : CCtx Head n}
    {a b A : CTm Head n} (d : CEqual P Γ a b A) (ρ : Env.{u} n)
    (sat : Sat heads consts Γ ρ) : ev heads consts a ρ = ev heads consts b ρ :=
  ((CDerivable.sound model d) ρ sat).1

/-- A derivable closed term inhabits the value of its type. -/
theorem CDerivable.inhabited (model : SetModel heads consts P) {t A : CTm Head 0}
    (d : CTyped P .nil t A) : ev heads consts t Fin.elim0 ∈ ev heads consts A Fin.elim0 :=
  (CDerivable.sound model d) Fin.elim0 (sat_nil heads consts Fin.elim0)

/-- **Relative consistency, generic form.** A closed type whose value is
empty in some set model has no derivable closed inhabitant. -/
theorem CDerivable.no_closed_inhabitant (model : SetModel heads consts P) {A : CTm Head 0}
    (empty : ∀ z, z ∉ ev heads consts A Fin.elim0) (t : CTm Head 0) :
    ¬ CTyped P .nil t A :=
  fun d => empty _ (CDerivable.inhabited model d)

/-! ## The annotated fragment of the candidate judgment -/

/-- A candidate statement lies in the annotated fragment of a rule package
when some derivation of an annotation `P` of the package erases to it. -/
def InAnnotatedImage (P : ChurchRules R) (s : Statement Head) : Prop :=
  ∃ s' : CStatement Head, CDerivable P s' ∧ s'.erase = s

/-- The candidate judgment contains the annotated fragment. -/
theorem inAnnotatedImage_derivable {s : Statement Head} (image : InAnnotatedImage P s) :
    Derivable R s := by
  obtain ⟨s', d, rfl⟩ := image
  exact d.erase

/-- Every annotated derivation erases into the fragment. -/
theorem CDerivable.inAnnotatedImage {s : CStatement Head} (d : CDerivable P s) :
    InAnnotatedImage P s.erase :=
  ⟨s, d, rfl⟩

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
