import Mettapedia.Languages.Metamath.GroundedSemantics
import Mettapedia.Languages.Metamath.LanguageDefDSL
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises

/-!
# Metamath Simulation Scaffold

First bridge lemmas connecting language-labeled transitions to
`StateCorresponds`.
-/

namespace Mettapedia.Languages.Metamath.Simulation

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.GroundedSemantics
open Mettapedia.Languages.Metamath.LanguageDefDSL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises

/-- Label lookup over the authored Metamath rewrite table. -/
def hasRewriteByName (label : String) : Bool :=
  metamathCore.rewrites.any (fun rw => rw.name == label)

def AuthoredRewriteLabel (label : String) : Prop :=
  ∃ rw, rw ∈ metamathCore.rewrites ∧ (rw.name == label) = true

theorem authoredRewriteLabel_iff_hasRewriteByName_true
    (label : String) :
    AuthoredRewriteLabel label ↔ hasRewriteByName label = true := by
  unfold AuthoredRewriteLabel hasRewriteByName
  constructor
  · intro h
    rcases h with ⟨rw, hrw, hname⟩
    exact List.any_eq_true.mpr ⟨rw, hrw, hname⟩
  · intro h
    rcases List.any_eq_true.mp h with ⟨rw, hrw, hname⟩
    exact ⟨rw, hrw, hname⟩

/-- A language transition is a runtime step whose label is present in the
    authored Metamath rewrite set. -/
def LanguageTransition (rt rt' : RuntimeState) (label : String) : Prop :=
  AuthoredRewriteLabel label ∧ RuntimeState.step? rt label = some rt'

/-- `stepSpec?` is exactly runtime stepping followed by bridge projection. -/
theorem stepSpec?_iff
    (rt : RuntimeState) (label : String) (sp' : SpecState) :
    RuntimeState.stepSpec? rt label = some sp' ↔
      ∃ rt', RuntimeState.step? rt label = some rt' ∧
        RuntimeState.toSpecState? rt' = some sp' := by
  unfold RuntimeState.stepSpec?
  constructor
  · intro h
    cases hstep : RuntimeState.step? rt label with
    | none =>
        simp [hstep] at h
    | some rt' =>
        refine ⟨rt', ?_, ?_⟩
        · simp
        simp [hstep] at h
        exact h
  · intro h
    rcases h with ⟨rt', hstep, hspec⟩
    simp [hstep, hspec]

theorem stepSpec?_sound
    (rt : RuntimeState) (label : String) (sp' : SpecState)
    (h : RuntimeState.stepSpec? rt label = some sp') :
    ∃ rt', RuntimeState.step? rt label = some rt' ∧ StateCorresponds rt' sp' := by
  rcases (stepSpec?_iff rt label sp').1 h with ⟨rt', hrt, hspec⟩
  exact ⟨rt', hrt, RuntimeState.toSpecState?_sound rt' sp' hspec⟩

/-- Completeness direction: if a runtime step exists and the stepped state
    corresponds to `sp'`, then `stepSpec?` returns `sp'`. -/
theorem stepSpec?_complete
    (rt : RuntimeState) (label : String) (rt' : RuntimeState) (sp' : SpecState)
    (hStep : RuntimeState.step? rt label = some rt')
    (hCorr : StateCorresponds rt' sp') :
    RuntimeState.stepSpec? rt label = some sp' := by
  apply (stepSpec?_iff rt label sp').2
  refine ⟨rt', hStep, ?_⟩
  exact RuntimeState.toSpecState?_complete rt' sp' hCorr

theorem languageTransition_stepSpec?_sound
    (rt : RuntimeState) (label : String) (sp' : SpecState)
    (hRule : AuthoredRewriteLabel label)
    (hStep : RuntimeState.stepSpec? rt label = some sp') :
    ∃ rt', LanguageTransition rt rt' label ∧ StateCorresponds rt' sp' := by
  rcases stepSpec?_sound rt label sp' hStep with ⟨rt', hrt, hcorr⟩
  exact ⟨rt', ⟨hRule, hrt⟩, hcorr⟩

theorem languageTransition_stepSpec?_complete
    (rt rt' : RuntimeState) (label : String) (sp' : SpecState)
    (hTrans : LanguageTransition rt rt' label)
    (hCorr : StateCorresponds rt' sp') :
    RuntimeState.stepSpec? rt label = some sp' := by
  exact stepSpec?_complete rt label rt' sp' hTrans.2 hCorr

/-- Under a known authored rewrite label, runtime/spec correspondence is
equivalent to obtaining a `stepSpec?` image. -/
theorem languageTransition_stepSpec?_iff
    (rt : RuntimeState) (label : String) (sp' : SpecState)
    (hRule : AuthoredRewriteLabel label) :
    RuntimeState.stepSpec? rt label = some sp' ↔
      ∃ rt', LanguageTransition rt rt' label ∧ StateCorresponds rt' sp' := by
  constructor
  · intro hStep
    exact languageTransition_stepSpec?_sound rt label sp' hRule hStep
  · intro h
    rcases h with ⟨rt', hTrans, hCorr⟩
    exact languageTransition_stepSpec?_complete rt rt' label sp' hTrans hCorr

theorem languageTransition_stepSpec?_iff_of_hasRewriteByName
    (rt : RuntimeState) (label : String) (sp' : SpecState)
    (hRule : hasRewriteByName label = true) :
    RuntimeState.stepSpec? rt label = some sp' ↔
      ∃ rt', LanguageTransition rt rt' label ∧ StateCorresponds rt' sp' := by
  apply languageTransition_stepSpec?_iff rt label sp'
  exact (authoredRewriteLabel_iff_hasRewriteByName_true label).2 hRule

/-- Runtime stepping along a finite trace of rewrite labels. -/
def RuntimeState.stepMany? (rt : RuntimeState) (labels : List String) : Option RuntimeState :=
  labels.foldlM (fun st lbl => RuntimeState.step? st lbl) rt

/-- Optional spec image after finite runtime trace stepping. -/
def RuntimeState.stepManySpec? (rt : RuntimeState) (labels : List String) : Option SpecState := do
  let rt' ← RuntimeState.stepMany? rt labels
  RuntimeState.toSpecState? rt'

theorem stepManySpec?_iff
    (rt : RuntimeState) (labels : List String) (sp' : SpecState) :
    RuntimeState.stepManySpec? rt labels = some sp' ↔
      ∃ rt', RuntimeState.stepMany? rt labels = some rt' ∧
        RuntimeState.toSpecState? rt' = some sp' := by
  unfold RuntimeState.stepManySpec?
  constructor
  · intro h
    cases hstep : RuntimeState.stepMany? rt labels with
    | none =>
        simp [hstep] at h
    | some rt' =>
        refine ⟨rt', ?_, ?_⟩
        · rfl
        simpa [hstep] using h
  · intro h
    rcases h with ⟨rt', hstep, hspec⟩
    simp [hstep, hspec]

theorem stepManySpec?_sound
    (rt : RuntimeState) (labels : List String) (sp' : SpecState)
    (h : RuntimeState.stepManySpec? rt labels = some sp') :
    ∃ rt', RuntimeState.stepMany? rt labels = some rt' ∧ StateCorresponds rt' sp' := by
  rcases (stepManySpec?_iff rt labels sp').1 h with ⟨rt', hrt, hspec⟩
  exact ⟨rt', hrt, RuntimeState.toSpecState?_sound rt' sp' hspec⟩

theorem stepManySpec?_complete
    (rt : RuntimeState) (labels : List String) (rt' : RuntimeState) (sp' : SpecState)
    (hStep : RuntimeState.stepMany? rt labels = some rt')
    (hCorr : StateCorresponds rt' sp') :
    RuntimeState.stepManySpec? rt labels = some sp' := by
  apply (stepManySpec?_iff rt labels sp').2
  refine ⟨rt', hStep, ?_⟩
  exact RuntimeState.toSpecState?_complete rt' sp' hCorr

/-- A finite language trace transition has only authored labels and follows
runtime trace stepping. -/
def LanguageTraceTransition
    (rt rt' : RuntimeState) (labels : List String) : Prop :=
  (∀ label ∈ labels, AuthoredRewriteLabel label) ∧
    RuntimeState.stepMany? rt labels = some rt'

theorem languageTrace_stepManySpec?_sound
    (rt : RuntimeState) (labels : List String) (sp' : SpecState)
    (hAuthored : ∀ label ∈ labels, AuthoredRewriteLabel label)
    (hStep : RuntimeState.stepManySpec? rt labels = some sp') :
    ∃ rt', LanguageTraceTransition rt rt' labels ∧ StateCorresponds rt' sp' := by
  rcases stepManySpec?_sound rt labels sp' hStep with ⟨rt', hrt, hcorr⟩
  exact ⟨rt', ⟨hAuthored, hrt⟩, hcorr⟩

theorem languageTrace_stepManySpec?_complete
    (rt rt' : RuntimeState) (labels : List String) (sp' : SpecState)
    (hTrans : LanguageTraceTransition rt rt' labels)
    (hCorr : StateCorresponds rt' sp') :
    RuntimeState.stepManySpec? rt labels = some sp' := by
  exact stepManySpec?_complete rt labels rt' sp' hTrans.2 hCorr

theorem languageTrace_stepManySpec?_iff
    (rt : RuntimeState) (labels : List String) (sp' : SpecState)
    (hAuthored : ∀ label ∈ labels, AuthoredRewriteLabel label) :
    RuntimeState.stepManySpec? rt labels = some sp' ↔
      ∃ rt', LanguageTraceTransition rt rt' labels ∧ StateCorresponds rt' sp' := by
  constructor
  · intro hStep
    exact languageTrace_stepManySpec?_sound rt labels sp' hAuthored hStep
  · intro h
    rcases h with ⟨rt', hTrans, hCorr⟩
    exact languageTrace_stepManySpec?_complete rt rt' labels sp' hTrans hCorr

/-- A labeled top-level engine step that witnesses the exact authored rewrite
rule used (before contextual congruence lifting). -/
def EngineLabeledTopStep (p q : Pattern) (label : String) : Prop :=
  ∃ rw, rw ∈ metamathCore.rewrites ∧ rw.name = label ∧
    q ∈ applyRuleWithPremisesUsing RelationEnv.empty metamathCore rw p

/-- Any labeled top-level engine step carries an authored rewrite witness. -/
theorem engineLabeledTopStep_authored
    {p q : Pattern} {label : String}
    (h : EngineLabeledTopStep p q label) :
    AuthoredRewriteLabel label := by
  rcases h with ⟨rw, hrw, hname, _⟩
  refine ⟨rw, hrw, ?_⟩
  simp [hname]

/-- Top-level labeled engine steps embed into contextual one-step rewriting. -/
theorem engineLabeledTopStep_in_context
    {p q : Pattern} {label : String}
    (h : EngineLabeledTopStep p q label) :
    q ∈ rewriteWithContextWithPremises metamathCore p := by
  rcases h with ⟨rw, hrw, _hname, hq⟩
  unfold rewriteWithContextWithPremises
  unfold rewriteWithContextWithPremisesUsing
  rw [List.mem_append]
  left
  unfold rewriteStepWithPremisesUsing
  rw [List.mem_flatMap]
  exact ⟨rw, hrw, hq⟩

/-- Top-level labeled engine steps satisfy the declarative premise-aware
reduction relation directly. -/
theorem engineLabeledTopStep_decl
    {p q : Pattern} {label : String}
    (h : EngineLabeledTopStep p q label) :
    DeclReducesWithPremises RelationEnv.empty metamathCore p q := by
  rcases h with ⟨rw, hrw, _hname, hq⟩
  unfold applyRuleWithPremisesUsing at hq
  rw [List.mem_flatMap] at hq
  rcases hq with ⟨bs0, hbs0, hq⟩
  rw [List.mem_map] at hq
  rcases hq with ⟨bs, hprem, hq⟩
  exact .topRule rw hrw bs0 hbs0 bs hprem hq

/-- Contextual one-step engine rewriting and declarative premise-aware
reduction are equivalent for the authored Metamath language. -/
theorem metamath_engine_context_iff_decl
    {p q : Pattern} :
    q ∈ rewriteWithContextWithPremises metamathCore p ↔
      DeclReducesWithPremises RelationEnv.empty metamathCore p q := by
  constructor
  · intro h
    exact (declReducesWithPremises_iff_langReducesWithPremises
      (lang := metamathCore) (p := p) (q := q)).2 h
  · intro h
    exact (declReducesWithPremises_iff_langReducesWithPremises
      (lang := metamathCore) (p := p) (q := q)).1 h

/-! ## Engine-Level Acceptance Layer (DeclReducesWithPremises) -/

/-- One-step authored Metamath engine reduction at the declarative layer. -/
abbrev LanguageDefStep (p q : Pattern) : Prop :=
  DeclReducesWithPremises RelationEnv.empty metamathCore p q

/-- Many-step authored Metamath engine reduction (reflexive-transitive closure). -/
abbrev LanguageDefAccepts (start finish : Pattern) : Prop :=
  Relation.ReflTransGen LanguageDefStep start finish

/-- Finite list witness for step-by-step declarative reduction. -/
def ReducesAlong : List Pattern → Prop
  | [] => False
  | [_] => True
  | p :: q :: rest => LanguageDefStep p q ∧ ReducesAlong (q :: rest)

/-- Explicit trace witness at the engine layer. -/
structure LanguageDefEngineTraceWitness (start finish : Pattern) where
  trace : List Pattern
  head_eq : trace.head? = some start
  last_eq : trace.getLast? = some finish
  reduces : ReducesAlong trace

/-- Engine-labeled top-step witnesses produce declarative one-step reductions. -/
theorem engineLabeledTopStep_languageDefStep
    {p q : Pattern} {label : String}
    (h : EngineLabeledTopStep p q label) :
    LanguageDefStep p q := by
  exact engineLabeledTopStep_decl h

/-- A single engine-labeled step is a many-step acceptance witness. -/
theorem engineLabeledTopStep_accepts
    {p q : Pattern} {label : String}
    (h : EngineLabeledTopStep p q label) :
    LanguageDefAccepts p q := by
  exact Relation.ReflTransGen.single (engineLabeledTopStep_languageDefStep h)

/-- `LanguageDefStep` is equivalent to contextual engine membership. -/
theorem languageDefStep_iff_engineContext
    {p q : Pattern} :
    LanguageDefStep p q ↔ q ∈ rewriteWithContextWithPremises metamathCore p := by
  simpa [LanguageDefStep] using (metamath_engine_context_iff_decl (p := p) (q := q)).symm

private theorem reducesAlong_cons_to_accepts
    (p : Pattern) (tail : List Pattern) (finish : Pattern)
    (hLast : (p :: tail).getLast? = some finish)
    (hRed : ReducesAlong (p :: tail)) :
    LanguageDefAccepts p finish := by
  induction tail generalizing p finish with
  | nil =>
      simp [ReducesAlong] at hRed
      have hFinish : p = finish := by simpa using hLast
      simpa [hFinish] using (Relation.ReflTransGen.refl : LanguageDefAccepts p p)
  | cons q tail ih =>
      simp [ReducesAlong] at hRed
      rcases hRed with ⟨hpq, hTail⟩
      have hLastTail : (q :: tail).getLast? = some finish := by simpa using hLast
      have hTailAcc : LanguageDefAccepts q finish :=
        ih q finish hLastTail hTail
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single hpq) hTailAcc

/-- Any explicit declarative trace witness yields engine-level acceptance. -/
theorem languageDefEngineTraceWitness_accepts
    {start finish : Pattern}
    (hTrace : LanguageDefEngineTraceWitness start finish) :
    LanguageDefAccepts start finish := by
  rcases hTrace with ⟨trace, hHead, hLast, hRed⟩
  cases trace with
  | nil =>
      simp at hHead
  | cons p tail =>
      have hStart : p = start := by simpa using hHead
      have hAcc : LanguageDefAccepts p finish :=
        reducesAlong_cons_to_accepts p tail finish hLast hRed
      simpa [hStart] using hAcc

/-- A labeled engine trace that records which authored rewrite fires at each
step. -/
def LabeledReducesAlong : List Pattern → List String → Prop
  | [], _ => False
  | [_], [] => True
  | [_], _ :: _ => False
  | _ :: _ :: _, [] => False
  | p :: q :: rest, lbl :: labels =>
      EngineLabeledTopStep p q lbl ∧ LabeledReducesAlong (q :: rest) labels

private theorem labeledReducesAlong_to_reducesAlong :
    ∀ {states labels},
      LabeledReducesAlong states labels → ReducesAlong states
  | [], _, h => False.elim h
  | [_], [], _ => by
      simp [ReducesAlong]
  | [_], _ :: _, h => False.elim h
  | _ :: _ :: _, [], h => False.elim h
  | p :: q :: rest, _lbl :: labels, h => by
      rcases h with ⟨hStepLbl, hTail⟩
      have hStep : LanguageDefStep p q :=
        engineLabeledTopStep_languageDefStep hStepLbl
      have hTailRed : ReducesAlong (q :: rest) :=
        labeledReducesAlong_to_reducesAlong hTail
      simpa [ReducesAlong] using And.intro hStep hTailRed

private theorem labeledReducesAlong_labels_authored :
    ∀ {states labels},
      LabeledReducesAlong states labels →
      ∀ label ∈ labels, AuthoredRewriteLabel label
  | [], _, h => False.elim h
  | [_], [], h => by
      intro label hMem
      cases hMem
  | [_], _ :: _, h => False.elim h
  | _ :: _ :: _, [], h => by
      intro label hMem
      cases hMem
  | _p :: _q :: rest, lbl :: labels, h => by
      rcases h with ⟨hStepLbl, hTail⟩
      intro label hMem
      simp at hMem
      rcases hMem with rfl | hTailMem
      · exact engineLabeledTopStep_authored hStepLbl
      · exact labeledReducesAlong_labels_authored hTail label hTailMem

/-- Explicit engine trace witness carrying both state path and fired rewrite
labels. -/
structure LabeledLanguageDefEngineTraceWitness (start finish : Pattern) where
  trace : List Pattern
  labels : List String
  head_eq : trace.head? = some start
  last_eq : trace.getLast? = some finish
  reduces : LabeledReducesAlong trace labels

/-- Any labeled engine trace witness induces declarative engine acceptance. -/
theorem labeledLanguageDefEngineTraceWitness_accepts
    {start finish : Pattern}
    (hTrace : LabeledLanguageDefEngineTraceWitness start finish) :
    LanguageDefAccepts start finish := by
  rcases hTrace with ⟨trace, labels, hHead, hLast, hRedLbl⟩
  have hRed : ReducesAlong trace :=
    labeledReducesAlong_to_reducesAlong hRedLbl
  exact languageDefEngineTraceWitness_accepts ⟨trace, hHead, hLast, hRed⟩

/-- Labels carried by a labeled engine trace are all authored rewrite names. -/
theorem labeledLanguageDefEngineTraceWitness_labels_authored
    {start finish : Pattern}
    (hTrace : LabeledLanguageDefEngineTraceWitness start finish) :
    ∀ label ∈ hTrace.labels, AuthoredRewriteLabel label := by
  rcases hTrace with ⟨trace, labels, _hHead, _hLast, hRedLbl⟩
  exact labeledReducesAlong_labels_authored hRedLbl

example : hasRewriteByName "BeginLower" = true := by native_decide
example : hasRewriteByName "CompileLinearizeDone" = true := by native_decide
example : hasRewriteByName "DefinitelyMissingRule" = false := by native_decide

example : AuthoredRewriteLabel "BeginLower" := by
  exact (authoredRewriteLabel_iff_hasRewriteByName_true "BeginLower").2 (by native_decide)

example : ¬ AuthoredRewriteLabel "DefinitelyMissingRule" := by
  intro h
  have hTrue : hasRewriteByName "DefinitelyMissingRule" = true :=
    (authoredRewriteLabel_iff_hasRewriteByName_true "DefinitelyMissingRule").1 h
  have hFalse : hasRewriteByName "DefinitelyMissingRule" = false := by native_decide
  exact Bool.false_ne_true (hFalse.trans hTrue)

example (rt : RuntimeState) :
    RuntimeState.stepMany? rt [] = some rt := by
  rfl

end Mettapedia.Languages.Metamath.Simulation
