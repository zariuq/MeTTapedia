import Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTaCollection
import Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTaFrontier
import Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTaQuery
import Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTaPublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Laws
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ElaborationHygiene
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.WellFormedRuns

/-!
# Transform-MeTTa argument demand and explicit activation

Both presets lower into the same scoped computations. The primitive demand
table is supplied by the language implementation. Held syntax keeps its
original term, even when that term contains an explicit activation.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTa
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open SourceLanguage SourceLanguage.Elaboration Hosting

inductive Preset where | native | eager
  deriving DecidableEq

def Preset.params (preset : Preset) (primitive : String → Bool) : Params :=
  ⟨fun f _ => if primitive f || preset == .eager then .value else .data, false, true⟩

mutual

/-- The producer of a collector belongs under its delimiter. Even an
explicit `run` in that producer is part of the suspended source. -/
private def holdCollectorOperands : View → View
  | .call orig head [producer] =>
      .call orig head [if Collection.collectorHead head then
        .holdMark producer.orig producer.orig else holdCollectorOperands producer]
  | .call orig head args => .call orig head (holdCollectorArgs args)
  | .runMark orig inside => .runMark orig (holdCollectorOperands inside)
  | other => other

private def holdCollectorArgs : List View → List View
  | [] => []
  | arg :: rest => holdCollectorOperands arg :: holdCollectorArgs rest

end

open ElaborationHygiene in
mutual

private theorem holdCollectorOperands_within {A : Name mkeys → Prop} :
    ∀ v : View, NamesWithin A v → NamesWithin A (holdCollectorOperands v)
  | .call _ head [producer], within => by
      refine ⟨within.1, ?_, trivial⟩
      by_cases collect : Collection.collectorHead head
      · rw [if_pos collect]
        exact ⟨within.2.1.orig, within.2.1.orig⟩
      · rw [if_neg collect]
        exact holdCollectorOperands_within producer within.2.1
  | .call _ _ [], within => within
  | .call _ _ (first :: second :: rest), within =>
      ⟨within.1, holdCollectorArgs_within (first :: second :: rest) within.2⟩
  | .runMark _ inside, within => ⟨within.1, holdCollectorOperands_within inside within.2⟩
  | .holdMark _ _, within | .var _ _, within | .symbol _ _, within
  | .inert _, within | .other _, within => within

private theorem holdCollectorArgs_within {A : Name mkeys → Prop} :
    ∀ args : List View, NamesWithin.NamesWithinArgs A args →
      NamesWithin.NamesWithinArgs A (holdCollectorArgs args)
  | [], _ => trivial
  | arg :: rest, within =>
      ⟨holdCollectorOperands_within arg within.1, holdCollectorArgs_within rest within.2⟩

end

def textView (text : MData) : View := holdCollectorOperands (viewAtWith true false text rfl)

def lower (preset : Preset) (primitive : String → Bool) (decls : List Decl)
    (modes : Name mkeys → VarMode) (site : List Nat) (source : SComp) :=
  elabComp (preset.params primitive) decls modes site source textView

def compile (preset : Preset) (primitive : String → Bool) (source : SProgram) :
    SourceLanguage.Program mkeys [] () MTy :=
  let params := preset.params primitive
  ⟨source.equations.map (fun e =>
    ⟨e.site, tuple (sym e.head :: e.params),
      lower preset primitive source.decls (paramModes params source.decls e) (1 :: e.site) e.body⟩),
    fun t => lower preset primitive source.decls (fun _ => .value) [2, freshIndex t] (.text t)⟩

theorem compiled_reading_hygienic (p : Preset) (ops : String → Bool) (source : SProgram) :
    Hygiene.ReadingHygienic (compile p ops source).reflect := by
  constructor
  · intro t; exact ElaborationHygiene.fresh_reading_apart _ _ t (textView t)
  · intro t; exact ElaborationHygiene.fresh_reading_uniform _ _ t (textView t)
      (holdCollectorOperands_within _ (ElaborationHygiene.viewAtWith_within true t rfl false))

theorem collect_holds_producer (preset : Preset) (ops : String → Bool)
    (modes : Name mkeys → VarMode) (site : List Nat) (orig : MData) (head : String)
    (producer : View) (collects : Collection.collectorHead head) :
    elabText (preset.params ops) [] modes site (holdCollectorOperands (.call orig head [producer])) =
      .apply (tuple [sym head, producer.orig]) := by
  simp [holdCollectorOperands, collects, elabText, elabArgs, passOf, finish, declOf]

/-- Source code recovered from a captured datum goes through the original
profile compiler. A runtime-only constant has no authored readback. -/
def readAuthored? (p : Preset) (ops : String → Bool) (source : SProgram) (t : Collection.Datum) :=
  (Collection.authored? t).map fun text => Collection.embedComp ((compile p ops source).reflect text)

theorem read_embedded (p : Preset) (ops : String → Bool) (s : SProgram) (t : MData) :
    readAuthored? p ops s (Collection.embed t) = some (Collection.embedComp ((compile p ops s).reflect t)) := by
  simp [readAuthored?]

theorem handle_has_no_authored_readback (p : Preset) (ops : String → Bool) (s : SProgram) (i : Nat) :
    readAuthored? p ops s (Collection.token i) = none := rfl

/-- Match snapshots its selected row bindings and returns its template as data. -/
def heldMatch (space pattern template : MData) : SComp :=
  .query space pattern (.text (hold template))

theorem lower_heldMatch (p : Preset) (ops ds env path sp pat template) :
    lower p ops ds env path (heldMatch sp pat template) = .query sp pat (.ret template) := rfl

theorem hold_keeps_source (p : Preset) (ops ds env path t) :
    lower p ops ds env path (.text (hold t)) = .ret t := rfl

theorem activate_held_call (p : Preset) (ops env path head) :
    lower p ops [] env path (.text (run (hold (tuple [sym head])))) = .apply (tuple [sym head]) := rfl

theorem activate_held_variable (p : Preset) (ops ds env path site index) :
    lower p ops ds env path (.text (run (hold (mvar site index)))) = .run (mvar site index) := rfl

theorem annotated_agreement (ops ds env path t) (marks : Laws.Annotated (textView t)) :
    lower .native ops ds env path (.text t) = lower .eager ops ds env path (.text t) :=
  Laws.elabText_annotated _ _ _ _ _ _ _ marks

/-- Unmarked ordinary arguments either retain their term or run once at the
argument's lexical site. The two occurrences of a parameter in the callee
refer to the same result of that evaluation. -/
theorem duplicate_demand (env path) :
    let two := tuple [sym "two"]
    let t := tuple [sym "dup", two]
    lower .native (fun _ => false) [] env path (.text t) = .apply t ∧
      lower .eager (fun _ => false) [] env path (.text t) =
        .let_ (path ++ [0]) (slot (path ++ [0])) (.apply two)
          (.apply (tuple [sym "dup", slot (path ++ [0])])) := ⟨rfl, rfl⟩

/-- Compile the actual two `q` definitions under either policy. Explicitly
holding the open argument makes the entry point independent of its demand.
The native unmarked call elaborates to this same entry point. -/
theorem counted_surface (preset : Preset) :
    let eqn : SEquation := ⟨Query.Edges.clause.site, "q", [Query.Edges.tag],
      heldMatch (sym "&self") Query.Edges.clause.pattern Query.Edges.y⟩
    let code : SProgram := ⟨[], [eqn, eqn]⟩
    let p := compile preset (fun _ => false) code
    let q := lower preset (fun _ => false) [] (fun _ => .value) [3]
      (.text (tuple [sym "q", hold Query.Edges.x]))
    ∃ final, AnswerCollection.CollectorRuns numbers.discipline p (fun n => cnum n)
      (AnswerCollection.State.initial (Config.initial (Query.world Query.Edges.facts).spaces q)) final ∧
      ∃ valid, AnswerCollection.reify final valid = some Query.Edges.bag := by
  intro eqn code p q
  exact Query.Edges.source_reifies_target p rfl

/-- Current Nik closes both spellings to an unordered bag. The earlier
ordered collapse proposal is an explicit composition with serialization. -/
def collapseCanonical? {D : Discipline MSig [] ()} {Key : Type} [LinearOrder Key]
    (key : Branch mkeys [] () D.Ty → WithBot Key)
    (state : AnswerCollection.State mkeys [] () D) :
    Option (List (Branch mkeys [] () D.Ty)) := do
  let rows ← state.finish?
  AnswerCollection.serializeBy? key rows

theorem canonical_retains_snapshots {D : Discipline MSig [] ()} {Key : Type} [LinearOrder Key]
    (key : Branch mkeys [] () D.Ty → WithBot Key)
    (state : AnswerCollection.State mkeys [] () D) (valid : state.Valid)
    (sequence : List (Branch mkeys [] () D.Ty)) (completed : collapseCanonical? key state = some sequence) :
    ∃ bag, AnswerCollection.reify state valid = some bag ∧
      (sequence : Multiset (Branch mkeys [] () D.Ty)) = bag.rows := by
  cases finish : state.finish? with
  | none => simp [collapseCanonical?, finish] at completed
  | some rows =>
    obtain ⟨empty, rfl⟩ := (state.finish_some_iff _).mp finish
    simp [collapseCanonical?, finish] at completed
    refine ⟨⟨state.reverseAnswers, fun b hb => valid.answers b (Multiset.mem_coe.mp hb)⟩, ?_, ?_⟩
    · simp [AnswerCollection.reify, empty]
    · exact Multiset.coe_eq_coe.mpr ((AnswerCollection.serialized_rows _ _ _ completed).trans (List.reverse_perm _))

/-- A bare logical input can wake once dereferencing exposes executable
syntax. Its printed variable is insufficient evidence to run it. -/
abbrev Activates (p : SourceLanguage.Program mkeys [] () MTy) := Collection.Activation p

theorem activation_moves (p : SourceLanguage.Program mkeys [] () MTy) (supply : Nat → MClosed)
    (world known text frames pending body) (activated : Activates p known text body) :
    Move numbers.discipline p supply world ⟨known, .eval (.run text), frames, pending⟩ world
      {⟨known, .eval body, frames, pending⟩} := by
  obtain ⟨θ, principal, _, rfl⟩ := activated
  exact .run _ _ _ _ _ θ principal

theorem unbound_input_waits (p : SourceLanguage.Program mkeys [] () MTy) (site index body) :
    ¬ Activates p [] (Toolkit.foD [] site index) body := by
  rintro ⟨θ, principal, ready, _⟩
  have idModel : Models (ContextualFamily.generator (fam mkeys)) ([] : List (Constraint mkeys [] ())) := fun _ h => nomatch h
  have fixed := principal.2 _ _ idModel (Toolkit.fo [] site index)
  rw [ContextualFamily.instantiate_identity] at fixed
  rw [Toolkit.instantiate_foD, fixed] at ready
  contradiction

/-- The two hosted queries are distinct whenever their held templates are. -/
theorem query_encoding_retains_template (p : SourceLanguage.Program mkeys [] () MTy)
    (space pattern : MData) :
    Function.Injective (fun template => start mettaNodes p (.query space pattern (.ret template))) :=
  fun _ _ same => (start_held_query_components mettaNodes p same).2.2

/-- Bidirectional reachable-run correspondence for the call/arrow portion of
a compiled profile, with its precise domain stated on the lowered program. -/
theorem arrow_correspondence (preset : Preset) (primitive : String → Bool) (source : SProgram)
    (query : SComp) (spaces : MClosed → Multiset (Row mkeys [] ())) (supply : Nat → MClosed)
    (site : List Nat) :
    let p := compile preset primitive source
    let q := lower preset primitive source.decls (fun _ => .value) [3] query
    (∀ e ∈ p.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs) →
    q.Scoped [site] → (site :: q.sites).Nodup → ArrowComp q →
    (∀ C, Runs numbers.discipline p supply (Config.initial spaces q) C →
      ∃ frontier : Multiset (Branch mkeys [] () MTy × HostState MSig × Nat),
        ArrowFrontier mettaNodes p C frontier ∧ C.answers (D := numbers.discipline) = frontierAnswers (D := numbers.discipline) mettaNodes frontier ∧
        ∀ x ∈ frontier, Relation.ReflTransGen (Fires mettaNodes p) (start mettaNodes p q) x.2.1) ∧
    (∀ s, Relation.ReflTransGen (Fires mettaNodes p) (start mettaNodes p q) s →
      ∃ C b a, Runs numbers.discipline p supply (Config.initial spaces q) C ∧ b ∈ C.branches ∧
        Represents mettaNodes p C.world.scope b s a ∧ ArrowBranch b) := by
  intro p q equations scope distinct arrow
  constructor
  · intro C run
    obtain ⟨L, represented, reached⟩ := arrow_runs_forward_of_scoped (D := numbers.discipline) (P := p) (supply := supply) mettaNodes spaces q equations scope distinct arrow run
    exact ⟨L, represented, arrowFrontier_answers mettaNodes represented, reached⟩
  · intro s run
    exact arrow_runs_reflected_of_scoped (D := numbers.discipline) (P := p) (supply := supply) mettaNodes spaces q equations scope distinct arrow run

end Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTa
