import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.AnswerCollection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Counting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Elaboration
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Nodes
import Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTaQuery
import Mettapedia.Machines.RevisionDependencySet

/-!
# Delimited collection of constrained answers

A saved caller and the other pending alternatives belong to the parent. The
child starts with the caller's knowledge and its own empty continuation.
Finishing a child appends an immutable bag to the answer heap and resumes
the caller with one rigid handle. Reopening that handle reuses the stored
caller identities. Handles are separate operators from authored MeTTa terms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTa.Collection
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage
open Mettapedia.Machines (RevisionDependencySet RevisionEnvironment StoreOccurrenceId)
open Mettapedia.Machines.Cursor.StampedSnapshots (Store)
open Elaboration AnswerCollection

abbrev RuntimeSig := signature MSig (fun _ : Nat => ([], ()))
abbrev keys : Keys RuntimeSig := ⟨MKey, List Nat, MKey.site, MKey.arity, inferInstance⟩
abbrev Datum := Data keys [] ()

instance : DecidableEq RuntimeSig.Srt := inferInstanceAs (DecidableEq Unit)
instance (sort : RuntimeSig.Srt) : DecidableEq (RuntimeSig.Op sort) :=
  inferInstanceAs (DecidableEq
    (MSig.Op sort ⊕ Operator (S := MSig) (fun _ : Nat => ([], ())) sort))

section Tuples
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
variable {A : Type} {decl : A → MetaArity RuntimeSig} {ctx : Ctx RuntimeSig}

private def firstTag : {arities : List (List Unit × Unit)} →
    Args (signature RuntimeSig decl) arities ctx → Option String
  | _, .cons (.op (.inl (.inl (.sym label))) _) _ => some label
  | _, _ => none

private def tagOf {sort : Unit} : Term (signature RuntimeSig decl) ctx sort → Option String
  | .op (.inl _) args => firstTag args
  | _ => none

private def runtimeSymbol (name : String) : Term (signature RuntimeSig decl) ctx () :=
  .op (.inl (.inl (.sym name))) .nil

private def runtimeTuple (n : Nat)
    (args : Args (signature RuntimeSig decl) (List.replicate n ([], ())) [] ) :
    Term (signature RuntimeSig decl) [] () := .op (.inl (.inl (.tup n))) args

private theorem runtimeTuple_inj {n : Nat}
    {xs ys : Args (signature RuntimeSig decl) (List.replicate n ([], ())) []}
    (same : runtimeTuple n xs = runtimeTuple n ys) : xs = ys := by
  unfold runtimeTuple at same
  injection same

private def runtimeNode (kind : Tag) (args : Fin kind.arity → Term (signature RuntimeSig decl) [] ()) :
    Term (signature RuntimeSig decl) [] () :=
  runtimeTuple (kind.arity + 1)
    (Args.cons (bs := []) (runtimeSymbol kind.name) (argsOfFn kind.arity args))

private theorem runtimeNode_tag (kind : Tag) (args : Fin kind.arity → Term (signature RuntimeSig decl) [] ()) :
    tagOf (runtimeNode kind args) = some kind.name := rfl

/-- The same tagged control tuples admit runtime constants in their arguments. -/
def runtimeNodes : Nodes RuntimeSig [] () where
  node kind args := runtimeNode kind args
  instantiate_node σ kind args := by
    unfold runtimeNode
    change runtimeTuple (kind.arity + 1)
      (Args.cons (bs := []) (runtimeSymbol kind.name) (instantiateArgs σ (argsOfFn kind.arity args))) = _
    rw [instantiateArgs_argsOfFn]
  tag_eq same := Tag.name_injective (Option.some.inj
    ((runtimeNode_tag _ _).symm.trans ((congrArg tagOf same).trans (runtimeNode_tag _ _))))
  args_eq {_ _ k args args'} same := by
    change runtimeNode k args = runtimeNode k args' at same
    exact argsOfFn_injective k.arity (Args.cons.inj (runtimeTuple_inj same)).2

end Tuples

mutual
/-- Lift authored syntax and contextual names into the rigid-handle signature.
Object-variable positions and binder arities are preserved. -/
def embed {ctx sort} : Term (signature MSig (fam mkeys)) ctx sort → Term (signature RuntimeSig (fam keys)) ctx sort
  | .var v => .var v
  | .op (.inl op) xs => .op (.inl (.inl op)) (embedArgs xs)
  | .op (.inr (.mk x)) xs => .op (.inr (.mk (⟨x.scopes, x.key⟩ : Name keys))) (embedArgs xs)
def embedArgs {ctx arities} : Args (signature MSig (fam mkeys)) arities ctx →
    Args (signature RuntimeSig (fam keys)) arities ctx
  | .nil => .nil
  | .cons t ts => .cons (embed t) (embedArgs ts)
end

mutual
def authored? {ctx sort} : Term (signature RuntimeSig (fam keys)) ctx sort →
    Option (Term (signature MSig (fam mkeys)) ctx sort)
  | .var v => some (.var v)
  | .op (.inl (.inl op)) xs => return .op (.inl op) (← authoredArgs? xs)
  | .op (.inl (.inr _)) _ => none
  | .op (.inr (.mk x)) xs => return .op (.inr (.mk (⟨x.scopes, x.key⟩ : Name mkeys))) (← authoredArgs? xs)
def authoredArgs? {ctx arities} : Args (signature RuntimeSig (fam keys)) arities ctx →
    Option (Args (signature MSig (fam mkeys)) arities ctx)
  | .nil => some .nil
  | .cons t ts => return .cons (← authored? t) (← authoredArgs? ts)
end

mutual
@[simp] theorem authored_embed : ∀ {ctx sort} (t : Term (signature MSig (fam mkeys)) ctx sort),
    authored? (embed t) = some t
  | _, _, .var _ => rfl
  | _, _, .op (.inl op) xs => by
    change (do return Term.op (S := signature MSig (fam mkeys)) (.inl op) (← authoredArgs? (embedArgs xs))) = _
    rw [authoredArgs_embed xs]; rfl
  | _, _, .op (.inr (.mk x)) xs => by
    change (do return Term.op (S := signature MSig (fam mkeys)) (.inr (.mk x)) (← authoredArgs? (embedArgs xs))) = _
    rw [authoredArgs_embed xs]; rfl
@[simp] theorem authoredArgs_embed : ∀ {ctx arities} (xs : Args (signature MSig (fam mkeys)) arities ctx),
    authoredArgs? (embedArgs xs) = some xs
  | _, _, .nil => rfl
  | _, _, .cons t ts => by
    change (do return Args.cons (← authored? (embed t)) (← authoredArgs? (embedArgs ts))) = _
    rw [authored_embed t, authoredArgs_embed ts]; rfl
end

/-- Carry the source compiler's control into the handle signature. Terms,
binder sites and declared types keep their source meanings. -/
def embedComp {Ty : Type} : Comp mkeys [] () Ty → Comp keys [] () Ty
  | .ret x => .ret (embed x)
  | .run x => .run (embed x)
  | .apply x => .apply (embed x)
  | .let_ s x a b => .let_ s (embed x) (embedComp a) (embedComp b)
  | .choice a b => .choice (embedComp a) (embedComp b)
  | .fail => .fail
  | .query s p b => .query (embed s) (embed p) (embedComp b)
  | .add s x b => .add (embed s) (embed x) (embedComp b)
  | .remove s x b => .remove (embed s) (embed x) (embedComp b)
  | .new s x b => .new s (embed x) (embedComp b)
  | .check ty a => .check ty (embedComp a)
  | .delay s x a b => .delay s (embed x) (embedComp a) (embedComp b)
  | .force x => .force (embed x)

abbrev token (n : Nat) : Datum := .op (.inl (.inr (.mk n))) .nil

theorem token_injective : Function.Injective token := by
  intro i j same
  injection same with _ _ op
  exact congrArg Operator.key (Sum.inr.inj (Sum.inl.inj op))

/-- A public source term, including a source symbol that spells a handle,
cannot equal one of the opaque runtime constants. -/
theorem authored_closed_ne_handle (t : MClosed) (n : Nat) :
    Rigid.includeTerm (fun _ : Nat => (([], ()) : MetaArity MSig)) t ≠
      (.op (.inr (.mk n)) .nil : Term RuntimeSig [] ()) := by
  cases t with
  | var impossible => cases impossible
  | op original args =>
    intro same
    injection same with _ _ op
    cases op

variable (D : Discipline RuntimeSig [] ())
abbrev Heap := List (AnswerSpace keys [] () D)
abbrev Region := Term RuntimeSig [] ()
abbrev Revisions := RevisionEnvironment Region Nat
abbrev ReadSet := RevisionDependencySet Region Nat

structure Delimiter where
  caller : Branch keys [] () D.Ty
  parent : State keys [] () D
  observed : ReadSet := ∅

structure Cursor where
  active : State keys [] () D
  saved : List (Delimiter D)
  heap : Heap D
  revisions : Revisions := ⟨fun _ => 0⟩

variable {D}

/-- The scheduler has selected this caller. The rest of its parent remains
at the delimiter, including already collected and refuted alternatives. -/
def enter (w : World keys [] ()) (caller : Branch keys [] () D.Ty)
    (body : Comp keys [] () D.Ty) (rest : Multiset (Branch keys [] () D.Ty))
    (journal : List (Branch keys [] () D.Ty)) (dead : Multiset (Branch keys [] () D.Ty))
    (stack : List (Delimiter D)) (heap : Heap D) (revisions : Revisions := ⟨fun _ => 0⟩) : Cursor D :=
  ⟨State.initial ⟨w, {⟨caller.store, .eval body, [], caller.pending⟩}⟩,
    ⟨caller, ⟨⟨w, rest⟩, journal, dead⟩, ∅⟩ :: stack, heap, revisions⟩

def restore (k : Delimiter D) (childWorld : World keys [] ()) (id : Nat) : State keys [] () D :=
  let caller := { k.caller with focus := .value (token id) }
  ⟨⟨{k.parent.current.world with scope := childWorld.scope},
      caller ::ₘ k.parent.current.branches⟩, k.parent.reverseAnswers, k.parent.refuted⟩

def close? (c : Cursor D) (valid : c.active.Valid) : Option (Cursor D) := do
  let k :: stack := c.saved | none
  let bag ← reify c.active valid
  return ⟨restore k c.active.current.world c.heap.length, stack, c.heap ++ [bag], c.revisions⟩

def reopen (heap : Heap D) (id : Nat) (world : World keys [] ())
    (caller : Branch keys [] () D.Ty) : Option (Config keys [] () D.Ty) := do
  let bag ← heap[id]?
  return bag.reflect world caller

theorem pending_prevents_return (c : Cursor D) (valid : c.active.Valid)
    (b : Branch keys [] () D.Ty) (pending : b ∈ c.active.current.branches) :
    close? c valid = none := by
  cases h : c.saved <;> simp [close?, h, reify_none_of_pending _ valid _ pending]

/-- A closing step restores exactly the immediately enclosing continuation,
makes a single value in it, and preserves lookup of every prior answer bag. -/
theorem close_spec (c next : Cursor D) (valid : c.active.Valid) (step : close? c valid = some next) :
    ∃ k ks bag, c.saved = k :: ks ∧ reify c.active valid = some bag ∧
      next.active = restore k c.active.current.world c.heap.length ∧ next.saved = ks ∧
      next.heap[c.heap.length]? = some bag ∧
      ∀ i < c.heap.length, next.heap[i]? = c.heap[i]? := by
  cases hs : c.saved with
  | nil => simp [close?, hs] at step
  | cons k ks =>
    cases hb : reify c.active valid with
    | none => simp [close?, hs, hb] at step
    | some bag =>
      simp [close?, hs, hb] at step
      subst next
      exact ⟨k, ks, bag, rfl, rfl, rfl, rfl, by simp, fun i hi => List.getElem?_append_left hi⟩

def unary (head : String) (arg : Datum) : Datum :=
  .op (.inl (.inl (.tup 2))) (.cons (.op (.inl (.inl (.sym head))) .nil) (.cons arg .nil))

/-- Text can be activated once its principal image exposes code. An
unassigned first-order input retains the branch for a later binding. -/
def bare {S : Signature} {κ : Keys S} {Γ : Ctx S} {s : S.Srt} (t : Data κ Γ s) : Bool :=
  match t with
  | .op (.inr (.mk name)) _ => (κ.arity name.key).1.isEmpty
  | _ => false

def Activation {S : Signature} {κ : Keys S} {Γ : Ctx S} {s : S.Srt} {Ty : Type}
    (p : Program κ Γ s Ty) (known : List (Constraint κ Γ s)) (t : Data κ Γ s) (body : Comp κ Γ s Ty) : Prop :=
  ∃ θ, Principal known θ ∧ bare (instantiate θ t) = false ∧ body = p.reflect (instantiate θ t)

def collectorHead (head : String) : Prop := head = "reify" ∨ head = "collapse"

instance (head : String) : Decidable (collectorHead head) :=
  inferInstanceAs (Decidable (head = "reify" ∨ head = "collapse"))

private def isService (code : Comp keys [] () D.Ty) : Prop :=
  ∃ arg, (∃ head, collectorHead head ∧ code = .apply (unary head arg)) ∨
    code = .apply (unary "reflect" arg) ∨ code = .run arg

private def isQuery (code : Comp keys [] () D.Ty) : Bool :=
  match code with
  | .query .. => true
  | _ => false

private def publicWrite : Comp keys [] () D.Ty → Bool
  | .add .. | .remove .. | .new .. => true
  | _ => false

/-- A source move can run under a delimiter when it preserves the public
snapshot. An immediate public write is refused even if it would change no row. -/
def permitsMove (atRoot : Prop) (focus : Focus keys [] () D.Ty) : Prop :=
  match focus with
  | .eval code => ¬ isService (D := D) code ∧ (isQuery (D := D) code = false ∧
      (atRoot ∨ publicWrite (D := D) code = false))
  | _ => True

private abbrev available (stack : List (Delimiter D)) (focus : Focus keys [] () D.Ty) : Prop :=
  permitsMove (stack = []) focus

def selectedBranch (caller : Branch keys [] () D.Ty) (pattern template : Datum) (scope : Nat)
    (row : Row keys [] ()) : Branch keys [] () D.Ty :=
  { caller with
    store := caller.store ++ NativeQuery.MatchKernel.Opened.rowEquations
      (Query.openStoredRow scope row) pattern
    focus := .value template }

/-- Each live row occurrence opens at its own fresh scope. The template
is returned under the extended store and the original continuation. -/
def selectRows (caller : Branch keys [] () D.Ty) (pattern template : Datum) (scope : Nat)
    (view : Store (Row keys [] ())) : List (Nat × Branch keys [] () D.Ty) :=
  (Query.Versioned.liveRows view).map fun (slot, row) =>
    (slot, selectedBranch caller pattern template (scope + slot) row)

def snapshotRows (view : Store (Row keys [] ())) : Multiset (Row keys [] ()) :=
  ((Query.Versioned.liveRows view).map Prod.snd : List (Row keys [] ()))

namespace Read

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Hosting RuleSyntax.SchematicRows
open SourceLanguage.NativeQuery.MatchKernel (observedStore observed_models)
open SourceLanguage.NativeQuery.MatchKernel.Hosted
open Query.Versioned
open Mettapedia.Machines.Cursor
open StampedSnapshots

abbrev names : Interface.Frames.Frame RuntimeSig := ⟨Name keys, fam keys⟩
abbrev frames := Interface.Frames.contextual RuntimeSig
abbrev extensions := RuleSyntax.Contextual.declarations RuntimeSig
abbrev Observed := RuleSyntax.Contextual.Terms RuntimeSig

def issue (control : Nat) (caller : Branch keys [] () D.Ty) (space pattern template : Datum) :
    HostState RuntimeSig :=
  ⟨names, observedStore caller.store, {control},
    fun _ => observe (request runtimeNodes space pattern template (encStack runtimeNodes id caller.frames))⟩

/-- Slots carry the same identity and stamps when used as a closure index. -/
def keyed (view : Store (SourceLanguage.Row keys [] ())) : Store Nat :=
  ⟨view.clock, view.next, fun i => (view.row i).map fun r => ⟨i, r.born, r.death⟩⟩

private theorem keyed_slot (view : Store (SourceLanguage.Row keys [] ())) (i : Nat)
    (row : SourceLanguage.Row keys [] ()) (found : (i, row) ∈ liveRows view) :
    (i, i) ∈ liveRows (keyed view) ∧ (view.row i).map StampedSnapshots.Row.value = some row := by
  obtain ⟨inside, atSlot⟩ := (mem_liveRows view i row).mp found
  cases rowAt : view.row i with
  | none => simp [atTime, rowAt] at atSlot
  | some entry =>
    by_cases here : visible view.clock entry = true
    · have eq := (show entry.value = row from by simpa [atTime, rowAt, here] using atSlot)
      have liveKey : atTime (keyed view) (keyed view).clock i = some (i, i) := by
        simpa [atTime, keyed, rowAt, visible] using here
      exact ⟨(mem_liveRows _ _ _).mpr ⟨inside, liveKey⟩, by simp [eq]⟩
    · simp [atTime, rowAt, here] at atSlot

/-- Opening a row in a scheduler alternative allocates its scope first.
The held transform schema then carries exactly that row's equations and
value at that opening. -/
def closure (scope : Nat) (address : Region) (view : Store (SourceLanguage.Row keys [] ()))
    (i : Nat) : Closure Observed names :=
  let raw := ((view.row i).map StampedSnapshots.Row.value).getD ⟨Rigid.includeTerm (fam keys) address, []⟩
  let row := Query.openStoredRow (scope + i) raw
  Closure.capturedStore (observedStore row.store)
    (observe (fact runtimeNodes (Rigid.includeTerm (fam keys) address) row.atom))

private theorem closure_label (scope : Nat) (address : Region) (view : Store (SourceLanguage.Row keys [] ()))
    (i : Nat) (row : SourceLanguage.Row keys [] ()) (found : (i, row) ∈ liveRows view) :
    (closure scope address view i).schema.value =
      observe (fact runtimeNodes (F := names) (Rigid.includeTerm (fam keys) address)
        (Query.openStoredRow (scope + i) row).atom) := by
  simp only [closure, (keyed_slot view i row found).2, Option.getD_some, Closure.capturedStore]

private theorem ruleMember :
    rule runtimeNodes ∈ ({rule runtimeNodes} : RuleSyntax.Program Observed) := Set.mem_singleton _

theorem candidate_models (control scope : Nat) (caller : Branch keys [] () D.Ty)
    (space pattern template : Datum) (address : Region) (view : Store (SourceLanguage.Row keys [] ()))
    {i : Nat} {row : SourceLanguage.Row keys [] ()} (found : (i, row) ∈ liveRows view)
    (addressed : Determines caller.store space address) {target : Interface.Frames.Frame RuntimeSig}
    (point : Assignment (fam keys) target.arity) (answer : Observed target) :
    let host := issue control caller space pattern template
    let cut := keyed view
    let catalogue := closure scope address view
    let s := openedState runtimeNodes host address cut catalogue i
    let f := readSchema runtimeNodes host address cut catalogue i ruleMember control cut.clock
    let lift := RuleSyntax.Contextual.weakenNames RuntimeSig host.frame (closureAt cut catalogue i).schema.locals
    let b := selectedBranch caller pattern template (scope + i) row
    (Models point b.store ∧ observe (encBranch runtimeNodes (instantiate point) b) = answer) ↔
    ∃ image : Assignment (f.result frames s).frame.arity target.arity,
      (Assignment.compose image (extensions.weaken f.ext)).compose lift = point ∧
      frames.Models image (f.result frames s).knowledge ∧
      instantiateObservation image ((f.result frames s).label (freshId s)) = answer := by
  dsimp only
  let host := issue control caller space pattern template
  let cut := keyed view
  let catalogue := closure scope address view
  let r := Query.openStoredRow (scope + i) row
  obtain ⟨present, opened⟩ := keyed_slot view i row found
  have stored : catalogue i = Closure.capturedStore (Tm := Observed) (a := names) (observedStore r.store)
      (observe (fact runtimeNodes (F := names) (Rigid.includeTerm (fam keys) address) r.atom)) := by
    simp [catalogue, closure, opened, r]
  let stack := encStack runtimeNodes (fun t : Datum => t) caller.frames
  have rowLabel := closure_label scope address view i row found
  have well : (catalogue i).WellFormed := rfl
  have result := schema_answer_models runtimeNodes host address cut catalogue i ruleMember control
    present (Finset.mem_singleton_self _) space pattern template stack rfl
    r.atom rowLabel well point answer
  refine Iff.trans ?_ result
  rw [stored, Closure.readsAt_capturedStore_iff]
  change (Models point (caller.store ++ (r.store ++ [(pattern, r.atom)])) ∧
      observe (returned runtimeNodes (instantiate point template) (encStack runtimeNodes (instantiate point) caller.frames)) =
        answer) ↔ _
  rw [models_append, models_append, models_singleton]
  have hostStore : frames.Models (a := host.frame) (b := target) point host.knowledge ↔
      Models point caller.store := observed_models (future := target) point caller.store
  rw [hostStore, observed_models (future := target)]
  have same : frames.E
      (frames.act (a := names) (b := target) point
        (observe (fact runtimeNodes (F := names) (Rigid.includeTerm (fam keys) address) r.atom)))
      (observe (fact runtimeNodes (F := target) (Rigid.includeTerm target.arity address) (instantiate point pattern))) ↔
      instantiate point pattern = instantiate point r.atom := by
    let addressAt := Rigid.includeTerm (fam keys) address
    let outputAt := fact runtimeNodes (F := target) (Rigid.includeTerm target.arity address)
    have location := Rigid.instantiate_include point address
    have factImage := (instantiate_fact runtimeNodes (F := names) (B := target) point addressAt r.atom).trans
      (congrArg (fun h => fact runtimeNodes (F := target) h (instantiate point r.atom)) location)
    have storedImage : frames.act (a := names) (b := target) point
        (observe (fact runtimeNodes (F := names) addressAt r.atom)) =
        observe (outputAt (instantiate point r.atom)) := congrArg observe factImage
    constructor
    · intro sameFact
      exact (vec2_inj (runtimeNodes.args_eq
        (observe_injective (storedImage.symm.trans sameFact)))).2.symm
    · intro fits
      exact storedImage.trans (congrArg (fun x => observe (outputAt x)) fits.symm)
  have stackImage : instantiate point stack = encStack runtimeNodes (instantiate point) caller.frames := by
    unfold stack
    rw [instantiate_encStack]
  rw [same, stackImage]
  exact ⟨fun ⟨⟨known, rowStore, fits⟩, out⟩ =>
    ⟨known, addressed.2 target.arity point known, ⟨rowStore, fits⟩, out⟩,
    fun ⟨known, _, ⟨rowStore, fits⟩, out⟩ => ⟨⟨known, rowStore, fits⟩, out⟩⟩

/-- Membership in the scheduler's successful alternatives agrees with actual
admission of both firings, at the selected occurrence and the current stamp. -/
theorem candidate_admits (control scope stamp : Nat) (caller : Branch keys [] () D.Ty)
    (space pattern template : Datum) (address : Region) (view : Store (SourceLanguage.Row keys [] ()))
    {i : Nat} {row : SourceLanguage.Row keys [] ()} (found : (i, row) ∈ liveRows view)
    (addressed : Determines caller.store space address) :
    let host := issue control caller space pattern template
    let cut := keyed view
    let catalogue := closure scope address view
    ((openSchema runtimeNodes host address cut catalogue i).Admits frames ∅ ∧
      (readSchema runtimeNodes host address cut catalogue i ruleMember control stamp).Admits frames
        (openedState runtimeNodes host address cut catalogue i)) ↔
    stamp = view.clock ∧ Solvable (selectedBranch caller pattern template (scope + i) row).store := by
  dsimp only
  let host := issue control caller space pattern template
  let cut := keyed view
  let catalogue := closure scope address view
  let stack := encStack runtimeNodes (fun t : Datum => t) caller.frames
  let b := selectedBranch caller pattern template (scope + i) row
  have liveKey := (keyed_slot view i row found).1
  have label := closure_label scope address view i row found
  have well : (catalogue i).WellFormed := rfl
  have admission := schema_admits_iff runtimeNodes host address cut catalogue i ruleMember control stamp
    liveKey (Finset.mem_singleton_self _) space pattern template stack rfl _ label well
  refine Iff.trans admission (and_congr_right fun _ => ?_)
  have reply {target : Interface.Frames.Frame RuntimeSig} (point : Assignment (fam keys) target.arity) :=
    schema_answer_models runtimeNodes host address cut catalogue i ruleMember control
      liveKey (Finset.mem_singleton_self _) space pattern template stack rfl _ label well point
      (observe (encBranch runtimeNodes (instantiate point) b))
  have stackImage {target : Interface.Frames.Frame RuntimeSig} (point : Assignment (fam keys) target.arity) :
      instantiate point stack = encStack runtimeNodes (instantiate point) caller.frames := by
    unfold stack
    rw [instantiate_encStack]
  constructor
  · rintro ⟨target, point, known, located, matched⟩
    have built := (reply point).mp ⟨known, located, matched, by rw [stackImage]; rfl⟩
    have models := (candidate_models control scope caller space pattern template address view found
        addressed point _).mpr built
    exact ⟨target.Names, target.arity, point, models.1⟩
  · rintro ⟨names, arity, point, models⟩
    let target : Interface.Frames.Frame RuntimeSig := ⟨names, arity⟩
    have built := (candidate_models control scope caller space pattern template address view found
        addressed (target := target) point _).mp ⟨models, rfl⟩
    obtain ⟨known, located, matched, _⟩ := (reply (target := target) point).mpr built
    exact ⟨target, point, known, located, matched⟩

open Classical in
/-- The complete census retains the occurrences admitted by both firings. -/
noncomputable def admittedRows (control scope : Nat) (caller : Branch keys [] () D.Ty)
    (space pattern template : Datum) (address : Region) (view : Store (SourceLanguage.Row keys [] ())) :
    List (Nat × SourceLanguage.Row keys [] ()) :=
  let host := issue control caller space pattern template
  let cut := keyed view
  let catalogue := closure scope address view
  (liveRows view).filter fun (i, _) => decide
    ((openSchema runtimeNodes host address cut catalogue i).Admits frames ∅ ∧
      (readSchema runtimeNodes host address cut catalogue i ruleMember control cut.clock).Admits frames
        (openedState runtimeNodes host address cut catalogue i))

open Classical in
theorem admittedRows_exact (control scope : Nat) (caller : Branch keys [] () D.Ty)
    (space pattern template : Datum) (address : Region) (view : Store (SourceLanguage.Row keys [] ()))
    (addressed : Determines caller.store space address) :
    (admittedRows control scope caller space pattern template address view).map
      (fun (i, row) => selectedBranch caller pattern template (scope + i) row) =
      ((selectRows caller pattern template scope view).map Prod.snd).filter
        (fun b => decide (Solvable b.store)) := by
  unfold selectRows admittedRows
  rw [List.map_map, List.filter_map]
  congr 1
  apply List.filter_congr
  rintro ⟨i, row⟩ inside
  have same := candidate_admits control scope view.clock caller space pattern template address view inside addressed
  exact decide_eq_decide.mpr (same.trans (by simp))

end Read

/-- A completed read, including absence, names its region revision. -/
def readStamp (address : Region) (revision : Nat) : StoreOccurrenceId Region Nat :=
  ⟨⟨address, revision⟩, 0⟩

noncomputable def Delimiter.recordRead (stamp : StoreOccurrenceId Region Nat)
    (k : Delimiter D) : Delimiter D := by
  classical
  exact {k with observed := k.observed ∪ {stamp}}

def Cursor.Current (c : Cursor D) : Prop :=
  ∀ k ∈ c.saved, k.observed.ValidAt c.revisions

def Cursor.CanClose (c : Cursor D) : Prop :=
  ∀ k ∈ c.saved.head?, k.observed.ValidAt c.revisions

theorem Delimiter.recordRead_valid (k : Delimiter D) (revisions : Revisions) (address : Region) (epoch : Nat) :
    (k.recordRead (readStamp address epoch)).observed.ValidAt revisions ↔
      k.observed.ValidAt revisions ∧ revisions.current address = epoch := by
  classical
  simp only [Delimiter.recordRead, RevisionDependencySet.validAt_union_iff,
    RevisionDependencySet.validAt_singleton_iff, readStamp]

theorem Cursor.stale_reads_block_wakeup (c : Cursor D) {k : Delimiter D}
    (member : k ∈ c.saved) (address : Region) (epoch : Nat)
    (observed : readStamp address epoch ∈ k.observed)
    (stale : c.revisions.current address ≠ epoch) : ¬ c.Current :=
  fun valid => stale (valid k member _ observed)

/-- Ordinary writes to bag-valued regions advance the revision of the
regions they change. Allocation of a new handle does not change old bags. -/
noncomputable def afterWrite (revisions : Revisions) (before after : World keys [] ()) : Revisions := by
  classical
  exact ⟨fun key => if before.spaces key = after.spaces key then revisions.current key
    else revisions.current key + 1⟩

@[simp] theorem afterWrite_same (revisions : Revisions) (world : World keys [] ()) :
    afterWrite revisions world world = revisions := by
  cases revisions; simp [afterWrite]

/-- These clients wait for the name exposed by the current principal image. -/
inductive Awaits (b : Branch keys [] () D.Ty) (input : Datum) : Prop where
  | run (text : Datum) (image : Assignment (fam keys) (fam keys))
      (control : b.focus = .eval (.run text)) (principal : Principal b.store image)
      (wait : instantiate image text = input) : Awaits b input
  | read (space pattern template : Datum) (image : Assignment (fam keys) (fam keys))
      (control : b.focus = .eval (.query space pattern (.ret template))) (principal : Principal b.store image)
      (wait : instantiate image space = input) : Awaits b input

def withInput (b : Branch keys [] () D.Ty) (input : Datum) (value : Region) :
    Branch keys [] () D.Ty :=
  {b with store := b.store ++ [(input, Rigid.includeTerm (fam keys) value)]}

/-- Once live, an input on the unresolved address determines the exact
region in every solution of the resumed branch. -/
theorem withInput_determines (b : Branch keys [] () D.Ty) (space input : Datum)
    (value : Region) (image : Assignment (fam keys) (fam keys))
    (principal : Principal b.store image) (waits : instantiate image space = input)
    (live : Solvable (withInput b input value).store) :
    Determines (withInput b input value).store space value := by
  refine ⟨live, ?_⟩
  intro V arity point known
  obtain ⟨old, supplied⟩ := (models_append point _ _).mp known
  have same : Assignment.compose point image = point := funext (principal.2 arity point old)
  have carries : instantiate point (instantiate image space) = instantiate point space :=
    (instantiate_comp image point space).trans (congrArg (instantiate · space) same)
  have fixed := (models_singleton point _).mp supplied
  exact carries.symm.trans ((congrArg (instantiate point) waits).trans
    (fixed.trans (Rigid.instantiate_include point value)))

/-- The resumed branch's full store factors through the saved substitution
and every residual equation returned by the solver. -/
theorem withInput_residual_models (b : Branch keys [] () D.Ty) (input : Datum) (value : Region)
    (firstFuel fuel : Nat) {V : Type} {arity : V → MetaArity RuntimeSig}
    (point : Assignment (fam keys) arity) :
    let supplied := [(input, Rigid.includeTerm (fam keys) value)]
    Models point (withInput b input value).store ↔
      match (Query.solve firstFuel b.store).resume fuel
        (Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual.observeProblem supplied) with
      | .refuted _ => False
      | .residual next =>
        ∃ remaining : Assignment next.declaration arity,
          Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual.Models remaining next.remaining ∧
          Assignment.compose remaining next.answer = point := by
  dsimp only [withInput]
  let supplied : List (Constraint keys [] ()) := [(input, Rigid.includeTerm (fam keys) value)]
  have models := Query.resume_models b.store supplied firstFuel fuel point
  cases step : (Query.solve firstFuel b.store).resume fuel
      (Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual.observeProblem supplied) <;>
    simpa only [supplied, step] using models

/-- One external input extends all active requests waiting on that name.
The parent continuations and already captured rows remain owned as before. -/
noncomputable def wake (c : Cursor D) (input : Datum) (value : Region) : Cursor D := by
  classical
  exact {c with active := { c.active with current := { c.active.current with
    branches := c.active.current.branches.map fun b =>
      if Awaits b input then withInput b input value else b }}}

/-- The root can progress a sibling while the selected strand is parked.
The public world advances once. Every open collector keeps its read stamps. -/
noncomputable def advanceSibling (c : Cursor D) (ancestors : List (Delimiter D)) (root : Delimiter D)
    (world : World keys [] ()) (remaining : Multiset (Branch keys [] () D.Ty)) : Cursor D :=
  let root := {root with parent := {root.parent with current := {root.parent.current with branches := remaining}}}
  let see := fun k : Delimiter D =>
    {k with parent := {k.parent with current := {k.parent.current with world := world}}}
  let active := {c.active with current := {c.active.current with world := world}}
  ⟨active, (ancestors ++ [root]).map see, c.heap, afterWrite c.revisions c.active.current.world world⟩

theorem sibling_effect_stales_read (c : Cursor D) (ancestors : List (Delimiter D))
    (root : Delimiter D) (world : World keys [] ()) (remaining : Multiset (Branch keys [] () D.Ty))
    (parked : c.saved = ancestors ++ [root]) (owner : Delimiter D) (member : owner ∈ c.saved)
    (address : Region) (epoch : Nat) (read : readStamp address epoch ∈ owner.observed)
    (current : c.revisions.current address = epoch)
    (changed : c.active.current.world.spaces address ≠ world.spaces address) :
    ¬ (advanceSibling c ancestors root world remaining).Current := by
  classical
  let next := advanceSibling c ancestors root world remaining
  have kept : next.saved.map Delimiter.observed = c.saved.map Delimiter.observed := by
    simp [next, advanceSibling, parked, List.map_append, List.map_map, Function.comp_def]
  have found : owner.observed ∈ c.saved.map Delimiter.observed :=
    List.mem_map.mpr ⟨owner, member, rfl⟩
  rw [← kept] at found
  obtain ⟨new, active, same⟩ := List.mem_map.mp found
  apply Cursor.stale_reads_block_wakeup next active address epoch (same.symm ▸ read)
  simp [next, advanceSibling, afterWrite, changed, current]

/-- Execution along a selected strand. A child may remain suspended with
its parent and heap retained. `ordinary` chooses an actual source move. -/
inductive Step (p : Program keys [] () D.Ty) (supply : Nat → Term RuntimeSig [] ()) :
    Cursor D → Cursor D → Prop where
  | ordinary {w w' b bs} (rest journal dead stack heap revisions)
      (enabled : available stack b.focus) (live : Solvable b.store)
      (move : Move D p supply w b w' bs) :
      Step p supply ⟨⟨⟨w, b ::ₘ rest⟩, journal, dead⟩, stack, heap, revisions⟩
        ⟨⟨⟨w', bs + rest⟩, journal, dead⟩, stack, heap, afterWrite revisions w w'⟩
  | read (w) (b : Branch keys [] () D.Ty) (space pattern template : Datum)
      (address : Region) (view : Store (Row keys [] ())) (rest journal dead stack heap revisions)
      (request : b.focus = .eval (.query space pattern (.ret template)))
      (addressed : Determines b.store space address)
      (snapshot : snapshotRows view = w.spaces address)
      (current : revisions.current address = view.clock)
      (sameRead : ∀ k ∈ stack, ∀ stamp ∈ k.observed,
        stamp.read.storeId = address → stamp.read.revision = view.clock) :
      Step p supply ⟨⟨⟨w, b ::ₘ rest⟩, journal, dead⟩, stack, heap, revisions⟩
        ⟨⟨⟨{w with scope := w.scope + view.next + 1},
          (((selectRows b pattern template w.scope view).map Prod.snd :
            List (Branch keys [] () D.Ty)) : Multiset _) + rest⟩,
          journal, dead⟩, stack.map (Delimiter.recordRead (readStamp address view.clock)), heap, revisions⟩
  | activate (w store text frames pending rest journal dead stack heap revisions body)
      (exposed : Activation p store text body) :
      Step p supply ⟨⟨⟨w, ⟨store, .eval (.run text), frames, pending⟩ ::ₘ rest⟩, journal, dead⟩, stack, heap, revisions⟩
        ⟨⟨⟨w, ⟨store, .eval body, frames, pending⟩ ::ₘ rest⟩, journal, dead⟩, stack, heap, revisions⟩
  | journal {before after} (stack heap revisions) (step : Admin before after) :
      Step p supply ⟨before, stack, heap, revisions⟩ ⟨after, stack, heap, revisions⟩
  | push (w b rest journal dead stack heap revisions arg head)
      (collects : collectorHead head)
      (atCollect : b.focus = .eval (.apply (unary head arg))) (live : Solvable b.store) :
      Step p supply ⟨⟨⟨w, b ::ₘ rest⟩, journal, dead⟩, stack, heap, revisions⟩
        (enter w b (p.reflect arg) rest journal dead stack heap revisions)
  | pop {c next} (valid : c.active.Valid) (current : c.CanClose)
      (closed : close? c valid = some next) : Step p supply c next
  | input (c : Cursor D) (input : Datum) (value : Region) (unbound : bare input = true)
      (waiting : ∃ b ∈ c.active.current.branches, Awaits b input)
      (current : c.Current) : Step p supply c (wake c input value)
  | sibling (c : Cursor D) (ancestors : List (Delimiter D)) (root : Delimiter D)
      (parked : c.saved = ancestors ++ [root])
      {b remaining after out} (pending : root.parent.current.branches = b ::ₘ remaining)
      (enabled : available [] b.focus) (live : Solvable b.store)
      (move : Move D p supply c.active.current.world b after out) :
      Step p supply c (advanceSibling c ancestors root after (out + remaining))
  | reflect (w : World keys [] ()) (b : Branch keys [] () D.Ty) (rest journal dead stack) (heap : Heap D)
      (revisions : Revisions) (arg : Datum) (id : Nat) (bag : AnswerSpace keys [] () D)
      (atReflect : b.focus = .eval (.apply (unary "reflect" arg)))
      (address : Determines b.store arg (Term.op (.inr (.mk id)) .nil : Term RuntimeSig [] ()))
      (found : heap[id]? = some bag) :
      Step p supply ⟨⟨⟨w, b ::ₘ rest⟩, journal, dead⟩, stack, heap, revisions⟩
        ⟨⟨⟨w, (bag.reflect w b).branches + rest⟩, journal, dead⟩, stack, heap, revisions⟩

private theorem nested_move_public {p : Program keys [] () D.Ty} {supply : Nat → Term RuntimeSig [] ()}
    {w w' b out} {k : Delimiter D} {stack}
    (allowed : available (k :: stack) b.focus) (move : Move D p supply w b w' out) :
    w'.spaces = w.spaces ∧ w'.handles = w.handles := by
  cases move <;> try exact ⟨rfl, rfl⟩
  all_goals simp [available, permitsMove, publicWrite] at allowed

/-- Every parked delimiter sees the same public snapshot as the active
read-only child. The fresh-name counter can advance while the child runs. -/
def Aligned (c : Cursor D) : Prop :=
  ∀ k ∈ c.saved, k.parent.current.world.spaces = c.active.current.world.spaces ∧
    k.parent.current.world.handles = c.active.current.world.handles

theorem step_aligned {p : Program keys [] () D.Ty} {supply : Nat → Term RuntimeSig [] ()}
    {c next : Cursor D} (step : Step p supply c next) (aligned : Aligned c) : Aligned next := by
  cases step with
  | ordinary rest journal dead stack heap revisions allowed live move =>
    cases stack with
    | nil => exact fun _ h => (List.not_mem_nil h).elim
    | cons k ks =>
      obtain ⟨spaces, handles⟩ := nested_move_public allowed move
      intro frame member
      obtain ⟨sp, h⟩ := aligned frame member
      exact ⟨sp.trans spaces.symm, h.trans handles.symm⟩
  | journal stack heap revisions admin => cases admin <;> exact aligned
  | push w b rest journal dead stack heap revisions arg head collects atCollect live =>
    intro k hk
    rcases List.mem_cons.mp hk with rfl | older
    · exact ⟨rfl,rfl⟩
    · exact aligned k older
  | read =>
    intro k member
    obtain ⟨old, contained, rfl⟩ := List.mem_map.mp member
    exact aligned old contained
  | sibling =>
    intro delimiter member
    simp only [advanceSibling, List.mem_map] at member
    obtain ⟨_, _, rfl⟩ := member
    exact ⟨rfl, rfl⟩
  | activate | reflect | input => exact aligned
  | pop valid current closed =>
    obtain ⟨top, ks, _, was, _, active, saved, _, _⟩ := close_spec _ _ valid closed
    intro k member
    rw [saved] at member
    have older := aligned k (was ▸ List.mem_cons_of_mem _ member)
    have head := aligned top (was ▸ List.mem_cons_self)
    rw [active]
    exact ⟨older.1.trans head.1.symm, older.2.trans head.2.symm⟩

theorem step_preserves_handles {p : Program keys [] () D.Ty} {supply : Nat → Term RuntimeSig [] ()}
    {c next : Cursor D} (step : Step p supply c next) :
    c.heap.length ≤ next.heap.length ∧ ∀ i < c.heap.length, next.heap[i]? = c.heap[i]? := by
  cases step with
  | ordinary | read | journal | push | reflect | activate | input | sibling => exact ⟨le_rfl, fun _ _ => rfl⟩
  | pop valid current step =>
    obtain ⟨_, _, _, _, _, _, _, added, old⟩ := close_spec _ _ valid step
    refine ⟨?_, old⟩
    by_contra! h
    rw [List.getElem?_eq_none (by omega)] at added
    contradiction

theorem run_preserves_handles {p : Program keys [] () D.Ty} {supply : Nat → Term RuntimeSig [] ()}
    {c next : Cursor D} (path : Relation.ReflTransGen (Step p supply) c next) :
    c.heap.length ≤ next.heap.length ∧ ∀ i < c.heap.length, next.heap[i]? = c.heap[i]? := by
  induction path with
  | refl => exact ⟨le_rfl, fun _ _ => rfl⟩
  | tail _ step ih =>
    obtain ⟨grows, old⟩ := step_preserves_handles step
    exact ⟨ih.1.trans grows, fun i hi => (old i (hi.trans_le ih.1)).trans (ih.2 i hi)⟩

section ReadCollection

variable {p : Program keys [] () D.Ty} {supply : Nat → Region}

/-- A selected, finished-template query can drive the inner collector to
publication. Its owned answer bag contains precisely the admitted replies. -/
theorem read_closes (w : World keys [] ()) (caller : Branch keys [] () D.Ty)
    (space pattern template : Datum) (address : Region) (view : Store (Row keys [] ()))
    (owner : Delimiter D) (outer : List (Delimiter D)) (heap : Heap D) (revisions : Revisions)
    (control : Nat)
    (request : caller.focus = .eval (.query space pattern (.ret template)))
    (addressed : Determines caller.store space address)
    (frames : caller.frames = []) (snapshot : snapshotRows view = w.spaces address)
    (current : revisions.current address = view.clock)
    (validReads : ∀ k ∈ owner :: outer, k.observed.ValidAt revisions) :
    let start : Cursor D := ⟨State.initial ⟨w, {caller}⟩, owner :: outer, heap, revisions⟩
    ∃ (next : Cursor D) (bag : AnswerSpace keys [] () D),
      Relation.ReflTransGen (Step p supply) start next ∧ next.heap[heap.length]? = some bag ∧
      bag.rows = ((Read.admittedRows control w.scope caller space pattern template address view).map
        (fun (i, row) => selectedBranch caller pattern template (w.scope + i) row) :
          Multiset (Branch keys [] () D.Ty)) := by
  dsimp only
  let stamp := readStamp address view.clock
  let top := owner.recordRead stamp
  let tail := outer.map (Delimiter.recordRead stamp)
  let world := {w with scope := w.scope + view.next + 1}
  let work := (selectRows caller pattern template w.scope view).map Prod.snd
  let carry := fun active : State keys [] () D => (⟨active, top :: tail, heap, revisions⟩ : Cursor D)
  have selection : Step p supply ⟨State.initial ⟨w, {caller}⟩, owner :: outer, heap, revisions⟩
      (carry (State.initial ⟨world, work⟩)) := by
    simpa only [carry, State.initial, world, work, top, tail, stamp, List.map_cons, Multiset.add_zero,
      Multiset.cons_zero] using
      Step.read (p := p) (supply := supply) w caller space pattern template address view 0 [] 0
        (owner :: outer) heap revisions request addressed snapshot current
        (by
          intro k member old captured there
          exact (validReads k member old captured).symm.trans
            ((congrArg revisions.current there).trans current))
  have finished : ∀ b ∈ work, b.Finished (D := D) := by
    intro b member
    unfold work selectRows at member
    rw [List.map_map] at member
    obtain ⟨⟨i, row⟩, _, rfl⟩ := List.mem_map.mp member
    exact ⟨frames, template, rfl⟩
  obtain ⟨endState, ran, valid, bag, published, rows⟩ := collect_finished world work finished
  have adminPath := ran.lift carry (fun _ _ h => Step.journal (p := p) (supply := supply) _ _ _ h)
  let next : Cursor D := ⟨restore top endState.current.world heap.length, tail, heap ++ [bag], revisions⟩
  have currentClose : (carry endState).CanClose := by
    intro k member
    have eq : top = k := by simpa [carry] using member
    subst k
    exact (Delimiter.recordRead_valid owner revisions address view.clock).mpr
      ⟨validReads owner List.mem_cons_self, current⟩
  have closed : close? (carry endState) valid = some next := by simp [close?, carry, published, next]
  refine ⟨next, bag, (adminPath.head selection).tail (.pop valid currentClose closed), by simp [next], ?_⟩
  rw [Read.admittedRows_exact control w.scope caller space pattern template address view addressed]
  exact rows

/-- A suspended address resumes through the same scoped read and closing
firing. The input is added to the branch store before matching any row. -/
theorem wake_read_closes (w : World keys [] ()) (caller : Branch keys [] () D.Ty)
    (space pattern template input : Datum) (address : Region) (view : Store (Row keys [] ()))
    (owner : Delimiter D) (outer : List (Delimiter D)) (heap : Heap D) (revisions : Revisions)
    (control : Nat) (image : Assignment (fam keys) (fam keys))
    (request : caller.focus = .eval (.query space pattern (.ret template)))
    (principal : Principal caller.store image) (waits : instantiate image space = input)
    (unbound : bare input = true) (live : Solvable (withInput caller input address).store)
    (frames : caller.frames = []) (snapshot : snapshotRows view = w.spaces address)
    (current : revisions.current address = view.clock)
    (validReads : ∀ k ∈ owner :: outer, k.observed.ValidAt revisions) :
    let start : Cursor D := ⟨State.initial ⟨w, {caller}⟩, owner :: outer, heap, revisions⟩
    ∃ (next : Cursor D) (bag : AnswerSpace keys [] () D),
      Relation.ReflTransGen (Step p supply) start next ∧ next.heap[heap.length]? = some bag ∧
      bag.rows = ((Read.admittedRows control w.scope (withInput caller input address)
          space pattern template address view).map
        (fun (i, row) => selectedBranch (withInput caller input address) pattern template (w.scope + i) row) :
          Multiset (Branch keys [] () D.Ty)) := by
  classical
  let start : Cursor D := ⟨State.initial ⟨w, {caller}⟩, owner :: outer, heap, revisions⟩
  have waiting : Awaits caller input := .read space pattern template image request principal waits
  have resumed := Step.input (p := p) (supply := supply) start input address unbound
    ⟨caller, Multiset.mem_singleton_self _, waiting⟩ validReads
  have ready := withInput_determines caller space input address image principal waits live
  obtain ⟨next, bag, ran, retained, exactRows⟩ :=
    read_closes (p := p) (supply := supply) w (withInput caller input address) space pattern template address
      view owner outer heap revisions control request ready frames snapshot current validReads
  have wakes := show wake start input address =
      ⟨State.initial ⟨w, {withInput caller input address}⟩, owner :: outer, heap, revisions⟩ by
    simp [wake, start, State.initial, waiting]
  exact ⟨next, bag, ran.head (wakes ▸ resumed), retained, exactRows⟩

end ReadCollection

section Nested

/-- One completed inner bag, even an empty one, is one answer of the outer
collector. Every alternative parked beside it is retained at the outer level. -/
theorem nested_returns_one (w : World keys [] ()) (caller : Branch keys [] () D.Ty)
    (finishedFrames : caller.frames = []) (live : Solvable caller.store)
    (outer : Delimiter D) (stack : List (Delimiter D)) (heap : Heap D) (revisions : Revisions)
    (inner : State keys [] () D) (valid : inner.Valid) (bag : AnswerSpace keys [] () D)
    (closed : reify inner valid = some bag) :
    let parent : Delimiter D := ⟨caller, State.initial ⟨w, 0⟩, ∅⟩
    let c : Cursor D := ⟨inner, parent :: outer :: stack, heap, revisions⟩
    ∃ middle captured next, close? c valid = some middle ∧
      Admin middle.active captured ∧
      ∃ good : captured.Valid, close? {middle with active := captured} good = some next ∧
        next.saved = stack ∧ next.heap[heap.length]? = some bag ∧
        ∃ wrapper, next.heap[heap.length + 1]? = some wrapper ∧
          wrapper.rows = { {caller with focus := .value (token heap.length)} } := by
  intro parent c
  let value : Branch keys [] () D.Ty := {caller with focus := .value (token heap.length)}
  let returnedWorld : World keys [] () := { w with scope := inner.current.world.scope }
  let captured : State keys [] () D := ⟨⟨returnedWorld, 0⟩, [value], 0⟩
  have ready : value.Finished (D := D) := ⟨finishedFrames, _, rfl⟩
  have good : captured.Valid := by
    constructor
    · intro b hb
      obtain rfl := List.mem_singleton.mp hb
      exact ⟨ready, live⟩
    · intro b hb
      exact (Multiset.notMem_zero b hb).elim
  let wrapper : AnswerSpace keys [] () D := ⟨{value}, fun b hb => by
    obtain rfl := Multiset.mem_singleton.mp hb; exact ⟨ready, live⟩⟩
  let middle : Cursor D := ⟨restore parent inner.current.world heap.length, outer :: stack, heap ++ [bag], revisions⟩
  let next : Cursor D := ⟨restore outer returnedWorld (heap ++ [bag]).length, stack,
    (heap ++ [bag]) ++ [wrapper], revisions⟩
  refine ⟨middle, captured, next, ?_, .capture returnedWorld value 0 [] 0 ready live, good, ?_, rfl, ?_, wrapper, ?_, rfl⟩
  · simp [close?, c, middle, closed]
  · rfl
  · change ((heap ++ [bag]) ++ [wrapper])[heap.length]? = _
    rw [List.getElem?_append_left (by simp)]
    simp
  · change ((heap ++ [bag]) ++ [wrapper])[heap.length + 1]? = _
    simp

/-- Concrete nested source programs constructed from the empty producer. -/
private def emptyText : Datum :=
  .op (.inl (.inl (.tup 1))) (.cons (.op (.inl (.inl (.sym "empty"))) .nil) .nil)

private def nest : Nat → Datum
  | 0 => emptyText
  | n+1 => unary "reify" (nest n)

private noncomputable def nestedProgram (D : Discipline RuntimeSig [] ()) : Program keys [] () D.Ty := by
  classical
  exact ⟨[], fun t => if t = emptyText then .fail else .apply t⟩

private theorem nest_ne_empty (n : Nat) : nest (n+1) ≠ emptyText := by
  intro same
  injection same with _ _ op
  simp at op

private abbrev branch (code : Comp keys [] () D.Ty) : Branch keys [] () D.Ty := ⟨[], .eval code, [], []⟩
private abbrev result (id : Nat) : Branch keys [] () D.Ty := ⟨[], .value (token id), [], []⟩
private theorem consistent : Solvable ([] : List (Constraint keys [] ())) :=
  ⟨_, _, generator (fam keys), fun _ h => nomatch h⟩

def layers (base : Nat) : Nat → List (Branch keys [] () D.Ty)
  | 0 => []
  | n+1 => [result (base+n)]

private def wrapped (base level : Nat) : AnswerSpace keys [] () D :=
  ⟨(layers (D := D) base level : Multiset (Branch keys [] () D.Ty)), by
    cases level with
    | zero => exact fun b h => (Multiset.notMem_zero b h).elim
    | succ n =>
      intro b hb
      obtain rfl := List.mem_singleton.mp (Multiset.mem_coe.mp hb)
      exact ⟨⟨rfl, _, rfl⟩, consistent⟩⟩

private def extendHeap (heap : Heap D) : Nat → Heap D
  | 0 => heap
  | n+1 => extendHeap heap n ++ [wrapped heap.length n]

private theorem length_extendHeap (heap : Heap D) (n : Nat) :
    (extendHeap heap n).length = heap.length + n := by
  induction n <;> simp_all [extendHeap, Nat.add_assoc]

/-- From source entry, each level allocates one address and stores the
complete result of its child. The innermost bag is empty, every outer bag
contains one handle to the previous bag, and any outer stack is preserved. -/
theorem execute_nested_empty (w : World keys [] ()) (heap : Heap D) (depth : Nat)
    (stack : List (Delimiter D)) (revisions : Revisions) (supply : Nat → Term RuntimeSig [] ()) :
    let p := nestedProgram D
    Relation.ReflTransGen (Step p supply)
      ⟨State.initial ⟨w, {branch (p.reflect (nest depth))}⟩, stack, heap, revisions⟩
      ⟨⟨⟨w, 0⟩, layers heap.length depth, 0⟩, stack, extendHeap heap depth, revisions⟩ := by
  intro p
  induction depth generalizing stack with
  | zero =>
    have failed : p.reflect (nest 0) = .fail := by simp [p, nestedProgram, nest]
    rw [failed]
    refine .single ?_
    simpa only [afterWrite_same, State.initial, layers, extendHeap, branch,
      Multiset.zero_add, Multiset.cons_zero] using
      Step.ordinary (p := p) (supply := supply) 0 [] 0 stack heap revisions
      (by simp [available, permitsMove, isService, isQuery, publicWrite]) consistent (.fail w _ _ _)
  | succ n ih =>
    have read : p.reflect (nest (n+1)) = .apply (unary "reify" (nest n)) := by
      change (if nest (n+1) = emptyText then Comp.fail else .apply (nest (n+1))) = _
      exact if_neg (nest_ne_empty n)
    rw [read]
    let k : Delimiter D := ⟨branch (.apply (unary "reify" (nest n))), State.initial ⟨w, 0⟩, ∅⟩
    have push := Step.push (D := D) (p := p) (supply := supply) w k.caller 0 [] 0 stack heap revisions
      (nest n) "reify" (.inl rfl) rfl consistent
    have middle := ih (k :: stack)
    let child : State keys [] () D := ⟨⟨w, 0⟩, layers heap.length n, 0⟩
    have valid : child.Valid :=
      ⟨fun b hb => (wrapped (D := D) heap.length n).ready b (Multiset.mem_coe.mpr hb),
        fun b hb => (Multiset.notMem_zero b hb).elim⟩
    have pop : Step p supply ⟨child, k :: stack, extendHeap heap n, revisions⟩
        ⟨⟨⟨w, {result (heap.length+n)}⟩, [], 0⟩, stack, extendHeap heap (n+1), revisions⟩ := by
      refine Step.pop valid ?_ ?_
      · simp [Cursor.CanClose, k]
      · change (some ⟨restore k w (extendHeap heap n).length, stack,
        extendHeap heap n ++ [wrapped heap.length n], revisions⟩ : Option (Cursor D)) = _
        rw [length_extendHeap]
        rfl
    have save := Step.journal (D := D) (p := p) (supply := supply) stack (extendHeap heap (n+1))
      revisions (Admin.capture w (result (D := D) (heap.length+n)) 0 [] 0 ⟨rfl, _, rfl⟩ consistent)
    exact (((Relation.ReflTransGen.single push).trans middle).tail pop).tail save

end Nested

namespace CloseFiring
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open AnnotatedRuns

/-- Occurrence identities are local to this delimiter. The row indices
address full branch snapshots in the journal, including duplicates. -/
inductive Port where | caller | returned | work (i : Nat) | answer (i : Nat)
  deriving DecidableEq
inductive Label where | caller | returned | work | answer
  deriving DecidableEq
def label : Port → Label
  | .caller => .caller | .returned => .returned | .work _ => .work | .answer _ => .answer

abbrev action := RuleSyntax.RuleOccurrences.Closed.action Label

def table (state : State keys [] () D) (children : Nat := 0) : Configuration Label Port :=
  ⟨[], insert .caller ((Finset.range (state.current.branches.card + children)).image Port.work ∪
    (Finset.range state.reverseAnswers.length).image Port.answer)⟩

def close : Firing Label PUnit.{1} Port :=
  ⟨⟨[.caller], [], [], [.predicate .none .work], [.returned]⟩, [], ⟨[.caller], [], [.returned]⟩⟩

private theorem enabled (s : State keys [] () D) (children : Nat) :
    Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Enabled
      label (table s children).present close.selection.commit := by
  constructor <;> simp [table, close, Selection.commit]

/-- The fixed close rule asks absence over live work occurrences. A
suspended child counts as outstanding. Captured answers never enter this
absence check or become conjoined as logical knowledge. -/
theorem admitted_iff_outstanding (s : State keys [] () D) (children : Nat) :
    close.Valid action label (table s children) ↔ s.current.branches = 0 ∧ children = 0 := by
  have known : action.Models PUnit.unit (close.selection.problem label close.rule (table s children)) := by
    intro eq h
    simp [Selection.problem, Selection.equations, table, close] at h
    subst eq
    rfl
  constructor
  · intro ok
    by_contra outstanding
    have pos : 0 < s.current.branches.card + children := by
      contrapose! outstanding
      exact ⟨Multiset.card_eq_zero.mp (by omega), by omega⟩
    have member : Port.work 0 ∈ (table s children).present := by simp [table, pos]
    exact ok.firing.checks (.predicate .none .work) (List.mem_singleton_self _) PUnit.unit known _ member rfl
  · rintro ⟨empty, rfl⟩
    refine ⟨⟨by decide, by decide, rfl, rfl, rfl, enabled s 0, ⟨_, known⟩, ?_⟩, fun _ h => by cases h⟩
    intro check mem σ _
    obtain rfl := List.mem_singleton.mp mem
    intro o ho
    change Label.work ≠ label o
    cases o <;> simp_all [table, label]

theorem admitted_iff (s : State keys [] () D) :
    close.Valid action label (table s) ↔ s.current.branches = 0 := by
  simpa only [and_true, eq_self] using admitted_iff_outstanding s 0

theorem completion_iff_admitted (s : State keys [] () D) (valid : s.Valid) :
    (∃ bag, reify s valid = some bag) ↔ close.Valid action label (table s) := by
  rw [admitted_iff]
  by_cases done_ : s.current.branches = 0
  · simp [reify, done_]
  · simp [reify, done_]

theorem pop_iff_admitted (c : Cursor D) (valid : c.active.Valid) (waiting : c.saved ≠ []) :
    (∃ next, close? c valid = some next) ↔ close.Valid action label (table c.active) := by
  rw [← completion_iff_admitted c.active valid]
  cases saved : c.saved with
  | nil => contradiction
  | cons k ks =>
    cases finished : reify c.active valid <;> simp [close?, saved, finished]

theorem retained_row (s : State keys [] () D) (i : Nat) (children : Nat := 0) :
    Port.answer i ∈ (close.result label (table s children)).present ↔ i < s.reverseAnswers.length := by
  simp [Firing.result, Selection.result,
    Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.fire, Selection.commit, close, table]

/-- Read the full answer snapshots at the occurrence ports retained by the close firing. -/
def journal (s : State keys [] () D) (children : Nat) : List (Branch keys [] () D.Ty) :=
  (s.reverseAnswers.zipIdx.filter fun (_, i) =>
    decide (Port.answer i ∈ (close.result label (table s children)).present)).map Prod.fst

theorem journal_eq (s : State keys [] () D) (children : Nat) :
    journal s children = s.reverseAnswers := by
  have keeps : ∀ entry ∈ s.reverseAnswers.zipIdx,
      decide (Port.answer entry.2 ∈ (close.result label (table s children)).present) = true := by
    intro entry member
    exact decide_eq_true ((retained_row s entry.2 children).mpr (List.mem_zipIdx' member).1)
  unfold journal
  rw [List.filter_eq_self.mpr keeps, List.zipIdx_map_fst]

def answerSpace (s : State keys [] () D) (valid : s.Valid) (children : Nat) : AnswerSpace keys [] () D :=
  ⟨journal s children, fun row member => valid.answers row (Multiset.mem_coe.mp (by
    rw [← journal_eq s children]
    exact member))⟩

end CloseFiring

/-- A collector closes when its complete journal can fire and the selected
public revisions are still current. -/
theorem current_close_iff (c : Cursor D) (valid : c.active.Valid) (waiting : c.saved ≠ []) :
    (∃ next, c.CanClose ∧ close? c valid = some next) ↔
      c.CanClose ∧ CloseFiring.close.Valid CloseFiring.action CloseFiring.label
        (CloseFiring.table c.active) := by
  rw [← CloseFiring.pop_iff_admitted c valid waiting]
  constructor
  · rintro ⟨next, current, closed⟩
    exact ⟨current, next, closed⟩
  · rintro ⟨current, next, closed⟩
    exact ⟨next, current, closed⟩

/-- A writer to a consulted region invalidates a pending publication, even
when the observation at that address was an empty match. -/
theorem conflicting_write_blocks_close (c : Cursor D) (after : World keys [] ())
    (owner : Delimiter D) (tail : List (Delimiter D)) (saved : c.saved = owner :: tail)
    (address : Region) (epoch : Nat) (observed : readStamp address epoch ∈ owner.observed)
    (current : c.revisions.current address = epoch)
    (changed : c.active.current.world.spaces address ≠ after.spaces address) :
    ¬ ({c with revisions := afterWrite c.revisions c.active.current.world after}).CanClose := by
  classical
  intro canClose
  have valid := canClose owner (by simp [saved])
  have still := valid (readStamp address epoch) observed
  simp [afterWrite, readStamp, changed, current] at still

/-- A revision change outside the consulted support is invisible to closing
the selected collector. -/
theorem unrelated_write_preserves_close (c : Cursor D) (after : Revisions)
    (owner : Delimiter D) (tail : List (Delimiter D)) (saved : c.saved = owner :: tail)
    (outside : ∀ stamp ∈ owner.observed,
      after.current stamp.read.storeId = c.revisions.current stamp.read.storeId) :
    ({c with revisions := after}).CanClose ↔ c.CanClose := by
  simpa [Cursor.CanClose, saved] using
    (show owner.observed.ValidAt after ↔ owner.observed.ValidAt c.revisions from
      ⟨fun valid stamp present => (outside stamp present).symm.trans (valid stamp present),
       fun valid stamp present => (outside stamp present).trans (valid stamp present)⟩)

end Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTa.Collection
