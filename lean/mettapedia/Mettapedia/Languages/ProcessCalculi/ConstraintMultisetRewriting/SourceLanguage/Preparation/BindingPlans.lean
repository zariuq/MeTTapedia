import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Semantics
import Mettapedia.Machines.Specialization.Assembly
import Mettapedia.OSLF.Syntax.ContextualFiniteSupport
import Mathlib.Logic.Function.Basic

/-!
# Static lexical binding plans

A finite, effect-free equation body lowers to a sequence of constraints
and one held result. Binder links refer to the earlier lexical opening
of the same site. Values use dense contextual slots. The runtime offset
of a binder is its position in the sequence, relative to entry.

The plan preserves the source's equations rather than replacing them by
ground values. In particular, unresolved variables and aliases shared
by a returned value and a continuation remain shared.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.BindingPlans

open Mettapedia.OSLF.Binding hiding instantiate
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.OSLF.Binding.ContextualFamily.FiniteSupport
open Mettapedia.Machines.Specialization

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt} {Ty : Type}

inductive ExitKind where
  | answer
  | tailCall
  deriving DecidableEq

def ExitKind.focus (datum : Data κ Γ star) : ExitKind → Focus κ Γ star Ty
  | .answer => .value datum
  | .tailCall => .eval (.apply datum)

def ExitKind.debit : ExitKind → Nat
  | .answer => 1
  | .tailCall => 0

variable {ending : ExitKind}

/-- The straight-line part of the source control algebra. Producers
must return values. The continuation may leave a call at the boundary
where equation selection and other effects can resume. -/
inductive Fragment (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty : Type) :
    ExitKind → Comp κ Γ star Ty → Type where
  | hold (datum : Data κ Γ star) : Fragment κ Γ star Ty .answer (.ret datum)
  | call (datum : Data κ Γ star) : Fragment κ Γ star Ty .tailCall (.apply datum)
  | binding {bound body : Comp κ Γ star Ty} {ending : ExitKind} (site : κ.Site) (pattern : Data κ Γ star)
      (producer : Fragment κ Γ star Ty .answer bound) (continuation : Fragment κ Γ star Ty ending body) :
      Fragment κ Γ star Ty ending (.let_ site pattern bound body)

def recognize : (code : Comp κ Γ star Ty) → Option (Σ ending, Fragment κ Γ star Ty ending code)
  | .ret datum => some ⟨.answer, .hold datum⟩
  | .apply datum => some ⟨.tailCall, .call datum⟩
  | .let_ site pattern bound body => do
    match ← recognize bound with
    | ⟨.answer, producer⟩ =>
      let ⟨ending, continuation⟩ ← recognize body
      some ⟨ending, .binding site pattern producer continuation⟩
    | ⟨.tailCall, _⟩ => none
  | _ => none

def Fragment.bindings : {ending : ExitKind} → {code : Comp κ Γ star Ty} → Fragment κ Γ star Ty ending code → Nat
  | _, _, .hold _ => 0
  | _, _, .call _ => 0
  | _, _, .binding _ _ producer continuation => producer.bindings + 1 + continuation.bindings

/-- A binding has an entry move and a resume move. Each leaf has one
hold move. The length includes the movements discharged by fusion. -/
def Fragment.moves : {ending : ExitKind} → {code : Comp κ Γ star Ty} → Fragment κ Γ star Ty ending code → Nat
  | _, _, .hold _ => 1
  | _, _, .call _ => 0
  | _, _, .binding _ _ producer continuation => 1 + producer.moves + 1 + continuation.moves

theorem Fragment.moves_eq {code : Comp κ Γ star Ty} (shape : Fragment κ Γ star Ty ending code) :
    shape.moves = 3 * shape.bindings + ending.debit := by
  induction shape with
  | hold => rfl
  | call => rfl
  | binding _ _ _ _ ihProducer ihBody =>
    simp only [moves, bindings, ihProducer, ihBody, ExitKind.debit]
    omega

/-- The static association of lexical sites with their latest opening. -/
abbrev Context (κ : Keys S) := List (κ.Site × Nat)

def parent (context : Context κ) (site : κ.Site) : Option Nat :=
  (context.find? (fun earlier => decide (earlier.1 = site))).map Prod.snd

@[simp] theorem parent_cons_same (context : Context κ) (site : κ.Site) (offset : Nat) :
    parent ((site, offset) :: context) site = some offset := by simp [parent, List.find?]

theorem parent_cons_other (context : Context κ) {site other : κ.Site} (offset : Nat) (neq : site ≠ other) :
    parent ((site, offset) :: context) other = parent context other := by simp [parent, List.find?, neq]

theorem parent_mem {context : Context κ} {site : κ.Site} {offset : Nat}
    (found : parent context site = some offset) : (site, offset) ∈ context := by
  obtain ⟨⟨key, position⟩, got, same⟩ := Option.map_eq_some_iff.mp found
  have member := List.mem_of_find?_eq_some got
  have accepted := List.find?_some got
  have hit : key = site := of_decide_eq_true accepted
  change position = offset at same
  subst site
  subst offset
  exact member

/-- A logical table of opening chains. The executable representation may
use arrays or retain shared tails behind handles. -/
abbrev ScopeTable := Nat → List Nat

def chain (table : ScopeTable) : Option Nat → List Nat
  | none => []
  | some offset => table offset

/-- Slots refer only to chains that are in scope when this datum is held. -/
structure Operand (κ : Keys S) (Γ : Ctx S) (star : S.Srt) where
  names : List (Name κ)
  references : List (Option Nat)
  size : references.length = names.length
  assemble : Assembly.Code (Assignment (declaration (source := fam κ) names) (fam κ)) (Data κ Γ star)

def Operand.compile [DecidableEq κ.Key] (context : Context κ) (datum : Data κ Γ star) :
    Operand κ Γ star :=
  let names := firstNames (support datum)
  let positional := FiniteSupport.compile names datum (fun _ member => mem_firstNames.mpr member)
  ⟨names, names.map (fun name => parent context (κ.site name.key)), List.length_map _,
    Assembly.lower (Assembly.contextual _ _) positional⟩

def Operand.reference (operand : Operand κ Γ star) (port : Fin operand.names.length) : Option Nat :=
  operand.references[port.val]'(by rw [operand.size]; exact port.isLt)

def Operand.readSlots (operand : Operand κ Γ star)
    (slots : Fin operand.names.length → List Nat) (entry : List Nat) : Data κ Γ star :=
  operand.assemble.run fun port =>
    let name := operand.names[port]
    generator (fam κ) ⟨slots port ++ entry ++ name.scopes, name.key⟩

def Operand.read (operand : Operand κ Γ star) (table : ScopeTable) (entry : List Nat) : Data κ Γ star :=
  operand.readSlots (fun port => chain table (operand.reference port)) entry

def scopeNames (siteScopes : κ.Site → List Nat) (entry : List Nat) (name : Name κ) : List Nat :=
  siteScopes (κ.site name.key) ++ entry ++ name.scopes

theorem Operand.read_compile [DecidableEq κ.Key] (context : Context κ) (table : ScopeTable)
    (entry : List Nat) (datum : Data κ Γ star) :
    (Operand.compile context datum).read table entry =
      instantiate (relabel κ (scopeNames (fun site => chain table (parent context site)) entry)) datum := by
  unfold Operand.compile Operand.read Operand.readSlots Operand.reference
  dsimp only
  rw [Assembly.lower_contextual]
  rw [← instantiate_compile (firstNames (support datum))
    (relabel κ (scopeNames (fun site => chain table (parent context site)) entry)) datum
    (fun _ member => mem_firstNames.mpr member)]
  congr 1
  funext port
  change Fin (firstNames (support datum)).length at port
  dsimp only [slots, relabel, scopeNames]
  rw [List.getElem_map]
  rfl

/-- Relabelling retains the declaration key. Opening acts only at the
statically selected site, including when that site is opened again. -/
theorem instantiate_open (site : κ.Site) (fresh : Nat) (siteScopes : κ.Site → List Nat)
    (entry : List Nat) (datum : Data κ Γ star) :
    instantiate (openAt κ site fresh) (instantiate (relabel κ (scopeNames siteScopes entry)) datum) =
      instantiate (relabel κ (scopeNames
        (Function.update siteScopes site (fresh :: siteScopes site)) entry)) datum := by
  rw [instantiate_comp]
  congr 1
  funext name
  simp only [relabel, instantiate_generator, openAt, scopeNames]
  by_cases same : κ.site name.key = site
  · rw [if_pos same, same, Function.update_self]
    rfl
  · rw [if_neg same, Function.update_of_ne same]

theorem comp_open (site : κ.Site) (fresh : Nat) (siteScopes : κ.Site → List Nat) (entry : List Nat)
    (code : Comp κ Γ star Ty) :
    (code.inst (relabel κ (scopeNames siteScopes entry))).inst (openAt κ site fresh) =
      code.inst (relabel κ (scopeNames
        (Function.update siteScopes site (fresh :: siteScopes site)) entry)) := by
  simp only [Comp.inst, Comp.mapData_comp]
  congr 1
  funext datum
  exact instantiate_open site fresh siteScopes entry datum

structure Binding (κ : Keys S) (Γ : Ctx S) (star : S.Srt) where
  parent : Option Nat
  pattern : Operand κ Γ star
  value : Operand κ Γ star

structure Plan (κ : Keys S) (Γ : Ctx S) (star : S.Srt) where
  code : List (Binding κ Γ star)
  result : Operand κ Γ star
  ending : ExitKind

/-- Emit one chain node and two operand references per lexical binding.
A chain node points to an earlier node, so nested openings can share their
tails. Source control and site comparisons are resolved during lowering. -/
def lower [DecidableEq κ.Key] : {ending : ExitKind} → {code : Comp κ Γ star Ty} →
    Fragment κ Γ star Ty ending code → Context κ → Nat → Plan κ Γ star
  | _, _, .hold datum, context, _ => ⟨[], .compile context datum, .answer⟩
  | _, _, .call datum, context, _ => ⟨[], .compile context datum, .tailCall⟩
  | _, _, .binding site pattern producer continuation, context, offset =>
    let left := lower producer context offset
    let atBind := offset + producer.bindings
    let inner := (site, atBind) :: context
    let right := lower continuation inner (atBind + 1)
    ⟨left.code ++ ⟨parent context site, .compile inner pattern, left.result⟩ :: right.code,
      right.result, right.ending⟩

theorem lower_length [DecidableEq κ.Key] {code : Comp κ Γ star Ty}
    (shape : Fragment κ Γ star Ty ending code) (context : Context κ) (offset : Nat) :
    (lower shape context offset).code.length = shape.bindings := by
  induction shape generalizing context offset with
  | hold => rfl
  | call => rfl
  | binding _ _ _ _ ihProducer ihBody =>
    simp only [lower, Fragment.bindings, List.length_append, List.length_cons, ihProducer, ihBody]
    omega

def compile [DecidableEq κ.Key] (code : Comp κ Γ star Ty) : Option (Plan κ Γ star) :=
  (recognize code).map fun admitted => lower admitted.2 [] 0

theorem lower_ending [DecidableEq κ.Key] {code : Comp κ Γ star Ty}
    (shape : Fragment κ Γ star Ty ending code) (context : Context κ) (offset : Nat) :
    (lower shape context offset).ending = ending := by
  induction shape generalizing context offset with
  | hold => rfl
  | call => rfl
  | binding _ _ _ _ _ continuation => exact continuation _ _

def Binding.extend (binding : Binding κ Γ star) (origin offset : Nat) (table : ScopeTable) :
    ScopeTable :=
  Function.update table offset ((origin + offset) :: chain table binding.parent)

/-- Each instruction writes one opening chain and appends one equation.
It reads the producer in the earlier environment and the pattern in the
extended environment. -/
def executeBindings (origin : Nat) (entry : List Nat) :
    List (Binding κ Γ star) → Nat → ScopeTable → ScopeTable × List (Constraint κ Γ star)
  | [], _, table => (table, [])
  | binding :: later, offset, table =>
    let extended := binding.extend origin offset table
    let equation := (binding.pattern.read extended entry, binding.value.read table entry)
    let result := executeBindings origin entry later (offset + 1) extended
    (result.1, equation :: result.2)

def Plan.execute (plan : Plan κ Γ star) (origin : Nat) (entry : List Nat)
    (offset : Nat) (table : ScopeTable) :
    (ScopeTable × List (Constraint κ Γ star)) × Data κ Γ star :=
  let result := executeBindings origin entry plan.code offset table
  (result, plan.result.read result.1 entry)

theorem executeBindings_append (origin : Nat) (entry : List Nat)
    (first later : List (Binding κ Γ star)) (offset : Nat) (table : ScopeTable) :
    executeBindings origin entry (first ++ later) offset table =
      let earlier := executeBindings origin entry first offset table
      let after := executeBindings origin entry later (offset + first.length) earlier.1
      (after.1, earlier.2 ++ after.2) := by
  induction first generalizing offset table with
  | nil => simp [executeBindings]
  | cons binding rest ih =>
    simp only [List.cons_append, executeBindings, ih, List.length_cons]
    rw [show offset + 1 + rest.length = offset + (rest.length + 1) by omega]

theorem executeBindings_earlier (origin : Nat) (entry : List Nat)
    (code : List (Binding κ Γ star)) (offset : Nat) (table : ScopeTable)
    {earlier : Nat} (before : earlier < offset) :
    (executeBindings origin entry code offset table).1 earlier = table earlier := by
  induction code generalizing offset table with
  | nil => rfl
  | cons binding later ih =>
    simp only [executeBindings]
    rw [ih _ _ (Nat.lt_succ_of_lt before)]
    exact Function.update_of_ne (by omega) _ _

@[simp] theorem executeBindings_length (origin : Nat) (entry : List Nat)
    (code : List (Binding κ Γ star)) (offset : Nat) (table : ScopeTable) :
    (executeBindings origin entry code offset table).2.length = code.length := by
  induction code generalizing offset table with
  | nil => rfl
  | cons binding later ih => simp [executeBindings, ih]

def Context.earlier (context : Context κ) (offset : Nat) : Prop :=
  ∀ opening ∈ context, opening.2 < offset

theorem Context.earlier_of_le {context : Context κ} {first later : Nat}
    (earlier : context.earlier first) (le : first ≤ later) : context.earlier later :=
  fun opening member => Nat.lt_of_lt_of_le (earlier opening member) le

theorem Context.push_earlier {context : Context κ} {offset : Nat} (site : κ.Site)
    (earlier : context.earlier offset) : Context.earlier ((site, offset) :: context) (offset + 1) := by
  intro opening member
  rcases List.mem_cons.mp member with rfl | member
  · omega
  · exact Nat.lt_succ_of_lt (earlier opening member)

def Context.scopes (context : Context κ) (table : ScopeTable) (site : κ.Site) : List Nat :=
  chain table (parent context site)

theorem Context.scopes_agree (context : Context κ) (first later : ScopeTable) (offset : Nat)
    (older : context.earlier offset) (same : ∀ index < offset, first index = later index) :
    context.scopes first = context.scopes later := by
  funext site
  unfold scopes
  cases found : parent context site with
  | none => rfl
  | some index => exact same index (older (site, index) (parent_mem found))

theorem Context.scopes_after_bindings (context : Context κ) (origin : Nat) (entry : List Nat)
    (code : List (Binding κ Γ star)) (offset : Nat) (table : ScopeTable)
    (earlier : context.earlier offset) :
    context.scopes (executeBindings origin entry code offset table).1 = context.scopes table :=
  scopes_agree context _ table offset earlier
    (fun _ before => executeBindings_earlier origin entry code offset table before)

theorem Context.scopes_push (context : Context κ) (site : κ.Site) (offset origin : Nat)
    (table : ScopeTable) (older : context.earlier offset) :
    Context.scopes ((site, offset) :: context)
      (Function.update table offset ((origin + offset) :: context.scopes table site)) =
    Function.update (context.scopes table) site ((origin + offset) :: context.scopes table site) := by
  let updated := Function.update table offset ((origin + offset) :: context.scopes table site)
  funext sought
  by_cases same : sought = site
  · subst sought
    simp [scopes, chain]
  · have preserves := scopes_agree context updated table offset older
      (fun _ before => Function.update_of_ne (by omega) _ _)
    change Context.scopes ((site, offset) :: context) updated sought = _
    rw [Function.update_of_ne same, ← preserves]
    simp only [scopes, parent_cons_other context offset (Ne.symm same)]

theorem execute_lower_binding [DecidableEq κ.Key] {bound body : Comp κ Γ star Ty}
    (site : κ.Site) (pattern : Data κ Γ star) (producer : Fragment κ Γ star Ty .answer bound)
    (continuation : Fragment κ Γ star Ty ending body) (context : Context κ)
    (origin offset : Nat) (entry : List Nat) (table : ScopeTable) :
    (lower (.binding site pattern producer continuation) context offset).execute origin entry offset table =
      let first := (lower producer context offset).execute origin entry offset table
      let atBind := offset + producer.bindings
      let inner := (site, atBind) :: context
      let extended := Function.update first.1.1 atBind
        ((origin + atBind) :: context.scopes first.1.1 site)
      let equation := ((Operand.compile inner pattern).read extended entry, first.2)
      let later := (lower continuation inner (atBind + 1)).execute origin entry (atBind + 1) extended
      ((later.1.1, first.1.2 ++ equation :: later.1.2), later.2) := by
  simp only [Plan.execute, lower, executeBindings_append, lower_length, executeBindings,
    Binding.extend, Context.scopes]

def Operand.readsEarlier (operand : Operand κ Γ star) (bound : Nat) : Prop :=
  ∀ port offset, operand.reference port = some offset → offset < bound

theorem Operand.compile_readsEarlier [DecidableEq κ.Key] (context : Context κ) (datum : Data κ Γ star)
    {bound : Nat} (earlier : context.earlier bound) : (Operand.compile context datum).readsEarlier bound := by
  intro port offset located
  have valid : port.val < ((firstNames (support datum)).map (fun name => parent context (κ.site name.key))).length := by
    rw [List.length_map]
    exact port.isLt
  change ((firstNames (support datum)).map (fun name => parent context (κ.site name.key)))[port.val]'valid =
    some offset at located
  rw [List.getElem_map] at located
  exact earlier _ (parent_mem located)

/-- Every referenced producer and parent already exists. The pattern
may also use the chain introduced by its own instruction. -/
inductive LexicalOrder (κ : Keys S) (Γ : Ctx S) (star : S.Srt) : Nat → List (Binding κ Γ star) → Prop
  | empty (offset : Nat) : LexicalOrder κ Γ star offset []
  | bind {offset : Nat} {instruction : Binding κ Γ star} {later : List (Binding κ Γ star)}
      (parent : ∀ earlier, instruction.parent = some earlier → earlier < offset)
      (producer : instruction.value.readsEarlier offset)
      (pattern : instruction.pattern.readsEarlier (offset + 1))
      (continuation : LexicalOrder κ Γ star (offset + 1) later) :
    LexicalOrder κ Γ star offset (instruction :: later)

theorem LexicalOrder.append {offset : Nat} {first later : List (Binding κ Γ star)}
    (placed : LexicalOrder κ Γ star offset first)
    (following : LexicalOrder κ Γ star (offset + first.length) later) :
    LexicalOrder κ Γ star offset (first ++ later) := by
  induction placed with
  | empty => simpa using following
  | @bind offset instruction rest parent producer pattern _ ih =>
    refine LexicalOrder.bind parent producer pattern (ih ?_)
    rw [show offset + 1 + rest.length = offset + (instruction :: rest).length by
      simp only [List.length_cons]; omega]
    exact following

theorem lower_lexical [DecidableEq κ.Key] {code : Comp κ Γ star Ty}
    (shape : Fragment κ Γ star Ty ending code) (context : Context κ) (offset : Nat)
    (earlier : context.earlier offset) :
    let plan := lower shape context offset
    LexicalOrder κ Γ star offset plan.code ∧ plan.result.readsEarlier (offset + plan.code.length) := by
  induction shape generalizing context offset with
  | hold datum =>
    exact ⟨.empty _, Operand.compile_readsEarlier context datum earlier⟩
  | call datum =>
    exact ⟨.empty _, Operand.compile_readsEarlier context datum earlier⟩
  | binding site pattern producer continuation ihProducer ihContinuation =>
    let atBind := offset + producer.bindings
    let inner : Context κ := (site, atBind) :: context
    have outside : context.earlier atBind := Context.earlier_of_le earlier (by dsimp [atBind]; omega)
    have inside : inner.earlier (atBind + 1) := Context.push_earlier site outside
    obtain ⟨ordered, reads⟩ := ihProducer context offset earlier
    obtain ⟨laterOrdered, laterReads⟩ := ihContinuation inner (atBind + 1) inside
    have parentEarlier : ∀ ancestor, parent context site = some ancestor → ancestor < atBind :=
      fun _ found => outside _ (parent_mem found)
    constructor
    · simp only [lower]
      apply ordered.append
      rw [lower_length]
      exact .bind parentEarlier (by simpa only [lower_length] using reads)
        (Operand.compile_readsEarlier inner pattern inside) laterOrdered
    · simp only [lower, List.length_append, List.length_cons, lower_length]
      change (lower continuation inner (atBind + 1)).result.readsEarlier _
      have same : offset + (producer.bindings + (continuation.bindings + 1)) =
          atBind + 1 + continuation.bindings := by dsimp [atBind]; omega
      rw [same]
      simpa only [lower_length] using laterReads

def Plan.templateCount (plan : Plan κ Γ star) : Nat := 3 * plan.code.length + 1

theorem lower_templateCount [DecidableEq κ.Key] {code : Comp κ Γ star Ty}
    (shape : Fragment κ Γ star Ty ending code) (context : Context κ) (offset : Nat) :
    (lower shape context offset).templateCount = 3 * shape.bindings + 1 := by
  rw [Plan.templateCount, lower_length]

def Plan.sourceDebit (plan : Plan κ Γ star) : Nat := 3 * plan.code.length + plan.ending.debit

theorem lower_debit [DecidableEq κ.Key] {code : Comp κ Γ star Ty}
    (shape : Fragment κ Γ star Ty ending code) (context : Context κ) (offset : Nat) :
    (lower shape context offset).sourceDebit = shape.moves := by
  rw [Plan.sourceDebit, lower_length, lower_ending, Fragment.moves_eq]

def Plan.operandWeight (weight : Operand κ Γ star → Nat) (plan : Plan κ Γ star) : Nat :=
  (plan.code.map (fun binding => weight binding.pattern + weight binding.value)).sum + weight plan.result

def Fragment.operandWeight (weight : Data κ Γ star → Nat) :
    {ending : ExitKind} → {code : Comp κ Γ star Ty} → Fragment κ Γ star Ty ending code → Nat
  | _, _, .hold datum => weight datum
  | _, _, .call datum => weight datum
  | _, _, .binding _ pattern left right =>
    left.operandWeight weight + weight pattern + right.operandWeight weight

theorem Operand.compile_slots_le [DecidableEq κ.Key] (context : Context κ) (datum : Data κ Γ star) :
    (Operand.compile context datum).names.length ≤ (support datum).length := by
  simpa only [Operand.compile, firstNames, List.length_reverse] using
    (List.dedup_sublist ((support datum).reverse)).length_le

theorem lower_operandWeight_le [DecidableEq κ.Key]
    (residual : Operand κ Γ star → Nat) (authored : Data κ Γ star → Nat)
    (operandBound : ∀ context datum, residual (.compile context datum) ≤ authored datum)
    {code : Comp κ Γ star Ty}
    (shape : Fragment κ Γ star Ty ending code) (context : Context κ) (offset : Nat) :
    (lower shape context offset).operandWeight residual ≤ shape.operandWeight authored := by
  induction shape generalizing context offset with
  | hold datum =>
    simpa [Plan.operandWeight, lower, Fragment.operandWeight] using operandBound context datum
  | call datum =>
    simpa [Plan.operandWeight, lower, Fragment.operandWeight] using operandBound context datum
  | binding site pattern left right ihLeft ihRight =>
    let inner : Context κ := (site, offset + left.bindings) :: context
    have leftBound := ihLeft context offset
    have rightBound := ihRight inner (offset + left.bindings + 1)
    have patternBound := operandBound inner pattern
    simp only [Plan.operandWeight, lower, Fragment.operandWeight, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons] at leftBound rightBound ⊢
    dsimp only [inner] at rightBound patternBound
    omega

def Plan.scopeReferences (plan : Plan κ Γ star) : Nat :=
  plan.operandWeight fun operand => operand.names.length

def Fragment.nameUses {code : Comp κ Γ star Ty} (shape : Fragment κ Γ star Ty ending code) : Nat :=
  shape.operandWeight fun datum => (support datum).length

/-- The shared scope graph uses one link per binding. The number of
operand coordinates is bounded by the number of authored name uses. -/
theorem lower_scopeReferences_le [DecidableEq κ.Key] {code : Comp κ Γ star Ty}
    (shape : Fragment κ Γ star Ty ending code) (context : Context κ) (offset : Nat) :
    (lower shape context offset).scopeReferences ≤ shape.nameUses :=
  lower_operandWeight_le _ _ Operand.compile_slots_le shape context offset

theorem Operand.compile_nodes [DecidableEq κ.Key] (context : Context κ) (datum : Data κ Γ star) :
    (Operand.compile context datum).assemble.nodes = termSize datum := by
  change (Assembly.lower (Assembly.contextual _ _) (FiniteSupport.compile
    (firstNames (support datum)) datum (fun _ member => mem_firstNames.mpr member))).nodes = _
  rw [Assembly.lower_size, Assembly.dense_size]

/-- Size in portable instruction templates and their operand coordinates.
Literal and declaration payloads use references to their source objects. -/
def Plan.size (plan : Plan κ Γ star) : Nat :=
  plan.templateCount + plan.operandWeight fun operand => operand.assemble.nodes + 2 * operand.names.length

def Fragment.size {code : Comp κ Γ star Ty} (shape : Fragment κ Γ star Ty ending code) : Nat :=
  shape.bindings + shape.operandWeight termSize

theorem Fragment.operandWeight_scale (rate : Nat) (weight : Data κ Γ star → Nat)
    {code : Comp κ Γ star Ty} (shape : Fragment κ Γ star Ty ending code) :
    shape.operandWeight (fun datum => rate * weight datum) = rate * shape.operandWeight weight := by
  induction shape with
  | hold => rfl
  | call => rfl
  | binding _ _ _ _ left right =>
    simp only [operandWeight, left, right, Nat.mul_add]

theorem lower_size [DecidableEq κ.Key] {code : Comp κ Γ star Ty}
    (shape : Fragment κ Γ star Ty ending code) (context : Context κ) (offset : Nat) :
    (lower shape context offset).size ≤ 3 * shape.size + 1 := by
  have operands := lower_operandWeight_le
    (fun operand => operand.assemble.nodes + 2 * operand.names.length)
    (fun datum => 3 * termSize datum) (fun context datum => by
      rw [Operand.compile_nodes]
      have coordinates := (Operand.compile_slots_le context datum).trans (Assembly.support_le_size datum)
      omega) shape context offset
  rw [Fragment.operandWeight_scale] at operands
  rw [Plan.size, lower_templateCount, Fragment.size, Nat.mul_add]
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.BindingPlans
