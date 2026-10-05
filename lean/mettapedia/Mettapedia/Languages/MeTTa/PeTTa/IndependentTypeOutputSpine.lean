import Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutputRoot

/-!
# Incremental output spines for independent structural typing

Proper tuple construction and Prolog's incremental cons construction are
operationally different when a queried element can observe the unfinished
output spine. This module represents that spine explicitly. Its private
cell bindings are invisible only under a proved support condition; the
shared-output case is not silently identified with the eager tuple model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.Spine

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.UnificationRenaming
open Mettapedia.Logic.LP.IndependentOutputUnification
open IntrinsicTypeFacts (signature TypeTerm Declaration)
open Structural Admission

/-- Tuple constructors keep their arity; cons and nil are separate symbols.
The distinction makes an unfinished list different from a proper tuple. -/
abbrev spineSignature : LPSignature where
  constants := Sum IntrinsicTypeFacts.Scalar Unit
  vars := Nat
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Sum Nat Unit
  functionArity
    | .inl arity => arity
    | .inr _ => 2

abbrev SpineTerm := Term spineSignature

/-- Preserve all payload variables and their aliases when moving a type
term into the spine signature. A payload is not an opaque constant. -/
def embed : TypeTerm → SpineTerm
  | .var name => .var name
  | .const value => .const (.inl value)
  | .app arity children => .app (.inl arity) (fun index => embed (children index))

def extend (store : Subst signature) : Subst spineSignature :=
  fun name => embed (store name)

@[simp] theorem embed_var (name : Nat) : embed (.var name) = .var name := rfl

@[simp] theorem embed_apply (store : Subst signature) (term : TypeTerm) :
    embed (store.applyTerm term) = (extend store).applyTerm (embed term) := by
  induction term with
  | var _ => rfl
  | const _ => rfl
  | app arity children ih => simp only [Subst.applyTerm, embed, ih]

@[simp] theorem embed_freeVars (term : TypeTerm) : (embed term).freeVars = term.freeVars := by
  induction term with
  | var _ => rfl
  | const _ => rfl
  | app arity children ih =>
      simp only [embed, Term.freeVars, ih]
      rfl

@[simp] theorem extend_id : extend (Subst.id signature) = Subst.id spineSignature := rfl

@[simp] theorem extend_comp (first second : Subst signature) :
    extend (first ∘ₛ second) = extend first ∘ₛ extend second := by
  funext name
  exact embed_apply first (second name)

def nil : SpineTerm := .const (.inr ())

def cons (head tail : SpineTerm) : SpineTerm :=
  .app (.inr ()) (fun index => if index.val = 0 then head else tail)

@[simp] theorem apply_nil (store : Subst spineSignature) : store.applyTerm nil = nil := rfl

@[simp] theorem apply_cons (store : Subst spineSignature) (head tail : SpineTerm) :
    store.applyTerm (cons head tail) = cons (store.applyTerm head) (store.applyTerm tail) := by
  simp only [cons, Subst.applyTerm]
  congr 1
  funext index
  split <;> rfl

@[simp] theorem cons_freeVars (head tail : SpineTerm) :
    (cons head tail).freeVars = head.freeVars ∪ tail.freeVars := by
  ext name
  change name ∈ (Term.app (Sum.inr ()) (fun index : Fin 2 => if index.val = 0 then head else tail)).freeVars ↔ _
  rw [Term.mem_freeVars_app (σ := spineSignature)]
  simp only [Finset.mem_union]
  constructor
  · rintro ⟨index, present⟩
    fin_cases index
    · exact Or.inl present
    · exact Or.inr present
  · rintro (present | present)
    · exact ⟨0, present⟩
    · exact ⟨1, present⟩

/-- Close a list of payloads over a chosen tail. This also describes an
unfinished prefix when the tail is an unbound private variable. -/
def chain : List SpineTerm → SpineTerm → SpineTerm
  | [], tail => tail
  | head :: rest, tail => cons head (chain rest tail)

@[simp] theorem apply_chain (store : Subst spineSignature) (heads : List SpineTerm) (tail : SpineTerm) :
    store.applyTerm (chain heads tail) = chain (heads.map store.applyTerm) (store.applyTerm tail) := by
  induction heads with
  | nil => rfl
  | cons head rest ih => simp only [chain, apply_cons, List.map_cons, ih]

/-- Ordinary first-order matching of a fresh tail performs exactly one cons
extension. There is no advance binding of the remaining tail to a list. -/
theorem match_fresh_cell (tail head next : Nat) (headApart : tail ≠ head) (nextApart : tail ≠ next) :
    unifyTotal [(cons (.var head) (.var next), .var tail)] =
      some (Subst.single tail (cons (.var head) (.var next))) := by
  apply nonvariable_output_match
  · intro name same
    cases same
  · simp only [cons_freeVars, Term.freeVars, Finset.mem_union, Finset.mem_singleton, not_or]
    exact ⟨headApart, nextApart⟩

/-- Closing happens only at the empty-input rule. -/
theorem match_fresh_end (tail : Nat) :
    unifyTotal [(nil, .var tail)] = some (Subst.single tail nil) := by
  apply nonvariable_output_match
  · intro name same
    cases same
  · simp [nil, Term.freeVars]

/-- A cell extension cannot change a payload that contains no tail name.
This is the actual substitution generated by the preceding unifier. -/
theorem cell_preserves_payload (tail head next : Nat) (term : TypeTerm)
    (absent : tail ∉ term.freeVars) :
    (Subst.single tail (cons (.var head) (.var next))).applyTerm (embed term) = embed term := by
  apply Subst.applyTerm_eq_self
  intro name present
  have different : name ≠ tail := by
    intro same
    apply absent
    simpa only [embed_freeVars, same] using present
  exact Subst.single_ne _ different

/-- The additional tails occupy a namespace outside all field heads and
all recursive field-query allocations. -/
def tailName (path : Path) (position : Nat) : Nat := freshSupply (6 :: path) position

theorem tail_ne_field (path : Path) (position field : Nat) :
    tailName path position ≠ freshSupply (3 :: path) field := by
  simp [tailName, fresh_supply_injective]

theorem tail_ne_child (path stem : Path) (position field slot : Nat) :
    tailName path position ≠ freshSupply (stem ++ 0 :: field :: 4 :: path) slot := by
  intro same
  have paths := ((fresh_supply_injective _ _ _ _).mp same).1
  have lengths := congrArg List.length paths
  simp only [List.length_cons, List.length_append] at lengths
  omega

theorem tail_injective (path : Path) : Function.Injective (tailName path) := by
  intro first second same
  exact ((fresh_supply_injective _ _ _ _).mp same).2

/-- The existing query exclusion law discharges tail absence for every
actual child answer. It is not an assumed property of a replacement oracle. -/
theorem field_answer_excludes_tail (library : List Declaration) (fuel : Nat)
    (path : Path) (position tail : Nat) (subject : TypeTerm) (answers : List TypeTerm)
    (returned : fieldAnswers library fuel path position subject = some answers) :
    ∀ answer ∈ answers, tailName path tail ∉ answer.freeVars := by
  unfold fieldAnswers at returned
  split at returned
  · simp only [Option.some.injEq] at returned
    subst answers
    intro answer present
    simp only [List.mem_singleton] at present
    subst answer
    simpa only [Term.freeVars, Finset.mem_singleton] using tail_ne_field path tail position
  · apply run_output_excludes_name library fuel (0 :: position :: 4 :: path) subject
      (some (.var (freshSupply (3 :: path) position))) answers (tailName path tail)
      (fun stem slot => (tail_ne_child path stem tail position slot).symm) _ returned
    intro term present
    simp only [Option.toList_some, List.mem_singleton] at present
    subst term
    simpa only [Term.freeVars, Finset.mem_singleton] using tail_ne_field path tail position

/-- Matching a field answer back to its own field also fixes every tail.
Solved-form relevance rules out a previously excluded tail returning through
later substitution ranges. -/
theorem field_match_fixes_tail (library : List Declaration) (fuel : Nat)
    (path : Path) (position tail : Nat) (subject : TypeTerm) (answers : List TypeTerm)
    (returned : fieldAnswers library fuel path position subject = some answers)
    (candidate : TypeTerm) (present : candidate ∈ answers) (refinement : Subst signature)
    (matched : unifyTotal [(candidate, .var (freshSupply (3 :: path) position))] = some refinement) :
    refinement (tailName path tail) = .var (tailName path tail) := by
  apply (unifyTotal_relevantIdempotent _ _ matched).fixes
  have absent := field_answer_excludes_tail library fuel path position tail subject answers returned candidate present
  simp only [eqVars, Term.freeVars, Finset.union_empty, Finset.mem_union,
    Finset.mem_singleton, not_or]
  exact ⟨absent, tail_ne_field path tail position⟩


/-- A payload matcher keeps its actual finite solved-form support after the
signature embedding. It cannot acquire a cons-tail variable by embedding. -/
theorem extend_relevant (store : Subst signature) (support : Finset Nat)
    (relevant : store.RelevantIdempotent support) :
    (extend store).RelevantIdempotent support where
  fixes name absent := by simp only [extend, relevant.fixes name absent, embed]
  range name present := by simpa only [extend, embed_freeVars] using relevant.range name present
  unbound name other occurs := by
    have present : other ∈ (store name).freeVars := by simpa only [extend, embed_freeVars] using occurs
    simp only [extend, relevant.unbound name other present, embed]

/-- A checked field action consists of the actual matcher's substitution and
its relevant finite support. The constructor below derives this evidence
from the existing recursive intrinsic query. -/
structure FieldAction (path : Path) (position : Nat) where
  substitution : Subst signature
  support : Finset Nat
  relevant : substitution.RelevantIdempotent support
  names : ∀ name ∈ support, FieldName path position name

private theorem field_values_supported (library : List Declaration) (fuel : Nat)
    (path : Path) (position : Nat) (subject : TypeTerm) (answers : List TypeTerm)
    (returned : fieldAnswers library fuel path position subject = some answers)
    (candidate : TypeTerm) (present : candidate ∈ answers) :
    ∀ name ∈ candidate.freeVars, FieldName path position name := by
  unfold fieldAnswers at returned
  split at returned
  · simp only [Option.some.injEq] at returned
    subst answers
    simp only [List.mem_singleton] at present
    subst candidate
    intro name occurs
    exact Or.inl ((Term.mem_freeVars_var (σ := signature)).mp occurs)
  · exact field_answer_names library fuel path position subject answers returned candidate present

def actualFieldAction (library : List Declaration) (fuel : Nat)
    (path : Path) (position : Nat) (subject : TypeTerm) (answers : List TypeTerm)
    (returned : fieldAnswers library fuel path position subject = some answers)
    (candidate : TypeTerm) (present : candidate ∈ answers) (refinement : Subst signature)
    (accepted : unifyTotal [(candidate, .var (freshSupply (3 :: path) position))] = some refinement) :
    FieldAction path position where
  substitution := refinement
  support := eqVars [(candidate, .var (freshSupply (3 :: path) position))]
  relevant := unifyTotal_relevantIdempotent _ _ accepted
  names name member := by
    simp only [eqVars, Term.freeVars, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at member
    rcases member with inside | equal
    · exact field_values_supported library fuel path position subject answers returned candidate present name inside
    · exact Or.inl equal

private theorem tail_not_field_name (path : Path) (tail field : Nat) :
    ¬ FieldName path field (tailName path tail) := by
  rintro (equal | ⟨stem, slot, equal⟩)
  · exact tail_ne_field path tail field equal
  · exact tail_ne_child path stem tail field slot equal

/-- One cell of the output spine; the last tail remains unbound. -/
def cell (path : Path) (position : Nat) : Subst spineSignature :=
  Subst.single (tailName path position)
    (cons (.var (freshSupply (3 :: path) position)) (.var (tailName path (position + 1))))

def closeTail (path : Path) (position : Nat) : Subst spineSignature :=
  Subst.single (tailName path position) nil

theorem cell_is_match (path : Path) (position : Nat) :
    unifyTotal [(cons (.var (freshSupply (3 :: path) position)) (.var (tailName path (position + 1))),
      .var (tailName path position))] = some (cell path position) := by
  exact match_fresh_cell _ _ _ (tail_ne_field path position position)
    (fun same => by have equal := tail_injective path same; omega)

theorem closeTail_is_match (path : Path) (position : Nat) :
    unifyTotal [(nil, .var (tailName path position))] = some (closeTail path position) :=
  match_fresh_end _

/-- A current field's actual refinement commutes with building any later
cell. This is the substantive reordering law: their solved supports are
proved disjoint, including the ranges of the substitutions. -/
theorem action_commutes_later_cell (path : Path) (position later : Nat)
    (different : position ≠ later) (action : FieldAction path position) :
    extend action.substitution ∘ₛ cell path later =
      cell path later ∘ₛ extend action.substitution := by
  apply relevant_substitutions_commute _ _ action.support
    (eqVars [(cons (.var (freshSupply (3 :: path) later)) (.var (tailName path (later + 1))),
      .var (tailName path later))])
    (extend_relevant _ _ action.relevant) (unifyTotal_relevantIdempotent _ _ (cell_is_match path later))
  apply Finset.disjoint_left.mpr
  intro name present member
  have supported := action.names name present
  simp only [eqVars, cons_freeVars, Term.freeVars, Finset.union_empty, Finset.mem_union,
    Finset.mem_singleton] at member
  rcases member with (rfl | rfl) | rfl
  · exact field_names_disjoint path position later _ different supported (Or.inl rfl)
  · exact tail_not_field_name path (later + 1) position supported
  · exact tail_not_field_name path later position supported

theorem action_commutes_closeTail (path : Path) (position tail : Nat)
    (action : FieldAction path position) :
    extend action.substitution ∘ₛ closeTail path tail = closeTail path tail ∘ₛ extend action.substitution := by
  apply relevant_substitutions_commute _ _ action.support
    (eqVars [(nil, .var (tailName path tail))])
    (extend_relevant _ _ action.relevant) (unifyTotal_relevantIdempotent _ _ (closeTail_is_match path tail))
  apply Finset.disjoint_left.mpr
  intro name present member
  simp only [eqVars, nil, Term.freeVars, Finset.empty_union, Finset.union_empty, Finset.mem_singleton] at member
  subst name
  exact tail_not_field_name path tail position (action.names _ present)

/-- Build the complete spine before processing any fields. This is the
old eager schedule, represented with explicit cons cells for comparison. -/
def build (path : Path) (position : Nat) : Nat → Subst spineSignature
  | 0 => closeTail path position
  | count + 1 => build path (position + 1) count ∘ₛ cell path position

theorem action_commutes_later_build (path : Path) (position later count : Nat)
    (after : position < later) (action : FieldAction path position) :
    extend action.substitution ∘ₛ build path later count =
      build path later count ∘ₛ extend action.substitution := by
  induction count generalizing later with
  | zero => exact action_commutes_closeTail path position later action
  | succ count ih =>
      simp only [build]
      rw [← Subst.comp_assoc, ih (later + 1) (by omega), Subst.comp_assoc,
        action_commutes_later_cell path position later (by omega) action, ← Subst.comp_assoc]

/-- The action sequence is indexed by source position, so preserving its
order also preserves every answer's field position. -/
inductive FieldActions (path : Path) : Nat → Type where
  | done (position : Nat) : FieldActions path position
  | step {position : Nat} (action : FieldAction path position)
      (later : FieldActions path (position + 1)) : FieldActions path position

namespace FieldActions

def length {path : Path} {position : Nat} : FieldActions path position → Nat
  | .done _ => 0
  | .step _ later => later.length + 1

def payload {path : Path} {position : Nat} : FieldActions path position → Subst spineSignature
  | .done _ => Subst.id spineSignature
  | .step action later => later.payload ∘ₛ extend action.substitution

/-- Bind one cell, process its field, then continue; bind nil only after the
last field. This is the incremental schedule used by Prolog maplist. -/
def incremental {path : Path} {position : Nat} : FieldActions path position → Subst spineSignature
  | .done position => closeTail path position
  | .step action later => later.incremental ∘ₛ extend action.substitution ∘ₛ cell path position

/-- Processing any checked field sequence incrementally produces exactly
the eager schedule's substitution. The proof commutes each field action
only past later private cells; no query-output correspondence is assumed. -/
theorem incremental_eq_eager {path : Path} {position : Nat} (actions : FieldActions path position) :
    actions.incremental = actions.payload ∘ₛ build path position actions.length := by
  induction actions with
  | done position => exact (Subst.comp_id_left _).symm
  | @step position action later ih =>
      simp only [incremental, length, payload, build]
      rw [ih, Subst.comp_assoc later.payload, ← action_commutes_later_build path position
        (position + 1) later.length (by omega) action]
      simp only [Subst.comp_assoc]

end FieldActions

/-- Source payloads and the unvisited field and tail names are unchanged
at an admitted maplist entry. No condition is placed on already built cells. -/
structure Ready (path : Path) (position : Nat) (items : List TypeTerm)
    (store : Subst spineSignature) : Prop where
  source : ∀ item ∈ items, store.applyTerm (embed item) = embed item
  field : ∀ later, position ≤ later → store (freshSupply (3 :: path) later) = .var (freshSupply (3 :: path) later)
  tail : ∀ later, position ≤ later → store (tailName path later) = .var (tailName path later)

theorem ready_id (path : Path) (position : Nat) (items : List TypeTerm) :
    Ready path position items (Subst.id spineSignature) where
  source _ _ := Subst.applyTerm_id _
  field _ _ := rfl
  tail _ _ := rfl

theorem action_preserves_apart (path : Path) (position : Nat)
    (action : FieldAction path position) (term : TypeTerm)
    (apart : FieldsApart path position term) :
    action.substitution.applyTerm term = term := by
  apply Subst.applyTerm_eq_self
  intro name occurs
  apply action.relevant.fixes
  intro present
  exact apart position (Nat.le_refl _) name occurs (action.names name present)

theorem action_fixes_other_field (path : Path) (position later : Nat)
    (action : FieldAction path position) (different : position ≠ later) :
    action.substitution (freshSupply (3 :: path) later) = .var (freshSupply (3 :: path) later) := by
  apply action.relevant.fixes
  intro present
  exact field_names_disjoint path position later _ different
    (action.names _ present) (Or.inl rfl)

theorem action_fixes_tail (path : Path) (position tail : Nat) (action : FieldAction path position) :
    action.substitution (tailName path tail) = .var (tailName path tail) := by
  apply action.relevant.fixes
  intro present
  exact tail_not_field_name path tail position (action.names _ present)

/-- Immediately after the current cons is installed, both actual child
operands still equal their original payloads. In particular, this is not
true if the source contains the current output tail. -/
theorem cell_preserves_query (path : Path) (position : Nat) (subject : TypeTerm)
    (rest : List TypeTerm) (store : Subst spineSignature)
    (ready : Ready path position (subject :: rest) store)
    (tailAbsent : tailName path position ∉ subject.freeVars) :
    (cell path position ∘ₛ store).applyTerm (embed subject) = embed subject ∧
    (cell path position ∘ₛ store) (freshSupply (3 :: path) position) =
      .var (freshSupply (3 :: path) position) := by
  constructor
  · rw [Subst.applyTerm_comp, ready.source subject List.mem_cons_self]
    exact cell_preserves_payload _ _ _ subject tailAbsent
  · change (cell path position).applyTerm (store (freshSupply (3 :: path) position)) = _
    rw [ready.field position (Nat.le_refl _)]
    exact Subst.single_ne (σ := spineSignature) _ (tail_ne_field path position position).symm

/-- One real field refinement advances the frame invariant. Its solved
support excludes later fields and all tail variables, including its ranges. -/
theorem ready_step (path : Path) (position : Nat) (subject : TypeTerm) (rest : List TypeTerm)
    (store : Subst spineSignature) (ready : Ready path position (subject :: rest) store)
    (sourceApart : ∀ term ∈ rest, FieldsApart path position term)
    (tailsApart : ∀ term ∈ rest, tailName path position ∉ term.freeVars)
    (action : FieldAction path position) :
    Ready path (position + 1) rest (extend action.substitution ∘ₛ cell path position ∘ₛ store) where
  source term present := by
    simp only [Subst.applyTerm_comp]
    rw [ready.source term (List.mem_cons_of_mem _ present)]
    change (extend action.substitution).applyTerm
      ((Subst.single (tailName path position) (cons (.var (freshSupply (3 :: path) position))
        (.var (tailName path (position + 1))))).applyTerm (embed term)) = _
    rw [cell_preserves_payload _ _ _ term (tailsApart term present), ← embed_apply,
      action_preserves_apart path position action term (sourceApart term present)]
  field later after := by
    rw [Subst.comp_assoc]
    change (extend action.substitution).applyTerm
      ((cell path position).applyTerm (store (freshSupply (3 :: path) later))) = _
    rw [ready.field later (by omega)]
    rw [show (cell path position).applyTerm (.var (freshSupply (3 :: path) later)) =
      .var (freshSupply (3 :: path) later) from Subst.single_ne (σ := spineSignature) _ (tail_ne_field path position later).symm]
    change embed (action.substitution (freshSupply (3 :: path) later)) = _
    rw [action_fixes_other_field path position later action (by omega)]
    rfl
  tail later after := by
    rw [Subst.comp_assoc]
    change (extend action.substitution).applyTerm
      ((cell path position).applyTerm (store (tailName path later))) = _
    rw [ready.tail later (by omega)]
    rw [show (cell path position).applyTerm (.var (tailName path later)) =
      .var (tailName path later) from Subst.single_ne (σ := spineSignature) _
        (fun same => by have equal := tail_injective path same; omega)]
    change embed (action.substitution (tailName path later)) = _
    rw [action_fixes_tail path position later action]
    rfl

/-- The actual matcher sees a fresh tail at every admitted entry. -/
theorem ready_cell_match (path : Path) (position : Nat) (items : List TypeTerm)
    (store : Subst spineSignature) (ready : Ready path position items store) :
    unifyTotal [(cons (.var (freshSupply (3 :: path) position)) (.var (tailName path (position + 1))),
      store (tailName path position))] = some (cell path position) := by
  rw [ready.tail position (Nat.le_refl _)]
  exact cell_is_match path position

/-- Actual child answers always match their own fresh field. The skipped
source-variable case is the identity equation, not an omitted alternative. -/
theorem field_match_succeeds (library : List Declaration) (fuel : Nat)
    (path : Path) (position : Nat) (subject : TypeTerm) (answers : List TypeTerm)
    (returned : fieldAnswers library fuel path position subject = some answers)
    (candidate : TypeTerm) (present : candidate ∈ answers) :
    ∃ refinement, unifyTotal [(candidate, .var (freshSupply (3 :: path) position))] = some refinement := by
  unfold fieldAnswers at returned
  split at returned
  · simp only [Option.some.injEq] at returned
    subst answers
    simp only [List.mem_singleton] at present
    subst candidate
    exact ⟨Subst.id signature, by simp [unifyTotal]⟩
  · exact query_variable_match_succeeds library fuel (0 :: position :: 4 :: path) subject
      (freshSupply (3 :: path) position)
      (fun stem slot => Ne.symm (field_name_ne_child_allocation path stem position position slot))
      answers returned candidate present

/-- A trace keeps the answer as well as its actual matching action. The
support certificate is derived when the answer is produced, not postulated. -/
inductive FieldTrace (path : Path) : Nat → Type where
  | done (position : Nat) : FieldTrace path position
  | step {position : Nat} (candidate : TypeTerm) (action : FieldAction path position)
      (later : FieldTrace path (position + 1)) : FieldTrace path position

namespace FieldTrace

def values {path : Path} {position : Nat} : FieldTrace path position → List TypeTerm
  | .done _ => []
  | .step candidate _ later => candidate :: later.values

def actions {path : Path} {position : Nat} : FieldTrace path position → FieldActions path position
  | .done position => .done position
  | .step _ action later => .step action later.actions

@[simp] theorem actions_length {path : Path} {position : Nat} (trace : FieldTrace path position) :
    trace.actions.length = trace.values.length := by
  induction trace with
  | done => rfl
  | step candidate action later ih => simp only [actions, values, FieldActions.length, List.length_cons, ih]

end FieldTrace

/-- Ordered field queries with their successful first-order matcher traces.
`none` still denotes an incomplete query and `some []` normal exhaustion. -/
noncomputable def traces (library : List Declaration) (fuel : Nat) (path : Path) (position : Nat) :
    List TypeTerm → Option (List (FieldTrace path position))
  | [] => some [.done position]
  | subject :: rest =>
      match returned : fieldAnswers library fuel path position subject with
      | none => none
      | some first => collect first.attach fun entry =>
          match accepted : unifyTotal [(entry.val, .var (freshSupply (3 :: path) position))] with
          | none => some []
          | some refinement =>
              let action := actualFieldAction library fuel path position subject first returned
                entry.val entry.property refinement accepted
              (traces library fuel path (position + 1) rest).map
                (List.map (FieldTrace.step entry.val action))

/-- Attaching membership evidence leaves the ordered branching unchanged. -/
private theorem collect_attached {α β : Type} (items : List α) (visit : α → Option (List β)) :
    collect items.attach (fun item => visit item.val) = collect items visit := by
  have same := Coordinates.collect_inputs items.attach Subtype.val visit
  simpa using same.symm

/-- The trace enumerator retains the original query's order, multiplicity,
normal exhaustion, and incompleteness. No failed matcher was erased without
proving that the corresponding child output actually matches. -/
theorem traces_values (library : List Declaration) (fuel : Nat) (path : Path)
    (position : Nat) (items : List TypeTerm) :
    (traces library fuel path position items).map (List.map FieldTrace.values) =
      fieldRows library fuel path position items := by
  induction items generalizing position with
  | nil => rfl
  | cons subject rest ih =>
      simp only [traces, fieldRows]
      split
      · rename_i returned
        simp only [returned, Option.map_none, bind, Option.bind]
      · rename_i first returned
        simp only [returned, bind, Option.bind]
        rw [← Coordinates.collect_results]
        conv_rhs => rw [← collect_attached]
        apply Coordinates.collect_congr
        intro entry member
        split
        · rename_i accepted
          obtain ⟨refinement, matched⟩ := field_match_succeeds library fuel path position subject
            first returned entry.val entry.property
          rw [accepted] at matched
          cases matched
        · rename_i refinement accepted
          simp only [Option.map_map, List.map_map, Function.comp_def, FieldTrace.values]
          have later := ih (position + 1)
          cases got : traces library fuel path (position + 1) rest with
          | none => simp only [got, Option.map_none] at later ⊢; rw [← later]; rfl
          | some values =>
              simp only [got, Option.map_some] at later ⊢
              rw [← later]
              simp only [Option.map_some, List.map_map, Function.comp_def]

/-- Every complete ordered trace gives the same entire final store under
the eager and incremental spine schedules. Aliases and correlations are
preserved by equality of substitutions, before any answer projection. -/
theorem ordered_spine_stores (library : List Declaration) (fuel : Nat) (path : Path)
    (position : Nat) (items : List TypeTerm) (initial : Subst spineSignature) :
    (traces library fuel path position items).map (List.map fun trace =>
      trace.actions.incremental ∘ₛ initial) =
    (traces library fuel path position items).map (List.map fun trace =>
      trace.actions.payload ∘ₛ build path position trace.actions.length ∘ₛ initial) := by
  congr 1
  funext rows
  apply List.map_congr_left
  intro trace _
  rw [trace.actions.incremental_eq_eager]

/-- Each trace node records a real child-query branch and its real unifier. -/
inductive QueryTrace (library : List Declaration) (fuel : Nat) (path : Path) :
    (position : Nat) → List TypeTerm → FieldTrace path position → Prop where
  | done (position : Nat) : QueryTrace library fuel path position [] (.done position)
  | step {position : Nat} {subject : TypeTerm} {rest : List TypeTerm}
      {candidate : TypeTerm} {action : FieldAction path position}
      {later : FieldTrace path (position + 1)} {answers : List TypeTerm}
      (returned : fieldAnswers library fuel path position subject = some answers)
      (present : candidate ∈ answers)
      (accepted : unifyTotal [(candidate, .var (freshSupply (3 :: path) position))] = some action.substitution)
      (tail : QueryTrace library fuel path (position + 1) rest later) :
      QueryTrace library fuel path position (subject :: rest) (.step candidate action later)

/-- The ordered enumerator contains only actual recursive query traces. -/
theorem traces_sound (library : List Declaration) (fuel : Nat) (path : Path)
    (position : Nat) (items : List TypeTerm) (rows : List (FieldTrace path position))
    (returned : traces library fuel path position items = some rows) :
    ∀ trace ∈ rows, QueryTrace library fuel path position items trace := by
  induction items generalizing position rows with
  | nil =>
      simp only [traces, Option.some.injEq] at returned
      subst rows
      intro trace present
      simp only [List.mem_singleton] at present
      subst trace
      exact .done position
  | cons subject rest ih =>
      simp only [traces] at returned
      split at returned
      · cases returned
      · rename_i answers queried
        intro trace present
        obtain ⟨entry, _, branch, branchRun, inBranch⟩ := collect_member _ _ _ returned present
        split at branchRun
        · simp only [Option.some.injEq] at branchRun
          subst branch
          exact False.elim (List.not_mem_nil inBranch)
        · rename_i refinement accepted
          cases laterRun : traces library fuel path (position + 1) rest with
          | none => simp only [laterRun, Option.map_none] at branchRun; cases branchRun
          | some laterRows =>
              simp only [laterRun, Option.map_some, Option.some.injEq] at branchRun
              subst branch
              obtain ⟨later, member, rfl⟩ := List.mem_map.mp inBranch
              exact .step queried entry.property accepted (ih (position + 1) laterRows laterRun later member)

/-- A spine execution exposes the actual operands at every step. It builds
one cell before the field query, performs that field's actual match, and
closes the current tail only in the empty-input rule. -/
inductive Executes (library : List Declaration) (fuel : Nat) (path : Path) :
    (position : Nat) → List TypeTerm → Subst spineSignature → FieldTrace path position → Prop where
  | done {position : Nat} {store : Subst spineSignature}
      (closed : unifyTotal [(nil, store (tailName path position))] = some (closeTail path position)) :
      Executes library fuel path position [] store (.done position)
  | step {position : Nat} {subject : TypeTerm} {rest : List TypeTerm}
      {store : Subst spineSignature} {candidate : TypeTerm} {action : FieldAction path position}
      {later : FieldTrace path (position + 1)} {answers : List TypeTerm}
      (cellMatched : unifyTotal [(cons (.var (freshSupply (3 :: path) position)) (.var (tailName path (position + 1))),
        store (tailName path position))] = some (cell path position))
      (sourceResolved : (cell path position ∘ₛ store).applyTerm (embed subject) = embed subject)
      (fieldResolved : (cell path position ∘ₛ store) (freshSupply (3 :: path) position) =
        .var (freshSupply (3 :: path) position))
      (returned : fieldAnswers library fuel path position subject = some answers)
      (present : candidate ∈ answers)
      (accepted : unifyTotal [(candidate, .var (freshSupply (3 :: path) position))] = some action.substitution)
      (tail : Executes library fuel path (position + 1) rest
        (extend action.substitution ∘ₛ cell path position ∘ₛ store) later) :
      Executes library fuel path position (subject :: rest) store (.step candidate action later)

/-- Allocation noncapture discharges every operational premise of the
incremental execution, including the source and required operand frame.
The frame is propagated through each actual solved-form refinement. -/
theorem admitted_query_trace_executes (library : List Declaration) (fuel : Nat) (path : Path)
    (position : Nat) (items : List TypeTerm) (trace : FieldTrace path position)
    (query : QueryTrace library fuel path position items trace)
    (store : Subst spineSignature) (ready : Ready path position items store)
    (apart : ∀ item ∈ items, AllocationApart path item) :
    Executes library fuel path position items store trace := by
  induction query generalizing store with
  | done position =>
      apply Executes.done
      rw [ready.tail position (Nat.le_refl _)]
      exact closeTail_is_match path position
  | @step position subject rest candidate action later answers returned present accepted tail ih =>
      have sourceApart : ∀ item ∈ rest, FieldsApart path position item :=
        fun item member => (apart item (List.mem_cons_of_mem _ member)).fieldsApart position
      have tailsApart : ∀ item ∈ rest, tailName path position ∉ item.freeVars :=
        fun item member => apart item (List.mem_cons_of_mem _ member) [6] position
      have operands := cell_preserves_query path position subject rest store ready
        (apart subject List.mem_cons_self [6] position)
      exact .step (ready_cell_match path position (subject :: rest) store ready)
        operands.1 operands.2 returned present accepted
        (ih (extend action.substitution ∘ₛ cell path position ∘ₛ store)
          (ready_step path position subject rest store ready sourceApart tailsApart action)
          (fun item member => apart item (List.mem_cons_of_mem _ member)))

/-- Every enumerated answer is realized by the incremental operational
rules from the initial store. This includes all ordered alternatives and
does not assume an eager/incremental query equivalence. -/
theorem traces_execute (library : List Declaration) (fuel : Nat) (path : Path)
    (position : Nat) (items : List TypeTerm) (rows : List (FieldTrace path position))
    (returned : traces library fuel path position items = some rows)
    (apart : ∀ item ∈ items, AllocationApart path item) :
    ∀ trace ∈ rows, Executes library fuel path position items (Subst.id spineSignature) trace := by
  intro trace present
  exact admitted_query_trace_executes library fuel path position items trace
    (traces_sound library fuel path position items rows returned trace present)
    (Subst.id spineSignature) (ready_id path position items) apart

namespace FieldActions

/-- The payload refinements, without the additional private spine cells. -/
def store {path : Path} {position : Nat} : FieldActions path position → Subst signature
  | .done _ => Subst.id signature
  | .step action later => later.store ∘ₛ action.substitution

@[simp] theorem payload_extend {path : Path} {position : Nat} (actions : FieldActions path position) :
    actions.payload = extend actions.store := by
  induction actions with
  | done => rfl
  | step action later ih => simp only [payload, store, extend_comp, ih]

end FieldActions

theorem build_fixes_field (path : Path) (position count field : Nat) :
    build path position count (freshSupply (3 :: path) field) = .var (freshSupply (3 :: path) field) := by
  induction count generalizing position with
  | zero => exact Subst.single_ne (σ := spineSignature) _ (tail_ne_field path position field).symm
  | succ count ih =>
      change (build path (position + 1) count).applyTerm
        (cell path position (freshSupply (3 :: path) field)) = _
      rw [show cell path position (freshSupply (3 :: path) field) = .var (freshSupply (3 :: path) field)
        from Subst.single_ne (σ := spineSignature) _ (tail_ne_field path position field).symm]
      exact ih (position + 1)

/-- The eager cell matcher builds exactly a closed cons chain in source
position order; its field payloads have not yet been refined. -/
theorem build_start (path : Path) (position count : Nat) :
    build path position count (tailName path position) =
      chain ((fieldVariables path position count).map embed) nil := by
  induction count generalizing position with
  | zero => exact Subst.single_eq (σ := spineSignature) _ _
  | succ count ih =>
      change (build path (position + 1) count).applyTerm
        (cell path position (tailName path position)) = _
      rw [show cell path position (tailName path position) =
        cons (.var (freshSupply (3 :: path) position)) (.var (tailName path (position + 1)))
        from Subst.single_eq (σ := spineSignature) _ _, apply_cons]
      change cons (build path (position + 1) count (freshSupply (3 :: path) position))
        (build path (position + 1) count (tailName path (position + 1))) = _
      rw [build_fixes_field, ih]
      rfl

/-- Only a finished spine is read back as a proper tuple. An open tail has
no tuple representation and is never silently turned into a closed list. -/
def readSpine : SpineTerm → Option (List SpineTerm)
  | .const (.inr _) => some []
  | .app (.inr _) children => (readSpine (children 1)).map (children 0 :: ·)
  | _ => none

@[simp] theorem read_chain (items : List SpineTerm) : readSpine (chain items nil) = some items := by
  induction items with
  | nil => rfl
  | cons head rest ih =>
      change (readSpine (chain rest nil)).map (head :: ·) = _
      rw [ih]
      rfl

/-- The completed incremental spine contains exactly the ordinary payload
refinements applied to the original field vector, preserving aliases. -/
theorem incremental_readback {path : Path} {position : Nat} (actions : FieldActions path position) :
    readSpine (actions.incremental (tailName path position)) =
      some (((fieldVariables path position actions.length).map actions.store.applyTerm).map embed) := by
  rw [actions.incremental_eq_eager, actions.payload_extend]
  change readSpine ((extend actions.store).applyTerm
    (build path position actions.length (tailName path position))) = _
  rw [build_start, apply_chain, apply_nil, read_chain]
  simp only [List.map_map, Function.comp_def, ← embed_apply]

/-- The open tail is observable if it is allowed to occur in a query.
This negative control is precisely the frame condition admission excludes. -/
theorem cell_changes_shared_source (path : Path) (position : Nat) :
    (cell path position).applyTerm (embed (.var (tailName path position))) ≠
      embed (.var (tailName path position)) := by
  rw [embed_var]
  change cell path position (tailName path position) ≠ .var (tailName path position)
  rw [show cell path position (tailName path position) =
    cons (.var (freshSupply (3 :: path) position)) (.var (tailName path (position + 1)))
    from Subst.single_eq (σ := spineSignature) _ _]
  intro same
  cases same

/-- Installing a cell does not make the list proper. Finishing the later
tail changes that observation, so eager construction is not valid generally. -/
theorem open_cell_has_no_readback (head tail : Nat) :
    readSpine (cons (.var head) (.var tail)) = none := rfl

theorem closed_cell_has_readback (head tail : Nat) :
    readSpine ((Subst.single tail nil).applyTerm (cons (.var head) (.var tail))) =
      some [(Subst.single tail nil).applyTerm (.var head)] := by
  rw [apply_cons]
  change readSpine (cons _ (Subst.single tail nil tail)) = _
  rw [Subst.single_eq (σ := spineSignature)]
  rfl

private theorem action_preserves_field_value (path : Path) (position later : Nat)
    (different : position ≠ later) (action : FieldAction path position) (term : TypeTerm)
    (supported : ∀ name ∈ term.freeVars, FieldName path later name) :
    action.substitution.applyTerm term = term := by
  apply Subst.applyTerm_eq_self
  intro name present
  apply action.relevant.fixes
  intro member
  exact field_names_disjoint path position later name different
    (action.names name member) (supported name present)

namespace QueryTrace

theorem length {library : List Declaration} {fuel : Nat} {path : Path}
    {position : Nat} {items : List TypeTerm} {trace : FieldTrace path position}
    (query : QueryTrace library fuel path position items trace) :
    trace.values.length = items.length := by
  induction query with
  | done => rfl
  | step returned present accepted tail ih => simp only [FieldTrace.values, List.length_cons, ih]

/-- Earlier field refinements fix the complete later constraint family,
not just each later field's root name. -/
theorem equations_fixed {library : List Declaration} {fuel : Nat} {path : Path}
    {position : Nat} {items : List TypeTerm} {trace : FieldTrace path position}
    (query : QueryTrace library fuel path position items trace)
    (earlier : Nat) (before : earlier < position) (action : FieldAction path earlier) :
    action.substitution.applyEqs (fieldEquations path position trace.values) =
      fieldEquations path position trace.values := by
  induction query with
  | done => rfl
  | @step position subject rest candidate own later answers returned present accepted tail ih =>
      have fixed := action_preserves_field_value path earlier position (by omega) action candidate
        (field_values_supported library fuel path position subject answers returned candidate present)
      have fieldFixed := action_fixes_other_field path earlier position action (by omega)
      simp only [FieldTrace.values, fieldEquations, Subst.applyEqs, List.map_cons]
      rw [fixed, show action.substitution.applyTerm (.var (freshSupply (3 :: path) position)) =
        .var (freshSupply (3 :: path) position) from fieldFixed]
      congr 1
      exact ih (by omega)

/-- Publish the payload component of a real incremental trace. Its joint
caller observations equal solving all the trace's field equations together.
This preserves correlations, rather than comparing answers one variable
at a time or quotienting a set of duplicate alternatives. -/
theorem publication {library : List Declaration} {fuel : Nat} {path : Path}
    {position : Nat} {items : List TypeTerm} {trace : FieldTrace path position}
    (query : QueryTrace library fuel path position items trace)
    (result : TypeTerm) (output : Nat) (observations : List TypeTerm)
    (outputApart : FieldsApart path position (.var output))
    (observationsApart : ∀ term ∈ observations, FieldsApart path position term) :
    solutions [(trace.actions.store.applyTerm result, .var output)] observations =
      solutions (fieldEquations path position trace.values ++ [(result, .var output)]) observations := by
  induction query generalizing result with
  | done => simp only [FieldTrace.actions, FieldActions.store, Subst.applyTerm_id,
      FieldTrace.values, fieldEquations, List.nil_append]
  | @step position subject rest candidate action later answers returned present accepted tail ih =>
      simp only [FieldTrace.actions, FieldActions.store, Subst.applyTerm_comp]
      rw [ih (action.substitution.applyTerm result)
        (outputApart.later (by omega)) (fun term member => (observationsApart term member).later (by omega))]
      have fixedEquations := tail.equations_fixed position (by omega) action
      have outputFixed := action_preserves_apart path position action (.var output) outputApart
      have observationsFixed : observations.map action.substitution.applyTerm = observations := by
        conv_rhs => rw [← List.map_id observations]
        apply List.map_congr_left
        intro term member
        exact action_preserves_apart path position action term (observationsApart term member)
      have contextFixed : action.substitution.applyEqs
          (fieldEquations path (position + 1) later.values ++ [(result, .var output)]) =
          fieldEquations path (position + 1) later.values ++
            [(action.substitution.applyTerm result, .var output)] := by
        simp only [Subst.applyEqs, List.map_append, List.map_cons, List.map_nil]
        change action.substitution.applyEqs (fieldEquations path (position + 1) later.values) ++ _ = _
        rw [fixedEquations, outputFixed]
      have exactMatch := solutions_after_unifyTotal
        [(candidate, .var (freshSupply (3 :: path) position))]
        (fieldEquations path (position + 1) later.values ++ [(result, .var output)])
        action.substitution accepted observations
      rw [contextFixed, observationsFixed] at exactMatch
      exact exactMatch.symm

end QueryTrace

/-- The proper tuple represented by a completed cons spine. The readback
lemma below ties this payload representation to the actual spine store. -/
def traceTuple {path : Path} {position : Nat} (trace : FieldTrace path position) : TypeTerm :=
  trace.actions.store.applyTerm (row (fieldVariables path position trace.actions.length))

/-- Ordered publication of the incremental trace's completed tuple is
exactly the existing structural query's publication. The recursive child
service is the real existing `run`; the noncapture premises are solely the
independent-output admission and allocator separation. -/
theorem structural_incremental_publication (library : List Declaration) (fuel : Nat)
    (path : Path) (items : List TypeTerm) (output : Nat) (observations : List TypeTerm)
    (independent : ∀ item ∈ items, output ∉ item.freeVars)
    (sourceApart : ∀ item ∈ items, AllocationApart path item)
    (outputApart : AllocationApart path (.var output))
    (observationsApart : ∀ term ∈ observations, AllocationApart path term) :
    (traces library fuel path 0 items).map (List.map fun trace =>
      solutions [(traceTuple trace, .var output)] observations) =
    (structural freshSupply (run library freshSupply fuel) path items (some (.var output))).map
      (List.map fun answer => solutions [(answer, .var output)] observations) := by
  rw [structural_independent_product library fuel path items output observations independent
    (fun item member => (sourceApart item member).fieldsApart 0) (outputApart.fieldsApart 0)
    (fun term member => (observationsApart term member).fieldsApart 0),
    ← traces_values library fuel path 0 items, Option.map_map]
  cases returned : traces library fuel path 0 items with
  | none => rfl
  | some rows =>
      simp only [Option.map_some, List.map_map, Function.comp_def, Option.some.injEq]
      apply List.map_congr_left
      intro trace present
      have query := traces_sound library fuel path 0 items rows returned trace present
      have length := query.length
      simp only [traceTuple, FieldTrace.actions_length, length]
      exact query.publication _ output observations (outputApart.fieldsApart 0)
        (fun term member => (observationsApart term member).fieldsApart 0)

private theorem row_apply (store : Subst signature) (items : List TypeTerm) :
    store.applyTerm (row items) = row (items.map store.applyTerm) := by
  simp only [row, Subst.applyTerm, Term.app.injEq, List.length_map, true_and]
  apply (Fin.heq_fun_iff (List.length_map store.applyTerm).symm).mpr
  intro index
  simp

/-- A completed cons chain and the corresponding proper tuple have the
same payloads, in the same positions, with all payload variable names kept. -/
inductive RepresentsTuple : SpineTerm → TypeTerm → Prop where
  | closed (fields : List TypeTerm) :
      RepresentsTuple (chain (fields.map embed) nil) (row fields)

/-- This representation theorem uses the full store reordering law, not a
separately constructed list of expected answers. -/
theorem incremental_represents_tuple {path : Path} {position : Nat} (trace : FieldTrace path position) :
    RepresentsTuple (trace.actions.incremental (tailName path position)) (traceTuple trace) := by
  rw [trace.actions.incremental_eq_eager, trace.actions.payload_extend]
  change RepresentsTuple ((extend trace.actions.store).applyTerm
    (build path position trace.actions.length (tailName path position))) _
  rw [build_start, apply_chain, apply_nil]
  simp only [traceTuple, row_apply, List.map_map, Function.comp_def, ← embed_apply]
  simpa only [List.map_map, Function.comp_def] using
    RepresentsTuple.closed ((fieldVariables path position trace.actions.length).map trace.actions.store.applyTerm)

/-- The arbitrary-requirement child matcher cannot refine an external
source term. This stronger frame law includes compound and shared formals;
it uses actual recursive output support and actual unifier relevance. -/
theorem query_match_preserves_separate_source (library : List Declaration) (fuel : Nat)
    (path : Path) (subject required source : TypeTerm) (answers : List TypeTerm)
    (sourceApart : AllocationApart path source)
    (requirementApart : Disjoint source.freeVars required.freeVars)
    (returned : run library freshSupply fuel path subject (some required) = some answers)
    (candidate : TypeTerm) (present : candidate ∈ answers) (refinement : Subst signature)
    (accepted : unifyTotal [(candidate, required)] = some refinement) :
    refinement.applyTerm source = source := by
  apply Subst.applyTerm_eq_self
  intro name occurs
  have absentRequired : name ∉ required.freeVars := fun member =>
    Finset.disjoint_left.mp requirementApart occurs member
  have absentCandidate : name ∉ candidate.freeVars := by
    apply run_output_excludes_name library fuel path subject (some required) answers name
      (fun stem slot same => sourceApart stem slot (same.symm ▸ occurs)) _ returned candidate present
    intro term member
    simp only [Option.toList_some, List.mem_singleton] at member
    subst term
    exact absentRequired
  apply (unifyTotal_relevantIdempotent _ _ accepted).fixes
  simp only [eqVars, Finset.union_empty, Finset.mem_union, not_or]
  exact ⟨absentCandidate, absentRequired⟩

/-- The same matched child preserves absence of every protected source
name in all remaining formals and results. A solved name cannot return
through the range of a later refinement. -/
theorem query_match_preserves_source_separation (library : List Declaration) (fuel : Nat)
    (path : Path) (subject required source term : TypeTerm) (answers : List TypeTerm)
    (sourceApart : AllocationApart path source)
    (requirementApart : Disjoint source.freeVars required.freeVars)
    (termApart : Disjoint source.freeVars term.freeVars)
    (returned : run library freshSupply fuel path subject (some required) = some answers)
    (candidate : TypeTerm) (present : candidate ∈ answers) (refinement : Subst signature)
    (accepted : unifyTotal [(candidate, required)] = some refinement) :
    Disjoint source.freeVars (refinement.applyTerm term).freeVars := by
  apply Finset.disjoint_left.mpr
  intro name occurs after
  have absentRequired : name ∉ required.freeVars := fun member =>
    Finset.disjoint_left.mp requirementApart occurs member
  have absentCandidate : name ∉ candidate.freeVars := by
    apply run_output_excludes_name library fuel path subject (some required) answers name
      (fun stem slot same => sourceApart stem slot (same.symm ▸ occurs)) _ returned candidate present
    intro value member
    simp only [Option.toList_some, List.mem_singleton] at member
    subst value
    exact absentRequired
  exact match_excludes_name candidate required name refinement accepted absentCandidate absentRequired
    term (fun member => Finset.disjoint_left.mp termApart occurs member) after

end Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.Spine
