import Mettapedia.OSLF.MeTTaIL.ContextSubstitution
import Mathlib.Data.List.Range
import Mathlib.Data.List.Nodup

/-!
# Translation-time identity of PeTTa callable values

The reference translation allocates one name per source lambda occurrence,
then returns that name or a partial application carrying ordered captures.
The independently implemented preparation walk annotates the nonbinding
domain of a `Lam` node before the node is eligible for structural interning.
Instantiation and further partial application preserve this domain.

The source and target use the existing neutral, locally nameless `Pattern`
carrier for executable bodies. No binding rule is changed. The value observer
compares nominal domains and ordered captured values, rather than executable
bodies or their display names. Capture equality here is ordinary equality on
a supplied closed-data carrier. This establishes the nominal component shared
by `==` and `=alpha` at that boundary; open variable variants, numeric equality,
cyclic captures, and equality of foreign objects require their own observers.

The finite source preparation and closure operations are executable models,
not a proof about C source preparation, address interning, or a native parser.
In particular, token freshness across sessions/revisions, nonwrapping machine
counters, capture-layout agreement with reference free-variable discovery,
and every native copy/substitution path remain integration obligations.
Nothing here decides extensional equality of higher-order functions.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IncrementalConformance.NominalCallables

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution

universe u

/-- One source occurrence, with an explicitly ordered capture layout. The
body has already been abstracted into neutral, locally nameless syntax. -/
structure Declaration where
  parameters : List String
  body : Pattern
  captureSlots : List Nat
deriving Repr

namespace Reference

/-- A generated callable name and its compiled definition. Executing the
definition does not generate another name. -/
structure Definition where
  name : Nat
  source : Declaration
deriving Repr

/-- Reference name allocation enumerates source occurrences before closure
instantiation. The first generated name is one greater than the old counter. -/
def translate (counter : Nat) (sources : List Declaration) : List Definition :=
  (sources.zipIdx (counter + 1)).map fun pair => ⟨pair.2, pair.1⟩

/-- The reference has a bare name when no arguments are captured, and a
nonempty partial application otherwise. -/
inductive Callable (Value : Type u) where
  | named (name : Nat)
  | captured (name : Nat) (first : Value) (rest : List Value)
deriving DecidableEq, Repr

def close {Value : Type u} (name : Nat) : List Value → Callable Value
  | [] => .named name
  | first :: rest => .captured name first rest

def name {Value : Type u} : Callable Value → Nat
  | .named token => token
  | .captured token _ _ => token

def captures {Value : Type u} : Callable Value → List Value
  | .named _ => []
  | .captured _ first rest => first :: rest

/-- Reference observation is equality of the generated value constructors,
including the ordered arguments of a partial application. -/
def same {Value : Type u} [DecidableEq Value]
    (left right : Callable Value) : Bool := decide (left = right)

def instantiate {Value : Type u} (environment : Nat → Value)
    (definition : Definition) : Callable Value :=
  close definition.name (definition.source.captureSlots.map environment)

def bind {Value : Type u} (callable : Callable Value)
    (arguments : List Value) : Callable Value :=
  close (name callable) (captures callable ++ arguments)

@[simp] theorem name_close {Value : Type u} (token : Nat) (values : List Value) :
    name (close token values) = token := by
  cases values <;> rfl

@[simp] theorem captures_close {Value : Type u} (token : Nat) (values : List Value) :
    captures (close token values) = values := by
  cases values <;> rfl

theorem close_eq_iff {Value : Type u} (left right : Nat)
    (earlier later : List Value) :
    close left earlier = close right later ↔ left = right ∧ earlier = later := by
  cases earlier <;> cases later <;> simp [close]

theorem same_close {Value : Type u} [DecidableEq Value] (left right : Nat)
    (earlier later : List Value) :
    same (close left earlier) (close right later) =
      decide (left = right ∧ earlier = later) := by
  simp only [same, close_eq_iff]

@[simp] theorem name_bind {Value : Type u} (callable : Callable Value)
    (arguments : List Value) : name (bind callable arguments) = name callable := by
  simp [bind]

@[simp] theorem captures_bind {Value : Type u} (callable : Callable Value)
    (arguments : List Value) :
    captures (bind callable arguments) = captures callable ++ arguments := by
  simp [bind]

end Reference

/-- A closed constructor encoding, never a free or bound variable. A native
realization can use a fixed-size nominal atom instead of this unary numeral. -/
def numeral : Nat → Pattern
  | 0 => .apply "$PeTTa.Token.Zero" []
  | n + 1 => .apply "$PeTTa.Token.Succ" [numeral n]

def nominalDomain (token : Nat) : Pattern :=
  .apply "$PeTTa.Callable" [numeral token]

/-- Independent decoding also rules out malformed nominal numerals. -/
def decodeNumeral : Pattern → Option Nat
  | .apply "$PeTTa.Token.Zero" [] => some 0
  | .apply "$PeTTa.Token.Succ" [previous] => (decodeNumeral previous).map Nat.succ
  | _ => none
termination_by pattern => sizeOf pattern

@[simp] theorem decodeNumeral_numeral (token : Nat) :
    decodeNumeral (numeral token) = some token := by
  induction token with
  | zero => simp [numeral, decodeNumeral]
  | succ token ih => simp [numeral, decodeNumeral, ih]

theorem numeral_injective : Function.Injective numeral := by
  intro left right same
  have decoded := congrArg decodeNumeral same
  simp only [decodeNumeral_numeral, Option.some.injEq] at decoded
  exact decoded

def tokenView : Pattern → Option Nat
  | .apply "$PeTTa.Callable" [encoded] => decodeNumeral encoded
  | _ => none

@[simp] theorem tokenView_nominalDomain (token : Nat) :
    tokenView (nominalDomain token) = some token := by
  simp [tokenView, nominalDomain]

theorem nominalDomain_injective : Function.Injective nominalDomain := by
  intro left right same
  have decoded := congrArg tokenView same
  simp only [tokenView_nominalDomain, Option.some.injEq] at decoded
  exact decoded

/-- `Lam`'s domain is outside its body binder. The multi-binder is the existing
neutral ABT representation, including inert authored-name metadata. -/
def canonical (token : Nat) (source : Declaration) : Pattern :=
  .apply "Lam" [nominalDomain token,
    .multiLambda source.parameters.length source.parameters source.body]

def domainView : Pattern → Option Pattern
  | .apply "Lam" [domain, _] => some domain
  | _ => none

def bodyView : Pattern → Option Pattern
  | .apply "Lam" [_, body] => some body
  | _ => none

@[simp] theorem domainView_canonical (token : Nat) (source : Declaration) :
    domainView (canonical token source) = some (nominalDomain token) := rfl

@[simp] theorem bodyView_canonical (token : Nat) (source : Declaration) :
    bodyView (canonical token source) =
      some (.multiLambda source.parameters.length source.parameters source.body) := rfl

theorem canonical_token_injective (source : Declaration) :
    Function.Injective (fun token => canonical token source) := by
  intro left right same
  have domains := congrArg domainView same
  simp only [domainView_canonical, Option.some.injEq] at domains
  exact nominalDomain_injective domains

structure Plan where
  code : Pattern
  captureSlots : List Nat
deriving Repr

/-- Preparation walks the input, incrementing the counter before annotating
each occurrence. The annotation is part of immutable content before interning. -/
def prepare (counter : Nat) : List Declaration → Nat × List Plan
  | [] => (counter, [])
  | source :: rest =>
      let token := counter + 1
      let prepared := prepare token rest
      (prepared.1, ⟨canonical token source, source.captureSlots⟩ :: prepared.2)

/-- A relation between independently allocated definitions and prepared
neutral code. This is not used as a premise of the preparation theorem. -/
def RelatedPlan (reference : Reference.Definition) (plan : Plan) : Prop :=
  plan.code = canonical reference.name reference.source ∧
    plan.captureSlots = reference.source.captureSlots

theorem prepare_counter (counter : Nat) (sources : List Declaration) :
    (prepare counter sources).1 = counter + sources.length := by
  induction sources generalizing counter with
  | nil => simp [prepare]
  | cons source rest ih => simp [prepare, ih]; omega

theorem prepare_length (counter : Nat) (sources : List Declaration) :
    (prepare counter sources).2.length = sources.length := by
  induction sources generalizing counter with
  | nil => rfl
  | cons source rest ih => simpa [prepare] using congrArg Nat.succ (ih (counter + 1))

/-- Whole-input correspondence follows from the independent enumeration and
counter walk, rather than assuming the desired per-occurrence relation. -/
theorem prepare_related (counter : Nat) (sources : List Declaration) :
    List.Forall₂ RelatedPlan (Reference.translate counter sources)
      (prepare counter sources).2 := by
  induction sources generalizing counter with
  | nil => exact .nil
  | cons source rest ih =>
      simp only [Reference.translate, List.zipIdx_cons, List.map_cons, prepare]
      exact .cons ⟨rfl, rfl⟩ (ih (counter + 1))

/-- Incremental source preparation retains the original prepared prefix and
starts the extension at the actual final counter of that prefix. -/
theorem prepare_extension (counter : Nat) (earlier later : List Declaration) :
    prepare counter (earlier ++ later) =
      let first := prepare counter earlier
      let second := prepare first.1 later
      (second.1, first.2 ++ second.2) := by
  induction earlier generalizing counter with
  | nil => simp [prepare]
  | cons source rest ih =>
      simp only [List.cons_append, prepare, ih]

theorem prepared_prefix_preserved (counter : Nat) (earlier later : List Declaration) :
    (prepare counter (earlier ++ later)).2.take earlier.length =
      (prepare counter earlier).2 := by
  rw [prepare_extension]
  have length := prepare_length counter earlier
  rw [← length]
  exact List.take_left

theorem reference_names (counter : Nat) (sources : List Declaration) :
    (Reference.translate counter sources).map Reference.Definition.name =
      List.range' (counter + 1) sources.length := by
  induction sources generalizing counter with
  | nil => rfl
  | cons source rest ih =>
      simp only [Reference.translate, List.zipIdx_cons, List.map_cons,
        List.length_cons, List.range'_succ]
      simpa only [Reference.translate, List.map_map] using
        congrArg (List.cons (counter + 1)) (ih (counter + 1))

private theorem rangeName_lower (counter count value : Nat)
    (present : value ∈ List.range' counter count) : counter ≤ value := by
  induction count generalizing counter with
  | zero => simp at present
  | succ count ih =>
      rw [List.range'_succ] at present
      rcases List.mem_cons.mp present with same | later
      · subst value
        exact Nat.le_refl _
      · exact Nat.le_trans (Nat.le_succ counter) (ih (counter + 1) later)

private theorem rangeNames_unique (counter count : Nat) :
    (List.range' counter count).Nodup := by
  induction count generalizing counter with
  | zero => exact .nil
  | succ count ih =>
      rw [List.range'_succ]
      refine .cons ?_ (ih (counter + 1))
      intro present
      exact Nat.not_succ_le_self counter (rangeName_lower (counter + 1) count counter present)

/-- Even identical declarations receive distinct source-occurrence names. -/
theorem reference_names_unique (counter : Nat) (sources : List Declaration) :
    ((Reference.translate counter sources).map Reference.Definition.name).Nodup := by
  rw [reference_names]
  exact rangeNames_unique _ _

theorem canonical_domains_unique (counter : Nat) (sources : List Declaration) :
    (((Reference.translate counter sources).map Reference.Definition.name).map
      nominalDomain).Nodup :=
  (reference_names_unique counter sources).map nominalDomain_injective

theorem prepared_domains (counter : Nat) (sources : List Declaration) :
    (prepare counter sources).2.map (fun plan => domainView plan.code) =
      (Reference.translate counter sources).map (fun definition => some (nominalDomain definition.name)) := by
  have mapped : ∀ references plans, List.Forall₂ RelatedPlan references plans →
      plans.map (fun plan => domainView plan.code) =
        references.map (fun definition => some (nominalDomain definition.name)) := by
    intro references plans correspondence
    induction correspondence with
    | nil => rfl
    | cons related _ ih =>
        simp only [List.map_cons, related.1, domainView_canonical, ih]
  exact mapped _ _ (prepare_related counter sources)

/-- Freshness is a property of the actual prepared code, including inputs
whose bodies and capture layouts coincide. -/
theorem prepared_domains_unique (counter : Nat) (sources : List Declaration) :
    ((prepare counter sources).2.map (fun plan => domainView plan.code)).Nodup := by
  rw [prepared_domains]
  have injective : Function.Injective (fun token => some (nominalDomain token)) := by
    intro left right same
    exact nominalDomain_injective (Option.some.inj same)
  simpa only [List.map_map, Function.comp_def] using
    (reference_names_unique counter sources).map injective

structure Closure (Value : Type u) where
  code : Pattern
  captures : List Value
deriving Repr

/-- A target frame lookup traverses the capture layout. This recursive walk
is independent of the reference's direct list-map instantiation. -/
def gather {Value : Type u} (environment : Nat → Value) : List Nat → List Value
  | [] => []
  | slot :: rest => environment slot :: gather environment rest

theorem gather_eq_map {Value : Type u} (environment : Nat → Value)
    (slots : List Nat) : gather environment slots = slots.map environment := by
  induction slots with
  | nil => rfl
  | cons slot rest ih => simp [gather, ih]

def instantiate {Value : Type u} (environment : Nat → Value)
    (plan : Plan) : Closure Value :=
  ⟨plan.code, gather environment plan.captureSlots⟩

/-- Value correspondence retains the definition's name and the full ordered
capture environment, including duplicate occurrences. -/
def RelatedValue {Value : Type u} (reference : Reference.Callable Value)
    (closure : Closure Value) : Prop :=
  domainView closure.code = some (nominalDomain (Reference.name reference)) ∧
    closure.captures = Reference.captures reference

theorem related_instantiation {Value : Type u} (reference : Reference.Definition)
    (plan : Plan) (related : RelatedPlan reference plan) (environment : Nat → Value) :
    RelatedValue (Reference.instantiate environment reference) (instantiate environment plan) := by
  rcases related with ⟨code, slots⟩
  simp [RelatedValue, Reference.instantiate, instantiate, code, slots, gather_eq_map]

/-- Every occurrence in a complete prepared input has a corresponding value
without an assumed simulation relation or assumed token-freshness law. -/
theorem prepared_values_related {Value : Type u} (counter : Nat)
    (sources : List Declaration) (environment : Nat → Value) :
    List.Forall₂ RelatedValue
      ((Reference.translate counter sources).map (Reference.instantiate environment))
      ((prepare counter sources).2.map (instantiate environment)) := by
  have mapped : ∀ references plans, List.Forall₂ RelatedPlan references plans →
      List.Forall₂ RelatedValue (references.map (Reference.instantiate environment))
        (plans.map (instantiate environment)) := by
    intro references plans correspondence
    induction correspondence with
    | nil => exact .nil
    | cons related _ ih =>
        exact .cons (related_instantiation _ _ related environment) ih
  exact mapped _ _ (prepare_related counter sources)

/-- Target equality reads the nominal domain from neutral code and compares
ordered captures. It neither looks up nor compares executable bodies. -/
def same {Value : Type u} [DecidableEq Value]
    (left right : Closure Value) : Bool :=
  match domainView left.code, domainView right.code with
  | some earlier, some later => decide (earlier = later ∧ left.captures = right.captures)
  | _, _ => false

def close {Value : Type u} (token : Nat) (source : Declaration)
    (captures : List Value) : Closure Value := ⟨canonical token source, captures⟩

theorem same_close {Value : Type u} [DecidableEq Value] (left right : Nat)
    (earlier later : Declaration) (capturesLeft capturesRight : List Value) :
    same (close left earlier capturesLeft) (close right later capturesRight) =
      decide (left = right ∧ capturesLeft = capturesRight) := by
  have injective : nominalDomain left = nominalDomain right ↔ left = right :=
    ⟨fun equal => nominalDomain_injective equal, congrArg nominalDomain⟩
  simp [same, close, injective]

/-- The observers are derived from separate reference value constructors and
target ABT-domain inspection; they agree for every token/body/capture pair. -/
theorem closed_observer_correspondence {Value : Type u} [DecidableEq Value]
    (left right : Nat) (earlier later : Declaration)
    (capturesLeft capturesRight : List Value) :
    same (close left earlier capturesLeft) (close right later capturesRight) =
      Reference.same (Reference.close left capturesLeft) (Reference.close right capturesRight) := by
  rw [same_close, Reference.same_close]

theorem instantiation_correspondence {Value : Type u} [DecidableEq Value]
    (left right : Reference.Definition) (leftPlan rightPlan : Plan)
    (earlier : RelatedPlan left leftPlan) (later : RelatedPlan right rightPlan)
    (environmentLeft environmentRight : Nat → Value) :
    same (instantiate environmentLeft leftPlan) (instantiate environmentRight rightPlan) =
      Reference.same (Reference.instantiate environmentLeft left)
        (Reference.instantiate environmentRight right) := by
  rcases earlier with ⟨leftCode, leftSlots⟩
  rcases later with ⟨rightCode, rightSlots⟩
  simp only [instantiate, Reference.instantiate, leftCode, rightCode,
    leftSlots, rightSlots, gather_eq_map]
  exact closed_observer_correspondence ..

def bind {Value : Type u} (closure : Closure Value)
    (arguments : List Value) : Closure Value :=
  ⟨closure.code, closure.captures ++ arguments⟩

@[simp] theorem bind_preserves_domain {Value : Type u} (closure : Closure Value)
    (arguments : List Value) :
    domainView (bind closure arguments).code = domainView closure.code := rfl

theorem bind_correspondence {Value : Type u} [DecidableEq Value]
    (left right : Nat) (earlier later : Declaration)
    (capturesLeft capturesRight argsLeft argsRight : List Value) :
    same (bind (close left earlier capturesLeft) argsLeft)
      (bind (close right later capturesRight) argsRight) =
      Reference.same (Reference.bind (Reference.close left capturesLeft) argsLeft)
        (Reference.bind (Reference.close right capturesRight) argsRight) := by
  simp only [bind, close, Reference.bind, Reference.name_close, Reference.captures_close]
  exact closed_observer_correspondence ..

/-- Copying traverses the value's capture spine, preserving each occurrence.
It does not allocate a new callable token. -/
def copy {Value : Type u} (closure : Closure Value) : Closure Value :=
  ⟨closure.code, closure.captures.map id⟩

theorem copy_preserves_observer {Value : Type u} [DecidableEq Value]
    (left right : Closure Value) : same (copy left) (copy right) = same left right := by
  simp [copy]

@[simp] theorem substitute_numeral (assignment : Assignment) (token : Nat) :
    substitute assignment (numeral token) = numeral token := by
  induction token with
  | zero => rfl
  | succ token ih => simp [numeral, substitute, substituteList, ih]

@[simp] theorem substitute_nominalDomain (assignment : Assignment) (token : Nat) :
    substitute assignment (nominalDomain token) = nominalDomain token := by
  simp [nominalDomain, substitute, substituteList]

/-- Actual neutral context substitution descends into the body with a binder
lift, but it cannot rename or capture the closed nominal domain. -/
theorem substitute_canonical (assignment : Assignment) (token : Nat)
    (source : Declaration) :
    substitute assignment (canonical token source) =
      canonical token { source with
        body := substitute (lift source.parameters.length assignment) source.body } := by
  simp [canonical, substitute, substituteList]

theorem substitute_preserves_domain (assignment : Assignment) (token : Nat)
    (source : Declaration) :
    domainView (substitute assignment (canonical token source)) = some (nominalDomain token) := by
  rw [substitute_canonical, domainView_canonical]

def substituteCode {Value : Type u} (assignment : Assignment)
    (closure : Closure Value) : Closure Value :=
  ⟨substitute assignment closure.code, closure.captures⟩

theorem substitution_preserves_observer {Value : Type u} [DecidableEq Value]
    (first second : Assignment) (left right : Nat) (earlier later : Declaration)
    (capturesLeft capturesRight : List Value) :
    same (substituteCode first (close left earlier capturesLeft))
      (substituteCode second (close right later capturesRight)) =
      same (close left earlier capturesLeft) (close right later capturesRight) := by
  simp only [substituteCode, close, same, substitute_preserves_domain, domainView_canonical]
  rfl

/-- Changing display labels of the existing de Bruijn binders does not change
the occurrence token or binder arity. -/
def renameParameters (source : Declaration) (rename : String → String) : Declaration :=
  { source with parameters := source.parameters.map rename }

theorem parameter_alpha_preserves_domain (token : Nat) (source : Declaration)
    (rename : String → String) :
    domainView (canonical token (renameParameters source rename)) =
      domainView (canonical token source) := by
  simp

theorem parameter_alpha_preserves_body (source : Declaration) (rename : String → String) :
    (renameParameters source rename).body = source.body := rfl

theorem parameter_alpha_preserves_arity (source : Declaration) (rename : String → String) :
    (renameParameters source rename).parameters.length = source.parameters.length := by
  simp [renameParameters]

theorem parameter_alpha_preserves_observer {Value : Type u} [DecidableEq Value]
    (left right : Nat) (earlier later : Declaration)
    (renameLeft renameRight : String → String) (capturesLeft capturesRight : List Value) :
    same (close left (renameParameters earlier renameLeft) capturesLeft)
      (close right (renameParameters later renameRight) capturesRight) =
      same (close left earlier capturesLeft) (close right later capturesRight) := by
  rw [same_close, same_close]

/-- A body-only cache key deliberately drops the nominal domain while keeping
the complete executable binder and every captured occurrence. -/
def bodyKey {Value : Type u} (closure : Closure Value) : Option Pattern × List Value :=
  (bodyView closure.code, closure.captures)

theorem bodyKey_collision {Value : Type u} (left right : Nat) (source : Declaration)
    (captures : List Value) : bodyKey (close left source captures) = bodyKey (close right source captures) := by
  simp [bodyKey, close]

theorem distinct_occurrences_distinguished {Value : Type u} [DecidableEq Value]
    (left right : Nat) (different : left ≠ right) (earlier later : Declaration)
    (capturesLeft capturesRight : List Value) :
    same (close left earlier capturesLeft) (close right later capturesRight) = false := by
  simp [same_close, different]

theorem different_captures_distinguished {Value : Type u} [DecidableEq Value]
    (token : Nat) (earlier later : Declaration) (capturesLeft capturesRight : List Value)
    (different : capturesLeft ≠ capturesRight) :
    same (close token earlier capturesLeft) (close token later capturesRight) = false := by
  simp [same_close, different]

/-- No observer of body-only keys can recover even comparison against a fixed
callable. This blocks body-only interning as a value-preserving representation. -/
theorem nominal_observer_does_not_descend_to_bodyKey {Value : Type u} [DecidableEq Value]
    (token : Nat) (source : Declaration) (captures : List Value) :
    ¬ ∃ observe : (Option Pattern × List Value) → Bool,
      ∀ other : Nat, observe (bodyKey (close other source captures)) =
        same (close token source captures) (close other source captures) := by
  rintro ⟨observe, exactObservation⟩
  have self := exactObservation token
  have other := exactObservation (token + 1)
  have collision := bodyKey_collision token (token + 1) source captures
  rw [← collision] at other
  have selfTrue : same (close token source captures) (close token source captures) = true := by
    rw [same_close]
    exact decide_eq_true ⟨rfl, rfl⟩
  have otherFalse : same (close token source captures) (close (token + 1) source captures) = false := by
    rw [same_close]
    exact decide_eq_false (by intro equal; omega)
  have trueFalse : true = false := (self.trans selfTrue).symm.trans (other.trans otherFalse)
  exact Bool.noConfusion trueFalse

namespace Controls

def identitySource : Declaration := ⟨["x"], .bvar 0, []⟩
def capturedSource : Declaration := ⟨["x"], .apply "pair" [.fvar "free", .bvar 0], [2, 0, 2]⟩

theorem distinct_identical_source_occurrences :
    (Reference.translate 0 [identitySource, identitySource]).map Reference.Definition.name = [1, 2] ∧
    (prepare 0 [identitySource, identitySource]).1 = 2 := by decide

theorem identical_bodies_remain_distinct :
    same (close 1 identitySource ([] : List Nat)) (close 2 identitySource []) = false := by
  decide

theorem reused_prepared_callable_agrees :
    let plan : Plan := ⟨canonical 1 capturedSource, capturedSource.captureSlots⟩
    same (instantiate (fun slot => slot + 10) plan)
      (copy (instantiate (fun slot => slot + 10) plan)) = true := by decide

theorem captures_keep_order_and_multiplicity :
    (instantiate (fun slot => slot + 10)
      ⟨canonical 1 capturedSource, capturedSource.captureSlots⟩).captures = [12, 10, 12] := by decide

theorem reordered_captures_change_observation :
    same (close 1 capturedSource [12, 10, 12]) (close 1 capturedSource [10, 12, 12]) = false := by
  decide

theorem alpha_labels_differ_as_syntax_but_not_as_values :
    canonical 1 identitySource ≠ canonical 1 (renameParameters identitySource (fun _ => "y")) ∧
    same (close 1 identitySource ([] : List Nat))
      (close 1 (renameParameters identitySource (fun _ => "y")) []) = true := by decide

theorem token_survives_nontrivial_substitution :
    substitute (fun _ => .apply "replacement" []) (canonical 1 ⟨["x"], .bvar 1, []⟩) =
      canonical 1 ⟨["x"], .apply "replacement" [], []⟩ := by decide

/-- A free-variable token would be vulnerable to the substitution machinery. -/
theorem variable_domain_is_not_stable :
    substitute (fun _ => .apply "replacement" []) (.apply "Lam" [.bvar 0, .multiLambda 1 ["x"] (.bvar 0)]) ≠
      .apply "Lam" [.bvar 0, .multiLambda 1 ["x"] (.bvar 0)] := by decide

theorem body_only_interning_merges_distinct_values :
    bodyKey (close 1 identitySource ([] : List Nat)) = bodyKey (close 2 identitySource []) ∧
    same (close 1 identitySource ([] : List Nat)) (close 2 identitySource []) = false := by decide

theorem partial_arguments_are_value_observations :
    same (bind (close 1 identitySource ([] : List Nat)) [4])
      (bind (close 1 identitySource []) [5]) = false := by decide

theorem malformed_lam_not_nominally_equal :
    same (⟨.bvar 0, []⟩ : Closure Nat) ⟨.bvar 0, []⟩ = false := by decide

/-- Resetting allocation while old values remain live would reuse a nominal
token for unrelated executable definitions. -/
theorem reset_counter_collides_with_live_definition :
    let changed : Declaration := ⟨["x"], .apply "different-body" [], []⟩
    let oldPlan : Plan := ((prepare 0 [identitySource]).2)[0]'(by decide)
    let newPlan : Plan := ((prepare 0 [changed]).2)[0]'(by decide)
    oldPlan.code ≠ newPlan.code ∧
      same (instantiate (fun _ => 0) oldPlan) (instantiate (fun _ => 0) newPlan) = true := by
  decide

end Controls

end Mettapedia.Machines.IncrementalConformance.NominalCallables
