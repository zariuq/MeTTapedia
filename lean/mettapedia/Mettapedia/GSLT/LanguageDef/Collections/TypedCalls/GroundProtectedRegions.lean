import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ContractBindingFacts
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.UninterpretedLocalMultiplicity

/-!
# Ground-protected return recipes under arbitrary two-way bindings

The source evaluator is the existing substitution-threaded `evalUnifying`.
Its no-fallback structural grammar can contain interpreted constants and
patterns. The empty declaration family is used only to derive its actual
substitution-extension invariant, not as the declaration space of any guard.
A ground protected observation is unchanged by every such extension.

The source return-pattern analysis then proves that every observed result is
the original protected value. Actual declaration-dependent protocol guards
can be removed when that value is both ground and uninterpreted. This does
not require unrelated declarations to be functional.

An explicit captured entry record is installed before evaluating each unary
activation. It can contain arbitrary interpreted or open values. Recursive
calls use the existing unary oracle and reinstall that same captured record;
this is a fixed captured-record profile, not arbitrary live caller-frame
transport. The oracle returns values rather than substitution-bearing call
outcomes, so caller-binding changes made inside recursive callees are not
modeled by that interface. Case, match, external calls and complete native
fact-flow lowering are not part of the structural grammar below.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.GroundProtectedRegions

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open UnifyingRegions UnifyingFrames
open UninterpretedLocalMultiplicity (emptyDecls empty_safe)

theorem empty_clean (state : Substitution) : Clean emptyDecls state :=
  fun name => empty_safe Atom.var (state name)

theorem empty_oracle_clean (oracle : SelfOracle) : OracleClean emptyDecls oracle :=
  fun _ _ result _ => empty_safe Atom.var result

/-- The actual MGU-composed state is an extension, even if interpreted
symbols occur in the source or the captured record. No typing space changes
in the evaluator: its structural operations do not inspect declarations. -/
theorem structural_extension (fallback : Fallback) (oracle : SelfOracle)
    {body : Expr} (accepted : UnifyingRegions.Accepted emptyDecls body)
    (state : Substitution) (out : Outcome)
    (returned : out ∈ evalUnifying fallback oracle body state) :
    Extends emptyDecls state out.2 :=
  (accepted_good fallback oracle (empty_oracle_clean oracle) accepted state (empty_clean state) out returned).2.2

theorem ground_observation_unchanged {state after : Substitution} {value : Atom}
    (extension : Extends emptyDecls state after)
    (ground : support (substA state value) = ∅) :
    substA after value = substA state value := by
  obtain ⟨delta, _, rfl⟩ := extension
  rw [← substA_compose]
  exact CapturedUninterpretedRegions.subst_ground ground delta

/-- Return analysis identifies a recipe, and groundness proves its current
value cannot change through any subsequent two-way binding in this run. -/
theorem protected_ground_return (fallback : Fallback) (oracle : SelfOracle)
    (parameter : String) {body : Expr} (accepted : UnifyingRegions.Accepted emptyDecls body)
    (returns : ReturnsPat (.var parameter) body) (state : Substitution)
    (ground : support (state parameter) = ∅) (out : Outcome)
    (returned : out ∈ evalUnifying fallback oracle body state) :
    observe out = state parameter := by
  have recipe := returns_argument fallback oracle parameter returns accepted state out returned
  have extension := structural_extension fallback oracle accepted state out returned
  unfold observe
  rw [recipe]
  exact ground_observation_unchanged extension ground

/-- The protected value is installed at the current activation's parameter;
all other captured entries remain as supplied. -/
def enter (captured : Substitution) (parameter : String) (value : Atom) : Substitution :=
  Function.update captured parameter value

def capturedBody (fallback : Fallback) (captured : Substitution) (parameter : String)
    (body : Expr) (oracle : SelfOracle) : List Atom → Multiset Atom
  | [value] => (evalUnifying fallback oracle body (enter captured parameter value)).map observe
  | _ => 0

theorem captured_body_returns_original (fallback : Fallback) (captured : Substitution)
    (parameter : String) {body : Expr} (accepted : UnifyingRegions.Accepted emptyDecls body)
    (returns : ReturnsPat (.var parameter) body) (oracle : SelfOracle) (value : Atom)
    (ground : support value = ∅) :
    ∀ result ∈ capturedBody fallback captured parameter body oracle [value], result = value := by
  intro result present
  simp only [capturedBody, Multiset.mem_map] at present
  obtain ⟨out, returned, rfl⟩ := present
  have fixed := protected_ground_return fallback oracle parameter accepted returns
    (enter captured parameter value) (by simpa [enter] using ground) out returned
  simpa [enter] using fixed

/-- Reuse the existing native-style footprint checker on an actual value,
under the identity substitution and no claims about source names. -/
def dataCheck (decls : Decls) (value : Atom) : Bool :=
  ContractBindingFacts.patternUninterpreted decls [] value

theorem dataCheck_sound {decls : Decls} {value : Atom} (checked : dataCheck decls value = true) :
    Uninterp decls value := by
  have checked' := ContractBindingFacts.patternUninterpreted_sound
    (Γ := decls) (facts := []) (σ := Atom.var) (by intro entry member; cases member)
    value (by intro name _ _; rfl) checked
  simpa only [substA_var_self] using checked'

private theorem patternsCheck (decls : Decls) : ∀ values : List Atom,
    (∀ value ∈ values, dataCheck decls value = true) →
      ContractBindingFacts.patternsUninterpreted decls [] values = true
  | [], _ => rfl
  | value :: values, all => by
      simp only [ContractBindingFacts.patternsUninterpreted]
      rw [show ContractBindingFacts.patternUninterpreted decls [] value = true from all value (by simp),
        patternsCheck decls values (fun value member => all value (by simp [member]))]
      rfl

theorem dataCheck_complete {decls : Decls} : ∀ value : Atom,
    Uninterp decls value → dataCheck decls value = true := by
  intro value
  induction value using Atom.rec
      (motive_2 := fun values => ∀ value ∈ values, Uninterp decls value → dataCheck decls value = true) with
  | var name => intro _; rfl
  | symbol name =>
      intro clean
      change decls name = [] at clean
      simp [dataCheck, ContractBindingFacts.patternUninterpreted, clean]
  | grounded value => intro _; rfl
  | expression values ih =>
      intro clean
      apply patternsCheck decls values
      intro value member
      exact ih value member
        (ContractBindingFacts.uninterpreted_member values (UnifyAtoms.safeAll_of_uninterp clean) value member)
  | nil value member => cases member
  | cons first rest ihFirst ihRest value member clean =>
      rcases List.mem_cons.mp member with rfl | present
      · exact ihFirst clean
      · exact ihRest value present clean

def groundValueGate (decls : Decls) (value : Atom) : Bool :=
  decide (support value = ∅) && dataCheck decls value

theorem groundValueGate_iff (decls : Decls) (value : Atom) :
    groundValueGate decls value = true ↔ support value = ∅ ∧ Uninterp decls value := by
  constructor
  · intro gate
    obtain ⟨ground, clean⟩ := Bool.and_eq_true_iff.mp gate
    exact ⟨of_decide_eq_true ground, dataCheck_sound clean⟩
  · rintro ⟨ground, clean⟩
    simp [groundValueGate, ground, dataCheck_complete value clean]

def gate (decls : Decls) : List Atom → Bool
  | [value] => groundValueGate decls value
  | _ => false

theorem gate_iff (decls : Decls) (args : List Atom) :
    gate decls args = true ↔ ∃ value, args = [value] ∧ support value = ∅ ∧ Uninterp decls value := by
  cases args with
  | nil => simp [gate]
  | cons value rest =>
      cases rest with
      | nil => simpa [gate] using groundValueGate_iff decls value
      | cons next rest => simp [gate]

def row (typeVariable : String) : Ty String := arrow [.var typeVariable] (.var typeVariable)

/-- The actual declaration space remains on every protocol guard. The
empty declaration family above supplied only substitution-extension facts. -/
theorem admitted_call_elides {decls : Decls} (kind : Atom → String)
    (fallback : Fallback) (captured : Substitution) (parameter typeVariable : String)
    {body : Expr} (accepted : UnifyingRegions.Accepted emptyDecls body) (returns : ReturnsPat (.var parameter) body)
    (oracle : SelfOracle) (args : List Atom) (admitted : gate decls args = true) :
    chainCall decls kind (capturedBody fallback captured parameter body oracle) (row typeVariable) args =
      capturedBody fallback captured parameter body oracle args := by
  obtain ⟨value, rfl, ground, clean⟩ := (gate_iff decls args).mp admitted
  have law := UninterpretedLocalMultiplicity.pair_protocol_clean kind [] [] typeVariable
    (capturedBody fallback captured parameter body oracle) [] [] value rfl clean (by
      intro result present
      have fixed := captured_body_returns_original fallback captured parameter accepted returns oracle value ground
        result present
      refine ⟨Atom.var, ?_, fun _ => trivial⟩
      rw [substA_var_self]
      exact fixed)
  simpa only [row, List.map_nil, List.nil_append, argCount, one_mul, one_nsmul] using law

/-- A second, already delivered argument supplies an actual captured source entry.
The protected argument is installed last, and is not inferred from claims
about the source name of the other argument. This does not identify the
source demand of an `Atom` formal with the demand of `%Undefined%`. -/
def capturedAnyBody (fallback : Fallback) (captured : Substitution)
    (parameter anyParameter : String) (body : Expr) (oracle : SelfOracle) : List Atom → Multiset Atom
  | [value, other] => capturedBody fallback (enter captured anyParameter other) parameter body oracle [value]
  | _ => 0

theorem captured_any_entry (captured : Substitution) (parameter anyParameter : String)
    (different : anyParameter ≠ parameter) (value other : Atom) :
    enter (enter captured anyParameter other) parameter value parameter = value ∧
      enter (enter captured anyParameter other) parameter value anyParameter = other := by
  simp [enter, different]

/-- At a delivered-argument boundary, every unguarded closed formal has the
same guard count. Its prior source demand is not changed by this theorem. -/
theorem captured_unguarded_protocol_elides {decls : Decls} (kind : Atom → String)
    (fallback : Fallback) (captured : Substitution) (parameter anyParameter typeVariable : String)
    (formal : Ty Empty) (unguarded : demand formal.lift ≠ .guarded)
    {body : Expr} (accepted : UnifyingRegions.Accepted emptyDecls body) (returns : ReturnsPat (.var parameter) body)
    (oracle : SelfOracle) (value other : Atom) (ground : support value = ∅) (clean : Uninterp decls value) :
    chainCall decls kind (capturedAnyBody fallback captured parameter anyParameter body oracle)
      (arrow [.var typeVariable, formal.lift] (.var typeVariable)) [value, other] =
        capturedAnyBody fallback captured parameter anyParameter body oracle [value, other] := by
  have law := UninterpretedLocalMultiplicity.pair_protocol_clean kind [] [formal] typeVariable
    (capturedAnyBody fallback captured parameter anyParameter body oracle) [] [other] value rfl clean (by
      intro result present
      have fixed := captured_body_returns_original fallback (enter captured anyParameter other)
        parameter accepted returns oracle value ground result present
      refine ⟨Atom.var, ?_, fun _ => trivial⟩
      rw [substA_var_self]
      exact fixed)
  simpa [argCount, unguarded, one_nsmul] using law

theorem captured_any_protocol_elides {decls : Decls} (kind : Atom → String)
    (fallback : Fallback) (captured : Substitution) (parameter anyParameter typeVariable : String)
    {body : Expr} (accepted : UnifyingRegions.Accepted emptyDecls body) (returns : ReturnsPat (.var parameter) body)
    (oracle : SelfOracle) (value other : Atom) (ground : support value = ∅) (clean : Uninterp decls value) :
    chainCall decls kind (capturedAnyBody fallback captured parameter anyParameter body oracle)
      (arrow [.var typeVariable, .sym "Atom"] (.var typeVariable)) [value, other] =
        capturedAnyBody fallback captured parameter anyParameter body oracle [value, other] :=
  captured_unguarded_protocol_elides kind fallback captured parameter anyParameter typeVariable
    (.sym "Atom") (by decide +kernel) accepted returns oracle value other ground clean

theorem captured_undefined_protocol_elides {decls : Decls} (kind : Atom → String)
    (fallback : Fallback) (captured : Substitution) (parameter anyParameter typeVariable : String)
    {body : Expr} (accepted : UnifyingRegions.Accepted emptyDecls body) (returns : ReturnsPat (.var parameter) body)
    (oracle : SelfOracle) (value other : Atom) (ground : support value = ∅) (clean : Uninterp decls value) :
    chainCall decls kind (capturedAnyBody fallback captured parameter anyParameter body oracle)
      (arrow [.var typeVariable, .sym "%Undefined%"] (.var typeVariable)) [value, other] =
        capturedAnyBody fallback captured parameter anyParameter body oracle [value, other] :=
  captured_unguarded_protocol_elides kind fallback captured parameter anyParameter typeVariable
    (.sym "%Undefined%") (by decide +kernel) accepted returns oracle value other ground clean

theorem atom_and_undefined_demands_differ :
    demand (.sym "Atom") = .raw ∧ demand (.sym "%Undefined%") = .unchecked ∧
      demand (.sym "Atom") ≠ demand (.sym "%Undefined%") := by decide +kernel

/-- Every activation chooses its own boundary. Rejected admission retains
the canonical guard, rather than returning no answer or assuming a clean
recursive call from an earlier activation's facts. -/
noncomputable def gatedBody (decls : Decls) (kind : Atom → String)
    (fallback : Fallback) (captured : Substitution) (parameter typeVariable : String)
    (body : Expr) (oracle : SelfOracle) (args : List Atom) : Multiset Atom :=
  if gate decls args then capturedBody fallback captured parameter body oracle args
  else chainCall decls kind (capturedBody fallback captured parameter body oracle) (row typeVariable) args

/-- No new evaluator or recursive engine: the existing version runner uses
the local gate, and the existing canonical runner keeps the actual protocol. -/
theorem recursive_per_call_exact (decls : Decls) (grounded : String → Bool)
    (fallback : Fallback) (captured : Substitution) (parameter typeVariable : String)
    {body : Expr} (accepted : UnifyingRegions.Accepted emptyDecls body) (returns : ReturnsPat (.var parameter) body) :
    ∀ fuel args,
      versionRun (gatedBody decls (metatype grounded) fallback captured parameter typeVariable body) fuel args =
        protocolRun decls grounded (capturedBody fallback captured parameter body) (row typeVariable) fuel args := by
  intro fuel
  induction fuel with
  | zero => intro args; rfl
  | succ fuel ih =>
      intro args
      simp only [versionRun, protocolRun, gatedBody]
      have oracles : versionRun (gatedBody decls (metatype grounded) fallback captured parameter typeVariable body) fuel =
          protocolRun decls grounded (capturedBody fallback captured parameter body) (row typeVariable) fuel :=
        funext ih
      rw [oracles]
      split
      · exact (admitted_call_elides (metatype grounded) fallback captured parameter typeVariable accepted returns _ args ‹_›).symm
      · rfl

theorem nonground_keeps_guard (decls : Decls) (kind : Atom → String)
    (fallback : Fallback) (captured : Substitution) (parameter typeVariable : String)
    (body : Expr) (oracle : SelfOracle) (value : Atom) (openValue : support value ≠ ∅) :
    gatedBody decls kind fallback captured parameter typeVariable body oracle [value] =
      chainCall decls kind (capturedBody fallback captured parameter body oracle) (row typeVariable) [value] := by
  simp [gatedBody, gate, groundValueGate, openValue]

namespace Controls

def declarations : Decls := fun name =>
  if name = "Known" then [.sym "Tagged"]
  else if name = "overloaded" then [.sym "Number", .sym "String"] else []

def capture : Substitution := UnifyingFrames.Controls.aliases
def parameterName : String := "source-a"
def body : Expr := ContractBindingFacts.Controls.aliasBody
def known : Atom := .symbol "Known"
def free : Atom := .symbol "free"
def fallback : Fallback := fun _ _ => 0
def silent : SelfOracle := fun _ => 0

theorem body_accepted : UnifyingRegions.Accepted emptyDecls body :=
  .letE trivial (.const known (empty_safe Atom.var known)) (.var parameterName)

theorem body_returns : ReturnsPat (.var parameterName) body := .letE .refl

theorem real_space_is_not_functional : ¬ Functional declarations := by
  intro all
  have bad := all "overloaded"
  simp [declarations] at bad

theorem capture_contains_interpreted_data : ¬ Clean declarations capture := by
  intro all
  have known := all "unrelated"
  simp [capture, UnifyingFrames.Controls.aliases, declarations, Uninterp, Safe] at known

theorem interpreted_binding_with_ground_protected :
    capturedBody fallback capture parameterName body silent [free] = {free} ∧
      gate declarations [free] = true := by
  constructor
  · cbv
  · decide +kernel

theorem ground_call_protocol_exact (kind : Atom → String) :
    chainCall declarations kind (capturedBody fallback capture parameterName body silent) (row "a") [free] = {free} := by
  rw [admitted_call_elides kind fallback capture parameterName "a" body_accepted body_returns _ _
    interpreted_binding_with_ground_protected.2]
  exact interpreted_binding_with_ground_protected.1

theorem any_argument_may_be_interpreted (kind : Atom → String) :
    chainCall declarations kind (capturedAnyBody fallback capture parameterName "source-b" body silent)
      (arrow [.var "a", .sym "Atom"] (.var "a")) [free, known] = {free} := by
  rw [captured_any_protocol_elides kind fallback capture parameterName "source-b" "a"
    body_accepted body_returns silent free known (by decide +kernel) (by simp [Uninterp, Safe, declarations, free])]
  cbv

theorem undefined_argument_may_be_interpreted (kind : Atom → String) :
    chainCall declarations kind (capturedAnyBody fallback capture parameterName "source-b" body silent)
      (arrow [.var "a", .sym "%Undefined%"] (.var "a")) [free, known] = {free} := by
  rw [captured_undefined_protocol_elides kind fallback capture parameterName "source-b" "a"
    body_accepted body_returns silent free known (by decide +kernel) (by simp [Uninterp, Safe, declarations, free])]
  cbv

theorem open_alias_is_rejected : gate declarations [.var "shared"] = false := by decide +kernel

theorem open_alias_changes_protected :
    capturedBody fallback capture parameterName body silent [.var "shared"] = {known} ∧
      Uninterp declarations (.var "shared") ∧ ¬ Uninterp declarations known := by
  constructor
  · cbv
  · constructor
    · trivial
    · simp [declarations, known, Uninterp, Safe]

theorem ground_but_interpreted_is_rejected :
    support known = ∅ ∧ gate declarations [known] = false := by decide +kernel

theorem all_inputs_keep_canonical_guards (grounded : String → Bool) (fuel : Nat) (args : List Atom) :
    versionRun (gatedBody declarations (metatype grounded) fallback capture parameterName "a" body) fuel args =
      protocolRun declarations grounded (capturedBody fallback capture parameterName body) (row "a") fuel args :=
  recursive_per_call_exact declarations grounded fallback capture parameterName "a" body_accepted body_returns fuel args

/-- This source executes a genuine self call before the interpreted bind.
The child sees a new ground protected argument; the parent retains its own. -/
def afterChild : Expr := .letE (.var "child") (.self [.const truth]) body

def recursiveBody : Expr := .ifE (.var parameterName) (.var parameterName) afterChild

def off : Atom := .grounded (.bool false)

theorem afterChild_accepted : UnifyingRegions.Accepted emptyDecls afterChild :=
  .letE trivial (.self (.const truth (empty_safe Atom.var truth))) body_accepted

theorem afterChild_returns : ReturnsPat (.var parameterName) afterChild := .letE body_returns

theorem recursiveBody_accepted : UnifyingRegions.Accepted emptyDecls recursiveBody :=
  .ifE (.var parameterName) (.var parameterName) afterChild_accepted

theorem recursiveBody_returns : ReturnsPat (.var parameterName) recursiveBody :=
  .ifE .refl afterChild_returns

theorem both_recursive_entries_admitted :
    gate declarations [off] = true ∧ gate declarations [truth] = true := by decide +kernel

/-- One activation runs out of recursive fuel; two complete the child and
return the parent's false value, rather than the child's true value. -/
theorem real_recursion_is_required :
    versionRun (capturedBody fallback capture parameterName recursiveBody) 1 [off] = 0 ∧
      versionRun (capturedBody fallback capture parameterName recursiveBody) 2 [off] = {off} := by
  constructor <;> cbv

theorem recursive_protocol_result (grounded : String → Bool) :
    protocolRun declarations grounded (capturedBody fallback capture parameterName recursiveBody)
      (row "a") 2 [off] = {off} := by
  rw [← recursive_per_call_exact declarations grounded fallback capture parameterName "a"
    recursiveBody_accepted recursiveBody_returns]
  cbv

def duplicatedChild : SelfOracle := fun args => if args = [truth] then {truth, truth} else 0

theorem duplicate_answers_are_retained :
    capturedBody fallback capture parameterName afterChild duplicatedChild [free] = {free, free} := by
  cbv

theorem duplicate_protocol_is_exact (kind : Atom → String) :
    chainCall declarations kind (capturedBody fallback capture parameterName afterChild duplicatedChild)
      (row "a") [free] = {free, free} := by
  rw [admitted_call_elides kind fallback capture parameterName "a" afterChild_accepted afterChild_returns
    _ _ interpreted_binding_with_ground_protected.2]
  exact duplicate_answers_are_retained

theorem deduplicating_changes_the_result : ({free, free} : Multiset Atom) ≠ {free} := by decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.GroundProtectedRegions
