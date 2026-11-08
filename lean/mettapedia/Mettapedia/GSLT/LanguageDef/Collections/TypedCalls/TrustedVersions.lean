import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Protocol

/-!
# Trusted versions of typed relations

A typed relation runs its protocol at every call, its calls to itself
included. A **trusted version** runs the equations with the calls to itself
entering the version directly, skipping the protocol (`versionRun`); a
checked call runs the protocol once and enters the version. This module
proves that the version's answer bag is the protocol's, multiplicity
included, for every relation whose equations an analysis of the kind
CeTTa's contract analysis performs accepts.

* **Entry facts at metatype names.** The guard is
  `get-type(V, T) *-> true ; get-metatype(V, T)`. At a formal that
  `get-metatype` can return, `Expression`, `Symbol`, `Grounded` or `Variable`
  (`MetaName`), the guard can succeed with no answer of the type relation.
  So an entry fact at a metatype name says only that the guard succeeds once,
  and at any other closed type that the type relation types the value once
  (`Holds`). A fact of either kind discharges its guard
  (`Holds.guardCount`); only a fact of the second kind inverts a constructor
  or types a construction.
* **Entry facts where the protocol checks** (`EntryFacts`, `EntryPoly`): the fact of
  a parameter's type where the protocol guards it, and nothing at `%Undefined%`,
  `_` or `Atom`; patterns read no fact there (`eqFacts`), and a call to itself or
  into another version is asked nothing there (`CallsOK.self`,
  `CallsOK.selfGuarded`). A number meets the entry fact at `%Undefined%`, which the
  relation does not give it (`Controls.unchecked_entry`).
* **The version theorem** (`version_eq_protocol`): when every argument meeting
  the entry facts passes the argument guards once, the equations call
  themselves only with arguments meeting the entry facts, and every answer
  meets the result's fact whenever the calls to itself do, the protocol's run
  and the version's run agree at every fuel on arguments meeting the entry
  facts. A checked call then has the same answers through either
  (`checked_call_eq`), since under functional declarations an argument list
  that passes the guards meets the entry facts (`entryFacts_of_argCount`).
* **The analysis** (`Accepted`) reads facts from head patterns (`PatFact`: a
  variable takes its parameter's fact; an application of a constructor in the
  class, at a closed named type that is not a metatype name, gives each field
  that is not free its instance), types right-hand sides (`HasType`: literals
  by the relation, constructions by the class from parts typed at types that are
  not metatype names, calls to itself by the result type, operations PeTTa
  provides by the class of their values, typed calls of other relations by their
  result types, `let` and `match` by their body, `if` and `case` by a type every
  branch has, `(empty)` by any type), and checks that every call to itself meets
  the formals and every call entering another relation's version meets that
  version's entry facts (`CallsOK`). A variable that a `let`, a `case` arm or a
  `match` binds gets no fact, as in the C. Its rules are sound (`PatFact.sound`,
  `eval_sound`, `eval_congr`), so an accepted relation's version is its protocol
  (`accepted_version_eq_protocol`, `accepted_checked_call_eq`).
* **The range met** (`petta_open_answer_meet_range`): on arguments meeting the
  entry facts every answer of the version passes the result guard at the closed
  range once (`version_range_met`), so a checked call that entered its version
  answers exactly the version's answers (`checked_call_version`,
  `Controls.lsum_range_met`); without the version's proof the guard filters
  (`Controls.unproven_range_not_met`).
* **Ranges checked at the entry** (`PettaContractVersion.range_proved` false):
  when the calls to themselves are in tail positions only (`TailBodies`), the
  protocol's run is the version's run followed by one range check
  (`tail_version_eq_protocol`), since the check is idempotent under functional
  declarations (`rangeCheck_idem`); a checked call keeping its result check has
  the protocol's answers (`tail_checked_call_eq`, `Controls.cs_tail_version`).
  A call whose answers are used breaks it (`Controls.used_call_breaks`). The
  condition is the relation's: an equation that calls itself nowhere and one that
  proves its range, each fine alone, make a relation that is neither tail nor
  accepted, whose version differs from its protocol (`Controls.mixed_equations_break`).
* **Return checks across tail re-entry** (`checks_return`): when every typed head
  of a program has one closed range and the calls between heads are in tail
  positions only, the protocol's run is the run with no checks followed by one
  check (`chain_version_eq_protocol`). In general an activation of the machine
  owes a class (`return_class`, `machineRunS`): a call outside a tail position
  starts an activation owing its callee's class, a call in a tail position
  re-enters owing its caller's class or, where the caller owes none, the
  callee's, and a value is checked at the class of the activation that returns
  it. When an activation owing a class is one of a head whose protocol checks
  once there (`ChecksAt`), a typed head owing none has its range proved, and the
  equations read the oracle only at their calls outside tail positions
  (`ChainHyps`), the machine's run is the protocol's followed by the owed check
  (`machine_eq_protocol`), so a call from the evaluator has the protocol's
  answers (`machine_call_eq_protocol`); a tail call owing a second class does
  not occur (`ChainHyps.one_class`). Controls: `(+ 1 (cnt 3 0))` answers `4`
  (`Controls.top_nontail`); a tail call into a head of another class whose range
  is proved keeps its caller's class (`Controls.hand_label`); a call outside a
  tail position owing its caller's class would answer otherwise
  (`Controls.owe_caller_breaks`).
* **Structural parameters checked where another head calls**
  (`PREPARED_PURE_VALUE_STRUCTURAL`): for a head with a trusted version, the
  machine checks a call from outside the head, a value of its class at each value
  class, the type service typing the argument once at each structural formal, and
  nothing at `%Undefined%` or `_` (`MachineAccepts`), runs the version where the checks pass, its calls to itself
  and its structural range unchecked, and declines to the protocol elsewhere
  (`structuralRun`). The checks give the entry facts
  (`MachineAccepts.entryFacts`), so every call has the protocol's answers at every
  fuel (`structuralRun_eq_protocol`), and a head reading another through the
  machine reads its protocol (`structuralRun_oracle`). Controls: `(tsize (mk 6))`
  answers `127` (`Controls.tsize_mk`); `(tsize (Node 1 2))` answers nothing
  (`Controls.tsize_bad`); a call from `twice` is checked
  (`Controls.twice_checked`); the check is needed, as `tag`'s version answers a
  node of numbers that the protocol rejects (`Controls.tag_needs_check`); `mkbad`,
  whose range no version proves, is not accepted and keeps its range check
  (`Controls.mkbad_not_accepted`, `Controls.mkbad_answers`); a `%Undefined%`
  position beside a structural one is checked for nothing, and
  `(tagged (mk 3) anything)` answers `8` (`Controls.tagged_mk`).
* **The tail analysis** (`Tail`, `NoSelf`, `scan->tail`): calls to itself only
  in tail positions, at arguments meeting the formals, give the decomposition
  the tail theorem reads (`tail_decomp`, `tailBodies_of_tail`), so such equations'
  version is their protocol followed by one range check
  (`tail_accepted_version_eq_protocol`, `Controls.cs_eqs_version`).
* **Symbols keep closed declared types** (`contract_eval` on a symbol), an arrow
  included (`Controls.constant_closed_arrow`); a closed type other than the
  formal gives no fact and fails the guard (`Controls.constant_other_arrow`).
* **Entering other versions.** The version's run enters a callee's version
  where the protocol's run runs the callee's protocol. The two agree at the
  callee's entry facts and answer its result's fact there, which the callee's
  own version theorem gives (`callee_oracles`).
* **Protocols that factor** (`Factored`, `factored_version_eq`): the version
  theorem needs only that the protocol counts argument lists and answers, which
  closed rows do and rows with private polymorphic parameters do
  (`TypedCalls.Polymorphic`).

The fragment: one closed row with guarded parameters and a guarded result;
equations with linear head patterns; right-hand sides of variables, constants,
data, calls to itself, operations PeTTa provides, typed calls of other
relations, kept or entered, `let`, `if`, `(empty)`, `case` and `match` over
spaces that do not change during a call. Matching is one-way: a pattern binds
parts of a value, as unification does on ground values. Controls: the fold
`lsum` over lists of numbers is accepted (`Controls.lsum_accepted`), and its
version is its protocol (`Controls.lsum_version`); so are `lpos`, through
`let`, `if` and `case` (`Controls.lpos_version`, `Controls.lpos_answers`),
`weights`, through `match` over a space with two rows
(`Controls.weights_version`), and `total`, entering `lsum`'s version
(`Controls.total_version`). At the formal `Expression` the pattern `(C $s)`
gives `$s` no fact (`Controls.no_fact_at_metatype`), nor does a field declared
`%Undefined%` (`Controls.no_fact_at_unchecked_field`); a variable a `let` binds
has no fact, so the analysis does not enter a version at it
(`Controls.let_bound_untyped`, `Controls.no_enter_at_let_bound`); and the
functional precondition is necessary: read as SWI-PeTTa's `get-type` reads a
repeated row of `Cons`, the protocol answers `5` twice for `(Cons 5 Nil)` where
the version answers it once (`Controls.repeated_rows_break_version`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Facts at metatype names -/

/-- The names `get-metatype` returns. -/
def MetaName (T : Ty Empty) : Prop :=
  T = .sym "Expression" ∨ T = .sym "Symbol" ∨ T = .sym "Grounded" ∨ T = .sym "Variable"

instance (T : Ty Empty) : Decidable (MetaName T) := by
  unfold MetaName
  infer_instance

theorem metaName_metatype (grounded : String → Bool) (v : Atom) :
    MetaName (.sym (metatype grounded v)) := by
  cases v with
  | symbol s => by_cases h : grounded s <;> simp [metatype, MetaName, h]
  | var _ => simp [metatype, MetaName]
  | grounded _ => simp [metatype, MetaName]
  | expression _ => simp [metatype, MetaName]

section Facts

variable (Γ : Decls) (grounded : String → Bool)

/-- **An entry fact at a closed type**: at a metatype name, the guard succeeds
once; at any other type, the type relation types the value once. -/
def Holds (v : Atom) (T : Ty Empty) : Prop :=
  if MetaName T then guardCount (info Γ v) T (metatype grounded v) = 1
  else count (info Γ v) T = 1

variable {Γ grounded}

/-- Away from the metatype names the guard is the relation. -/
theorem guardCount_of_not_meta {T : Ty Empty} (h : ¬ MetaName T) (v : Atom) :
    guardCount (info Γ v) T (metatype grounded v) = count (info Γ v) T :=
  guardCount_of_ne _ _ _ fun same => h (same ▸ metaName_metatype grounded v)

/-- **A fact discharges its guard.** -/
theorem Holds.guardCount {v : Atom} {T : Ty Empty} (h : Holds Γ grounded v T) :
    TypedCalls.guardCount (info Γ v) T (metatype grounded v) = 1 := by
  unfold Holds at h
  split_ifs at h with hm
  · exact h
  · rw [guardCount_of_not_meta hm]
    exact h

/-- A value the relation types once meets the fact of its type. -/
theorem Holds.of_count {v : Atom} {T : Ty Empty} (h : count (info Γ v) T = 1) :
    Holds Γ grounded v T := by
  unfold Holds
  split_ifs
  · unfold TypedCalls.guardCount
    rw [if_neg (by omega), h]
  · exact h

/-- Away from the metatype names a fact is the relation's. -/
theorem Holds.count {v : Atom} {T : Ty Empty} (h : Holds Γ grounded v T) (hm : ¬ MetaName T) :
    TypedCalls.count (info Γ v) T = 1 := by
  unfold Holds at h
  rwa [if_neg hm] at h

/-- Under functional declarations, a guard that succeeds meets the fact. -/
theorem Holds.of_guardCount (hΓ : Functional Γ) {v : Atom} {T : Ty Empty}
    (h : TypedCalls.guardCount (info Γ v) T (metatype grounded v) ≠ 0) : Holds Γ grounded v T := by
  unfold Holds
  split_ifs with hm
  · unfold TypedCalls.guardCount at h ⊢
    have := count_le_one hΓ v T
    split_ifs at h ⊢ with h0 h1 <;> omega
  · rw [guardCount_of_not_meta hm] at h
    have := count_le_one hΓ v T
    omega

end Facts

/-! ## The version theorem -/

section Versions

variable (Γ : Decls) (grounded : String → Bool)

/-- A relation's run with the protocol at every call, its calls to itself
included. -/
noncomputable def protocolRun (body : (List Atom → Multiset Atom) → List Atom → Multiset Atom)
    (row : Ty String) : ℕ → List Atom → Multiset Atom
  | 0, _ => 0
  | n + 1, vs => chainCall Γ (metatype grounded) (body (protocolRun body row n)) row vs

/-- **The trusted version**: its calls to itself skip the protocol. -/
def versionRun (body : (List Atom → Multiset Atom) → List Atom → Multiset Atom) :
    ℕ → List Atom → Multiset Atom
  | 0, _ => 0
  | n + 1, vs => body (versionRun body n) vs

/-- The entry facts of a closed row's parameters: the fact of its type at each
parameter the protocol guards, and nothing at a parameter it does not check
(`%Undefined%`, `_`, or `Atom`, passed as written). -/
def EntryFacts (As : List (Ty Empty)) (vs : List Atom) : Prop :=
  List.Forall₂ (fun A v => demand A.lift = .guarded → Holds Γ grounded v A) As vs

/-- The entry facts of formals that may have type variables: at each guarded
formal the argument meets the fact of some closed instance of it; nothing
elsewhere. -/
def EntryPoly (Fs : List (Ty String)) (vs : List Atom) : Prop :=
  List.Forall₂ (fun F v => demand F = .guarded → ∃ τ : String → Ty Empty, Holds Γ grounded v (F.bind τ)) Fs vs

/-- At closed formals the two agree. -/
theorem entryPoly_lift_iff (As : List (Ty Empty)) (vs : List Atom) :
    EntryPoly Γ grounded (As.map Ty.lift) vs ↔ EntryFacts Γ grounded As vs := by
  unfold EntryPoly EntryFacts
  rw [List.forall₂_map_left_iff]
  constructor
  · exact fun h => h.imp fun A v hA hg => by
      obtain ⟨τ, hτ⟩ := hA hg
      rwa [Ty.lift_bind_ground] at hτ
  · exact fun h => h.imp fun A v hv hg => ⟨fun _ => default, by rw [Ty.lift_bind_ground]; exact hv hg⟩

/-- Facts that hold at every parameter give the entry facts. -/
theorem EntryFacts.of_holds {As : List (Ty Empty)} {vs : List Atom}
    (h : List.Forall₂ (fun A v => Holds Γ grounded v A) As vs) : EntryFacts Γ grounded As vs := by
  unfold EntryFacts
  exact List.Forall₂.imp (fun A _ hv => fun (_ : demand A.lift = .guarded) => hv) h

variable {Γ grounded}

/-- **The entry facts make every argument guard succeed exactly once.** -/
theorem argCount_of_entryFacts : ∀ {As : List (Ty Empty)} {vs : List Atom},
    EntryFacts Γ grounded As vs → argCount Γ (metatype grounded) As vs = 1
  | [], [], _ => rfl
  | A :: As, v :: vs, .cons hA hAs => by
      simp only [argCount]
      rw [argCount_of_entryFacts hAs, mul_one]
      split_ifs with hg
      · exact (hA hg).guardCount
      · rfl

/-- Under functional declarations, arguments that pass a closed row's guards
meet the entry facts. -/
theorem entryFacts_of_argCount (hΓ : Functional Γ) :
    ∀ {As : List (Ty Empty)} {vs : List Atom},
      argCount Γ (metatype grounded) As vs ≠ 0 → EntryFacts Γ grounded As vs
  | [], [], _ => .nil
  | A :: As, v :: vs, h => by
      simp only [argCount] at h
      refine .cons (fun hg => ?_) (entryFacts_of_argCount hΓ fun h0 => h (by rw [h0, mul_zero]))
      rw [if_pos hg] at h
      exact Holds.of_guardCount hΓ fun h0 => h (by rw [h0, zero_mul])
  | [], _ :: _, h => (h rfl).elim
  | _ :: _, [], h => by simp [argCount] at h

/-- The hypotheses of the version theorem, for a closed row `(-> A₁ … Aₖ R)`, the
equations `bodyP` the protocol's run reads and the equations `bodyV` the
version's run reads, each reading the calls to themselves through an oracle.
They differ where the version enters another relation's version and the
protocol runs that relation's protocol. -/
structure VersionHyps (bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom)
    (As : List (Ty Empty)) (R : Ty Empty) : Prop where
  /-- The result is guarded. -/
  resultGuarded : ResultGuarded R.lift
  /-- The equations call themselves only with arguments meeting the entry facts:
  two oracles that agree there, and answer there what the result's fact
  allows, give the same answers. -/
  calls : ∀ o o' : List Atom → Multiset Atom,
    (∀ ws, EntryFacts Γ grounded As ws → o ws = o' ws) →
    (∀ ws, EntryFacts Γ grounded As ws → ∀ r ∈ o ws, Holds Γ grounded r R) →
    ∀ vs, EntryFacts Γ grounded As vs → bodyP o vs = bodyV o' vs
  /-- Every answer meets the result's fact when the calls to itself do. -/
  results : ∀ o : List Atom → Multiset Atom,
    (∀ ws, EntryFacts Γ grounded As ws → ∀ r ∈ o ws, Holds Γ grounded r R) →
    ∀ vs, EntryFacts Γ grounded As vs → ∀ r ∈ bodyV o vs, Holds Γ grounded r R

theorem version_results {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty Empty)} {R : Ty Empty}
    (h : VersionHyps (Γ := Γ) (grounded := grounded) bodyP bodyV As R) :
    ∀ n vs, EntryFacts Γ grounded As vs → ∀ r ∈ versionRun bodyV n vs, Holds Γ grounded r R
  | 0, _, _, r, hr => absurd hr (Multiset.notMem_zero r)
  | n + 1, vs, hvs, r, hr => h.results _ (version_results h n) vs hvs r hr

/-- **The version is the protocol**: on arguments meeting the entry facts, the
run whose calls to themselves skip the protocol has, at every fuel, exactly
the answers of the run whose every call runs it. -/
theorem version_eq_protocol {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty Empty)} {R : Ty Empty}
    (h : VersionHyps (Γ := Γ) (grounded := grounded) bodyP bodyV As R) :
    ∀ n vs, EntryFacts Γ grounded As vs →
      protocolRun Γ grounded bodyP (arrow (As.map Ty.lift) R.lift) n vs = versionRun bodyV n vs
  | 0, _, _ => rfl
  | n + 1, vs, hvs => by
      simp only [protocolRun, versionRun]
      rw [chainCall_closed, argCount_of_entryFacts hvs, one_nsmul]
      simp only [if_pos h.resultGuarded]
      rw [h.calls _ _ (version_eq_protocol h n) (fun ws hws r hr => by
          rw [version_eq_protocol h n ws hws] at hr
          exact version_results h n ws hws r hr) vs hvs]
      refine (Multiset.bind_congr (g := fun r => ({r} : Multiset Atom)) fun r hr => ?_).trans ?_
      · rw [(h.results _ (version_results h n) vs hvs r hr).guardCount, one_nsmul]
      · rw [Multiset.bind_singleton, Multiset.map_id']

/-- **A checked call has the same answers through the version**: the protocol
runs once at the entry, and its arguments, when they pass, meet the entry
facts. -/
theorem checked_call_eq (hΓ : Functional Γ)
    {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty Empty)} {R : Ty Empty}
    (h : VersionHyps (Γ := Γ) (grounded := grounded) bodyP bodyV As R) (n : ℕ) (vs : List Atom) :
    chainCall Γ (metatype grounded) (bodyP (protocolRun Γ grounded bodyP (arrow (As.map Ty.lift) R.lift) n))
        (arrow (As.map Ty.lift) R.lift) vs =
      chainCall Γ (metatype grounded) (bodyV (versionRun bodyV n)) (arrow (As.map Ty.lift) R.lift) vs := by
  rw [chainCall_closed, chainCall_closed]
  by_cases h0 : argCount Γ (metatype grounded) As vs = 0
  · rw [h0, zero_nsmul, zero_nsmul]
  · have hvs := entryFacts_of_argCount hΓ h0
    rw [h.calls _ _ (version_eq_protocol h n) (fun ws hws r hr => by
      rw [version_eq_protocol h n ws hws] at hr
      exact version_results h n ws hws r hr) vs hvs]

/-- **The result check of a call run in its version is met**
(`petta_open_answer_meet_range`): on arguments meeting the entry facts, every
answer of the version passes the result guard at the closed range once, so the
guard leaves the version's answers as they are, multiplicities included. -/
theorem version_range_met {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty Empty)} {R : Ty Empty}
    (h : VersionHyps (Γ := Γ) (grounded := grounded) bodyP bodyV As R) (n : ℕ) (vs : List Atom)
    (hvs : EntryFacts Γ grounded As vs) :
    ((bodyV (versionRun bodyV n) vs).bind fun r =>
        TypedCalls.guardCount (info Γ r) R (metatype grounded r) • {r}) =
      bodyV (versionRun bodyV n) vs := by
  refine (Multiset.bind_congr (g := fun r => ({r} : Multiset Atom)) fun r hr => ?_).trans ?_
  · rw [(h.results _ (version_results h n) vs hvs r hr).guardCount, one_nsmul]
  · rw [Multiset.bind_singleton, Multiset.map_id']

/-- **A checked call that entered its version answers the version's answers**:
its argument guards pass once at the entry facts, and its result guard is met. -/
theorem checked_call_version {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty Empty)} {R : Ty Empty}
    (h : VersionHyps (Γ := Γ) (grounded := grounded) bodyP bodyV As R) (n : ℕ) (vs : List Atom)
    (hvs : EntryFacts Γ grounded As vs) :
    chainCall Γ (metatype grounded) (bodyV (versionRun bodyV n)) (arrow (As.map Ty.lift) R.lift) vs =
      bodyV (versionRun bodyV n) vs := by
  rw [chainCall_closed, argCount_of_entryFacts hvs, one_nsmul]
  simp only [if_pos h.resultGuarded]
  exact version_range_met h n vs hvs

/-! ### Versions whose range is checked at the entry -/

variable (Γ grounded) in
/-- The result guard at a closed range, on a bag of answers. -/
noncomputable def rangeCheck (R : Ty Empty) (m : Multiset Atom) : Multiset Atom :=
  m.bind fun r => TypedCalls.guardCount (info Γ r) R (metatype grounded r) • {r}

variable (Γ grounded) in
theorem rangeCheck_add (R : Ty Empty) (m m' : Multiset Atom) :
    rangeCheck Γ grounded R (m + m') = rangeCheck Γ grounded R m + rangeCheck Γ grounded R m' := by
  unfold rangeCheck
  rw [Multiset.add_bind]

variable (Γ grounded) in
theorem rangeCheck_bind {α : Type} (R : Ty Empty) (C : Multiset α) (o : α → Multiset Atom) :
    rangeCheck Γ grounded R (C.bind o) = C.bind fun ws => rangeCheck Γ grounded R (o ws) := by
  unfold rangeCheck
  rw [Multiset.bind_assoc]

variable (grounded) in
/-- **The range check is idempotent** under functional declarations: a value that
passed it passes again once. -/
theorem rangeCheck_idem (hΓ : Functional Γ) (R : Ty Empty) (m : Multiset Atom) :
    rangeCheck Γ grounded R (rangeCheck Γ grounded R m) = rangeCheck Γ grounded R m := by
  unfold rangeCheck
  rw [Multiset.bind_assoc]
  refine Multiset.bind_congr fun r _ => ?_
  have le := guardCount_le_one hΓ r R (metatype grounded r)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp le with h | h
  · rw [h, zero_nsmul, Multiset.zero_bind]
  · rw [h, one_nsmul, Multiset.singleton_bind, h, one_nsmul]

variable (Γ grounded) in
/-- **Calls to itself in tail positions only**: at arguments meeting the entry
facts, the equations' answers are answers `A` that do not read the calls to
itself, and the answers of calls to itself at argument lists `C` meeting the
entry facts, returned as they are; the protocol's equations and the version's
have the same `A`. -/
def TailBodies (As : List (Ty Empty))
    (bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom) : Prop :=
  ∀ vs, EntryFacts Γ grounded As vs → ∃ (A : Multiset Atom) (C : Multiset (List Atom)),
    (∀ ws ∈ C, EntryFacts Γ grounded As ws) ∧ (∀ o, bodyP o vs = A + C.bind o) ∧
      ∀ o, bodyV o vs = A + C.bind o

/-- **A version whose range is checked at the entry is the protocol**
(`PettaContractVersion.range_proved` false): when the calls to themselves are
in tail positions only, the run whose every call runs the protocol has, at
every fuel and on arguments meeting the entry facts, the answers of the
version's run followed by one range check. Each tail call's check tests the
values its caller returns at the same closed range, and passes once or not at
all, so the checks of the inner calls change no answer or multiplicity. -/
theorem tail_version_eq_protocol (hΓ : Functional Γ)
    {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty Empty)} {R : Ty Empty} (rg : ResultGuarded R.lift)
    (tail : TailBodies Γ grounded As bodyP bodyV) :
    ∀ n vs, EntryFacts Γ grounded As vs →
      protocolRun Γ grounded bodyP (arrow (As.map Ty.lift) R.lift) n vs =
        rangeCheck Γ grounded R (versionRun bodyV n vs)
  | 0, _, _ => by simp [protocolRun, versionRun, rangeCheck]
  | n + 1, vs, hvs => by
      obtain ⟨A, C, hC, hP, hV⟩ := tail vs hvs
      simp only [protocolRun, versionRun]
      rw [chainCall_closed, argCount_of_entryFacts hvs, one_nsmul]
      simp only [if_pos rg]
      change rangeCheck Γ grounded R (bodyP _ vs) = _
      rw [hP, hV, rangeCheck_add, rangeCheck_add, rangeCheck_bind, rangeCheck_bind]
      congr 1
      refine Multiset.bind_congr fun ws hws => ?_
      rw [tail_version_eq_protocol hΓ rg tail n ws (hC ws hws), rangeCheck_idem grounded hΓ]

/-- **A checked call entering such a version keeps its result check**: its
answers are the protocol's. -/
theorem tail_checked_call_eq (hΓ : Functional Γ)
    {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty Empty)} {R : Ty Empty} (rg : ResultGuarded R.lift)
    (tail : TailBodies Γ grounded As bodyP bodyV) (n : ℕ) (vs : List Atom)
    (hvs : EntryFacts Γ grounded As vs) :
    chainCall Γ (metatype grounded) (bodyV (versionRun bodyV n)) (arrow (As.map Ty.lift) R.lift) vs =
      protocolRun Γ grounded bodyP (arrow (As.map Ty.lift) R.lift) (n + 1) vs := by
  rw [tail_version_eq_protocol hΓ rg tail (n + 1) vs hvs, chainCall_closed,
    argCount_of_entryFacts hvs, one_nsmul]
  simp only [if_pos rg]
  rfl

/-! ### Tail chains through other heads -/

variable (Γ grounded) in
/-- **The run of a program of several heads**, every call running its head's
protocol: a typed head its closed row's, an untyped head its equations only. -/
noncomputable def protocolRunH {H : Type} (rows : H → Option (List (Ty Empty) × Ty Empty))
    (bodies : H → (H → List Atom → Multiset Atom) → List Atom → Multiset Atom) :
    ℕ → H → List Atom → Multiset Atom
  | 0, _, _ => 0
  | n + 1, h, vs => match rows h with
    | some (As, R) => chainCall Γ (metatype grounded) (bodies h (protocolRunH rows bodies n))
        (arrow (As.map Ty.lift) R.lift) vs
    | none => bodies h (protocolRunH rows bodies n) vs

/-- The run of a program of several heads with no checks at all. -/
def versionRunH {H : Type} (bodies : H → (H → List Atom → Multiset Atom) → List Atom → Multiset Atom) :
    ℕ → H → List Atom → Multiset Atom
  | 0, _, _ => 0
  | n + 1, h, vs => bodies h (versionRunH bodies n) vs

variable (Γ grounded) in
/-- A head's entry facts: a typed head's parameters', none for an untyped head. -/
def EntryH {H : Type} (rows : H → Option (List (Ty Empty) × Ty Empty)) (h : H) (vs : List Atom) : Prop :=
  ∀ As R, rows h = some (As, R) → EntryFacts Γ grounded As vs

/-- **Return checks across tail re-entry** (`checks_return`, `return_class`): when
every typed head of a program has the same closed range `R`, and every head's
equations make their calls, to themselves or to other heads, typed or not, in tail
positions only at arguments meeting the callee's entry facts, the protocol's run
of a typed head, every call checking its own result, is the run with no checks
followed by one check at `R`. The checks along a tail chain test one value at one
class, and under functional declarations pass it once or not at all; a tail call
into an untyped head leaves the value to the caller's check. -/
theorem chain_version_eq_protocol (hΓ : Functional Γ) {H : Type}
    {rows : H → Option (List (Ty Empty) × Ty Empty)}
    {bodies : H → (H → List Atom → Multiset Atom) → List Atom → Multiset Atom} {R : Ty Empty}
    (rg : ResultGuarded R.lift) (sameRange : ∀ h As R', rows h = some (As, R') → R' = R)
    (tail : ∀ h vs, EntryH Γ grounded rows h vs → ∃ (A : Multiset Atom) (C : Multiset (H × List Atom)),
      (∀ p ∈ C, EntryH Γ grounded rows p.1 p.2) ∧ ∀ o, bodies h o vs = A + C.bind fun p => o p.1 p.2) :
    ∀ n h vs, EntryH Γ grounded rows h vs →
      rangeCheck Γ grounded R (protocolRunH Γ grounded rows bodies n h vs) =
          rangeCheck Γ grounded R (versionRunH bodies n h vs) ∧
        ∀ As R', rows h = some (As, R') →
          protocolRunH Γ grounded rows bodies n h vs = rangeCheck Γ grounded R (versionRunH bodies n h vs)
  | 0, _, _, _ => ⟨rfl, fun _ _ _ => by simp [protocolRunH, versionRunH, rangeCheck]⟩
  | n + 1, h, vs, hvs => by
      obtain ⟨A, C, hC, hbody⟩ := tail h vs hvs
      have ih := fun p (hp : p ∈ C) => (chain_version_eq_protocol hΓ rg sameRange tail n p.1 p.2 (hC p hp)).1
      have checked : rangeCheck Γ grounded R (bodies h (protocolRunH Γ grounded rows bodies n) vs) =
          rangeCheck Γ grounded R (versionRunH bodies (n + 1) h vs) := by
        simp only [versionRunH]
        rw [hbody, hbody, rangeCheck_add, rangeCheck_add, rangeCheck_bind, rangeCheck_bind]
        congr 1
        exact Multiset.bind_congr fun p hp => ih p hp
      have typedCase : ∀ As R', rows h = some (As, R') →
          protocolRunH Γ grounded rows bodies (n + 1) h vs =
            rangeCheck Γ grounded R (versionRunH bodies (n + 1) h vs) := by
        intro As R' hrow
        have hR := sameRange h As R' hrow
        subst hR
        simp only [protocolRunH, hrow]
        rw [chainCall_closed, argCount_of_entryFacts (hvs As R' hrow), one_nsmul]
        simp only [if_pos rg]
        exact checked
      refine ⟨?_, typedCase⟩
      cases hrow : rows h with
      | some p =>
          rw [typedCase p.1 p.2 hrow, rangeCheck_idem grounded hΓ]
      | none =>
          simp only [protocolRunH, hrow]
          exact checked

/-! ### Activations, each owing a class -/

variable (Γ grounded) in
/-- The check an activation owes when it returns: none, or the range check at a
closed class. -/
noncomputable def owedCheck : Option (Ty Empty) → Multiset Atom → Multiset Atom
  | none, m => m
  | some R, m => rangeCheck Γ grounded R m

variable (Γ grounded) in
theorem owedCheck_bind {α : Type} (o : Option (Ty Empty)) (C : Multiset α) (f : α → Multiset Atom) :
    owedCheck Γ grounded o (C.bind f) = C.bind fun a => owedCheck Γ grounded o (f a) := by
  cases o with
  | none => rfl
  | some R => exact rangeCheck_bind Γ grounded R C f

variable (Γ grounded) in
/-- **A call whose protocol checks once at a closed range**: at the arguments
`vs`, the protocol of the row `T` around any equations is their answers, each
checked at `R`. -/
def ChecksAt (T : Ty String) (vs : List Atom) (R : Ty Empty) : Prop :=
  ∀ body : List Atom → Multiset Atom,
    chainCall Γ (metatype grounded) body T vs = rangeCheck Γ grounded R (body vs)

/-- A closed row whose parameters pass once checks once at its range. -/
theorem checksAt_closed {As : List (Ty Empty)} {R : Ty Empty} {vs : List Atom}
    (rg : ResultGuarded R.lift) (h : argCount Γ (metatype grounded) As vs = 1) :
    ChecksAt Γ grounded (arrow (As.map Ty.lift) R.lift) vs R := fun body => by
  rw [chainCall_closed, h, one_nsmul]
  simp only [if_pos rg]
  rfl

/-- What passed a range check meets the range's fact. -/
theorem holds_of_mem_rangeCheck (hΓ : Functional Γ) {R : Ty Empty} {m : Multiset Atom} {r : Atom}
    (h : r ∈ rangeCheck Γ grounded R m) : Holds Γ grounded r R := by
  obtain ⟨x, -, hx⟩ := Multiset.mem_bind.mp h
  obtain ⟨h0, hx⟩ := Multiset.mem_nsmul.mp hx
  rw [Multiset.mem_singleton] at hx
  subst hx
  exact Holds.of_guardCount hΓ h0

/-- An outcome's answers: the value returned, or the answers the oracle gives
for the call in a tail position. -/
def outcomeAnswers {H : Type} (O : H → List Atom → Multiset Atom) : Atom ⊕ (H × List Atom) → Multiset Atom
  | .inl r => {r}
  | .inr c => O c.1 c.2

variable (Γ grounded) in
/-- **The protocol's run of a program** whose equations `steps h O vs` give
outcomes, a value returned or a call in a tail position, the oracle `O`
answering their calls outside tail positions: every call runs its head's
protocol, a typed head's at its declared row `sig`, an untyped head's equations
as they are. -/
noncomputable def protocolRunS {H : Type} (sig : H → Option (Ty String))
    (steps : H → (H → List Atom → Multiset Atom) → List Atom → Multiset (Atom ⊕ (H × List Atom))) :
    ℕ → H → List Atom → Multiset Atom
  | 0, _, _ => 0
  | n + 1, h, vs => match sig h with
    | some T => chainCall Γ (metatype grounded)
        (fun ws => (steps h (protocolRunS sig steps n) ws).bind (outcomeAnswers (protocolRunS sig steps n))) T vs
    | none => (steps h (protocolRunS sig steps n) vs).bind (outcomeAnswers (protocolRunS sig steps n))

variable (Γ grounded) in
/-- **The machine's run** (`return_class`) of an activation owing the class `o`:
a call outside a tail position starts an activation owing the callee's class
`owe g ws`; a call in a tail position re-enters in place of its caller, owing the
class the caller owes, or the callee's where the caller owes none; a value the
activation returns is checked at the class it owes. -/
noncomputable def machineRunS {H : Type} (owe : H → List Atom → Option (Ty Empty))
    (steps : H → (H → List Atom → Multiset Atom) → List Atom → Multiset (Atom ⊕ (H × List Atom))) :
    ℕ → Option (Ty Empty) → H → List Atom → Multiset Atom
  | 0, _, _, _ => 0
  | n + 1, o, h, vs => (steps h (fun g ws => machineRunS owe steps n (owe g ws) g ws) vs).bind fun
      | .inl r => owedCheck Γ grounded o {r}
      | .inr c => machineRunS owe steps n (o.or (owe c.1 c.2)) c.1 c.2

variable (Γ grounded) in
/-- An oracle answers, at every call whose protocol checks once at a closed
range, values meeting that range's fact. -/
def AnswersMeet {H : Type} (sig : H → Option (Ty String)) (O : H → List Atom → Multiset Atom) : Prop :=
  ∀ g ws T R, sig g = some T → ChecksAt Γ grounded T ws R → ∀ r ∈ O g ws, Holds Γ grounded r R

variable (Γ grounded) in
/-- **The activations of a run**: an invariant `Act o h vs` of the head `h` at the
arguments `vs` in an activation owing `o`, with what the machine assumes of them. -/
structure ChainHyps {H : Type} (sig : H → Option (Ty String)) (owe : H → List Atom → Option (Ty Empty))
    (steps : H → (H → List Atom → Multiset Atom) → List Atom → Multiset (Atom ⊕ (H × List Atom)))
    (NonTail : H → List Atom → H → List Atom → Prop) (Act : Option (Ty Empty) → H → List Atom → Prop) :
    Prop where
  /-- An activation of a head that owes a class owes that class, and the head's
  protocol checks once there. -/
  owes : ∀ o h vs R, Act o h vs → owe h vs = some R →
    o = some R ∧ ∃ T, sig h = some T ∧ ChecksAt Γ grounded T vs R
  /-- A typed head that owes no class has its range proved: where the oracle's
  answers meet their facts, its protocol keeps each answer of its equations once. -/
  proven : ∀ o h vs T, Act o h vs → owe h vs = none → sig h = some T →
    ∀ O, AnswersMeet Γ grounded sig O →
      chainCall Γ (metatype grounded) (fun ws => (steps h O ws).bind (outcomeAnswers O)) T vs =
        (steps h O vs).bind (outcomeAnswers O)
  /-- The equations read the oracle at their calls outside tail positions only,
  where an oracle whose answers meet their facts makes them. -/
  congr : ∀ o h vs, Act o h vs → ∀ O O', AnswersMeet Γ grounded sig O' →
    (∀ g ws, NonTail h vs g ws → O g ws = O' g ws) → steps h O vs = steps h O' vs
  /-- A call outside a tail position starts an activation owing its callee's class. -/
  nonTail : ∀ o h vs g ws, Act o h vs → NonTail h vs g ws → Act (owe g ws) g ws
  /-- A call in a tail position re-enters owing the caller's class, or the callee's
  where the caller owes none. -/
  tail : ∀ o h vs O, Act o h vs → AnswersMeet Γ grounded sig O →
    ∀ g ws, .inr (g, ws) ∈ steps h O vs → Act (o.or (owe g ws)) g ws

section Chains

variable {H : Type} {sig : H → Option (Ty String)} {owe : H → List Atom → Option (Ty Empty)}
  {steps : H → (H → List Atom → Multiset Atom) → List Atom → Multiset (Atom ⊕ (H × List Atom))}
  {NonTail : H → List Atom → H → List Atom → Prop} {Act : Option (Ty Empty) → H → List Atom → Prop}

/-- **A tail call owing a second class has no activation**: where the caller owes
`c` and the callee `d`, the two are one, so a run that meets the hypotheses never
reaches the machine's decline (`a tail call owes two range classes`). -/
theorem ChainHyps.one_class (hyps : ChainHyps Γ grounded sig owe steps NonTail Act) {o : Option (Ty Empty)}
    {h g : H} {vs ws : List Atom} {O : H → List Atom → Multiset Atom} {c d : Ty Empty}
    (hA : Act o h vs) (hO : AnswersMeet Γ grounded sig O) (hc : .inr (g, ws) ∈ steps h O vs)
    (ho : o = some c) (hg : owe g ws = some d) : c = d := by
  have := (hyps.owes _ g ws d (hyps.tail o h vs O hA hO g ws hc) hg).1
  subst ho
  exact Option.some.inj this

variable (sig steps) in
/-- The protocol's answers meet their facts. -/
theorem answersMeet_protocol (hΓ : Functional Γ) :
    ∀ n, AnswersMeet Γ grounded sig (protocolRunS Γ grounded sig steps n)
  | 0 => fun _ _ _ _ _ _ r hr => absurd hr (Multiset.notMem_zero r)
  | n + 1 => fun g ws T R hg hT r hr => by
      simp only [protocolRunS, hg] at hr
      rw [hT] at hr
      exact holds_of_mem_rangeCheck hΓ hr

/-- The protocol's answers at an activation were checked already at the class
its head owes. -/
theorem owedCheck_protocol (hΓ : Functional Γ) (hyps : ChainHyps Γ grounded sig owe steps NonTail Act)
    {o : Option (Ty Empty)} {h : H} {vs : List Atom} (hA : Act o h vs) (n : ℕ) :
    owedCheck Γ grounded (owe h vs) (protocolRunS Γ grounded sig steps n h vs) =
      protocolRunS Γ grounded sig steps n h vs := by
  cases hR : owe h vs with
  | none => rfl
  | some R =>
      obtain ⟨-, T, hT, hc⟩ := hyps.owes o h vs R hA hR
      cases n with
      | zero => simp [owedCheck, protocolRunS, rangeCheck]
      | succ n =>
          simp only [owedCheck, protocolRunS, hT]
          rw [hc]
          exact rangeCheck_idem grounded hΓ R _

/-- At an activation, the class it owes sees the protocol's run of the head as
the head's equations over the protocol's runs of the calls. -/
theorem owedCheck_protocol_step (hΓ : Functional Γ) (hyps : ChainHyps Γ grounded sig owe steps NonTail Act)
    {o : Option (Ty Empty)} {h : H} {vs : List Atom} (hA : Act o h vs) (n : ℕ) :
    owedCheck Γ grounded o (protocolRunS Γ grounded sig steps (n + 1) h vs) =
      owedCheck Γ grounded o ((steps h (protocolRunS Γ grounded sig steps n) vs).bind
        (outcomeAnswers (protocolRunS Γ grounded sig steps n))) := by
  cases hR : owe h vs with
  | some R =>
      obtain ⟨rfl, T, hT, hc⟩ := hyps.owes o h vs R hA hR
      simp only [protocolRunS, hT, owedCheck]
      rw [hc, rangeCheck_idem grounded hΓ]
  | none =>
      cases hT : sig h with
      | none => simp only [protocolRunS, hT]
      | some T =>
          simp only [protocolRunS, hT]
          rw [hyps.proven o h vs T hA hR hT _ (answersMeet_protocol sig steps hΓ n)]

/-- **Return checks across tail re-entry and calls outside tail positions**
(`checks_return`, `return_class`): at every fuel, an activation's run on the
machine is the protocol's run, every call checking its own result, followed by
the check the activation owes. Each value is checked once, where the activation
that returns it returns; a call outside a tail position starts its own chain,
and the caller consumes its answers, which are the protocol's. -/
theorem machine_eq_protocol (hΓ : Functional Γ) (hyps : ChainHyps Γ grounded sig owe steps NonTail Act) :
    ∀ n o h vs, Act o h vs →
      machineRunS Γ grounded owe steps n o h vs =
        owedCheck Γ grounded o (protocolRunS Γ grounded sig steps n h vs)
  | 0, o, _, _, _ => by cases o <;> simp [machineRunS, protocolRunS, owedCheck, rangeCheck]
  | n + 1, o, h, vs, hA => by
      have ih := machine_eq_protocol hΓ hyps n
      have nonTailSame : ∀ g ws, NonTail h vs g ws →
          machineRunS Γ grounded owe steps n (owe g ws) g ws = protocolRunS Γ grounded sig steps n g ws := by
        intro g ws hg
        have hAg := hyps.nonTail o h vs g ws hA hg
        rw [ih _ g ws hAg, owedCheck_protocol hΓ hyps hAg n]
      rw [owedCheck_protocol_step hΓ hyps hA n, owedCheck_bind]
      simp only [machineRunS]
      rw [hyps.congr o h vs hA (fun g ws => machineRunS Γ grounded owe steps n (owe g ws) g ws) _
        (answersMeet_protocol sig steps hΓ n) nonTailSame]
      refine Multiset.bind_congr fun c hc => ?_
      rcases c with r | ⟨g, ws⟩
      · rfl
      · have hAg := hyps.tail o h vs _ hA (answersMeet_protocol sig steps hΓ n) g ws hc
        show machineRunS Γ grounded owe steps n (o.or (owe g ws)) g ws =
          owedCheck Γ grounded o (protocolRunS Γ grounded sig steps n g ws)
        rw [ih _ g ws hAg]
        cases o with
        | some c => rfl
        | none => exact owedCheck_protocol hΓ hyps hAg n

/-- **A call outside a tail position, or from the evaluator, runs as the machine
runs it**: its activation owes the callee's class, and its answers are the
protocol's. -/
theorem machine_call_eq_protocol (hΓ : Functional Γ) (hyps : ChainHyps Γ grounded sig owe steps NonTail Act)
    {h : H} {vs : List Atom} (hA : Act (owe h vs) h vs) (n : ℕ) :
    machineRunS Γ grounded owe steps n (owe h vs) h vs = protocolRunS Γ grounded sig steps n h vs := by
  rw [machine_eq_protocol hΓ hyps n _ h vs hA, owedCheck_protocol hΓ hyps hA n]

end Chains

/-! ### Protocols that factor -/

/-- A row's protocol that factors into counts: each argument list counted by its
guards, each answer by its result guard. Closed rows factor
(`chainCall_closed`), and so do rows whose type variables are private to their
parameters (`TypedCalls.Polymorphic`). -/
structure Factored (call : (List Atom → Multiset Atom) → List Atom → Multiset Atom) where
  args : List Atom → ℕ
  result : Atom → ℕ
  eq : ∀ (B : List Atom → Multiset Atom) (vs : List Atom),
    call B vs = args vs • (B vs).bind fun r => result r • {r}

/-- The run whose every call runs the protocol `call`. -/
def factoredRun (call : (List Atom → Multiset Atom) → List Atom → Multiset Atom)
    (body : (List Atom → Multiset Atom) → List Atom → Multiset Atom) : ℕ → List Atom → Multiset Atom
  | 0, _ => 0
  | n + 1, vs => call (body (factoredRun call body n)) vs

/-- **The version theorem for a factored protocol**: when the entry facts make
the argument count one, the result facts make the result count one, the
equations call themselves only at entry facts and answer the result facts
whenever the calls to themselves do, the version's run is the protocol's. The
protocol's run reads `bodyP` and the version's `bodyV`. -/
theorem factored_version_eq {call : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    (F : Factored call) {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {Entry : List Atom → Prop} {Res : Atom → Prop}
    (entry : ∀ vs, Entry vs → F.args vs = 1) (res : ∀ r, Res r → F.result r = 1)
    (calls : ∀ o o' : List Atom → Multiset Atom, (∀ ws, Entry ws → o ws = o' ws) →
      (∀ ws, Entry ws → ∀ r ∈ o ws, Res r) → ∀ vs, Entry vs → bodyP o vs = bodyV o' vs)
    (results : ∀ o : List Atom → Multiset Atom, (∀ ws, Entry ws → ∀ r ∈ o ws, Res r) →
      ∀ vs, Entry vs → ∀ r ∈ bodyV o vs, Res r) :
    ∀ n vs, Entry vs → factoredRun call bodyP n vs = versionRun bodyV n vs ∧
      ∀ r ∈ versionRun bodyV n vs, Res r
  | 0, _, _ => ⟨rfl, fun r hr => absurd hr (Multiset.notMem_zero r)⟩
  | n + 1, vs, hvs => by
      have ih := factored_version_eq F entry res calls results n
      have agree : ∀ ws, Entry ws → factoredRun call bodyP n ws = versionRun bodyV n ws :=
        fun ws hws => (ih ws hws).1
      have oracle : ∀ ws, Entry ws → ∀ r ∈ versionRun bodyV n ws, Res r := fun ws hws => (ih ws hws).2
      have answers : ∀ r ∈ bodyV (versionRun bodyV n) vs, Res r := results _ oracle vs hvs
      refine ⟨?_, answers⟩
      simp only [factoredRun, versionRun]
      rw [F.eq, entry vs hvs, one_nsmul, calls _ _ agree (fun ws hws r hr => by
        rw [agree ws hws] at hr
        exact oracle ws hws r hr) vs hvs]
      refine (Multiset.bind_congr (g := fun r => ({r} : Multiset Atom)) fun r hr => ?_).trans ?_
      · rw [res r (answers r hr), one_nsmul]
      · rw [Multiset.bind_singleton, Multiset.map_id']

end Versions

/-! ## Equations the analysis reads -/

/-- Patterns of an equation's parameters: variables, constants matched by
equality, and applications of a symbol to patterns. -/
inductive Pat where
  | var (x : String)
  | const (a : Atom)
  | ctor (c : String) (args : List Pat)

/-- Right-hand sides, as the analysis reads them (`contract_eval`): variables,
constants, data built by a symbol, the relation's calls to itself, operations
PeTTa provides (`contract_pure_operation`), typed calls of other relations that
keep their protocol, typed calls that enter another relation's version
(`contract_meets_version`), `let` (`let*` is nested lets), `if` (without an
else, the else is `empty`), `(empty)`, `case` with the patterns and bodies of
its arms, and `match` over a space. -/
inductive Expr where
  | var (x : String)
  | const (a : Atom)
  | ctor (c : String) (args : List Expr)
  | self (args : List Expr)
  | prim (op : String) (args : List Expr)
  | call (f : String) (args : List Expr)
  | enter (f : String) (args : List Expr)
  | letE (p : Pat) (val body : Expr)
  | ifE (c t e : Expr)
  | empty
  | caseE (key : Expr) (pats : List Pat) (bodies : List Expr)
  | matchE (src : Expr) (p : Pat) (t : Expr)

namespace Pat

mutual
/-- The variables of a pattern, in order. -/
def vars : Pat → List String
  | .var x => [x]
  | .const _ => []
  | .ctor _ ps => varsAll ps

/-- The variables of a list of patterns. -/
def varsAll : List Pat → List String
  | [] => []
  | p :: ps => vars p ++ varsAll ps
end

mutual
/-- Matching a value: the bindings of the pattern's variables. -/
def «match» : Pat → Atom → Option (List (String × Atom))
  | .var x, v => some [(x, v)]
  | .const a, v => if v = a then some [] else none
  | .ctor c ps, .expression (.symbol c' :: vs) => if c = c' then matchAll ps vs else none
  | .ctor _ _, _ => none

/-- Matching a list of values. -/
def matchAll : List Pat → List Atom → Option (List (String × Atom))
  | [], [] => some []
  | p :: ps, v :: vs =>
      match «match» p v, matchAll ps vs with
      | some ρ, some ρ' => some (ρ ++ ρ')
      | _, _ => none
  | [], _ :: _ => none
  | _ :: _, [] => none
end

mutual
/-- The bindings of a match bind the pattern's variables. -/
theorem match_keys : ∀ (p : Pat) (v : Atom) (ρ : List (String × Atom)), «match» p v = some ρ →
    ρ.map Prod.fst = vars p
  | .var x, v, ρ, h => by
      simp only [«match», Option.some.injEq] at h
      subst h
      rfl
  | .const a, v, ρ, h => by
      simp only [«match»] at h
      split_ifs at h
      cases h
      rfl
  | .ctor c ps, .expression (.symbol c' :: vs), ρ, h => by
      simp only [«match»] at h
      split_ifs at h
      exact matchAll_keys ps vs ρ h
  | .ctor _ _, .symbol _, _, h => by simp [«match»] at h
  | .ctor _ _, .var _, _, h => by simp [«match»] at h
  | .ctor _ _, .grounded _, _, h => by simp [«match»] at h
  | .ctor _ _, .expression [], _, h => by simp [«match»] at h
  | .ctor _ _, .expression (.var _ :: _), _, h => by simp [«match»] at h
  | .ctor _ _, .expression (.grounded _ :: _), _, h => by simp [«match»] at h
  | .ctor _ _, .expression (.expression _ :: _), _, h => by simp [«match»] at h

theorem matchAll_keys : ∀ (ps : List Pat) (vs : List Atom) (ρ : List (String × Atom)),
    matchAll ps vs = some ρ → ρ.map Prod.fst = varsAll ps
  | [], [], ρ, h => by
      simp only [matchAll, Option.some.injEq] at h
      subst h
      rfl
  | p :: ps, v :: vs, ρ, h => by
      simp only [matchAll] at h
      split at h
      · next ρ₁ ρ₂ h₁ h₂ =>
          simp only [Option.some.injEq] at h
          subst h
          rw [List.map_append, match_keys p v ρ₁ h₁, matchAll_keys ps vs ρ₂ h₂]
          rfl
      · cases h
  | [], _ :: _, _, h => by simp [matchAll] at h
  | _ :: _, [], _, h => by simp [matchAll] at h
end

end Pat

namespace Pat

/-- Bindings extended by new ones: a variable already bound must be bound to the
same value. -/
def extend : List (String × Atom) → List (String × Atom) → Option (List (String × Atom))
  | ρ, [] => some ρ
  | ρ, (x, a) :: σ => match ρ.lookup x with
    | some b => if a = b then extend ρ σ else none
    | none => extend ((x, a) :: ρ) σ

/-- Matching a value under bindings, as `let`, `case` and `match` bind their
patterns. -/
def matchUnder (ρ : List (String × Atom)) (p : Pat) (v : Atom) : Option (List (String × Atom)) :=
  («match» p v).bind (extend ρ)

/-- **Extending bindings keeps every binding.** -/
theorem extend_lookup : ∀ (ρ σ ρ' : List (String × Atom)), extend ρ σ = some ρ' →
    ∀ x w, ρ.lookup x = some w → ρ'.lookup x = some w
  | ρ, [], ρ', h, x, w, hx => by
      simp only [extend, Option.some.injEq] at h
      subst h
      exact hx
  | ρ, (y, a) :: σ, ρ', h, x, w, hx => by
      simp only [extend] at h
      split at h
      · split_ifs at h
        exact extend_lookup ρ σ ρ' h x w hx
      · next hy =>
          refine extend_lookup _ σ ρ' h x w ?_
          have ne : x ≠ y := by
            rintro rfl
            rw [hy] at hx
            cases hx
          simp only [List.lookup, beq_false_of_ne ne, hx]

theorem matchUnder_lookup {ρ ρ' : List (String × Atom)} {p : Pat} {v : Atom}
    (h : matchUnder ρ p v = some ρ') {x : String} {w : Atom} (hx : ρ.lookup x = some w) :
    ρ'.lookup x = some w := by
  unfold matchUnder at h
  cases hm : «match» p v with
  | none => rw [hm] at h; cases h
  | some σ =>
      rw [hm, Option.bind_some] at h
      exact extend_lookup ρ σ ρ' h x w hx

end Pat

/-- What a relation's equations read and do not change while a call runs: the
operations PeTTa provides, the typed calls of other relations that keep their
protocol, and the rows of the spaces. -/
structure Env where
  prim : String → List Atom → Multiset Atom
  kept : String → List Atom → Multiset Atom
  rows : Atom → Multiset Atom

/-- The calls a run makes through oracles: to itself, and into the versions of
other relations. -/
structure Oracle where
  self : List Atom → Multiset Atom
  enter : String → List Atom → Multiset Atom

/-- PeTTa's true, which `if` tests for. -/
def truth : Atom := .grounded (.bool true)

/-- The class of the values an operation PeTTa provides gives, at an arity
(`contract_pure_operation`): comparisons and connectives a `Bool`, arithmetic a
`Number`. -/
def primClass : String → ℕ → Option String
  | "==", 2 | "<", 2 | ">", 2 | "<=", 2 | ">=", 2 | "and", 2 | "or", 2 | "not", 1 => some "Bool"
  | "+", 2 | "-", 2 | "*", 2 | "/", 2 => some "Number"
  | _, _ => none

/-- The value of addition, where it does not raise. -/
def plus : Atom → Atom → Multiset Atom
  | .grounded (.int m), .grounded (.int n) => {.grounded (.int (m + n))}
  | _, _ => 0

namespace Expr

mutual
/-- Evaluation under bindings `ρ`. A `let`, a `case` arm and a `match` row bind
their pattern under `ρ`; `if` takes its then branch at `true` and its else
branch at any other value; `case` takes the first arm whose pattern matches. -/
def eval (E : Env) (O : Oracle) (ρ : List (String × Atom)) : Expr → Multiset Atom
  | .var x => match ρ.lookup x with
    | some v => {v}
    | none => 0
  | .const a => {a}
  | .ctor c args => (evalAll E O ρ args).map fun vs => .expression (.symbol c :: vs)
  | .self args => (evalAll E O ρ args).bind O.self
  | .prim op args => (evalAll E O ρ args).bind (E.prim op)
  | .call f args => (evalAll E O ρ args).bind (E.kept f)
  | .enter f args => (evalAll E O ρ args).bind (O.enter f)
  | .letE p val body => (eval E O ρ val).bind fun w =>
      match Pat.matchUnder ρ p w with
      | some ρ' => eval E O ρ' body
      | none => 0
  | .ifE c t e => (eval E O ρ c).bind fun w => if w = truth then eval E O ρ t else eval E O ρ e
  | .empty => 0
  | .caseE key pats bodies => (eval E O ρ key).bind fun w => evalArms E O ρ w pats bodies
  | .matchE src p t => (eval E O ρ src).bind fun sp => (E.rows sp).bind fun row =>
      match Pat.matchUnder ρ p row with
      | some ρ' => eval E O ρ' t
      | none => 0

/-- Evaluation of a list: one value list per choice of the values. -/
def evalAll (E : Env) (O : Oracle) (ρ : List (String × Atom)) : List Expr → Multiset (List Atom)
  | [] => {[]}
  | e :: es => (eval E O ρ e).bind fun v => (evalAll E O ρ es).map (v :: ·)

/-- The arms of a `case` at the key's value `w`: the first arm whose pattern
matches. -/
def evalArms (E : Env) (O : Oracle) (ρ : List (String × Atom)) (w : Atom) :
    List Pat → List Expr → Multiset Atom
  | p :: ps, b :: bs => match Pat.matchUnder ρ p w with
    | some ρ' => eval E O ρ' b
    | none => evalArms E O ρ w ps bs
  | _, _ => 0
end

end Expr

/-- An equation: patterns for the parameters and a right-hand side. -/
structure Equation where
  pats : List Pat
  rhs : Expr

/-- The equations of a relation: every equation whose patterns match
contributes its answers. -/
def equationsBody (E : Env) (eqs : List Equation) (O : Oracle) (vs : List Atom) : Multiset Atom :=
  (eqs : Multiset Equation).bind fun eq =>
    match Pat.matchAll eq.pats vs with
    | some ρ => eq.rhs.eval E O ρ
    | none => 0

/-! ## Matching, positionally -/

namespace Pat

theorem matchAll_length : ∀ (ps : List Pat) (vs : List Atom) (ρ : List (String × Atom)),
    matchAll ps vs = some ρ → ps.length = vs.length
  | [], [], _, _ => rfl
  | p :: ps, v :: vs, ρ, h => by
      simp only [matchAll] at h
      split at h
      · next ρ₁ ρ₂ _ h₂ => simp [matchAll_length ps vs ρ₂ h₂]
      · cases h
  | [], _ :: _, _, h => by simp [matchAll] at h
  | _ :: _, [], _, h => by simp [matchAll] at h

theorem vars_sublist_varsAll {p : Pat} : ∀ {ps : List Pat}, p ∈ ps → (vars p).Sublist (varsAll ps)
  | q :: qs, h => by
      rw [varsAll]
      rcases List.mem_cons.mp h with rfl | h
      · exact List.sublist_append_left _ _
      · exact (vars_sublist_varsAll h).trans (List.sublist_append_right _ _)

theorem vars_subset_varsAll {p : Pat} {ps : List Pat} (h : p ∈ ps) : vars p ⊆ varsAll ps :=
  (vars_sublist_varsAll h).subset

/-- **A binding of a field's variable comes from the field's own match**, when
the patterns are linear. -/
theorem field_binding {β : Type} {x : String} {w : Atom} :
    ∀ (Bs : List β) (ps : List Pat) (vs : List Atom) (ρ : List (String × Atom)),
      matchAll ps vs = some ρ → (varsAll ps).Nodup → ∀ (B : β) (p : Pat), (B, p) ∈ List.zip Bs ps →
      x ∈ vars p → (x, w) ∈ ρ →
      ∃ v ρ', (B, v) ∈ List.zip Bs vs ∧ «match» p v = some ρ' ∧ (x, w) ∈ ρ'
  | B₀ :: Bs, p₀ :: ps, v₀ :: vs, ρ, h, nodup, B, p, hB, hx, hw => by
      simp only [matchAll] at h
      split at h
      · next ρ₀ ρ₁ h₀ h₁ =>
          simp only [Option.some.injEq] at h
          subst h
          rw [varsAll, List.nodup_append] at nodup
          rw [List.zip_cons_cons, List.mem_cons] at hB
          have keys₀ := match_keys p₀ v₀ ρ₀ h₀
          have keys₁ := matchAll_keys ps vs ρ₁ h₁
          rcases hB with same | hB
          · simp only [Prod.mk.injEq] at same
            obtain ⟨rfl, rfl⟩ := same
            rcases List.mem_append.mp hw with hw | hw
            · exact ⟨v₀, ρ₀, by simp, h₀, hw⟩
            · have : x ∈ varsAll ps := keys₁ ▸ List.mem_map_of_mem (f := Prod.fst) hw
              exact absurd rfl (nodup.2.2 x hx x this)
          · have hp : p ∈ ps := (List.of_mem_zip hB).2
            rcases List.mem_append.mp hw with hw | hw
            · have : x ∈ vars p₀ := keys₀ ▸ List.mem_map_of_mem (f := Prod.fst) hw
              exact absurd rfl (nodup.2.2 x this x (vars_subset_varsAll hp hx))
            · obtain ⟨v, ρ', hv, hm, hw'⟩ := field_binding Bs ps vs ρ₁ h₁ nodup.2.1 B p hB hx hw
              exact ⟨v, ρ', by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hv, hm, hw'⟩
      · cases h
  | [], _, _, _, _, _, _, _, hB, _, _ => by simp at hB
  | _ :: _, [], _, _, _, _, _, _, hB, _, _ => by simp at hB
  | _ :: _, _ :: _, [], _, h, _, _, _, _, _, _ => by simp [matchAll] at h

end Pat

theorem forall₂_zip {α γ : Type} {P : α → γ → Prop} :
    ∀ {As : List α} {vs : List γ}, List.Forall₂ P As vs → ∀ a v, (a, v) ∈ List.zip As vs → P a v
  | [], [], .nil, _, _, h => by simp at h
  | _ :: _, _ :: _, .cons hp hps, a, v, h => by
      rw [List.zip_cons_cons, List.mem_cons] at h
      rcases h with same | h
      · simp only [Prod.mk.injEq] at same
        obtain ⟨rfl, rfl⟩ := same
        exact hp
      · exact forall₂_zip hps a v h

theorem zip_of_forall₂ {α β γ : Type} {P : β → γ → Prop} :
    ∀ {es : List β} {vs : List γ}, List.Forall₂ P es vs → ∀ (Bs : List α) (B : α) (v : γ),
      (B, v) ∈ List.zip Bs vs → ∃ e, (B, e) ∈ List.zip Bs es ∧ P e v
  | [], [], .nil, _, _, _, h => by simp at h
  | e :: es, v' :: vs, .cons hp hps, B₀ :: Bs, B, v, h => by
      rw [List.zip_cons_cons, List.mem_cons] at h
      rcases h with same | h
      · simp only [Prod.mk.injEq] at same
        obtain ⟨rfl, rfl⟩ := same
        exact ⟨e, by simp, hp⟩
      · obtain ⟨e', he', hp'⟩ := zip_of_forall₂ hps Bs B v h
        exact ⟨e', by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ he', hp'⟩
  | _ :: _, _ :: _, .cons _ _, [], _, _, h => by simp at h

namespace Expr

theorem evalAll_mem (E : Env) (O : Oracle) (ρ : List (String × Atom)) :
    ∀ (es : List Expr) (vs : List Atom), vs ∈ evalAll E O ρ es →
      List.Forall₂ (fun e v => v ∈ eval E O ρ e) es vs
  | [], vs, h => by
      simp only [evalAll, Multiset.mem_singleton] at h
      subst h
      exact .nil
  | e :: es, vs, h => by
      simp only [evalAll, Multiset.mem_bind, Multiset.mem_map] at h
      obtain ⟨v, hv, vs', hvs', rfl⟩ := h
      exact .cons hv (evalAll_mem E O ρ es vs' hvs')

theorem evalAll_congr {E : Env} {O O' : Oracle} {ρ : List (String × Atom)} :
    ∀ (es : List Expr), (∀ e ∈ es, eval E O ρ e = eval E O' ρ e) → evalAll E O ρ es = evalAll E O' ρ es
  | [], _ => rfl
  | e :: es, h => by
      simp only [evalAll]
      rw [h e (by simp), evalAll_congr es fun e' he' => h e' (by simp [he'])]

end Expr

/-! ## The analysis -/

section Analysis

variable (Γ : Decls) (res : String → Ty Empty) (ent : String → List (Ty Empty))

/-- **The facts the analysis reads from a pattern** at a parameter of closed
type `T` (`contract_invert`): a variable has the parameter's fact; an
application of a constructor in the class, at a closed named type that is
not a metatype name, gives each field that is not free the instance of its type
under the match of the result; a free field, `%Undefined%`, `_` or a type
variable named once, gives nothing. -/
inductive PatFact : Pat → Ty Empty → String → Ty Empty → Prop
  | var (x : String) (T : Ty Empty) : PatFact (.var x) T x T
  | ctor {c : String} {Bs : List (Ty String)} {R : Ty String} {ps : List Pat} {T : Ty Empty}
      {σ : String → Ty Empty} {x : String} {U : Ty Empty} {B : Ty String} {p : Pat}
      (row : Γ c = [arrow Bs R]) (cls : Constructor Bs R) (len : ps.length = Bs.length)
      (notMeta : ¬ MetaName T) (named : Named T) (hmatch : R.bind σ = T)
      (field : (B, p) ∈ List.zip Bs ps) (fixed : ¬ FreeField R B)
      (inner : PatFact p (B.bind σ) x U) : PatFact (.ctor c ps) T x U

/-- **The types the analysis gives right-hand sides**, under facts `Φ` for the
pattern variables, the relation's closed result type `R` and the closed result
types `res` of other relations: a variable its fact; a constant the type the
relation gives it; a construction the result of a constructor in the class, at
an instance its parts fix, each part at a field that is not free typed at a type
that is not a metatype name (`contract_constructed_type`); a call to itself the
result type; an operation PeTTa provides the class of its values; a typed call
of another relation, kept or entered, that relation's result type; a `let` and
a `match` the type of their body; an `if` and a `case` a type every branch has;
`(empty)` every type. The variables a `let`, a `case` arm or a `match` binds get
no fact (`contract_bind_any`, `contract_bind`). -/
inductive HasType (Φ : String → Ty Empty → Prop) (R : Ty Empty) : Expr → Ty Empty → Prop
  | var {x : String} {U : Ty Empty} : Φ x U → HasType Φ R (.var x) U
  | const {a : Atom} {T : Ty Empty} : count (info Γ a) T = 1 → HasType Φ R (.const a) T
  | ctor {c : String} {Bs : List (Ty String)} {R' : Ty String} {args : List Expr}
      {σ : String → Ty Empty} (row : Γ c = [arrow Bs R']) (cls : Constructor Bs R')
      (len : args.length = Bs.length)
      (notMeta : ∀ q ∈ List.zip Bs args, ¬ FreeField R' q.1 → ¬ MetaName (q.1.bind σ))
      (parts : ∀ q ∈ List.zip Bs args, ¬ FreeField R' q.1 → HasType Φ R q.2 (q.1.bind σ)) :
      HasType Φ R (.ctor c args) (R'.bind σ)
  | self {args : List Expr} : HasType Φ R (.self args) R
  | prim {op : String} {args : List Expr} {c : String} (cls : primClass op args.length = some c) :
      HasType Φ R (.prim op args) (.sym c)
  | call {f : String} {args : List Expr} : HasType Φ R (.call f args) (res f)
  | enter {f : String} {args : List Expr} : HasType Φ R (.enter f args) (res f)
  | letE {p : Pat} {val body : Expr} {T : Ty Empty} : HasType Φ R body T →
      HasType Φ R (.letE p val body) T
  | ifE {c t e : Expr} {T : Ty Empty} : HasType Φ R t T → HasType Φ R e T →
      HasType Φ R (.ifE c t e) T
  | empty {T : Ty Empty} : HasType Φ R .empty T
  | caseE {key : Expr} {pats : List Pat} {bodies : List Expr} {T : Ty Empty} :
      (∀ b ∈ bodies, HasType Φ R b T) → HasType Φ R (.caseE key pats bodies) T
  | matchE {src : Expr} {p : Pat} {t : Expr} {T : Ty Empty} : HasType Φ R t T →
      HasType Φ R (.matchE src p t) T

/-- **Every call to itself meets the formals** (`contract_self_call`): each
argument typed at an instance of its formal (`contract_meets_formal`; at a closed
formal, the formal itself), and **every call entering another relation's version
meets that version's entry facts** (`contract_meets_version`). -/
inductive CallsOK (Φ : String → Ty Empty → Prop) (R : Ty Empty) (As : List (Ty String)) :
    Expr → Prop
  | var {x : String} : CallsOK Φ R As (.var x)
  | const {a : Atom} : CallsOK Φ R As (.const a)
  | ctor {c : String} {args : List Expr} : (∀ e ∈ args, CallsOK Φ R As e) →
      CallsOK Φ R As (.ctor c args)
  | self {args : List Expr} : (∀ e ∈ args, CallsOK Φ R As e) →
      List.Forall₂ (fun A e => demand A = .guarded → ∃ τ : String → Ty Empty, HasType Γ res Φ R e (A.bind τ))
        As args →
      CallsOK Φ R As (.self args)
  | prim {op : String} {args : List Expr} : (∀ e ∈ args, CallsOK Φ R As e) →
      CallsOK Φ R As (.prim op args)
  | call {f : String} {args : List Expr} : (∀ e ∈ args, CallsOK Φ R As e) →
      CallsOK Φ R As (.call f args)
  | enter {f : String} {args : List Expr} : (∀ e ∈ args, CallsOK Φ R As e) →
      List.Forall₂ (fun A e => demand A.lift = .guarded → HasType Γ res Φ R e A) (ent f) args →
      CallsOK Φ R As (.enter f args)
  | letE {p : Pat} {val body : Expr} : CallsOK Φ R As val → CallsOK Φ R As body →
      CallsOK Φ R As (.letE p val body)
  | ifE {c t e : Expr} : CallsOK Φ R As c → CallsOK Φ R As t → CallsOK Φ R As e →
      CallsOK Φ R As (.ifE c t e)
  | empty : CallsOK Φ R As .empty
  | caseE {key : Expr} {pats : List Pat} {bodies : List Expr} : CallsOK Φ R As key →
      (∀ b ∈ bodies, CallsOK Φ R As b) → CallsOK Φ R As (.caseE key pats bodies)
  | matchE {src : Expr} {p : Pat} {t : Expr} : CallsOK Φ R As src → CallsOK Φ R As t →
      CallsOK Φ R As (.matchE src p t)

/-- The facts of an equation's pattern variables, read at the guarded parameters:
a parameter the protocol does not check gives none. -/
def eqFacts (As : List (Ty Empty)) (eq : Equation) (x : String) (U : Ty Empty) : Prop :=
  ∃ A p, (A, p) ∈ List.zip As eq.pats ∧ demand A.lift = .guarded ∧ PatFact Γ p A x U

/-- **An equation the analysis accepts** for the closed row `(-> A₁ … Aₖ R)`. -/
structure Accepted (As : List (Ty Empty)) (R : Ty Empty) (eq : Equation) : Prop where
  linear : (Pat.varsAll eq.pats).Nodup
  len : eq.pats.length = As.length
  calls : CallsOK Γ res ent (eqFacts Γ As eq) R (As.map Ty.lift) eq.rhs
  result : HasType Γ res (eqFacts Γ As eq) R eq.rhs R

variable {Γ res ent} in
/-- A call to itself at a closed row: each argument typed at its formal. -/
theorem CallsOK.selfClosed {Φ : String → Ty Empty → Prop} {R : Ty Empty} {As : List (Ty Empty)}
    {args : List Expr} (h : ∀ e ∈ args, CallsOK Γ res ent Φ R (As.map Ty.lift) e)
    (typed : List.Forall₂ (fun A e => HasType Γ res Φ R e A) As args) :
    CallsOK Γ res ent Φ R (As.map Ty.lift) (.self args) :=
  .self h (List.forall₂_map_left_iff.mpr (typed.imp fun _ _ hA _ =>
    ⟨fun _ => default, by rwa [Ty.lift_bind_ground]⟩))

variable {Γ res ent} in
/-- A call to itself at a closed row, its arguments typed at the guarded formals
only: nothing is asked at a formal the protocol does not check. -/
theorem CallsOK.selfGuarded {Φ : String → Ty Empty → Prop} {R : Ty Empty} {As : List (Ty Empty)}
    {args : List Expr} (h : ∀ e ∈ args, CallsOK Γ res ent Φ R (As.map Ty.lift) e)
    (typed : List.Forall₂ (fun A e => demand A.lift = .guarded → HasType Γ res Φ R e A) As args) :
    CallsOK Γ res ent Φ R (As.map Ty.lift) (.self args) :=
  .self h (List.forall₂_map_left_iff.mpr (typed.imp fun _ _ hA hg =>
    ⟨fun _ => default, by rw [Ty.lift_bind_ground]; exact hA hg⟩))

/-- **An equation the analysis accepts at a signature with private formals**
(`contract_private_formal`): at every closed instance of the formals, the facts
read at that instance type the right-hand side at the closed result, and every
call to itself meets some instance of the formals. -/
structure AcceptedPriv (Fs : List (Ty String)) (R : Ty Empty) (eq : Equation) : Prop where
  linear : (Pat.varsAll eq.pats).Nodup
  len : eq.pats.length = Fs.length
  calls : ∀ σ : String → Ty Empty,
    CallsOK Γ res ent (eqFacts Γ (Fs.map fun F => F.bind σ) eq) R Fs eq.rhs
  result : ∀ σ : String → Ty Empty,
    HasType Γ res (eqFacts Γ (Fs.map fun F => F.bind σ) eq) R eq.rhs R

end Analysis

/-! ## Soundness of the analysis -/

section Soundness

variable {Γ : Decls} {grounded : String → Bool} {res : String → Ty Empty}
  {ent : String → List (Ty Empty)}

theorem PatFact.mem_vars {p : Pat} {T : Ty Empty} {x : String} {U : Ty Empty}
    (h : PatFact Γ p T x U) : x ∈ Pat.vars p := by
  induction h with
  | var x T => simp [Pat.vars]
  | ctor _ _ _ _ _ _ field _ _ ih =>
      rw [Pat.vars]
      exact Pat.vars_subset_varsAll (List.of_mem_zip field).2 ih

/-- **The facts read from a pattern hold** of the bindings of a value that meets
the parameter's fact. -/
theorem PatFact.sound (hΓ : Functional Γ) {p : Pat} {T : Ty Empty} {x : String} {U : Ty Empty}
    (h : PatFact Γ p T x U) :
    ∀ {v : Atom} {ρ : List (String × Atom)} {w : Atom}, (Pat.vars p).Nodup →
      Pat.match p v = some ρ → Holds Γ grounded v T → (x, w) ∈ ρ → Holds Γ grounded w U := by
  induction h with
  | var x T =>
      intro v ρ w _ hm hv hw
      simp only [Pat.match, Option.some.injEq] at hm
      subst hm
      simp only [List.mem_singleton, Prod.mk.injEq, true_and] at hw
      subst hw
      exact hv
  | @ctor c Bs R ps T σ x U B p row cls len notMeta named hmatch field fixed inner ih =>
      intro v ρ w nodup hm hv hw
      match v, hm with
      | .expression (.symbol c' :: vs), hm =>
          simp only [Pat.match] at hm
          split_ifs at hm with hc
          subst hc
          have lenVs : vs.length = Bs.length := by
            rw [← Pat.matchAll_length ps vs ρ hm, len]
          obtain ⟨σ', hσ', fields⟩ := ctor_inversion hΓ row vs lenVs T named (hv.count notMeta)
          obtain ⟨v', ρ', hv', hm', hw'⟩ :=
            Pat.field_binding Bs ps vs ρ hm (by simpa [Pat.vars] using nodup) B p field
              (PatFact.mem_vars inner) hw
          have fixedB : ∀ y ∈ B.vars, y ∈ R.vars := by
            rcases cls.fields B (List.of_mem_zip field).1 with free | fixedB
            · exact absurd free fixed
            · exact fixedB
          have same : B.bind σ' = B.bind σ := fixed_instance_unique fixedB (hσ'.trans hmatch.symm)
          have typed := fields (B, v') hv' (checked_of_not_free fixed)
          rw [same] at typed
          have nodupPs : (Pat.varsAll ps).Nodup := by simpa [Pat.vars] using nodup
          exact ih ((nodupPs.sublist (Pat.vars_sublist_varsAll (List.of_mem_zip field).2)))
            hm' (Holds.of_count typed) hw'
      | .symbol _, hm => simp [Pat.match] at hm
      | .var _, hm => simp [Pat.match] at hm
      | .grounded _, hm => simp [Pat.match] at hm
      | .expression [], hm => simp [Pat.match] at hm
      | .expression (.var _ :: _), hm => simp [Pat.match] at hm
      | .expression (.grounded _ :: _), hm => simp [Pat.match] at hm
      | .expression (.expression _ :: _), hm => simp [Pat.match] at hm

/-- A number is typed `Number` once, whatever the declarations. -/
theorem count_int (Γ : Decls) (n : ℤ) : count (info Γ (.grounded (.int n))) (.sym "Number") = 1 := by
  classical
  unfold count
  rw [info_int]
  unfold eff
  simp only [Multiset.card_singleton, one_ne_zero, if_false, Multiset.filter_singleton]
  rw [if_pos ⟨fun _ => default, (solves_append _ _ _).mpr ⟨by simp [classDeriv],
    (solves_singleton _ _).mpr rfl⟩⟩]
  rfl

theorem forall₂_compose {α β γ : Type} {P : α → β → Prop} {Q : β → γ → Prop} {S : α → γ → Prop} :
    ∀ {As : List α} {es : List β} {ws : List γ}, List.Forall₂ P As es → List.Forall₂ Q es ws →
      (∀ A e w, e ∈ es → P A e → Q e w → S A w) → List.Forall₂ S As ws
  | [], [], [], .nil, .nil, _ => .nil
  | A :: As, e :: es, w :: ws, .cons hp hps, .cons hq hqs, h =>
      .cons (h A e w (by simp) hp hq)
        (forall₂_compose hps hqs fun A' e' w' he' => h A' e' w' (by simp [he']))

theorem lookup_of_mem_keys : ∀ (ρ : List (String × Atom)) (x : String), x ∈ ρ.map Prod.fst →
    ∃ w, ρ.lookup x = some w
  | [], x, h => by simp at h
  | (y, a) :: ρ, x, h => by
      by_cases hxy : x = y
      · exact ⟨a, by simp [List.lookup, hxy]⟩
      · have mem : x ∈ ρ.map Prod.fst := by
          simp only [List.map_cons, List.mem_cons] at h
          exact h.resolve_left hxy
        obtain ⟨w, hw⟩ := lookup_of_mem_keys ρ x mem
        exact ⟨w, by simp only [List.lookup, beq_false_of_ne hxy, hw]⟩

/-- A literal of a value class meets the fact of its class. -/
theorem holds_literal {c : String} {r : Atom} (h : Literal c r) : Holds Γ grounded r (.sym c) := by
  cases r with
  | grounded g =>
      exact Holds.of_count (by rw [count_class Γ (show valueClass g = some c from h), if_pos rfl])
  | symbol _ => exact (h : False).elim
  | var _ => exact (h : False).elim
  | expression _ => exact (h : False).elim

variable (Γ grounded) in
/-- Bindings that meet facts: every variable with a fact is bound, to a value
that meets it. -/
def MeetsFacts (Φ : String → Ty Empty → Prop) (ρ : List (String × Atom)) : Prop :=
  ∀ x U, Φ x U → ∃ w, ρ.lookup x = some w ∧ Holds Γ grounded w U

theorem MeetsFacts.extend {Φ : String → Ty Empty → Prop} {ρ ρ' : List (String × Atom)}
    (h : MeetsFacts Γ grounded Φ ρ) (keep : ∀ x w, ρ.lookup x = some w → ρ'.lookup x = some w) :
    MeetsFacts Γ grounded Φ ρ' :=
  fun x U hx => let ⟨w, hl, hw⟩ := h x U hx; ⟨w, keep x w hl, hw⟩

variable (Γ grounded res) in
/-- What a run assumes of the operations PeTTa provides, which answer values of
their class, and of the typed calls that keep their protocol, whose answers met
their result guard. -/
structure EnvOK (E : Env) : Prop where
  prim : ∀ op vs c, primClass op vs.length = some c → ∀ r ∈ E.prim op vs, Literal c r
  kept : ∀ f vs, ∀ r ∈ E.kept f vs, Holds Γ grounded r (res f)

variable (Γ grounded res ent) in
/-- What a run assumes of its oracles: a call to itself at the entry facts answers
the result's fact, and a call entering another relation's version at that
version's entry facts answers its result's fact. -/
structure OracleOK (As : List (Ty String)) (R : Ty Empty) (O : Oracle) : Prop where
  self : ∀ ws, EntryPoly Γ grounded As ws → ∀ r ∈ O.self ws, Holds Γ grounded r R
  enter : ∀ f ws, EntryFacts Γ grounded (ent f) ws → ∀ r ∈ O.enter f ws, Holds Γ grounded r (res f)

variable (Γ grounded ent) in
/-- Oracles that agree wherever the analysis calls them. -/
def OracleAgree (As : List (Ty String)) (O O' : Oracle) : Prop :=
  (∀ ws, EntryPoly Γ grounded As ws → O.self ws = O'.self ws) ∧
    ∀ f ws, EntryFacts Γ grounded (ent f) ws → O.enter f ws = O'.enter f ws

variable {Φ : String → Ty Empty → Prop} {R : Ty Empty} {As : List (Ty String)} {E : Env}

mutual
/-- **The types the analysis gives hold of every value**, under bindings that
meet the facts, when the operations, the kept calls and the oracles answer what
the analysis assumes. -/
theorem eval_sound (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E) {O : Oracle}
    (hO : OracleOK Γ grounded res ent As R O) :
    ∀ (e : Expr) (ρ : List (String × Atom)), MeetsFacts Γ grounded Φ ρ → ∀ (T : Ty Empty),
      HasType Γ res Φ R e T → CallsOK Γ res ent Φ R As e → ∀ v ∈ e.eval E O ρ, Holds Γ grounded v T
  | .var x, ρ, facts, T, h, _, v, hv => by
      cases h with
      | var hx =>
          obtain ⟨w, hl, hw⟩ := facts x T hx
          simp only [Expr.eval, hl, Multiset.mem_singleton] at hv
          subst hv
          exact hw
  | .const a, _, _, T, h, _, v, hv => by
      cases h with
      | const hc =>
          simp only [Expr.eval, Multiset.mem_singleton] at hv
          subst hv
          exact Holds.of_count hc
  | .ctor c args, ρ, facts, T, h, hc, v, hv => by
      cases h with
      | @ctor _ Bs R' _ σ row cls len notMeta parts =>
          cases hc with
          | ctor hargs =>
              simp only [Expr.eval, Multiset.mem_map] at hv
              obtain ⟨vs, hvs, rfl⟩ := hv
              have each := Expr.evalAll_mem E O ρ args vs hvs
              have lenVs : vs.length = Bs.length := by rw [← each.length_eq, len]
              refine Holds.of_count (ctor_construction hΓ row cls vs lenVs σ fun q hq hf => ?_)
              obtain ⟨e, he, hv⟩ := zip_of_forall₂ each Bs q.1 q.2 hq
              have mem : e ∈ args := (List.of_mem_zip he).2
              exact (List.forall_iff_forall_mem.mp (evalAll_sound hΓ hE hO args ρ facts) e mem
                (q.1.bind σ) (parts (q.1, e) he hf) (hargs e mem) q.2 hv).count
                (notMeta (q.1, e) he hf)
  | .self args, ρ, facts, T, h, hc, v, hv => by
      cases h with
      | self =>
          cases hc with
          | self hargs typed =>
              simp only [Expr.eval, Multiset.mem_bind] at hv
              obtain ⟨ws, hws, hv⟩ := hv
              exact hO.self ws (forall₂_compose typed (Expr.evalAll_mem E O ρ args ws hws)
                fun A e w he hA hw hg => by
                  obtain ⟨τ, hτ⟩ := hA hg
                  exact ⟨τ, List.forall_iff_forall_mem.mp
                    (evalAll_sound hΓ hE hO args ρ facts) e he _ hτ (hargs e he) w hw⟩) v hv
  | .prim op args, ρ, _, T, h, _, v, hv => by
      cases h with
      | prim cls =>
          simp only [Expr.eval, Multiset.mem_bind] at hv
          obtain ⟨ws, hws, hv⟩ := hv
          have len : ws.length = args.length := (Expr.evalAll_mem E O ρ args ws hws).length_eq.symm
          exact holds_literal (hE.prim op ws _ (by rw [len]; exact cls) v hv)
  | .call f args, ρ, _, T, h, _, v, hv => by
      cases h with
      | call =>
          simp only [Expr.eval, Multiset.mem_bind] at hv
          obtain ⟨ws, -, hv⟩ := hv
          exact hE.kept f ws v hv
  | .enter f args, ρ, facts, T, h, hc, v, hv => by
      cases h with
      | enter =>
          cases hc with
          | enter hargs typed =>
              simp only [Expr.eval, Multiset.mem_bind] at hv
              obtain ⟨ws, hws, hv⟩ := hv
              exact hO.enter f ws (forall₂_compose typed (Expr.evalAll_mem E O ρ args ws hws)
                fun A e w he hA hw hg => List.forall_iff_forall_mem.mp
                  (evalAll_sound hΓ hE hO args ρ facts) e he A (hA hg) (hargs e he) w hw) v hv
  | .letE p val body, ρ, facts, T, h, hc, v, hv => by
      cases h with
      | letE hb =>
          cases hc with
          | letE _ hcb =>
              simp only [Expr.eval, Multiset.mem_bind] at hv
              obtain ⟨w, -, hv⟩ := hv
              split at hv
              · next ρ' hm =>
                  exact eval_sound hΓ hE hO body ρ'
                    (facts.extend fun x w hx => Pat.matchUnder_lookup hm hx) T hb hcb v hv
              · exact absurd hv (Multiset.notMem_zero v)
  | .ifE c t e, ρ, facts, T, h, hc, v, hv => by
      cases h with
      | ifE ht he =>
          cases hc with
          | ifE _ hct hce =>
              simp only [Expr.eval, Multiset.mem_bind] at hv
              obtain ⟨w, -, hv⟩ := hv
              split_ifs at hv
              · exact eval_sound hΓ hE hO t ρ facts T ht hct v hv
              · exact eval_sound hΓ hE hO e ρ facts T he hce v hv
  | .empty, _, _, _, _, _, v, hv => absurd hv (Multiset.notMem_zero v)
  | .caseE key pats bodies, ρ, facts, T, h, hc, v, hv => by
      cases h with
      | caseE hbs =>
          cases hc with
          | caseE _ hcbs =>
              simp only [Expr.eval, Multiset.mem_bind] at hv
              obtain ⟨w, -, hv⟩ := hv
              exact evalArms_sound hΓ hE hO w pats bodies ρ facts T hbs hcbs v hv
  | .matchE src p t, ρ, facts, T, h, hc, v, hv => by
      cases h with
      | matchE ht =>
          cases hc with
          | matchE _ hct =>
              simp only [Expr.eval, Multiset.mem_bind] at hv
              obtain ⟨sp, -, row, -, hv⟩ := hv
              split at hv
              · next ρ' hm =>
                  exact eval_sound hΓ hE hO t ρ'
                    (facts.extend fun x w hx => Pat.matchUnder_lookup hm hx) T ht hct v hv
              · exact absurd hv (Multiset.notMem_zero v)

/-- The list version. -/
theorem evalAll_sound (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E) {O : Oracle}
    (hO : OracleOK Γ grounded res ent As R O) :
    ∀ (args : List Expr) (ρ : List (String × Atom)), MeetsFacts Γ grounded Φ ρ →
      List.Forall (fun e => ∀ (T : Ty Empty), HasType Γ res Φ R e T → CallsOK Γ res ent Φ R As e →
        ∀ v ∈ e.eval E O ρ, Holds Γ grounded v T) args
  | [], _, _ => trivial
  | e :: es, ρ, facts => (List.forall_cons _ e es).mpr
      ⟨eval_sound hΓ hE hO e ρ facts, evalAll_sound hΓ hE hO es ρ facts⟩

/-- The arms of a `case`. -/
theorem evalArms_sound (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E) {O : Oracle}
    (hO : OracleOK Γ grounded res ent As R O) (w : Atom) :
    ∀ (pats : List Pat) (bodies : List Expr) (ρ : List (String × Atom)),
      MeetsFacts Γ grounded Φ ρ → ∀ (T : Ty Empty), (∀ b ∈ bodies, HasType Γ res Φ R b T) →
      (∀ b ∈ bodies, CallsOK Γ res ent Φ R As b) →
      ∀ v ∈ Expr.evalArms E O ρ w pats bodies, Holds Γ grounded v T
  | p :: ps, b :: bs, ρ, facts, T, hbs, hcbs, v, hv => by
      simp only [Expr.evalArms] at hv
      split at hv
      · next ρ' hm =>
          exact eval_sound hΓ hE hO b ρ' (facts.extend fun x w hx => Pat.matchUnder_lookup hm hx) T
            (hbs b (by simp)) (hcbs b (by simp)) v hv
      · exact evalArms_sound hΓ hE hO w ps bs ρ facts T (fun b' hb' => hbs b' (by simp [hb']))
          (fun b' hb' => hcbs b' (by simp [hb'])) v hv
  | [], _, _, _, _, _, _, v, hv => by simp [Expr.evalArms] at hv
  | _ :: _, [], _, _, _, _, _, v, hv => by simp [Expr.evalArms] at hv
end

mutual
/-- **The calls the analysis checks are made where the oracles agree**: two
oracles that agree there give the same values. -/
theorem eval_congr (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E) {O O' : Oracle}
    (hO : OracleOK Γ grounded res ent As R O) (agree : OracleAgree Γ grounded ent As O O') :
    ∀ (e : Expr) (ρ : List (String × Atom)), MeetsFacts Γ grounded Φ ρ →
      CallsOK Γ res ent Φ R As e → e.eval E O ρ = e.eval E O' ρ
  | .var _, _, _, _ => rfl
  | .const _, _, _, _ => rfl
  | .ctor c args, ρ, facts, hc => by
      cases hc with
      | ctor hargs =>
          simp only [Expr.eval]
          rw [Expr.evalAll_congr args fun e he => List.forall_iff_forall_mem.mp
            (evalAll_congr hΓ hE hO agree args ρ facts) e he (hargs e he)]
  | .self args, ρ, facts, hc => by
      cases hc with
      | self hargs typed =>
          simp only [Expr.eval]
          rw [← Expr.evalAll_congr args fun e he => List.forall_iff_forall_mem.mp
            (evalAll_congr hΓ hE hO agree args ρ facts) e he (hargs e he)]
          refine Multiset.bind_congr fun ws hws => agree.1 ws ?_
          exact forall₂_compose typed (Expr.evalAll_mem E O ρ args ws hws)
            fun A e w he hA hw hg => by
              obtain ⟨τ, hτ⟩ := hA hg
              exact ⟨τ, List.forall_iff_forall_mem.mp
                (evalAll_sound hΓ hE hO args ρ facts) e he _ hτ (hargs e he) w hw⟩
  | .prim op args, ρ, facts, hc => by
      cases hc with
      | prim hargs =>
          simp only [Expr.eval]
          rw [Expr.evalAll_congr args fun e he => List.forall_iff_forall_mem.mp
            (evalAll_congr hΓ hE hO agree args ρ facts) e he (hargs e he)]
  | .call f args, ρ, facts, hc => by
      cases hc with
      | call hargs =>
          simp only [Expr.eval]
          rw [Expr.evalAll_congr args fun e he => List.forall_iff_forall_mem.mp
            (evalAll_congr hΓ hE hO agree args ρ facts) e he (hargs e he)]
  | .enter f args, ρ, facts, hc => by
      cases hc with
      | enter hargs typed =>
          simp only [Expr.eval]
          rw [← Expr.evalAll_congr args fun e he => List.forall_iff_forall_mem.mp
            (evalAll_congr hΓ hE hO agree args ρ facts) e he (hargs e he)]
          refine Multiset.bind_congr fun ws hws => agree.2 f ws ?_
          exact forall₂_compose typed (Expr.evalAll_mem E O ρ args ws hws)
            fun A e w he hA hw hg => List.forall_iff_forall_mem.mp
              (evalAll_sound hΓ hE hO args ρ facts) e he A (hA hg) (hargs e he) w hw
  | .letE p val body, ρ, facts, hc => by
      cases hc with
      | letE hcv hcb =>
          simp only [Expr.eval]
          rw [eval_congr hΓ hE hO agree val ρ facts hcv]
          refine Multiset.bind_congr fun w _ => ?_
          split
          · next ρ' hm =>
              exact eval_congr hΓ hE hO agree body ρ'
                (facts.extend fun x w hx => Pat.matchUnder_lookup hm hx) hcb
          · rfl
  | .ifE c t e, ρ, facts, hc => by
      cases hc with
      | ifE hcc hct hce =>
          simp only [Expr.eval]
          rw [eval_congr hΓ hE hO agree c ρ facts hcc, eval_congr hΓ hE hO agree t ρ facts hct,
            eval_congr hΓ hE hO agree e ρ facts hce]
  | .empty, _, _, _ => rfl
  | .caseE key pats bodies, ρ, facts, hc => by
      cases hc with
      | caseE hck hcbs =>
          simp only [Expr.eval]
          rw [eval_congr hΓ hE hO agree key ρ facts hck]
          exact Multiset.bind_congr fun w _ => evalArms_congr hΓ hE hO agree w pats bodies ρ facts hcbs
  | .matchE src p t, ρ, facts, hc => by
      cases hc with
      | matchE hcs hct =>
          simp only [Expr.eval]
          rw [eval_congr hΓ hE hO agree src ρ facts hcs]
          refine Multiset.bind_congr fun sp _ => Multiset.bind_congr fun row _ => ?_
          split
          · next ρ' hm =>
              exact eval_congr hΓ hE hO agree t ρ'
                (facts.extend fun x w hx => Pat.matchUnder_lookup hm hx) hct
          · rfl

/-- The list version. -/
theorem evalAll_congr (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E) {O O' : Oracle}
    (hO : OracleOK Γ grounded res ent As R O) (agree : OracleAgree Γ grounded ent As O O') :
    ∀ (args : List Expr) (ρ : List (String × Atom)), MeetsFacts Γ grounded Φ ρ →
      List.Forall (fun e => CallsOK Γ res ent Φ R As e → e.eval E O ρ = e.eval E O' ρ) args
  | [], _, _ => trivial
  | e :: es, ρ, facts => (List.forall_cons _ e es).mpr
      ⟨eval_congr hΓ hE hO agree e ρ facts, evalAll_congr hΓ hE hO agree es ρ facts⟩

/-- The arms of a `case`. -/
theorem evalArms_congr (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E) {O O' : Oracle}
    (hO : OracleOK Γ grounded res ent As R O) (agree : OracleAgree Γ grounded ent As O O') (w : Atom) :
    ∀ (pats : List Pat) (bodies : List Expr) (ρ : List (String × Atom)),
      MeetsFacts Γ grounded Φ ρ → (∀ b ∈ bodies, CallsOK Γ res ent Φ R As b) →
      Expr.evalArms E O ρ w pats bodies = Expr.evalArms E O' ρ w pats bodies
  | p :: ps, b :: bs, ρ, facts, hcbs => by
      simp only [Expr.evalArms]
      split
      · next ρ' hm =>
          exact eval_congr hΓ hE hO agree b ρ' (facts.extend fun x w hx => Pat.matchUnder_lookup hm hx)
            (hcbs b (by simp))
      · exact evalArms_congr hΓ hE hO agree w ps bs ρ facts fun b' hb' => hcbs b' (by simp [hb'])
  | [], _, _, _, _ => by simp [Expr.evalArms]
  | _ :: _, [], _, _, _ => by simp [Expr.evalArms]
end

/-- **The facts an accepted equation reads hold** of the bindings of arguments
that meet the entry facts. -/
theorem eqFacts_sound (hΓ : Functional Γ) {Cs : List (Ty Empty)} {eq : Equation}
    (linear : (Pat.varsAll eq.pats).Nodup)
    {vs : List Atom} {ρ : List (String × Atom)} (hm : Pat.matchAll eq.pats vs = some ρ)
    (hvs : EntryFacts Γ grounded Cs vs) : MeetsFacts Γ grounded (eqFacts Γ Cs eq) ρ := by
  rintro x U ⟨A, p, hAp, hg, hpf⟩
  have key : x ∈ ρ.map Prod.fst := by
    rw [Pat.matchAll_keys _ _ _ hm]
    exact Pat.vars_subset_varsAll (List.of_mem_zip hAp).2 hpf.mem_vars
  obtain ⟨w, hl⟩ := lookup_of_mem_keys ρ x key
  refine ⟨w, hl, ?_⟩
  have hw : (x, w) ∈ ρ := by
    obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp hl
    simp
  obtain ⟨v, ρ', hv, hm', hw'⟩ := Pat.field_binding Cs eq.pats vs ρ hm linear A p hAp
    hpf.mem_vars hw
  exact hpf.sound hΓ (linear.sublist (Pat.vars_sublist_varsAll (List.of_mem_zip hAp).2)) hm'
    (forall₂_zip hvs A v hv hg) hw'

/-- **An accepted relation meets the hypotheses of the version theorem**: its
protocol's run reads the callees' protocols `enP` and its version's run their
versions `enV`, which agree at their entry facts and answer their results'
facts there. -/
theorem accepted_versionHyps (hΓ : Functional Γ) {Cs : List (Ty Empty)} {eqs : List Equation} (rg : ResultGuarded R.lift)
    (acc : ∀ eq ∈ eqs, Accepted Γ res ent Cs R eq) (hE : EnvOK Γ grounded res E)
    (enP enV : String → List Atom → Multiset Atom)
    (enAgree : ∀ f ws, EntryFacts Γ grounded (ent f) ws → enP f ws = enV f ws)
    (enRes : ∀ f ws, EntryFacts Γ grounded (ent f) ws → ∀ r ∈ enV f ws, Holds Γ grounded r (res f)) :
    VersionHyps (Γ := Γ) (grounded := grounded) (fun o => equationsBody E eqs ⟨o, enP⟩)
      (fun o => equationsBody E eqs ⟨o, enV⟩) Cs R where
  resultGuarded := rg
  calls o o' agree oracle vs hvs := by
    unfold equationsBody
    refine Multiset.bind_congr fun eq heq => ?_
    split
    · next ρ hm =>
        exact eval_congr hΓ hE ⟨fun ws hws => oracle ws ((entryPoly_lift_iff _ _ Cs ws).mp hws),
          fun f ws hws r hr => enRes f ws hws r (enAgree f ws hws ▸ hr)⟩
          ⟨fun ws hws => agree ws ((entryPoly_lift_iff _ _ Cs ws).mp hws), enAgree⟩ eq.rhs ρ
          (eqFacts_sound hΓ (acc eq heq).linear hm hvs) (acc eq heq).calls
    · rfl
  results o oracle vs hvs r hr := by
    unfold equationsBody at hr
    obtain ⟨eq, heq, hr⟩ := Multiset.mem_bind.mp hr
    split at hr
    · next ρ hm =>
        exact eval_sound hΓ hE ⟨fun ws hws => oracle ws ((entryPoly_lift_iff _ _ Cs ws).mp hws), enRes⟩
          eq.rhs ρ (eqFacts_sound hΓ (acc eq heq).linear hm hvs) R (acc eq heq).result (acc eq heq).calls r hr
    · exact absurd hr (Multiset.notMem_zero r)

/-- **The version of an accepted relation is its protocol**, at every fuel, on
arguments that meet the entry facts: the protocol's run runs every typed call's
protocol, the version's run enters itself and the callees' versions directly. -/
theorem accepted_version_eq_protocol (hΓ : Functional Γ) {Cs : List (Ty Empty)} {eqs : List Equation}
    (rg : ResultGuarded R.lift) (acc : ∀ eq ∈ eqs, Accepted Γ res ent Cs R eq)
    (hE : EnvOK Γ grounded res E) (enP enV : String → List Atom → Multiset Atom)
    (enAgree : ∀ f ws, EntryFacts Γ grounded (ent f) ws → enP f ws = enV f ws)
    (enRes : ∀ f ws, EntryFacts Γ grounded (ent f) ws → ∀ r ∈ enV f ws, Holds Γ grounded r (res f))
    (n : ℕ) (vs : List Atom) (hvs : EntryFacts Γ grounded Cs vs) :
    protocolRun Γ grounded (fun o => equationsBody E eqs ⟨o, enP⟩) (arrow (Cs.map Ty.lift) R.lift) n vs =
      versionRun (fun o => equationsBody E eqs ⟨o, enV⟩) n vs :=
  version_eq_protocol (accepted_versionHyps hΓ rg acc hE enP enV enAgree enRes) n vs hvs

/-- **A checked call of an accepted relation has the protocol's answers through
the version**, for every argument list. -/
theorem accepted_checked_call_eq (hΓ : Functional Γ) {Cs : List (Ty Empty)} {eqs : List Equation}
    (rg : ResultGuarded R.lift)
    (acc : ∀ eq ∈ eqs, Accepted Γ res ent Cs R eq) (hE : EnvOK Γ grounded res E)
    (enP enV : String → List Atom → Multiset Atom)
    (enAgree : ∀ f ws, EntryFacts Γ grounded (ent f) ws → enP f ws = enV f ws)
    (enRes : ∀ f ws, EntryFacts Γ grounded (ent f) ws → ∀ r ∈ enV f ws, Holds Γ grounded r (res f))
    (n : ℕ) (vs : List Atom) :
    chainCall Γ (metatype grounded)
        (equationsBody E eqs ⟨protocolRun Γ grounded (fun o => equationsBody E eqs ⟨o, enP⟩)
          (arrow (Cs.map Ty.lift) R.lift) n, enP⟩)
        (arrow (Cs.map Ty.lift) R.lift) vs =
      chainCall Γ (metatype grounded)
        (equationsBody E eqs ⟨versionRun (fun o => equationsBody E eqs ⟨o, enV⟩) n, enV⟩)
        (arrow (Cs.map Ty.lift) R.lift) vs :=
  checked_call_eq hΓ (accepted_versionHyps hΓ rg acc hE enP enV enAgree enRes) n vs

/-- **Entering an accepted callee's version is sound**: the callee's protocol
and version runs, at one fuel, agree at its entry facts and answer its
result's fact there, which is what a caller entering it assumes. -/
theorem callee_oracles (hΓ : Functional Γ) {eqs : List Equation} {Bs : List (Ty Empty)} {S : Ty Empty}
    (rg : ResultGuarded S.lift) (res' : String → Ty Empty) (ent' : String → List (Ty Empty))
    (acc : ∀ eq ∈ eqs, Accepted Γ res' ent' Bs S eq) (hE : EnvOK Γ grounded res' E)
    (m : ℕ) (vs : List Atom) (hvs : EntryFacts Γ grounded Bs vs) :
    protocolRun Γ grounded (fun o => equationsBody E eqs ⟨o, fun _ _ => 0⟩)
        (arrow (Bs.map Ty.lift) S.lift) m vs =
      versionRun (fun o => equationsBody E eqs ⟨o, fun _ _ => 0⟩) m vs ∧
    ∀ r ∈ versionRun (fun o => equationsBody E eqs ⟨o, fun _ _ => 0⟩) m vs, Holds Γ grounded r S := by
  have hyps := accepted_versionHyps (ent := ent') hΓ rg acc hE (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ _ => rfl) (fun _ _ _ r hr => absurd hr (Multiset.notMem_zero r))
  exact ⟨version_eq_protocol hyps m vs hvs, version_results hyps m vs hvs⟩

/-! ### Calls to itself in tail positions -/

mutual
/-- No call to itself. -/
def NoSelf : Expr → Prop
  | .var _ => True
  | .const _ => True
  | .ctor _ args => NoSelfAll args
  | .self _ => False
  | .prim _ args => NoSelfAll args
  | .call _ args => NoSelfAll args
  | .enter _ args => NoSelfAll args
  | .letE _ v b => NoSelf v ∧ NoSelf b
  | .ifE c t e => NoSelf c ∧ NoSelf t ∧ NoSelf e
  | .empty => True
  | .caseE k _ bs => NoSelf k ∧ NoSelfAll bs
  | .matchE src _ t => NoSelf src ∧ NoSelf t

/-- No call to itself in any element. -/
def NoSelfAll : List Expr → Prop
  | [] => True
  | e :: es => NoSelf e ∧ NoSelfAll es
end

theorem noSelfAll_iff : ∀ es : List Expr, NoSelfAll es ↔ ∀ e ∈ es, NoSelf e
  | [] => by simp [NoSelfAll]
  | e :: es => by simp [NoSelfAll, noSelfAll_iff es]

mutual
/-- **An expression without calls to itself does not read the oracle for them.** -/
theorem eval_noSelf (E : Env) (en : String → List Atom → Multiset Atom) (o o' : List Atom → Multiset Atom) :
    ∀ (e : Expr) (ρ : List (String × Atom)), NoSelf e → e.eval E ⟨o, en⟩ ρ = e.eval E ⟨o', en⟩ ρ
  | .var _, _, _ => rfl
  | .const _, _, _ => rfl
  | .ctor _ args, ρ, h => by simp only [Expr.eval]; rw [evalAll_noSelf E en o o' args ρ h]
  | .self _, _, h => h.elim
  | .prim _ args, ρ, h => by simp only [Expr.eval]; rw [evalAll_noSelf E en o o' args ρ h]
  | .call _ args, ρ, h => by simp only [Expr.eval]; rw [evalAll_noSelf E en o o' args ρ h]
  | .enter _ args, ρ, h => by simp only [Expr.eval]; rw [evalAll_noSelf E en o o' args ρ h]
  | .letE p v b, ρ, ⟨hv, hb⟩ => by
      simp only [Expr.eval]
      rw [eval_noSelf E en o o' v ρ hv]
      refine Multiset.bind_congr fun w _ => ?_
      split
      · next ρ' _ => exact eval_noSelf E en o o' b ρ' hb
      · rfl
  | .ifE c t e, ρ, ⟨hc, ht, he⟩ => by
      simp only [Expr.eval]
      rw [eval_noSelf E en o o' c ρ hc, eval_noSelf E en o o' t ρ ht, eval_noSelf E en o o' e ρ he]
  | .empty, _, _ => rfl
  | .caseE k ps bs, ρ, ⟨hk, hbs⟩ => by
      simp only [Expr.eval]
      rw [eval_noSelf E en o o' k ρ hk]
      exact Multiset.bind_congr fun w _ => evalArms_noSelf E en o o' w ps bs ρ hbs
  | .matchE src p t, ρ, ⟨hs, ht⟩ => by
      simp only [Expr.eval]
      rw [eval_noSelf E en o o' src ρ hs]
      refine Multiset.bind_congr fun sp _ => Multiset.bind_congr fun row _ => ?_
      split
      · next ρ' _ => exact eval_noSelf E en o o' t ρ' ht
      · rfl

/-- The list version. -/
theorem evalAll_noSelf (E : Env) (en : String → List Atom → Multiset Atom) (o o' : List Atom → Multiset Atom) :
    ∀ (es : List Expr) (ρ : List (String × Atom)), NoSelfAll es →
      Expr.evalAll E ⟨o, en⟩ ρ es = Expr.evalAll E ⟨o', en⟩ ρ es
  | [], _, _ => rfl
  | e :: es, ρ, ⟨he, hes⟩ => by
      simp only [Expr.evalAll]
      rw [eval_noSelf E en o o' e ρ he, evalAll_noSelf E en o o' es ρ hes]

/-- The arms of a `case`. -/
theorem evalArms_noSelf (E : Env) (en : String → List Atom → Multiset Atom) (o o' : List Atom → Multiset Atom)
    (w : Atom) : ∀ (ps : List Pat) (bs : List Expr) (ρ : List (String × Atom)), NoSelfAll bs →
      Expr.evalArms E ⟨o, en⟩ ρ w ps bs = Expr.evalArms E ⟨o', en⟩ ρ w ps bs
  | p :: ps, b :: bs, ρ, ⟨hb, hbs⟩ => by
      simp only [Expr.evalArms]
      split
      · next ρ' _ => exact eval_noSelf E en o o' b ρ' hb
      · exact evalArms_noSelf E en o o' w ps bs ρ hbs
  | [], _, _, _ => by simp [Expr.evalArms]
  | _ :: _, [], _, _ => by simp [Expr.evalArms]
end

/-- **Calls to itself in tail positions only** (`scan->tail`): the body is tail;
the branches of an `if`, the body of a `let` and the arms of a `case` inherit
it; a condition, a bound value, a key, arguments, `match` and data are not
tail. -/
inductive Tail : Expr → Prop
  | plain {e : Expr} : NoSelf e → Tail e
  | self {args : List Expr} : NoSelfAll args → Tail (.self args)
  | letE {p : Pat} {v b : Expr} : NoSelf v → Tail b → Tail (.letE p v b)
  | ifE {c t e : Expr} : NoSelf c → Tail t → Tail e → Tail (.ifE c t e)
  | caseE {k : Expr} {ps : List Pat} {bs : List Expr} : NoSelf k → (∀ b ∈ bs, Tail b) →
      Tail (.caseE k ps bs)

/-- The decomposition a tail expression's values have: values that do not read
the calls to itself, and the answers of calls to itself at argument lists that
meet the entry facts. -/
def TailDecomp (Γ : Decls) (grounded : String → Bool) (As : List (Ty Empty)) (E : Env)
    (en : String → List Atom → Multiset Atom) (ρ : List (String × Atom)) (e : Expr) : Prop :=
  ∃ (A : Multiset Atom) (C : Multiset (List Atom)), (∀ ws ∈ C, EntryFacts Γ grounded As ws) ∧
    ∀ o, e.eval E ⟨o, en⟩ ρ = A + C.bind o

theorem tailDecomp_bind {α : Type} {As : List (Ty Empty)} (V : Multiset α)
    (f : (List Atom → Multiset Atom) → α → Multiset Atom)
    (hf : ∀ w ∈ V, ∃ (A : Multiset Atom) (C : Multiset (List Atom)),
      (∀ ws ∈ C, EntryFacts Γ grounded As ws) ∧ ∀ o, f o w = A + C.bind o) :
    ∃ (A : Multiset Atom) (C : Multiset (List Atom)), (∀ ws ∈ C, EntryFacts Γ grounded As ws) ∧
      ∀ o, V.bind (f o) = A + C.bind o := by
  classical
  choose! A C hC hAC using hf
  refine ⟨V.bind A, V.bind C, fun ws hws => ?_, fun o => ?_⟩
  · obtain ⟨w, hw, hws⟩ := Multiset.mem_bind.mp hws
    exact hC w hw ws hws
  · rw [Multiset.bind_congr fun w hw => hAC w hw o, Multiset.bind_add, Multiset.bind_assoc]

variable {Φ : String → Ty Empty → Prop} {R : Ty Empty} {As : List (Ty Empty)} {E : Env}

theorem tail_decomp (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E) {en : String → List Atom → Multiset Atom}
    (enRes : ∀ f ws, EntryFacts Γ grounded (ent f) ws → ∀ r ∈ en f ws, Holds Γ grounded r (res f)) :
    ∀ {e : Expr}, Tail e → ∀ ρ, MeetsFacts Γ grounded Φ ρ → CallsOK Γ res ent Φ R (As.map Ty.lift) e →
      TailDecomp Γ grounded As E en ρ e
  | _, .plain h, ρ, _, _ =>
      ⟨_, 0, by simp, fun o => by rw [Multiset.zero_bind, add_zero]; exact eval_noSelf E en o (fun _ => 0) _ ρ h⟩
  | .self args, .self h, ρ, facts, hc => by
      cases hc with
      | self hargs typed =>
          refine ⟨0, Expr.evalAll E ⟨fun _ => 0, en⟩ ρ args, fun ws hws => ?_, fun o => ?_⟩
          · have each := Expr.evalAll_mem E ⟨fun _ => 0, en⟩ ρ args ws hws
            have typed' : List.Forall₂ (fun A e => demand A.lift = .guarded → HasType Γ res Φ R e A)
                As args := by
              refine (List.forall₂_map_left_iff.mp typed).imp fun A e hA hg => ?_
              obtain ⟨τ, hτ⟩ := hA hg
              rwa [Ty.lift_bind_ground] at hτ
            exact forall₂_compose typed' each fun A e w he hA hw hg => List.forall_iff_forall_mem.mp
              (evalAll_sound hΓ hE (O := ⟨fun _ => 0, en⟩) ⟨fun _ _ r hr => absurd hr (Multiset.notMem_zero r),
                enRes⟩ args ρ facts) e he A (hA hg) (hargs e he) w hw
          · simp only [Expr.eval, zero_add]
            rw [evalAll_noSelf E en o (fun _ => 0) args ρ h]
  | .letE p v b, .letE hv hb, ρ, facts, hc => by
      cases hc with
      | letE _ hcb =>
          refine (tailDecomp_bind (Γ := Γ) (grounded := grounded) (Expr.eval E ⟨fun _ => 0, en⟩ ρ v)
            (fun o w => match Pat.matchUnder ρ p w with
              | some ρ' => Expr.eval E ⟨o, en⟩ ρ' b
              | none => 0) fun w _ => ?_).imp fun A ⟨C, hC, h⟩ => ⟨C, hC, fun o => ?_⟩
          · split
            · next ρ' hm =>
                exact tail_decomp hΓ hE enRes hb ρ' (facts.extend fun x w hx => Pat.matchUnder_lookup hm hx) hcb
            · exact ⟨0, 0, by simp, fun o => by simp⟩
          · rw [← h o]
            simp only [Expr.eval]
            rw [eval_noSelf E en o (fun _ => 0) v ρ hv]
  | .ifE c t e, .ifE hc' ht he, ρ, facts, hc => by
      cases hc with
      | ifE _ hct hce =>
          refine (tailDecomp_bind (Γ := Γ) (grounded := grounded) (Expr.eval E ⟨fun _ => 0, en⟩ ρ c)
            (fun o w => if w = truth then Expr.eval E ⟨o, en⟩ ρ t else Expr.eval E ⟨o, en⟩ ρ e) fun w _ => ?_).imp
            fun A ⟨C, hC, h⟩ => ⟨C, hC, fun o => ?_⟩
          · by_cases hw : w = truth
            · obtain ⟨A, C, hC, h⟩ := tail_decomp hΓ hE enRes ht ρ facts hct
              exact ⟨A, C, hC, fun o => by rw [if_pos hw]; exact h o⟩
            · obtain ⟨A, C, hC, h⟩ := tail_decomp hΓ hE enRes he ρ facts hce
              exact ⟨A, C, hC, fun o => by rw [if_neg hw]; exact h o⟩
          · rw [← h o]
            simp only [Expr.eval]
            rw [eval_noSelf E en o (fun _ => 0) c ρ hc']
  | .caseE k ps bs, .caseE hk hbs, ρ, facts, hc => by
      cases hc with
      | caseE _ hcbs =>
          refine (tailDecomp_bind (Γ := Γ) (grounded := grounded) (Expr.eval E ⟨fun _ => 0, en⟩ ρ k)
            (fun o w => Expr.evalArms E ⟨o, en⟩ ρ w ps bs) fun w _ => ?_).imp
            fun A ⟨C, hC, h⟩ => ⟨C, hC, fun o => ?_⟩
          · exact tail_arms hΓ hE enRes w ps bs ρ facts hbs hcbs
          · rw [← h o]
            simp only [Expr.eval]
            rw [eval_noSelf E en o (fun _ => 0) k ρ hk]
where
  tail_arms (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E) {en : String → List Atom → Multiset Atom}
      (enRes : ∀ f ws, EntryFacts Γ grounded (ent f) ws → ∀ r ∈ en f ws, Holds Γ grounded r (res f))
      (w : Atom) : ∀ (ps : List Pat) (bs : List Expr) (ρ : List (String × Atom)), MeetsFacts Γ grounded Φ ρ →
        (∀ b ∈ bs, Tail b) → (∀ b ∈ bs, CallsOK Γ res ent Φ R (As.map Ty.lift) b) →
        ∃ (A : Multiset Atom) (C : Multiset (List Atom)), (∀ ws ∈ C, EntryFacts Γ grounded As ws) ∧
          ∀ o, Expr.evalArms E ⟨o, en⟩ ρ w ps bs = A + C.bind o
    | p :: ps, b :: bs, ρ, facts, hbs, hcbs => by
        cases hm : Pat.matchUnder ρ p w with
        | some ρ' =>
            obtain ⟨A, C, hC, h⟩ := tail_decomp hΓ hE enRes (hbs b (by simp)) ρ'
              (facts.extend fun x w hx => Pat.matchUnder_lookup hm hx) (hcbs b (by simp))
            exact ⟨A, C, hC, fun o => by simp only [Expr.evalArms, hm]; exact h o⟩
        | none =>
            obtain ⟨A, C, hC, h⟩ := tail_arms hΓ hE enRes w ps bs ρ facts
              (fun b' hb' => hbs b' (by simp [hb'])) (fun b' hb' => hcbs b' (by simp [hb']))
            exact ⟨A, C, hC, fun o => by simp only [Expr.evalArms, hm]; exact h o⟩
    | [], _, _, _, _, _ => ⟨0, 0, by simp, fun o => by simp [Expr.evalArms]⟩
    | _ :: _, [], _, _, _, _ => ⟨0, 0, by simp, fun o => by simp [Expr.evalArms]⟩

/-- **Tail equations give tail bodies**: equations with linear head patterns whose
right-hand sides call themselves in tail positions only (`Tail`), at arguments
meeting the formals (`CallsOK`), have the decomposition the tail version theorem
reads; no range is proved. -/
theorem tailBodies_of_tail (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E)
    {en : String → List Atom → Multiset Atom}
    (enRes : ∀ f ws, EntryFacts Γ grounded (ent f) ws → ∀ r ∈ en f ws, Holds Γ grounded r (res f))
    {eqs : List Equation}
    (tail : ∀ eq ∈ eqs, (Pat.varsAll eq.pats).Nodup ∧ Tail eq.rhs ∧
      CallsOK Γ res ent (eqFacts Γ As eq) R (As.map Ty.lift) eq.rhs) :
    TailBodies Γ grounded As (fun o => equationsBody E eqs ⟨o, en⟩) (fun o => equationsBody E eqs ⟨o, en⟩) := by
  intro vs hvs
  obtain ⟨A, C, hC, h⟩ := tailDecomp_bind (Γ := Γ) (grounded := grounded) (As := As)
    (eqs : Multiset Equation) (fun o eq => match Pat.matchAll eq.pats vs with
      | some ρ => eq.rhs.eval E ⟨o, en⟩ ρ
      | none => 0) fun eq heq => by
    obtain ⟨linear, htail, hcalls⟩ := tail eq heq
    split
    · next ρ hm =>
        exact tail_decomp (Φ := eqFacts Γ As eq) (R := R) hΓ hE enRes htail ρ
          (eqFacts_sound hΓ linear hm hvs) hcalls
    · exact ⟨0, 0, by simp, fun o => by simp⟩
  exact ⟨A, C, hC, h, h⟩

/-- **The version of tail equations is their protocol followed by one range
check**, at every fuel, on arguments meeting the entry facts. -/
theorem tail_accepted_version_eq_protocol (hΓ : Functional Γ) (hE : EnvOK Γ grounded res E)
    {en : String → List Atom → Multiset Atom}
    (enRes : ∀ f ws, EntryFacts Γ grounded (ent f) ws → ∀ r ∈ en f ws, Holds Γ grounded r (res f))
    {eqs : List Equation} (rg : ResultGuarded R.lift)
    (tail : ∀ eq ∈ eqs, (Pat.varsAll eq.pats).Nodup ∧ Tail eq.rhs ∧
      CallsOK Γ res ent (eqFacts Γ As eq) R (As.map Ty.lift) eq.rhs)
    (n : ℕ) (vs : List Atom) (hvs : EntryFacts Γ grounded As vs) :
    protocolRun Γ grounded (fun o => equationsBody E eqs ⟨o, en⟩) (arrow (As.map Ty.lift) R.lift) n vs =
      rangeCheck Γ grounded R (versionRun (fun o => equationsBody E eqs ⟨o, en⟩) n vs) :=
  tail_version_eq_protocol hΓ rg (tailBodies_of_tail hΓ hE enRes tail) n vs hvs

end Soundness

/-! ## Structural parameters checked where another head calls -/

section Structural

variable (Γ : Decls) (grounded : String → Bool)

/-- **A structural formal** (`PREPARED_PURE_VALUE_STRUCTURAL`): a closed type that
is neither a value class nor a metatype name, as `Tree` or `(List Number)`. -/
def StructuralTy (A : Ty Empty) : Prop :=
  ¬ MetaName A ∧ ∀ c, A = .sym c → ¬ IsValueClass c

/-- **The machine's checks of a call from outside the head**
(`prepared_pure_typed_arguments_accepted`, `prepared_pure_structural_arguments_accepted`):
at a value class the argument is a value of that class; at a structural formal the
type service's bound query answers the formal exactly once
(`eval_petta_value_typed_once`); at `%Undefined%` or `_` nothing. -/
def MachineAccepts (As : List (Ty Empty)) (vs : List Atom) : Prop :=
  List.Forall₂ (fun A v => (∃ c, A = .sym c ∧ IsValueClass c ∧ Literal c v) ∨
    (StructuralTy A ∧ count (info Γ v) A = 1) ∨ Unchecked (A.lift : Ty String)) As vs

variable {Γ grounded}

/-- A type `get-type` never checks is not guarded. -/
theorem demand_of_unchecked {A : Ty String} (h : Unchecked A) : demand A = .unchecked := by
  unfold demand
  rw [if_neg, if_pos h]
  rintro rfl
  exact h.elim (fun e => absurd e (by decide)) fun e => absurd e (by decide)

/-- **The machine's checks give the entry facts.** -/
theorem MachineAccepts.entryFacts {As : List (Ty Empty)} {vs : List Atom}
    (h : MachineAccepts Γ As vs) : EntryFacts Γ grounded As vs :=
  h.imp fun A v hv hg => by
    rcases hv with ⟨c, rfl, -, hc⟩ | ⟨-, hcount⟩ | hu
    · exact holds_literal hc
    · exact Holds.of_count hcount
    · exact absurd (hg.symm.trans (demand_of_unchecked hu)) (by decide)

variable (Γ grounded) in
open Classical in
/-- **The machine's run of a call from outside the head**: where its checks pass,
the version, whose calls to itself skip the protocol and whose result is not
checked; where they fail, the canonical evaluator's protocol. -/
noncomputable def structuralRun (bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom)
    (As : List (Ty Empty)) (R : Ty Empty) (n : ℕ) (vs : List Atom) : Multiset Atom :=
  if MachineAccepts Γ As vs then versionRun bodyV n vs
  else protocolRun Γ grounded bodyP (arrow (As.map Ty.lift) R.lift) n vs

/-- **Structural parameters checked where another head calls**
(`PREPARED_PURE_VALUE_STRUCTURAL`, `eval_petta_structural_version`): for a head with a
trusted version, every call from outside the head, from the evaluator or from
another head's body, has at every fuel exactly the answers of the head's
protocol, every call running its protocol. A call the machine accepts meets the
entry facts, so its version, calls to itself unchecked, is the protocol, and the
range the version proves needs no check; a call it declines runs the protocol. -/
theorem structuralRun_eq_protocol
    {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty Empty)} {R : Ty Empty} (h : VersionHyps (Γ := Γ) (grounded := grounded) bodyP bodyV As R)
    (n : ℕ) (vs : List Atom) :
    structuralRun Γ grounded bodyP bodyV As R n vs =
      protocolRun Γ grounded bodyP (arrow (As.map Ty.lift) R.lift) n vs := by
  unfold structuralRun
  split_ifs with hacc
  · exact (version_eq_protocol h n vs hacc.entryFacts).symm
  · rfl

/-- **Another head reading this one through the machine reads the protocol**: as
an oracle, the machine's calls are the protocol's, so a caller's equations have
the same answers through either (mutual recursion goes through such calls). -/
theorem structuralRun_oracle
    {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty Empty)} {R : Ty Empty} (h : VersionHyps (Γ := Γ) (grounded := grounded) bodyP bodyV As R)
    (n : ℕ) : structuralRun Γ grounded bodyP bodyV As R n =
      protocolRun Γ grounded bodyP (arrow (As.map Ty.lift) R.lift) n :=
  funext (structuralRun_eq_protocol h n)

end Structural

/-! ## Controls -/

namespace Controls

open TypedCalls.Controls (decls decls_functional sym num str app listOf listNumber consRow
  cons_row cons_constructor)

/-- Subtraction where it does not raise. -/
def minus : Atom → Atom → Multiset Atom
  | .grounded (.int m), .grounded (.int n) => {.grounded (.int (m - n))}
  | _, _ => 0

/-- `>` on numbers. -/
def greater : Atom → Atom → Multiset Atom
  | .grounded (.int m), .grounded (.int n) => {.grounded (.bool (decide (n < m)))}
  | _, _ => 0

/-- `==` on numbers. -/
def numEq : Atom → Atom → Multiset Atom
  | .grounded (.int m), .grounded (.int n) => {.grounded (.bool (decide (m = n)))}
  | _, _ => 0

/-- The operations PeTTa provides that the controls use: `+`, `-`, `>` and `==` on
numbers; on other values they answer nothing here. -/
def ops (op : String) : List Atom → Multiset Atom
  | [a, b] => if op = "+" then plus a b else if op = "-" then minus a b
      else if op = ">" then greater a b else if op = "==" then numEq a b else 0
  | _ => 0

/-- The controls' environment: no kept calls, no spaces. -/
def env : Env := ⟨ops, fun _ _ => 0, fun _ => 0⟩

theorem ops_mem {op : String} {vs : List Atom} {r : Atom} (h : r ∈ ops op vs) :
    ∃ a b, vs = [a, b] ∧ ((op = "+" ∧ r ∈ plus a b) ∨ (op = "-" ∧ r ∈ minus a b) ∨
      (op = ">" ∧ r ∈ greater a b) ∨ (op = "==" ∧ r ∈ numEq a b)) := by
  match vs, h with
  | [a, b], h =>
      refine ⟨a, b, rfl, ?_⟩
      simp only [ops] at h
      split_ifs at h with h₁ h₂ h₃ h₄
      · exact .inl ⟨h₁, h⟩
      · exact .inr (.inl ⟨h₂, h⟩)
      · exact .inr (.inr (.inl ⟨h₃, h⟩))
      · exact .inr (.inr (.inr ⟨h₄, h⟩))
      · exact absurd h (Multiset.notMem_zero r)
  | [], h => simp [ops] at h
  | [_], h => simp [ops] at h
  | _ :: _ :: _ :: _, h => simp [ops] at h

theorem plus_literal {a b r : Atom} (h : r ∈ plus a b) : Literal "Number" r := by
  unfold plus at h
  split at h
  · rw [Multiset.mem_singleton] at h
    subst h
    rfl
  · exact absurd h (Multiset.notMem_zero r)

theorem minus_literal {a b r : Atom} (h : r ∈ minus a b) : Literal "Number" r := by
  unfold minus at h
  split at h
  · rw [Multiset.mem_singleton] at h
    subst h
    rfl
  · exact absurd h (Multiset.notMem_zero r)

theorem greater_literal {a b r : Atom} (h : r ∈ greater a b) : Literal "Bool" r := by
  unfold greater at h
  split at h
  · rw [Multiset.mem_singleton] at h
    subst h
    rfl
  · exact absurd h (Multiset.notMem_zero r)

theorem numEq_literal {a b r : Atom} (h : r ∈ numEq a b) : Literal "Bool" r := by
  unfold numEq at h
  split at h
  · rw [Multiset.mem_singleton] at h
    subst h
    rfl
  · exact absurd h (Multiset.notMem_zero r)

/-- The controls' environment meets the analysis's assumptions, under any
declarations: its operations answer their classes, and it keeps no call. -/
theorem env_ok {Γ : Decls} (grounded : String → Bool) (res : String → Ty Empty) :
    EnvOK Γ grounded res env where
  prim op vs c hc r hr := by
    obtain ⟨a, b, rfl, h⟩ := ops_mem (show r ∈ ops op vs from hr)
    rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · simp only [primClass, List.length, Option.some.injEq] at hc
      exact hc ▸ plus_literal h
    · simp only [primClass, List.length, Option.some.injEq] at hc
      exact hc ▸ minus_literal h
    · simp only [primClass, List.length, Option.some.injEq] at hc
      exact hc ▸ greater_literal h
    · simp only [primClass, List.length, Option.some.injEq] at hc
      exact hc ▸ numEq_literal h
  kept _ _ r hr := absurd hr (Multiset.notMem_zero r)

/-- No callees. -/
def noRes : String → Ty Empty := fun _ => .sym "Number"

/-- No callees' entry facts. -/
def noEnt : String → List (Ty Empty) := fun _ => []

/-- The oracle of no callee. -/
def noCallee : String → List Atom → Multiset Atom := fun _ _ => 0

/-- `(= (lsum Nil) 0)` and `(= (lsum (Cons $x $xs)) (+ $x (lsum $xs)))`. -/
def lsumEqs : List Equation :=
  [⟨[.const (sym "Nil")], .const (num 0)⟩,
   ⟨[.ctor "Cons" [.var "x", .var "xs"]], .prim "+" [.var "x", .self [.var "xs"]]⟩]

/-- The fact the fold reads for `$xs` from `(Cons $x $xs)` at `(List Number)`. -/
theorem xs_fact : PatFact decls (.ctor "Cons" [.var "x", .var "xs"]) listNumber "xs" listNumber := by
  have inst : ((listOf (Ty.var "a") : Ty String).bind fun _ => Ty.sym "Number") = listNumber := by
    simp [listOf, listNumber]
  refine PatFact.ctor (σ := fun _ => .sym "Number") (B := listOf (.var "a")) (p := .var "xs")
    cons_row cons_constructor rfl (by simp [MetaName, listNumber, listOf])
    (by simp [Named, listNumber, listOf]) inst (by simp) (by simp [FreeField, listOf]) ?_
  rw [inst]
  exact PatFact.var _ _

/-- **The fold `lsum` is accepted**: `$xs` is a `(List Number)`, so the call to
itself meets the formal, and the result, an addition, is a `Number`. -/
theorem lsum_accepted (res : String → Ty Empty) (ent : String → List (Ty Empty)) :
    ∀ eq ∈ lsumEqs, Accepted decls res ent [listNumber] (.sym "Number") eq := by
  intro eq heq
  simp only [lsumEqs, List.mem_cons, List.not_mem_nil, or_false] at heq
  rcases heq with rfl | rfl
  · exact ⟨by simp [Pat.varsAll, Pat.vars], rfl, .const, .const (count_int decls 0)⟩
  · refine ⟨by simp [Pat.varsAll, Pat.vars], rfl, .prim fun e he => ?_, .prim rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact .var
    · refine CallsOK.selfClosed (fun e he => by
        rw [List.mem_singleton] at he
        subst he
        exact .var) (.cons ?_ .nil)
      exact .var ⟨listNumber, .ctor "Cons" [.var "x", .var "xs"], by simp, by decide, xs_fact⟩

theorem number_guarded : ResultGuarded ((Ty.sym "Number" : Ty Empty).lift) := by
  simp [ResultGuarded, Ty.lift, Unchecked]

/-- `lsum`'s equations under the controls' environment, with no callee. -/
abbrev lsumBody : (List Atom → Multiset Atom) → List Atom → Multiset Atom :=
  fun o => equationsBody env lsumEqs ⟨o, noCallee⟩

/-- **The version of `lsum` is its protocol**, at every fuel, on every list that
meets the entry fact. -/
theorem lsum_version (grounded : String → Bool) (n : ℕ) (vs : List Atom)
    (hvs : EntryFacts decls grounded [listNumber] vs) :
    protocolRun decls grounded lsumBody (arrow ([listNumber].map Ty.lift)
        (Ty.sym "Number" : Ty Empty).lift) n vs =
      versionRun lsumBody n vs :=
  accepted_version_eq_protocol (res := noRes) (ent := noEnt) decls_functional number_guarded
    (lsum_accepted _ _) (env_ok grounded noRes) noCallee noCallee (fun _ _ _ => rfl)
    (fun _ _ _ r hr => absurd hr (Multiset.notMem_zero r)) n vs hvs

/-- **At a metatype name the analysis inverts nothing**: `(C $s)` at
`Expression` gives `$s` no fact (`contract_metatype_name`). -/
theorem no_fact_at_metatype (U : Ty Empty) :
    ¬ PatFact decls (.ctor "C" [.var "s"]) (.sym "Expression") "s" U := by
  intro h
  cases h with
  | ctor _ _ _ notMeta => exact notMeta (by simp [MetaName])

/-- **A field declared `%Undefined%` gives its pattern no fact**: `(UBox $x)` at
`Boxed` gives `$x` nothing (`contract_field_free`), though `(UBox v)` is a
`Boxed` for every `v` (`TypedCalls.Controls.unchecked_field_any`). -/
theorem no_fact_at_unchecked_field (U : Ty Empty) :
    ¬ PatFact decls (.ctor "UBox" [.var "x"]) (.sym "Boxed") "x" U := by
  intro h
  cases h with
  | ctor row _ _ _ _ _ field fixed _ =>
      rw [TypedCalls.Controls.ubox_row, List.cons.injEq] at row
      obtain ⟨hBs, -⟩ := arrow_inj row.1
      subst hBs
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton, Prod.mk.injEq] at field
      obtain ⟨rfl, -⟩ := field
      exact fixed (by simp [FreeField])

/-- The fold's version answers `5` once for `(Cons 5 Nil)`. -/
theorem lsum_five_version : versionRun lsumBody 2 [app "Cons" [num 5, sym "Nil"]] = {num 5} := by
  decide

/-- The fold's equations at `Nil`: `0`. -/
theorem lsum_body_nil (o : List Atom → Multiset Atom) : lsumBody o [sym "Nil"] = {num 0} := by
  unfold lsumBody equationsBody
  rw [show ((lsumEqs : List Equation) : Multiset Equation) =
    (⟨[.const (sym "Nil")], .const (num 0)⟩ : Equation) ::ₘ
      (⟨[.ctor "Cons" [.var "x", .var "xs"]], .prim "+" [.var "x", .self [.var "xs"]]⟩ : Equation) ::ₘ 0
    from rfl, Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
  have m1 : Pat.matchAll [.const (sym "Nil")] [sym "Nil"] = some [] := by decide
  have m2 : Pat.matchAll [.ctor "Cons" [.var "x", .var "xs"]] [sym "Nil"] = none := by decide
  simp only [m1, m2, Expr.eval, add_zero]

/-- The fold's equations at a cell: the head added to each answer for the rest. -/
theorem lsum_body_cons (o : List Atom → Multiset Atom) (n : ℤ) (rest : Atom) :
    lsumBody o [app "Cons" [num n, rest]] = (o [rest]).bind (plus (num n)) := by
  unfold lsumBody equationsBody
  rw [show ((lsumEqs : List Equation) : Multiset Equation) =
    (⟨[.const (sym "Nil")], .const (num 0)⟩ : Equation) ::ₘ
      (⟨[.ctor "Cons" [.var "x", .var "xs"]], .prim "+" [.var "x", .self [.var "xs"]]⟩ : Equation) ::ₘ 0
    from rfl, Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
  have m1 : Pat.matchAll [.const (sym "Nil")] [app "Cons" [num n, rest]] = none := by
    simp [Pat.matchAll, Pat.match]
  have m2 : Pat.matchAll [.ctor "Cons" [.var "x", .var "xs"]] [app "Cons" [num n, rest]] =
      some [("x", num n), ("xs", rest)] := by
    simp [Pat.matchAll, Pat.match]
  have lx : List.lookup "x" [("x", num n), ("xs", rest)] = some (num n) := rfl
  have lxs : List.lookup "xs" [("x", num n), ("xs", rest)] = some rest := rfl
  simp only [m1, m2, zero_add, Expr.eval, Expr.evalAll, lx, lxs, Multiset.singleton_bind,
    Multiset.map_singleton, Multiset.bind_map, Multiset.bind_assoc]
  exact Multiset.bind_congr fun x _ => by simp [env, ops]

/-- **The functional precondition is necessary.** Read as SWI-PeTTa's `get-type`
reads repeated rows, `Cons` declared twice types `(Cons 5 Nil)` twice at
`(List Number)`, so the protocol answers `5` twice where the version answers it
once. -/
theorem repeated_rows_break_version (grounded : String → Bool) :
    protocolRun (decls.addRow "Cons" consRow) grounded lsumBody
        (arrow ([listNumber].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift) 2
        [app "Cons" [num 5, sym "Nil"]] = {num 5, num 5} ∧
      versionRun lsumBody 2 [app "Cons" [num 5, sym "Nil"]] = {num 5} := by
  refine ⟨?_, lsum_five_version⟩
  have nilInfo : info (decls.addRow "Cons" consRow) (sym "Nil") = info decls (sym "Nil") := by
    rw [info_symbol, info_symbol]
    simp [Decls.addRow]
  have countNil : count (info (decls.addRow "Cons" consRow) (sym "Nil")) listNumber = 1 := by
    rw [nilInfo]
    exact TypedCalls.Controls.count_nil _
  have countFive :
      count (info (decls.addRow "Cons" consRow) (app "Cons" [num 5, sym "Nil"])) listNumber = 2 :=
    TypedCalls.Controls.repeated_rows_twice.1
  have notMetaList : ¬ MetaName listNumber := by simp [MetaName, listNumber, listOf]
  have guardedList : demand ((listNumber : Ty Empty).lift) = .guarded := by
    simp [demand, listNumber, listOf, Ty.lift, Unchecked]
  have notMetaNumber : ¬ MetaName (Ty.sym "Number") := by simp [MetaName]
  -- the call to itself at `Nil`
  have inner : protocolRun (decls.addRow "Cons" consRow) grounded lsumBody
      (arrow ([listNumber].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift) 1 [sym "Nil"] =
      {num 0} := by
    simp only [protocolRun]
    rw [chainCall_closed]
    simp only [if_pos number_guarded]
    have argNil : argCount (decls.addRow "Cons" consRow) (metatype grounded) [listNumber]
        [sym "Nil"] = 1 := by
      simp only [argCount, guardedList, if_true, mul_one]
      rw [guardCount_of_not_meta notMetaList, countNil]
    rw [argNil, one_nsmul, lsum_body_nil, Multiset.singleton_bind,
      guardCount_of_not_meta notMetaNumber, count_int, one_nsmul]
  simp only [protocolRun]
  rw [chainCall_closed]
  simp only [if_pos number_guarded]
  have argFive : argCount (decls.addRow "Cons" consRow) (metatype grounded) [listNumber]
      [app "Cons" [num 5, sym "Nil"]] = 2 := by
    simp only [argCount, guardedList, if_true, mul_one]
    rw [guardCount_of_not_meta notMetaList, countFive]
  rw [argFive, lsum_body_cons]
  simp only [protocolRun] at inner
  rw [inner, Multiset.singleton_bind]
  simp only [plus, Multiset.singleton_bind]
  rw [guardCount_of_not_meta notMetaNumber, count_int, one_nsmul]
  rfl

/-- **`lsum`'s checked call meets its result check**: entering the version at
`(Cons 5 Nil)`, the call answers the version's `5`, once. -/
theorem lsum_range_met (grounded : String → Bool) :
    chainCall decls (metatype grounded) (lsumBody (versionRun lsumBody 2))
        (arrow ([listNumber].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift)
        [app "Cons" [num 5, sym "Nil"]] = {num 5} := by
  rw [checked_call_version (accepted_versionHyps (res := noRes) (ent := noEnt) decls_functional
    number_guarded (lsum_accepted _ _) (env_ok grounded noRes) noCallee noCallee (fun _ _ _ => rfl)
    (fun _ _ _ r hr => absurd hr (Multiset.notMem_zero r))) 2 _
    (.cons (fun _ => Holds.of_count TypedCalls.Controls.cons_five_typed) .nil)]
  show versionRun lsumBody 3 [app "Cons" [num 5, sym "Nil"]] = {num 5}
  decide

/-- **Meeting the result check needs the version's proof**: a body answering
`"a"` at the range `Number`, which no version proves, has no answer through the
call's result guard. -/
theorem unproven_range_not_met (grounded : String → Bool) :
    chainCall decls (metatype grounded) (fun _ => {str "a"})
        (arrow (([] : List (Ty Empty)).map Ty.lift) (Ty.sym "Number" : Ty Empty).lift) [] = 0 := by
  have notMeta : ¬ MetaName (Ty.sym "Number") := by simp [MetaName]
  rw [chainCall_closed]
  simp only [argCount, one_nsmul, if_pos number_guarded, Multiset.singleton_bind]
  rw [guardCount_of_not_meta notMeta, count_class decls (g := .string "a") rfl]
  decide

/-! ### Symbols with closed declared types -/

/-- `(-> Number Number)`. -/
abbrev numArrow : Ty Empty := arrow [.sym "Number"] (.sym "Number")

/-- **A symbol keeps its closed declared type, an arrow included**
(`contract_eval` on a symbol): `inc`, declared `(-> Number Number)`, is typed once
at that type, so as a constant it has the fact, and a guard at the same closed
formal passes once. -/
theorem constant_closed_arrow (grounded : String → Bool) (res : String → Ty Empty)
    (Φ : String → Ty Empty → Prop) (R : Ty Empty) :
    HasType decls res Φ R (.const (sym "inc")) numArrow ∧
      argCount decls (metatype grounded) [numArrow] [sym "inc"] = 1 := by
  have count1 : count (info decls (sym "inc")) numArrow = 1 := by
    rw [count_symbol_closed decls "inc" numArrow (by simp [decls]; rfl), if_pos rfl]
  have notMeta : ¬ MetaName numArrow := by simp [MetaName, numArrow, arrow]
  have guarded : demand (numArrow.lift : Ty String) = .guarded := by decide
  refine ⟨.const count1, ?_⟩
  simp only [argCount, guarded, if_true, mul_one]
  rw [guardCount_of_not_meta notMeta, count1]

/-- **A closed symbol type that differs from the formal gives no fact**: `dblS`,
declared `(-> String String)`, is not typed at `(-> Number Number)`, so the
analysis cannot pass it there, and the protocol's guard there fails: a call
answers nothing. -/
theorem constant_other_arrow (grounded : String → Bool) (res : String → Ty Empty)
    (Φ : String → Ty Empty → Prop) (R : Ty Empty) :
    ¬ HasType decls res Φ R (.const (sym "dblS")) numArrow ∧
      argCount decls (metatype grounded) [numArrow] [sym "dblS"] = 0 := by
  have count0 : count (info decls (sym "dblS")) numArrow = 0 := by
    rw [count_symbol_closed decls "dblS" (arrow [.sym "String"] (.sym "String")) (by simp [decls]; rfl),
      if_neg (by simp [numArrow, arrow])]
  have notMeta : ¬ MetaName numArrow := by simp [MetaName, numArrow, arrow]
  have guarded : demand (numArrow.lift : Ty String) = .guarded := by decide
  refine ⟨fun h => ?_, ?_⟩
  · cases h with
    | const hc => rw [count0] at hc; cases hc
  · simp only [argCount, guarded, if_true, mul_one]
    rw [guardCount_of_not_meta notMeta, count0]

/-! ### Versions whose range is checked at the entry -/

/-- `(= (cs 0) b)` and `(= (cs $k) (cs (- $k 1)))` for `(: cs (-> Number Number))`: the
call to itself is in a tail position. -/
def tailBody (b : Atom) (o : List Atom → Multiset Atom) : List Atom → Multiset Atom
  | [.grounded (.int k)] => if k = 0 then {b} else o [.grounded (.int (k - 1))]
  | _ => 0

/-- `(let $r (nt (- $k 1)) 5)` in place of the tail call: the call's answers are used. -/
def usedBody (o : List Atom → Multiset Atom) : List Atom → Multiset Atom
  | [.grounded (.int k)] => if k = 0 then {str "s"} else (o [.grounded (.int (k - 1))]).bind fun _ => {num 5}
  | _ => 0

theorem tailBodies_cs (grounded : String → Bool) (b : Atom) :
    TailBodies decls grounded [.sym "Number"] (tailBody b) (tailBody b) := by
  intro vs hvs
  match vs with
  | [.grounded (.int k)] =>
      by_cases hk : k = 0
      · exact ⟨{b}, 0, by simp, fun o => by simp [tailBody, hk], fun o => by simp [tailBody, hk]⟩
      · refine ⟨0, {[.grounded (.int (k - 1))]}, fun ws hws => ?_, fun o => by simp [tailBody, hk],
          fun o => by simp [tailBody, hk]⟩
        rw [Multiset.mem_singleton] at hws
        subst hws
        exact .cons (fun _ => Holds.of_count (count_int decls _)) .nil
  | [] => exact ⟨0, 0, by simp, fun o => rfl, fun o => rfl⟩
  | [.symbol _] => exact ⟨0, 0, by simp, fun o => rfl, fun o => rfl⟩
  | [.var _] => exact ⟨0, 0, by simp, fun o => rfl, fun o => rfl⟩
  | [.expression _] => exact ⟨0, 0, by simp, fun o => rfl, fun o => rfl⟩
  | [.grounded (.string _)] => exact ⟨0, 0, by simp, fun o => rfl, fun o => rfl⟩
  | [.grounded (.bool _)] => exact ⟨0, 0, by simp, fun o => rfl, fun o => rfl⟩
  | [.grounded (.custom _ _)] => exact ⟨0, 0, by simp, fun o => rfl, fun o => rfl⟩
  | _ :: _ :: _ => exact ⟨0, 0, by simp, fun o => by simp [tailBody], fun o => by simp [tailBody]⟩

theorem range_number (grounded : String → Bool) :
    rangeCheck decls grounded (.sym "Number") {str "s"} = 0 ∧
      rangeCheck decls grounded (.sym "Number") {num 5} = {num 5} := by
  have notMeta : ¬ MetaName (Ty.sym "Number") := by simp [MetaName]
  constructor
  · simp only [rangeCheck, Multiset.singleton_bind]
    rw [guardCount_of_not_meta notMeta, count_class decls (g := .string "s") rfl]
    decide
  · simp only [rangeCheck, Multiset.singleton_bind]
    rw [guardCount_of_not_meta notMeta, count_int, one_nsmul]

/-- **A tail call's range is checked once, at the entry**: `cs`, whose base answers
`"s"` at the range `Number`, answers nothing through its protocol and through its
version with the entry's check; with the base `7` both answer `7` once. -/
theorem cs_tail_version (grounded : String → Bool) :
    protocolRun decls grounded (tailBody (str "s"))
        (arrow ([Ty.sym "Number"].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift) 3 [num 2] = 0 ∧
      versionRun (tailBody (str "s")) 3 [num 2] = {str "s"} ∧
      protocolRun decls grounded (tailBody (num 7))
        (arrow ([Ty.sym "Number"].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift) 3 [num 2] =
        rangeCheck decls grounded (.sym "Number") {num 7} := by
  have entry : EntryFacts decls grounded [.sym "Number"] [num 2] :=
    .cons (fun _ => Holds.of_count (count_int decls 2)) .nil
  have v₁ : versionRun (tailBody (str "s")) 3 [num 2] = {str "s"} := by decide
  have v₂ : versionRun (tailBody (num 7)) 3 [num 2] = {num 7} := by decide
  refine ⟨?_, v₁, ?_⟩
  · rw [tail_version_eq_protocol decls_functional number_guarded (tailBodies_cs grounded _) 3 _ entry, v₁]
    exact (range_number grounded).1
  · rw [tail_version_eq_protocol decls_functional number_guarded (tailBodies_cs grounded _) 3 _ entry, v₂]

/-- `(= (cs $k) (if (> $k 0) (cs (- $k 1)) "s"))` as the analysis reads it. -/
def csEqs : List Equation :=
  [⟨[.var "k"], .ifE (.prim ">" [.var "k", .const (num 0)])
    (.self [.prim "-" [.var "k", .const (num 1)]]) (.const (str "s"))⟩]

/-- **`cs` calls itself in a tail position only** (`scan->tail`): the call is a
branch of the `if`; its argument meets the formal. -/
theorem cs_tail : ∀ eq ∈ csEqs, (Pat.varsAll eq.pats).Nodup ∧ Tail eq.rhs ∧
    CallsOK decls noRes noEnt (eqFacts decls [.sym "Number"] eq) (.sym "Number")
      ([Ty.sym "Number"].map Ty.lift) eq.rhs := by
  intro eq heq
  simp only [csEqs, List.mem_singleton] at heq
  subst heq
  refine ⟨by simp [Pat.varsAll, Pat.vars], .ifE ⟨trivial, trivial, trivial⟩
    (.self ⟨⟨trivial, trivial, trivial⟩, trivial⟩) (.plain trivial), ?_⟩
  refine .ifE (.prim fun e he => ?_) (CallsOK.selfClosed (fun e he => ?_) (.cons (.prim rfl) .nil)) .const
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact .var
    · exact .const
  · rw [List.mem_singleton] at he
    subst he
    refine .prim fun e he => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact .var
    · exact .const

/-- **`cs`'s version, read from its equations, is its protocol followed by one
range check**: its base `"s"` is removed at the entry, as the protocol removes
it. -/
theorem cs_eqs_version (grounded : String → Bool) :
    protocolRun decls grounded (fun o => equationsBody env csEqs ⟨o, noCallee⟩)
        (arrow ([Ty.sym "Number"].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift) 3 [num 2] = 0 := by
  rw [tail_accepted_version_eq_protocol (res := noRes) (ent := noEnt) (en := noCallee) decls_functional
    (env_ok grounded noRes) (fun _ _ _ r hr => absurd hr (Multiset.notMem_zero r)) number_guarded
    cs_tail 3 [num 2] (.cons (fun _ => Holds.of_count (count_int decls 2)) .nil)]
  have v : versionRun (fun o => equationsBody env csEqs ⟨o, noCallee⟩) 3 [num 2] = {str "s"} := by
    decide
  rw [v]
  exact (range_number grounded).1

/-- **Owed classes along a tail chain**: two checks at the same class are one, and
checks at two classes keep nothing, so the run declines when they differ. -/
theorem chain_classes (grounded : String → Bool) :
    rangeCheck decls grounded (.sym "Number") (rangeCheck decls grounded (.sym "Number") {num 7}) = {num 7} ∧
      rangeCheck decls grounded (.sym "String") (rangeCheck decls grounded (.sym "Number") {num 7}) = 0 := by
  have notMeta : ¬ MetaName (Ty.sym "Number") := by simp [MetaName]
  have notMetaS : ¬ MetaName (Ty.sym "String") := by simp [MetaName]
  have num7 : rangeCheck decls grounded (.sym "Number") {num 7} = {num 7} := by
    simp only [rangeCheck, Multiset.singleton_bind]
    rw [guardCount_of_not_meta notMeta, count_int, one_nsmul]
  refine ⟨by rw [num7, num7], ?_⟩
  rw [num7]
  simp only [rangeCheck, Multiset.singleton_bind]
  rw [guardCount_of_not_meta notMetaS, count_class decls (g := .int 7) rfl]
  simp

/-- **The counterexample for a used call** (`nontail_self_call`): when the answers of
a call to itself are used, here bound by a `let` and replaced by `5`, the inner
call's check removes `"s"` in the protocol, which answers nothing, while the
version followed by the entry's check answers `5`. -/
theorem used_call_breaks (grounded : String → Bool) :
    protocolRun decls grounded usedBody
        (arrow ([Ty.sym "Number"].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift) 2 [num 1] = 0 ∧
      rangeCheck decls grounded (.sym "Number") (versionRun usedBody 2 [num 1]) = {num 5} := by
  have notMeta : ¬ MetaName (Ty.sym "Number") := by simp [MetaName]
  have guarded : demand ((Ty.sym "Number" : Ty Empty).lift) = .guarded := by decide
  have argNum : ∀ k : ℤ, argCount decls (metatype grounded) [.sym "Number"] [num k] = 1 := fun k => by
    simp only [argCount, guarded, if_true, mul_one]
    rw [guardCount_of_not_meta notMeta, count_int]
  refine ⟨?_, ?_⟩
  · have inner : protocolRun decls grounded usedBody
        (arrow ([Ty.sym "Number"].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift) 1 [num 0] = 0 := by
      simp only [protocolRun]
      rw [chainCall_closed, argNum, one_nsmul]
      simp only [if_pos number_guarded]
      show (({str "s"} : Multiset Atom).bind fun r =>
        guardCount (info decls r) (.sym "Number") (metatype grounded r) • {r}) = 0
      exact (range_number grounded).1
    simp only [protocolRun]
    rw [chainCall_closed, argNum, one_nsmul]
    simp only [if_pos number_guarded]
    simp only [protocolRun] at inner
    show ((((chainCall decls (metatype grounded) (usedBody fun _ => 0)
        (arrow ([Ty.sym "Number"].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift) [num 0]).bind
          fun _ => {num 5}).bind fun r =>
        guardCount (info decls r) (.sym "Number") (metatype grounded r) • {r}) = 0)
    rw [inner]
    rfl
  · have v : versionRun usedBody 2 [num 1] = {num 5} := by decide
    rw [v]
    exact (range_number grounded).2

/-! ### Activations owing classes -/

/-- The range check at a value class on a value of a class. -/
theorem rangeCheck_value (grounded : String → Bool) {g : GroundedValue} {c c' : String}
    (hg : valueClass g = some c) (hc' : ¬ MetaName (Ty.sym c')) :
    rangeCheck decls grounded (.sym c') {.grounded g} = if c' = c then {.grounded g} else 0 := by
  simp only [rangeCheck, Multiset.singleton_bind]
  rw [guardCount_of_not_meta hc', count_class decls hg]
  by_cases h : c' = c
  · subst h
    simp [one_nsmul]
  · simp [h]

theorem argCount_number {Γ : Decls} (grounded : String → Bool) (n : ℤ) :
    argCount Γ (metatype grounded) [.sym "Number"] [num n] = 1 := by
  have notMeta : ¬ MetaName (Ty.sym "Number") := by simp [MetaName]
  have guarded : demand ((Ty.sym "Number" : Ty Empty).lift) = .guarded := by decide
  simp only [argCount, guarded, if_true, mul_one]
  rw [guardCount_of_not_meta notMeta, count_int]

/-- `(-> Number %Undefined% …)` passes a number and any second argument once. -/
theorem cnt_argCount (grounded : String → Bool) (n : ℤ) (a : Atom) :
    argCount decls (metatype grounded) [.sym "Number", .sym "%Undefined%"] [num n, a] = 1 := by
  have notMeta : ¬ MetaName (Ty.sym "Number") := by simp [MetaName]
  have guarded : demand ((Ty.sym "Number" : Ty Empty).lift) = .guarded := by decide
  have unchecked : demand ((Ty.sym "%Undefined%" : Ty Empty).lift) ≠ .guarded := by decide
  simp only [argCount, guarded, if_true, if_neg unchecked, mul_one]
  rw [guardCount_of_not_meta notMeta, count_int]

theorem string_guarded : ResultGuarded ((Ty.sym "String" : Ty Empty).lift) := by decide

/-- The heads of `(= (cnt $n $acc) (if (== $n 0) $acc (cnt (- $n 1) (+ $acc 1))))`
and of `(= (top) (+ 1 (cnt 3 0)))`, whose call to `cnt` is outside a tail
position. -/
inductive CntHead
  | cnt
  | top

/-- `(: cnt (-> Number %Undefined% Number))`; `top` is not typed. -/
def cntSig : CntHead → Option (Ty String)
  | .cnt => some (arrow ([.sym "Number", .sym "%Undefined%"].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift)
  | .top => none

/-- `cnt`'s range is not proved, so it owes its class when it returns. -/
def cntOwe : CntHead → List Atom → Option (Ty Empty)
  | .cnt, _ => some (.sym "Number")
  | .top, _ => none

/-- The outcomes of the equations; `(+ $acc 1)` answers nothing off a number. -/
def cntSteps : CntHead → (CntHead → List Atom → Multiset Atom) → List Atom →
    Multiset (Atom ⊕ (CntHead × List Atom))
  | .cnt, _, [.grounded (.int n), a] =>
      if n = 0 then {.inl a} else (plus a (num 1)).map fun a' => .inr (.cnt, [num (n - 1), a'])
  | .top, O, [] => (O .cnt [num 3, num 0]).bind fun r => (plus (num 1) r).map .inl
  | _, _, _ => 0

/-- `top` calls `(cnt 3 0)` outside a tail position. -/
def cntNonTail : CntHead → List Atom → CntHead → List Atom → Prop
  | .top, [], .cnt, ws => ws = [num 3, num 0]
  | _, _, _, _ => False

/-- `cnt` at a number and anything owes `Number`; `top` owes nothing. -/
def cntAct : Option (Ty Empty) → CntHead → List Atom → Prop
  | o, .cnt, vs => o = some (.sym "Number") ∧ ∃ (n : ℤ) (a : Atom), vs = [num n, a]
  | o, .top, vs => o = none ∧ vs = []

theorem cnt_hyps (grounded : String → Bool) :
    ChainHyps decls grounded cntSig cntOwe cntSteps cntNonTail cntAct where
  owes := by
    rintro o (_ | _) vs R hA hR
    · obtain ⟨rfl, n, a, rfl⟩ := hA
      cases hR
      exact ⟨rfl, _, rfl, checksAt_closed number_guarded (cnt_argCount grounded n a)⟩
    · cases hR
  proven := by
    rintro o (_ | _) vs T hA hR hT
    · cases hR
    · cases hT
  congr := by
    rintro o (_ | _) vs hA O O' - hO
    · obtain ⟨rfl, n, a, rfl⟩ := hA
      rfl
    · obtain ⟨rfl, rfl⟩ := hA
      simp only [cntSteps]
      rw [hO .cnt [num 3, num 0] rfl]
  nonTail := by
    rintro o (_ | _) vs g ws hA hg
    · obtain ⟨rfl, n, a, rfl⟩ := hA
      exact hg.elim
    · obtain ⟨rfl, rfl⟩ := hA
      cases g with
      | cnt =>
          cases hg
          exact ⟨rfl, 3, num 0, rfl⟩
      | top => exact hg.elim
  tail := by
    rintro o (_ | _) vs O hA hO g ws hc
    · obtain ⟨rfl, n, a, rfl⟩ := hA
      simp only [cntSteps] at hc
      split_ifs at hc
      · simp at hc
      · obtain ⟨a', -, he⟩ := Multiset.mem_map.mp hc
        cases he
        exact ⟨rfl, n - 1, a', rfl⟩
    · obtain ⟨rfl, rfl⟩ := hA
      simp only [cntSteps] at hc
      obtain ⟨r, -, hr⟩ := Multiset.mem_bind.mp hc
      obtain ⟨_, -, he⟩ := Multiset.mem_map.mp hr
      cases he

theorem cnt_zero (grounded : String → Bool) (k : ℕ) (o : Option (Ty Empty)) (a : Atom) :
    machineRunS decls grounded cntOwe cntSteps (k + 1) o .cnt [num 0, a] = owedCheck decls grounded o {a} := by
  show (cntSteps .cnt _ [num 0, a]).bind _ = _
  simp [cntSteps]

theorem cnt_succ (grounded : String → Bool) (k : ℕ) (o : Option (Ty Empty)) {n : ℤ} (hn : n ≠ 0) (m : ℤ) :
    machineRunS decls grounded cntOwe cntSteps (k + 1) o .cnt [num n, num m] =
      machineRunS decls grounded cntOwe cntSteps k (o.or (some (.sym "Number"))) .cnt
        [num (n - 1), num (m + 1)] := by
  show (cntSteps .cnt _ [num n, num m]).bind _ = _
  simp only [cntSteps, if_neg hn, plus, Multiset.map_singleton, Multiset.singleton_bind, cntOwe]

/-- **A call outside a tail position starts its own chain** (`(+ 1 (cnt 10 0))` of
`prepared_return_checks`): `(cnt 3 0)` runs as an activation owing `Number`, its
tail calls re-entering in place, its value `3` checked once when it returns;
`top` consumes it and answers `4` once, as the protocol does, at every fuel from
five on. -/
theorem top_nontail (grounded : String → Bool) (k : ℕ) :
    machineRunS decls grounded cntOwe cntSteps (k + 5) none .top [] = {num 4} ∧
      protocolRunS decls grounded cntSig cntSteps (k + 5) .top [] = {num 4} := by
  have notMeta : ¬ MetaName (Ty.sym "Number") := by simp [MetaName]
  have run : machineRunS decls grounded cntOwe cntSteps (k + 5) none .top [] = {num 4} := by
    show ((cntSteps .top _ []).bind _ : Multiset Atom) = _
    simp only [cntSteps, cntOwe]
    rw [cnt_succ grounded _ _ (by decide), cnt_succ grounded _ _ (by decide), cnt_succ grounded _ _ (by decide)]
    norm_num
    rw [cnt_zero]
    simp [owedCheck, rangeCheck_value grounded (g := .int 3) (c := "Number") rfl notMeta, plus]
  refine ⟨run, ?_⟩
  rw [← machine_call_eq_protocol decls_functional (cnt_hyps grounded) (h := .top) (vs := []) ⟨rfl, rfl⟩]
  exact run

/-- The heads of `(= (hand $n $acc) (if (== $n 0) (label $acc) (hand (- $n 1) $acc)))`
and `(= (label $x) "done")`. -/
inductive HandHead
  | hand
  | label

/-- `(: hand (-> Number %Undefined% Number))` and `(: label (-> Number String))`. -/
def handSig : HandHead → Option (Ty String)
  | .hand => some (arrow ([.sym "Number", .sym "%Undefined%"].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift)
  | .label => some (arrow ([Ty.sym "Number"].map Ty.lift) (Ty.sym "String" : Ty Empty).lift)

/-- `hand` owes its class; `label`'s range is proved, so it owes none. -/
def handOwe : HandHead → List Atom → Option (Ty Empty)
  | .hand, _ => some (.sym "Number")
  | .label, _ => none

def handSteps : HandHead → (HandHead → List Atom → Multiset Atom) → List Atom →
    Multiset (Atom ⊕ (HandHead × List Atom))
  | .hand, _, [.grounded (.int n), a] =>
      if n = 0 then {.inr (.label, [a])} else {.inr (.hand, [num (n - 1), a])}
  | .label, _, [_] => {.inl (str "done")}
  | _, _, _ => 0

/-- `hand` at numbers owes `Number`; `label` at a number owes any class. -/
def handAct : Option (Ty Empty) → HandHead → List Atom → Prop
  | o, .hand, vs => o = some (.sym "Number") ∧ ∃ n m : ℤ, vs = [num n, num m]
  | _, .label, vs => ∃ m : ℤ, vs = [num m]

theorem hand_hyps (grounded : String → Bool) :
    ChainHyps decls grounded handSig handOwe handSteps (fun _ _ _ _ => False) handAct where
  owes := by
    rintro o (_ | _) vs R hA hR
    · obtain ⟨rfl, n, m, rfl⟩ := hA
      cases hR
      exact ⟨rfl, _, rfl, checksAt_closed number_guarded (cnt_argCount grounded n (num m))⟩
    · cases hR
  proven := by
    rintro o (_ | _) vs T hA hR hT O hO
    · cases hR
    · obtain ⟨m, rfl⟩ := hA
      cases hT
      have notMetaS : ¬ MetaName (Ty.sym "String") := by simp [MetaName]
      rw [chainCall_closed, argCount_number, one_nsmul]
      simp only [handSteps, outcomeAnswers, Multiset.singleton_bind, if_pos string_guarded]
      rw [guardCount_of_not_meta notMetaS, count_class decls (g := .string "done") rfl, if_pos rfl, one_nsmul]
  congr := by
    rintro o (_ | _) vs hA O O' - -
    · obtain ⟨-, n, m, rfl⟩ := hA
      rfl
    · obtain ⟨m, rfl⟩ := hA
      rfl
  nonTail := fun _ _ _ _ _ _ h => h.elim
  tail := by
    rintro o (_ | _) vs O hA hO g ws hc
    · obtain ⟨rfl, n, m, rfl⟩ := hA
      simp only [handSteps] at hc
      split_ifs at hc
      · rw [Multiset.mem_singleton] at hc
        cases hc
        exact ⟨m, rfl⟩
      · rw [Multiset.mem_singleton] at hc
        cases hc
        exact ⟨rfl, n - 1, m, rfl⟩
    · obtain ⟨m, rfl⟩ := hA
      simp [handSteps] at hc

theorem hand_zero (grounded : String → Bool) (k : ℕ) (o : Option (Ty Empty)) (a : Atom) :
    machineRunS decls grounded handOwe handSteps (k + 1) o .hand [num 0, a] =
      machineRunS decls grounded handOwe handSteps k o .label [a] := by
  show (handSteps .hand _ [num 0, a]).bind _ = _
  cases o <;> simp [handSteps, handOwe]

theorem hand_succ (grounded : String → Bool) (k : ℕ) (o : Option (Ty Empty)) {n : ℤ} (hn : n ≠ 0) (a : Atom) :
    machineRunS decls grounded handOwe handSteps (k + 1) o .hand [num n, a] =
      machineRunS decls grounded handOwe handSteps k (o.or (some (.sym "Number"))) .hand [num (n - 1), a] := by
  show (handSteps .hand _ [num n, a]).bind _ = _
  simp only [handSteps, if_neg hn, Multiset.singleton_bind, handOwe]

theorem label_run (grounded : String → Bool) (k : ℕ) (o : Option (Ty Empty)) (a : Atom) :
    machineRunS decls grounded handOwe handSteps (k + 1) o .label [a] = owedCheck decls grounded o {str "done"} := by
  show (handSteps .label _ [a]).bind _ = _
  simp [handSteps]

/-- **A tail call into a head of another class whose range is proved** (`hand` and
`label` of `prepared_return_checks`): `label` owes no class, so `hand`'s tail call
into it does not decline, and the activation keeps owing `Number`, whose check
removes `"done"`: `(hand 2 0)` answers nothing, as the protocol does; `(label 0)`
alone answers `"done"`. -/
theorem hand_label (grounded : String → Bool) (k : ℕ) :
    machineRunS decls grounded handOwe handSteps (k + 4) (some (.sym "Number")) .hand [num 2, num 0] = 0 ∧
      protocolRunS decls grounded handSig handSteps (k + 4) .hand [num 2, num 0] = 0 ∧
      protocolRunS decls grounded handSig handSteps (k + 1) .label [num 0] = {str "done"} := by
  have notMeta : ¬ MetaName (Ty.sym "Number") := by simp [MetaName]
  have run : machineRunS decls grounded handOwe handSteps (k + 4) (some (.sym "Number")) .hand
      [num 2, num 0] = 0 := by
    rw [hand_succ grounded _ _ (by decide), hand_succ grounded _ _ (by decide)]
    norm_num
    rw [hand_zero, label_run]
    simp only [owedCheck]
    rw [rangeCheck_value grounded (g := .string "done") (c := "String") rfl notMeta]
    simp
  refine ⟨run, ?_, ?_⟩
  · rw [← machine_call_eq_protocol decls_functional (hand_hyps grounded) (h := .hand) ⟨rfl, 2, 0, rfl⟩]
    exact run
  · rw [← machine_call_eq_protocol decls_functional (hand_hyps grounded) (h := .label) ⟨0, rfl⟩, label_run]
    rfl

/-- The heads of `(= (lab $x) "s")` and `(= (main $x) (let $y (lab $x) 5))`. -/
inductive LetHead
  | lab
  | main

/-- `(: lab (-> Number String))` and `(: main (-> Number Number))`. -/
def letSig : LetHead → Option (Ty String)
  | .lab => some (arrow ([Ty.sym "Number"].map Ty.lift) (Ty.sym "String" : Ty Empty).lift)
  | .main => some (arrow ([Ty.sym "Number"].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift)

def letSteps : LetHead → (LetHead → List Atom → Multiset Atom) → List Atom →
    Multiset (Atom ⊕ (LetHead × List Atom))
  | .lab, _, [_] => {.inl (str "s")}
  | .main, O, [x] => (O .lab [x]).bind fun _ => {.inl (num 5)}
  | _, _, _ => 0

/-- Each head owes its own class. -/
def letOwe : LetHead → List Atom → Option (Ty Empty)
  | .lab, _ => some (.sym "String")
  | .main, _ => some (.sym "Number")

/-- A machine whose call outside a tail position would owe its caller's class. -/
def letOweCaller : LetHead → List Atom → Option (Ty Empty) := fun _ _ => some (.sym "Number")

def letNonTail : LetHead → List Atom → LetHead → List Atom → Prop
  | .main, [x], .lab, ws => ws = [x]
  | _, _, _, _ => False

def letAct : Option (Ty Empty) → LetHead → List Atom → Prop
  | o, .lab, vs => o = some (.sym "String") ∧ ∃ m : ℤ, vs = [num m]
  | o, .main, vs => o = some (.sym "Number") ∧ ∃ m : ℤ, vs = [num m]

theorem let_hyps (grounded : String → Bool) :
    ChainHyps decls grounded letSig letOwe letSteps letNonTail letAct where
  owes := by
    rintro o (_ | _) vs R hA hR
    · obtain ⟨rfl, m, rfl⟩ := hA
      cases hR
      exact ⟨rfl, _, rfl, checksAt_closed string_guarded (argCount_number grounded m)⟩
    · obtain ⟨rfl, m, rfl⟩ := hA
      cases hR
      exact ⟨rfl, _, rfl, checksAt_closed number_guarded (argCount_number grounded m)⟩
  proven := by
    rintro o (_ | _) vs T hA hR <;> cases hR
  congr := by
    rintro o (_ | _) vs hA O O' - hO
    · obtain ⟨-, m, rfl⟩ := hA
      rfl
    · obtain ⟨-, m, rfl⟩ := hA
      simp only [letSteps]
      rw [hO .lab [num m] rfl]
  nonTail := by
    rintro o (_ | _) vs g ws hA hg
    · obtain ⟨-, m, rfl⟩ := hA
      exact hg.elim
    · obtain ⟨-, m, rfl⟩ := hA
      cases g with
      | lab =>
          cases hg
          exact ⟨rfl, m, rfl⟩
      | main => exact hg.elim
  tail := by
    rintro o (_ | _) vs O hA hO g ws hc
    · obtain ⟨-, m, rfl⟩ := hA
      simp [letSteps] at hc
    · obtain ⟨-, m, rfl⟩ := hA
      simp only [letSteps] at hc
      obtain ⟨_, -, hr⟩ := Multiset.mem_bind.mp hc
      simp at hr

theorem let_run (grounded : String → Bool) (owe : LetHead → List Atom → Option (Ty Empty)) (k : ℕ)
    (o : Option (Ty Empty)) (m : ℤ) :
    machineRunS decls grounded owe letSteps (k + 2) o .main [num m] =
      (owedCheck decls grounded (owe .lab [num m]) {str "s"}).bind fun _ =>
        owedCheck decls grounded o {num 5} := by
  show ((letSteps .main _ [num m]).bind _ : Multiset Atom) = _
  simp only [letSteps, Multiset.bind_assoc]
  show ((machineRunS decls grounded owe letSteps (k + 1) (owe .lab [num m]) .lab [num m]).bind _ :
    Multiset Atom) = _
  show ((letSteps .lab _ [num m]).bind _).bind _ = _
  simp only [letSteps, Multiset.singleton_bind]

/-- **A call outside a tail position owes its callee's class, not its caller's**:
`(main 1)` answers `5` once, as the protocol does, when the call `(lab 1)` owes
`String`; owing `main`'s `Number`, its `"s"` would be removed and `main` would
answer nothing, and `Number` is not a class `lab`'s protocol checks at. -/
theorem owe_caller_breaks (grounded : String → Bool) (k : ℕ) :
    protocolRunS decls grounded letSig letSteps (k + 2) .main [num 1] = {num 5} ∧
      machineRunS decls grounded letOwe letSteps (k + 2) (some (.sym "Number")) .main [num 1] = {num 5} ∧
      machineRunS decls grounded letOweCaller letSteps (k + 2) (some (.sym "Number")) .main [num 1] = 0 ∧
      ¬ ChecksAt decls grounded (arrow ([Ty.sym "Number"].map Ty.lift) (Ty.sym "String" : Ty Empty).lift)
        [num 1] (.sym "Number") := by
  have notMeta : ¬ MetaName (Ty.sym "Number") := by simp [MetaName]
  have notMetaS : ¬ MetaName (Ty.sym "String") := by simp [MetaName]
  have right : machineRunS decls grounded letOwe letSteps (k + 2) (some (.sym "Number")) .main [num 1] =
      {num 5} := by
    rw [let_run]
    simp only [letOwe, owedCheck]
    rw [rangeCheck_value grounded (g := .string "s") (c := "String") rfl notMetaS, if_pos rfl,
      Multiset.singleton_bind, rangeCheck_value grounded (g := .int 5) (c := "Number") rfl notMeta, if_pos rfl]
  refine ⟨?_, right, ?_, fun h => ?_⟩
  · rw [← machine_call_eq_protocol decls_functional (let_hyps grounded) (h := .main) ⟨rfl, 1, rfl⟩]
    exact right
  · rw [let_run]
    simp only [letOweCaller, owedCheck]
    rw [rangeCheck_value grounded (g := .string "s") (c := "String") rfl notMeta, if_neg (by decide)]
    rfl
  · have := h fun _ => {str "s"}
    rw [chainCall_closed, argCount_number, one_nsmul] at this
    simp only [Multiset.singleton_bind, if_pos string_guarded] at this
    rw [guardCount_of_not_meta notMetaS, count_class decls (g := .string "s") rfl, if_pos rfl, one_nsmul,
      rangeCheck_value grounded (g := .string "s") (c := "String") rfl notMeta, if_neg (by decide)] at this
    exact Multiset.singleton_ne_zero _ this

/-! ### The tail condition is the relation's -/

/-- `(= (ml 0) "z")`: no call to itself; its answer is no `Number`. -/
def mlBase : Equation := ⟨[.const (num 0)], .const (str "z")⟩

/-- `(= (ml $n) (if (> $n 0) (let $r (ml (- $n 1)) 5) (empty)))`: its answer is a
`Number`, and its call to itself is used. -/
def mlStep : Equation :=
  ⟨[.var "n"], .ifE (.prim ">" [.var "n", .const (num 0)])
    (.letE (.var "r") (.self [.prim "-" [.var "n", .const (num 1)]]) (.const (num 5))) .empty⟩

def mlEqs : List Equation := [mlBase, mlStep]

abbrev mlBody : (List Atom → Multiset Atom) → List Atom → Multiset Atom :=
  fun o => equationsBody env mlEqs ⟨o, noCallee⟩

theorem ml_body_one (o : List Atom → Multiset Atom) :
    mlBody o [num 1] = (o [num 0]).bind fun _ => {num 5} := by
  unfold mlBody equationsBody
  rw [show ((mlEqs : List Equation) : Multiset Equation) = mlBase ::ₘ mlStep ::ₘ 0 from rfl,
    Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
  have m1 : Pat.matchAll mlBase.pats [num 1] = none := by decide
  have m2 : Pat.matchAll mlStep.pats [num 1] = some [("n", num 1)] := by decide
  have lr : List.lookup "r" [("n", num 1)] = none := rfl
  simp only [m1, m2, zero_add]
  simp [mlStep, Expr.eval, Expr.evalAll, env, ops, greater, minus, truth, Pat.matchUnder, Pat.extend,
    Pat.match, lr]

theorem ml_body_zero (o : List Atom → Multiset Atom) : mlBody o [num 0] = {str "z"} := by
  unfold mlBody equationsBody
  rw [show ((mlEqs : List Equation) : Multiset Equation) = mlBase ::ₘ mlStep ::ₘ 0 from rfl,
    Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
  have m1 : Pat.matchAll mlBase.pats [num 0] = some [] := by decide
  have m2 : Pat.matchAll mlStep.pats [num 0] = some [("n", num 0)] := by decide
  simp only [m1, m2]
  simp [mlBase, mlStep, Expr.eval, Expr.evalAll, env, ops, greater, truth]

/-- **Each equation alone meets one of the two conditions, the relation neither,
and the answers differ** (`contract_range_left_to_entry_ok`,
`tail_range_versions`): `(= (ml 0) "z")` alone calls itself nowhere, so it is
tail; `ml`'s other equation alone proves its range. But `TailBodies` reads all the
equations at once, and the relation's body has no tail decomposition; nor is the
relation accepted at `Number`, since `"z"` is none. Its version followed by the
entry's check answers `5` for `(ml 1)`, where the protocol answers nothing. -/
theorem mixed_equations_break (grounded : String → Bool) :
    (∀ eq ∈ [mlBase], (Pat.varsAll eq.pats).Nodup ∧ Tail eq.rhs ∧
      CallsOK decls noRes noEnt (eqFacts decls [.sym "Number"] eq) (.sym "Number")
        ([Ty.sym "Number"].map Ty.lift) eq.rhs) ∧
      (∀ eq ∈ [mlStep], Accepted decls noRes noEnt [.sym "Number"] (.sym "Number") eq) ∧
      ¬ TailBodies decls grounded [.sym "Number"] mlBody mlBody ∧
      ¬ (∀ eq ∈ mlEqs, Accepted decls noRes noEnt [.sym "Number"] (.sym "Number") eq) ∧
      protocolRun decls grounded mlBody (arrow ([Ty.sym "Number"].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift)
        2 [num 1] = 0 ∧
      rangeCheck decls grounded (.sym "Number") (versionRun mlBody 2 [num 1]) = {num 5} := by
  have argNum : ∀ k : ℤ, argCount decls (metatype grounded) [.sym "Number"] [num k] = 1 :=
    argCount_number grounded
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro eq heq
    rw [List.mem_singleton] at heq
    subst heq
    exact ⟨by simp [mlBase, Pat.varsAll, Pat.vars], .plain trivial, .const⟩
  · intro eq heq
    rw [List.mem_singleton] at heq
    subst heq
    refine ⟨by simp [mlStep, Pat.varsAll, Pat.vars], rfl, .ifE (.prim fun e he => ?_)
      (.letE (CallsOK.selfClosed (fun e he => ?_) (.cons (.prim rfl) .nil)) .const) .empty,
      .ifE (.letE (.const (count_int decls 5))) .empty⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact .var
      · exact .const
    · rw [List.mem_singleton] at he
      subst he
      refine .prim fun e he => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact .var
      · exact .const
  · intro h
    obtain ⟨A, C, -, hP, -⟩ := h [num 1] (.cons (fun _ => Holds.of_count (count_int decls 1)) .nil)
    have h0 := hP fun _ => 0
    have h7 := hP fun _ => {num 7}
    rw [ml_body_one] at h0 h7
    simp only [Multiset.zero_bind, Multiset.bind_zero, add_zero] at h0
    subst h0
    rw [Multiset.singleton_bind, zero_add] at h7
    have mem : num 5 ∈ C.bind fun _ => ({num 7} : Multiset Atom) := by rw [← h7]; simp
    rw [Multiset.bind_singleton, Multiset.mem_map] at mem
    obtain ⟨_, -, he⟩ := mem
    exact absurd he (by decide)
  · intro h
    have := (h mlBase (by simp [mlEqs])).result
    cases this with
    | const hc =>
        rw [count_class decls (g := .string "z") rfl] at hc
        exact absurd hc (by decide)
  · have inner : protocolRun decls grounded mlBody
        (arrow ([Ty.sym "Number"].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift) 1 [num 0] = 0 := by
      simp only [protocolRun]
      rw [chainCall_closed, argNum, one_nsmul, ml_body_zero]
      simp only [if_pos number_guarded, Multiset.singleton_bind]
      rw [guardCount_of_not_meta (by simp [MetaName]), count_class decls (g := .string "z") rfl]
      simp
    simp only [protocolRun] at inner ⊢
    rw [chainCall_closed, argNum, one_nsmul, ml_body_one, inner]
    rfl
  · have v : versionRun mlBody 2 [num 1] = {num 5} := by
      show mlBody (versionRun mlBody 1) [num 1] = _
      rw [ml_body_one]
      show (mlBody (versionRun mlBody 0) [num 0]).bind _ = _
      rw [ml_body_zero, Multiset.singleton_bind]
    rw [v]
    exact (range_number grounded).2

/-! ### `let`, `if`, `case` and entering another relation's version -/

/-- `lpos`'s equation at a cell. -/
def lposCell : Equation :=
  ⟨[.ctor "Cons" [.var "x", .var "xs"]],
    .letE (.var "s") (.self [.var "xs"])
      (.ifE (.prim ">" [.var "x", .const (num 0)]) (.prim "+" [.var "x", .var "s"])
        (.caseE (.var "s") [.const (num 0), .var "t"]
          [.const (num 0), .prim "-" [.var "t", .const (num 0)]]))⟩

/-- `(= (lpos Nil) 0)` and `(= (lpos (Cons $x $xs)) (let $s (lpos $xs) (if (> $x 0)
(+ $x $s) (case $s ((0 0) ($t (- $t 0)))))))`. -/
def lposEqs : List Equation :=
  [⟨[.const (sym "Nil")], .const (num 0)⟩, lposCell]

/-- **A fold through `let`, `if` and `case` is accepted**: the `let` value is a call
to itself at `$xs`, which meets the formal; each branch of the `if` and each arm
of the `case` is a `Number`, though the variables `$s` and `$t` have no fact. -/
theorem lpos_accepted (res : String → Ty Empty) (ent : String → List (Ty Empty)) :
    ∀ eq ∈ lposEqs, Accepted decls res ent [listNumber] (.sym "Number") eq := by
  intro eq heq
  simp only [lposEqs, List.mem_cons, List.not_mem_nil, or_false] at heq
  rcases heq with rfl | rfl
  · exact ⟨by simp [Pat.varsAll, Pat.vars], rfl, .const, .const (count_int decls 0)⟩
  · refine ⟨by simp [lposCell, Pat.varsAll, Pat.vars], rfl, ?_, ?_⟩
    · refine .letE (CallsOK.selfClosed (fun e he => by
          rw [List.mem_singleton] at he
          subst he
          exact .var)
        (.cons (.var ⟨listNumber, .ctor "Cons" [.var "x", .var "xs"], by simp [lposCell], by decide, xs_fact⟩)
          .nil))
        (.ifE (.prim fun e he => ?_) (.prim fun e he => ?_) (.caseE .var fun b hb => ?_))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact .var
        · exact .const
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> exact .var
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact .const
        · refine .prim fun e he => ?_
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl
          · exact .var
          · exact .const
    · refine .letE (.ifE (.prim rfl) (.caseE fun b hb => ?_))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact .const (count_int decls 0)
      · exact .prim rfl

/-- `lpos`'s equations under the controls' environment, with no callee. -/
abbrev lposBody : (List Atom → Multiset Atom) → List Atom → Multiset Atom :=
  fun o => equationsBody env lposEqs ⟨o, noCallee⟩

/-- **The version of `lpos` is its protocol**, at every fuel, on every list that
meets the entry fact. -/
theorem lpos_version (grounded : String → Bool) (n : ℕ) (vs : List Atom)
    (hvs : EntryFacts decls grounded [listNumber] vs) :
    protocolRun decls grounded lposBody (arrow ([listNumber].map Ty.lift)
        (Ty.sym "Number" : Ty Empty).lift) n vs =
      versionRun lposBody n vs :=
  accepted_version_eq_protocol (res := noRes) (ent := noEnt) decls_functional number_guarded
    (lpos_accepted _ _) (env_ok grounded noRes) noCallee noCallee (fun _ _ _ => rfl)
    (fun _ _ _ r hr => absurd hr (Multiset.notMem_zero r)) n vs hvs

/-- `lpos` takes each branch: at `(Cons -1 (Cons 3 Nil))` the inner cell takes the
`then` branch, `3`, and the outer cell the `else` branch through the arm `$t`;
at `(Cons -1 Nil)` the arm `0`. -/
theorem lpos_answers :
    versionRun lposBody 3 [app "Cons" [num (-1), app "Cons" [num 3, sym "Nil"]]] = {num 3} ∧
      versionRun lposBody 2 [app "Cons" [num (-1), sym "Nil"]] = {num 0} := by
  constructor <;> decide

/-- **A variable a `let` binds has no fact** (`contract_bind_any`): in `lpos`, `$s`
is not typed, though every value it takes is a `Number`. -/
theorem let_bound_untyped (res : String → Ty Empty) (T : Ty Empty) :
    ¬ HasType decls res (eqFacts decls [listNumber] lposCell) (.sym "Number") (.var "s") T := by
  intro h
  cases h with
  | var hx =>
      obtain ⟨A, p, hAp, -, hpf⟩ := hx
      have mem := hpf.mem_vars
      simp [lposCell] at hAp
      obtain ⟨-, rfl⟩ := hAp
      simp [Pat.vars, Pat.varsAll] at mem

/-- `(= (total $l) (lsum $l))`: the call meets `lsum`'s entry fact, so it enters
`lsum`'s version. -/
def totalEqs : List Equation := [⟨[.var "l"], .enter "lsum" [.var "l"]⟩]

/-- `lsum`'s entry facts and result type, for its callers. -/
def lsumEnt : String → List (Ty Empty) := fun f => if f = "lsum" then [listNumber] else []

theorem total_accepted : ∀ eq ∈ totalEqs, Accepted decls noRes lsumEnt [listNumber] (.sym "Number") eq := by
  intro eq heq
  simp only [totalEqs, List.mem_singleton] at heq
  subst heq
  refine ⟨by simp [Pat.varsAll, Pat.vars], rfl, .enter (fun e he => by
    rw [List.mem_singleton] at he
    subst he
    exact .var) ?_, .enter⟩
  exact .cons (fun _ => .var ⟨listNumber, .var "l", by simp, by decide, .var _ _⟩) .nil

/-- **Not without the fact**: the analysis does not enter `lsum`'s version at `$s`,
which a `let` binds. -/
theorem no_enter_at_let_bound :
    ¬ CallsOK decls noRes lsumEnt (eqFacts decls [listNumber] lposCell)
      (.sym "Number") [listNumber.lift] (.enter "lsum" [.var "s"]) := by
  intro h
  cases h with
  | enter _ typed =>
      cases typed with
      | cons hs _ => exact let_bound_untyped noRes listNumber (hs (by decide))

/-- The callees' protocols and versions at fuel `m`: `lsum`'s, and nothing else. -/
noncomputable def lsumProtocol (grounded : String → Bool) (m : ℕ) : String → List Atom → Multiset Atom :=
  fun f ws => if f = "lsum" then
    protocolRun decls grounded lsumBody (arrow ([listNumber].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift) m ws
    else 0

def lsumVersion (m : ℕ) : String → List Atom → Multiset Atom :=
  fun f ws => if f = "lsum" then versionRun lsumBody m ws else 0

/-- **Entering a callee's version is the callee's protocol**: `total`'s version,
which enters `lsum`'s version, is `total`'s protocol, which runs `lsum`'s, at every
fuel of either. -/
theorem total_version (grounded : String → Bool) (m n : ℕ) (vs : List Atom)
    (hvs : EntryFacts decls grounded [listNumber] vs) :
    protocolRun decls grounded (fun o => equationsBody env totalEqs ⟨o, lsumProtocol grounded m⟩)
        (arrow ([listNumber].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift) n vs =
      versionRun (fun o => equationsBody env totalEqs ⟨o, lsumVersion m⟩) n vs := by
  have callee := fun ws (hws : EntryFacts decls grounded [listNumber] ws) =>
    callee_oracles (E := env) decls_functional number_guarded noRes noEnt (lsum_accepted _ _)
      (env_ok grounded noRes) m ws hws
  refine accepted_version_eq_protocol decls_functional number_guarded total_accepted
    (env_ok grounded noRes) _ _ (fun f ws hws => ?_) (fun f ws hws r hr => ?_) n vs hvs
  · unfold lsumProtocol lsumVersion
    split_ifs with hf
    · subst hf
      exact (callee ws hws).1
    · rfl
  · unfold lsumVersion at hr
    split_ifs at hr with hf
    · subst hf
      exact (callee ws hws).2 r hr
    · exact absurd hr (Multiset.notMem_zero r)

/-- `total` answers through `lsum`'s version: `5` for `(Cons 5 Nil)`. -/
theorem total_five :
    versionRun (fun o => equationsBody env totalEqs ⟨o, lsumVersion 2⟩) 1
      [app "Cons" [num 5, sym "Nil"]] = {num 5} := by
  decide

/-! ### `match` over a space -/

/-- A space `&weights` with the rows `(w a 3)` and `(w b 4)`. -/
def envRows : Env :=
  ⟨ops, fun _ _ => 0, fun sp => if sp = sym "&weights" then {app "w" [sym "a", num 3],
    app "w" [sym "b", num 4]} else 0⟩

theorem envRows_ok (grounded : String → Bool) (res : String → Ty Empty) :
    EnvOK decls grounded res envRows :=
  ⟨(env_ok (Γ := decls) grounded res).prim, (env_ok (Γ := decls) grounded res).kept⟩

/-- `(= (weights) (match &weights (w $k $n) (+ $n 0)))`. -/
def weightsEqs : List Equation :=
  [⟨[], .matchE (.const (sym "&weights")) (.ctor "w" [.var "k", .var "n"])
    (.prim "+" [.var "n", .const (num 0)])⟩]

/-- **A `match` over a space is accepted**: its template is a `Number`, though the
pattern's variables have no fact. -/
theorem weights_accepted (res : String → Ty Empty) (ent : String → List (Ty Empty)) :
    ∀ eq ∈ weightsEqs, Accepted decls res ent [] (.sym "Number") eq := by
  intro eq heq
  simp only [weightsEqs, List.mem_singleton] at heq
  subst heq
  refine ⟨by simp [Pat.varsAll], rfl, .matchE .const (.prim fun e he => ?_), .matchE (.prim rfl)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact .var
  · exact .const

/-- `weights`' equations, with no callee. -/
abbrev weightsBody : (List Atom → Multiset Atom) → List Atom → Multiset Atom :=
  fun o => equationsBody envRows weightsEqs ⟨o, noCallee⟩

/-- **The version of `weights` is its protocol**, at every fuel. -/
theorem weights_version (grounded : String → Bool) (n : ℕ) :
    protocolRun decls grounded weightsBody (arrow (([] : List (Ty Empty)).map Ty.lift)
        (Ty.sym "Number" : Ty Empty).lift) n [] =
      versionRun weightsBody n [] :=
  accepted_version_eq_protocol (res := noRes) (ent := noEnt) decls_functional number_guarded
    (weights_accepted _ _) (envRows_ok grounded noRes) noCallee noCallee (fun _ _ _ => rfl)
    (fun _ _ _ r hr => absurd hr (Multiset.notMem_zero r)) n [] .nil

/-- Each row is an answer: `3` and `4`. -/
theorem weights_answers : versionRun weightsBody 1 [] = {num 3, num 4} := by
  decide

/-! ### Structural parameters checked where another head calls -/

/-- `(: Tree Type)`, `(: Leaf Tree)`, `(: Node (-> Tree Tree Tree))`, `(: mk (-> Number Tree))`,
`(: tsize (-> Tree Number))`, `(: mkbad (-> Number Tree))`, `(: tag (-> Tree Number))` and
`(: tagged (-> Tree %Undefined% Number))`. -/
def treeDecls : Decls := fun s =>
  if s = "Tree" then [.sym "Type"]
  else if s = "Leaf" then [.sym "Tree"]
  else if s = "Node" then [arrow [.sym "Tree", .sym "Tree"] (.sym "Tree")]
  else if s = "mk" then [arrow [.sym "Number"] (.sym "Tree")]
  else if s = "tsize" then [arrow [.sym "Tree"] (.sym "Number")]
  else if s = "mkbad" then [arrow [.sym "Number"] (.sym "Tree")]
  else if s = "tag" then [arrow [.sym "Tree"] (.sym "Number")]
  else if s = "tagged" then [arrow [.sym "Tree", .sym "%Undefined%"] (.sym "Number")]
  else []

theorem treeDecls_functional : Functional treeDecls := by
  intro s
  unfold treeDecls
  split_ifs <;> simp

abbrev treeTy : Ty Empty := .sym "Tree"
abbrev leafA : Atom := sym "Leaf"
abbrev nodeA (l r : Atom) : Atom := app "Node" [l, r]

/-- `(mk k)`'s answer: the full tree of depth `k`. -/
def fullTree : ℕ → Atom
  | 0 => leafA
  | k + 1 => nodeA (fullTree k) (fullTree k)

/-- A full tree walks at `Tree` (`petta_type_walk_once`), so the bound query types it
there once. -/
theorem walk_fullTree : ∀ k, Walk treeDecls (fullTree k) treeTy
  | 0 => ⟨.sym "Tree", by simp [treeDecls], by simp [IsArrowTy], fun _ => default, rfl⟩
  | k + 1 => ⟨[.sym "Tree", .sym "Tree"], .sym "Tree", by simp [treeDecls], fun _ => default, rfl,
      .inr (.inl rfl), walk_fullTree k, .inr (.inl rfl), walk_fullTree k, trivial⟩

theorem leaf_tree : count (info treeDecls leafA) treeTy = 1 := walk_count (v := leafA) (walk_fullTree 0)

theorem tree_structural : StructuralTy treeTy :=
  ⟨by simp [MetaName], fun c hc => by cases hc; decide⟩

theorem tree_guarded : ResultGuarded treeTy.lift := by decide

theorem num_not_tree (n : ℤ) : count (info treeDecls (num n)) treeTy = 0 := by
  rw [count_class treeDecls (g := .int n) rfl]
  decide

theorem node_row : treeDecls "Node" = [arrow [.sym "Tree", .sym "Tree"] (.sym "Tree")] := by
  simp [treeDecls]

theorem node_constructor : Constructor [.sym "Tree", .sym "Tree"] (.sym "Tree") :=
  ⟨by simp [Named], by simp, by simp⟩

/-- A node with a child that is no `Tree` is no `Tree`. -/
theorem node_count_zero (l r : Atom)
    (h : count (info treeDecls l) treeTy = 0 ∨ count (info treeDecls r) treeTy = 0) :
    count (info treeDecls (nodeA l r)) treeTy = 0 := by
  have le := count_le_one treeDecls_functional (nodeA l r) treeTy
  by_contra ne
  have one : count (info treeDecls (nodeA l r)) treeTy = 1 := by omega
  obtain ⟨σ, -, fields⟩ := ctor_inversion treeDecls_functional node_row [l, r] rfl treeTy
    (by simp [Named]) one
  have hl : count (info treeDecls l) treeTy = 1 := fields (.sym "Tree", l) (by simp) (by simp [Unchecked])
  have hr : count (info treeDecls r) treeTy = 1 := fields (.sym "Tree", r) (by simp) (by simp [Unchecked])
  rcases h with h | h
  · rw [h] at hl
    exact absurd hl (by decide)
  · rw [h] at hr
    exact absurd hr (by decide)

/-- The machine declines such a node at `Tree`. -/
theorem tree_bad_rejected (l r : Atom)
    (h : count (info treeDecls l) treeTy = 0 ∨ count (info treeDecls r) treeTy = 0) :
    ¬ MachineAccepts treeDecls [treeTy] [nodeA l r] := by
  intro hacc
  cases hacc with
  | cons hv _ =>
      rcases hv with ⟨c, hc, hcls, -⟩ | ⟨-, hcount⟩ | hu
      · cases hc
        exact absurd hcls (by decide)
      · rw [node_count_zero l r h] at hcount
        exact absurd hcount (by decide)
      · exact absurd hu (by decide)

abbrev tsizeRow : Ty String := arrow ([treeTy].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift
abbrev mkRow : Ty String := arrow ([Ty.sym "Number"].map Ty.lift) treeTy.lift

/-- A value that is no `Tree` fails a `Tree` parameter's guard: the protocol answers
nothing. -/
theorem tree_protocol_zero (grounded : String → Bool)
    (body : (List Atom → Multiset Atom) → List Atom → Multiset Atom) (R : Ty Empty) (n : ℕ) (v : Atom)
    (hv : count (info treeDecls v) treeTy = 0) :
    protocolRun treeDecls grounded body (arrow ([treeTy].map Ty.lift) R.lift) (n + 1) [v] = 0 := by
  simp only [protocolRun]
  rw [chainCall_closed]
  have zero : argCount treeDecls (metatype grounded) [treeTy] [v] = 0 := by
    simp only [argCount, (show demand (treeTy.lift : Ty String) = .guarded by decide), if_true, mul_one]
    rw [guardCount_of_not_meta (by simp [MetaName]) v, hv]
  rw [zero, zero_nsmul]

/-- `(= (tsize Leaf) 1)` and `(= (tsize (Node $l $r)) (+ 1 (+ (tsize $l) (tsize $r))))`. -/
def tsizeEqs : List Equation :=
  [⟨[.const leafA], .const (num 1)⟩,
   ⟨[.ctor "Node" [.var "l", .var "r"]],
     .prim "+" [.const (num 1), .prim "+" [.self [.var "l"], .self [.var "r"]]]⟩]

theorem node_fact (x : String) (hx : x = "l" ∨ x = "r") :
    PatFact treeDecls (.ctor "Node" [.var "l", .var "r"]) treeTy x treeTy := by
  refine PatFact.ctor (σ := fun _ => default) (B := .sym "Tree") (p := .var x) node_row node_constructor rfl
    (by simp [MetaName]) (by simp [Named]) rfl (by rcases hx with rfl | rfl <;> simp) (by simp [FreeField]) ?_
  exact PatFact.var _ _

/-- **`tsize` is accepted**: `$l` and `$r` are `Tree`s, so its calls to itself meet
the formal, and its result, an addition, is a `Number`. -/
theorem tsize_accepted (res : String → Ty Empty) (ent : String → List (Ty Empty)) :
    ∀ eq ∈ tsizeEqs, Accepted treeDecls res ent [treeTy] (.sym "Number") eq := by
  intro eq heq
  simp only [tsizeEqs, List.mem_cons, List.not_mem_nil, or_false] at heq
  rcases heq with rfl | rfl
  · exact ⟨by simp [Pat.varsAll, Pat.vars], rfl, .const, .const (count_int treeDecls 1)⟩
  · refine ⟨by simp [Pat.varsAll, Pat.vars], rfl, .prim fun e he => ?_, .prim rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact .const
    · refine .prim fun e he => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · refine CallsOK.selfClosed (fun e he => by
          rw [List.mem_singleton] at he
          subst he
          exact .var) (.cons ?_ .nil)
        exact .var ⟨treeTy, .ctor "Node" [.var "l", .var "r"], by simp, by decide, node_fact "l" (.inl rfl)⟩
      · refine CallsOK.selfClosed (fun e he => by
          rw [List.mem_singleton] at he
          subst he
          exact .var) (.cons ?_ .nil)
        exact .var ⟨treeTy, .ctor "Node" [.var "l", .var "r"], by simp, by decide, node_fact "r" (.inr rfl)⟩

abbrev tsizeBody : (List Atom → Multiset Atom) → List Atom → Multiset Atom :=
  fun o => equationsBody env tsizeEqs ⟨o, noCallee⟩

theorem tsizeEqs_eq : ((tsizeEqs : List Equation) : Multiset Equation) =
    (⟨[.const leafA], .const (num 1)⟩ : Equation) ::ₘ
      (⟨[.ctor "Node" [.var "l", .var "r"]],
        .prim "+" [.const (num 1), .prim "+" [.self [.var "l"], .self [.var "r"]]]⟩ : Equation) ::ₘ 0 := rfl

theorem tsize_body_leaf (o : List Atom → Multiset Atom) : tsizeBody o [leafA] = {num 1} := by
  unfold tsizeBody equationsBody
  rw [tsizeEqs_eq, Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
  have m1 : Pat.matchAll [.const leafA] [leafA] = some [] := by decide
  have m2 : Pat.matchAll [.ctor "Node" [.var "l", .var "r"]] [leafA] = none := by decide
  simp only [m1, m2, Expr.eval, add_zero]

theorem tsize_body_node (o : List Atom → Multiset Atom) (l r : Atom) :
    tsizeBody o [nodeA l r] =
      ((o [l]).bind fun a => (o [r]).bind fun b => plus a b).bind (plus (num 1)) := by
  unfold tsizeBody equationsBody
  rw [tsizeEqs_eq, Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
  have m1 : Pat.matchAll [.const leafA] [nodeA l r] = none := by
    simp [Pat.matchAll, Pat.match]
  have m2 : Pat.matchAll [.ctor "Node" [.var "l", .var "r"]] [nodeA l r] =
      some [("l", l), ("r", r)] := by
    simp [Pat.matchAll, Pat.match]
  have ll : List.lookup "l" [("l", l), ("r", r)] = some l := rfl
  have lr : List.lookup "r" [("l", l), ("r", r)] = some r := rfl
  simp only [m1, m2, zero_add, Expr.eval, Expr.evalAll, ll, lr, Multiset.singleton_bind,
    Multiset.map_singleton, Multiset.bind_map, Multiset.bind_assoc]
  simp [env, ops]

/-- `tsize`'s version on the full tree of depth `k`: `2^(k+1) - 1`. -/
theorem tsize_version : ∀ k m : ℕ,
    versionRun tsizeBody (k + 1 + m) [fullTree k] = {num (2 ^ (k + 1) - 1)}
  | 0, m => by
      rw [show 0 + 1 + m = m + 1 by omega]
      exact tsize_body_leaf _
  | k + 1, m => by
      rw [show k + 1 + 1 + m = (k + 1 + m) + 1 by omega]
      show tsizeBody (versionRun tsizeBody (k + 1 + m)) [nodeA (fullTree k) (fullTree k)] = _
      rw [tsize_body_node, tsize_version k m]
      simp only [Multiset.singleton_bind, plus]
      congr 3
      ring

/-- A call to itself at the argument less one. -/
abbrev predCall : Expr := .self [.prim "-" [.var "n", .const (num 1)]]

/-- `(= (mk $n) (if (== $n 0) Leaf (Node (mk (- $n 1)) (mk (- $n 1)))))`. -/
def mkEqs : List Equation :=
  [⟨[.var "n"], .ifE (.prim "==" [.var "n", .const (num 0)]) (.const leafA) (.ctor "Node" [predCall, predCall])⟩]

/-- **`mk` is accepted, its structural range proved**: `Leaf` is a `Tree`, and so is a
`Node` of two calls to itself. -/
theorem mk_accepted (res : String → Ty Empty) (ent : String → List (Ty Empty)) :
    ∀ eq ∈ mkEqs, Accepted treeDecls res ent [.sym "Number"] treeTy eq := by
  intro eq heq
  simp only [mkEqs, List.mem_singleton] at heq
  subst heq
  have predOK : CallsOK treeDecls res ent (eqFacts treeDecls [.sym "Number"]
      ⟨[.var "n"], .ifE (.prim "==" [.var "n", .const (num 0)]) (.const leafA)
        (.ctor "Node" [predCall, predCall])⟩) treeTy ([.sym "Number"].map Ty.lift) predCall := by
    refine CallsOK.selfClosed (fun e he => ?_) (.cons (.prim rfl) .nil)
    rw [List.mem_singleton] at he
    subst he
    refine .prim fun e he => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact .var
    · exact .const
  refine ⟨by simp [Pat.varsAll, Pat.vars], rfl, .ifE (.prim fun e he => ?_) .const (.ctor fun e he => ?_), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact .var
    · exact .const
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> exact predOK
  · have fields : ∀ q ∈ List.zip ([.sym "Tree", .sym "Tree"] : List (Ty String)) [predCall, predCall],
        q = ((.sym "Tree" : Ty String), predCall) := by
      intro q hq
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> rfl
    refine .ifE (.const leaf_tree) ?_
    exact HasType.ctor (σ := fun _ => default) node_row node_constructor rfl
      (fun q hq _ => by rw [fields q hq]; simp [MetaName])
      (fun q hq _ => by rw [fields q hq]; exact .self)

abbrev mkBody : (List Atom → Multiset Atom) → List Atom → Multiset Atom :=
  fun o => equationsBody env mkEqs ⟨o, noCallee⟩

theorem mk_body (o : List Atom → Multiset Atom) (n : ℤ) :
    mkBody o [num n] = if n = 0 then {leafA} else
      (o [num (n - 1)]).bind fun a => (o [num (n - 1)]).map fun b => nodeA a b := by
  unfold mkBody equationsBody
  rw [show ((mkEqs : List Equation) : Multiset Equation) =
    (⟨[.var "n"], .ifE (.prim "==" [.var "n", .const (num 0)]) (.const leafA)
      (.ctor "Node" [predCall, predCall])⟩ : Equation) ::ₘ 0 from rfl,
    Multiset.cons_bind, Multiset.zero_bind, add_zero]
  have m1 : Pat.matchAll [.var "n"] [num n] = some [("n", num n)] := by
    simp [Pat.matchAll, Pat.match]
  have ln : List.lookup "n" [("n", num n)] = some (num n) := rfl
  simp only [m1, Expr.eval, Expr.evalAll, ln, Multiset.singleton_bind, Multiset.map_singleton,
    Multiset.bind_assoc]
  by_cases hn : n = 0
  · subst hn
    simp [env, ops, numEq, truth]
  · simp [env, ops, numEq, minus, truth, hn, Multiset.map_bind, Multiset.bind_singleton, Multiset.map_map]

/-- `mk`'s version at `k`: the full tree of depth `k`, once. -/
theorem mk_version : ∀ k m : ℕ, versionRun mkBody (k + 1 + m) [num k] = {fullTree k}
  | 0, m => by
      rw [show 0 + 1 + m = m + 1 by omega]
      show mkBody (versionRun mkBody m) [num 0] = _
      rw [mk_body, if_pos rfl]
      rfl
  | k + 1, m => by
      rw [show k + 1 + 1 + m = (k + 1 + m) + 1 by omega]
      show mkBody (versionRun mkBody (k + 1 + m)) [num ((k + 1 : ℕ) : ℤ)] = _
      rw [mk_body, if_neg (by omega), show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring,
        mk_version k m]
      simp [fullTree]

theorem tsize_hyps (grounded : String → Bool) :
    VersionHyps (Γ := treeDecls) (grounded := grounded) tsizeBody tsizeBody [treeTy] (.sym "Number") :=
  accepted_versionHyps (res := noRes) (ent := noEnt) treeDecls_functional number_guarded
    (tsize_accepted _ _) (env_ok grounded noRes) noCallee noCallee (fun _ _ _ => rfl)
    (fun _ _ _ r hr => absurd hr (Multiset.notMem_zero r))

theorem mk_hyps (grounded : String → Bool) :
    VersionHyps (Γ := treeDecls) (grounded := grounded) mkBody mkBody [.sym "Number"] treeTy :=
  accepted_versionHyps (res := noRes) (ent := noEnt) treeDecls_functional tree_guarded
    (mk_accepted _ _) (env_ok grounded noRes) noCallee noCallee (fun _ _ _ => rfl)
    (fun _ _ _ r hr => absurd hr (Multiset.notMem_zero r))

/-- **`(tsize (mk 6))` answers `127`** (`prepared_structural_types`): `(mk 6)` is
accepted and runs its version, the full tree, unchecked at its structural range;
`tsize` checks that tree once at `Tree`, through the walk, and runs its version.
The protocol, every call checked, answers the same. -/
theorem tsize_mk (grounded : String → Bool) :
    ((structuralRun treeDecls grounded mkBody mkBody [.sym "Number"] treeTy 7 [num 6]).bind fun t =>
        structuralRun treeDecls grounded tsizeBody tsizeBody [treeTy] (.sym "Number") 7 [t]) = {num 127} ∧
      ((protocolRun treeDecls grounded mkBody mkRow 7 [num 6]).bind fun t =>
        protocolRun treeDecls grounded tsizeBody tsizeRow 7 [t]) = {num 127} := by
  have hmk : versionRun mkBody 7 [num 6] = {fullTree 6} := by simpa using mk_version 6 0
  have hts : versionRun tsizeBody 7 [fullTree 6] = {num 127} := by simpa using tsize_version 6 0
  have mkAcc : MachineAccepts treeDecls [.sym "Number"] [num 6] :=
    .cons (.inl ⟨"Number", rfl, .inl rfl, rfl⟩) .nil
  have treeAcc : MachineAccepts treeDecls [treeTy] [fullTree 6] :=
    .cons (.inr (.inl ⟨tree_structural, walk_count (walk_fullTree 6)⟩)) .nil
  have machine : ((structuralRun treeDecls grounded mkBody mkBody [.sym "Number"] treeTy 7 [num 6]).bind
      fun t => structuralRun treeDecls grounded tsizeBody tsizeBody [treeTy] (.sym "Number") 7 [t]) =
        {num 127} := by
    rw [structuralRun, if_pos mkAcc, hmk, Multiset.singleton_bind, structuralRun, if_pos treeAcc, hts]
  refine ⟨machine, ?_⟩
  rw [← structuralRun_oracle (mk_hyps grounded) 7, ← structuralRun_oracle (tsize_hyps grounded) 7]
  exact machine

/-- **A node of numbers answers nothing** (`(tsize (Node 1 2))`): the machine's check
fails and the call goes to the protocol, whose guard at `Tree` fails. -/
theorem tsize_bad (grounded : String → Bool) (n : ℕ) :
    ¬ MachineAccepts treeDecls [treeTy] [nodeA (num 1) (num 2)] ∧
      structuralRun treeDecls grounded tsizeBody tsizeBody [treeTy] (.sym "Number") (n + 1)
        [nodeA (num 1) (num 2)] = 0 := by
  have bad := tree_bad_rejected (num 1) (num 2) (.inl (num_not_tree 1))
  refine ⟨bad, ?_⟩
  rw [structuralRun, if_neg bad]
  exact tree_protocol_zero grounded _ _ n _ (node_count_zero _ _ (.inl (num_not_tree 1)))

/-- `(= (twice $t) (+ (tsize $t) (tsize $t)))`, untyped: its calls to `tsize`, read
through `o`, come from outside `tsize`. -/
def twiceBody (o : List Atom → Multiset Atom) (t : Atom) : Multiset Atom :=
  (o [t]).bind fun a => (o [t]).bind fun b => plus a b

/-- **A call from another head is checked** (`(twice (Node Leaf Leaf))`, `(twice (Node
Leaf 7))`): through the machine, `twice` answers `6` once on a tree, and nothing on
a node holding `7`, whose check fails; the protocol answers the same. -/
theorem twice_checked (grounded : String → Bool) :
    twiceBody (structuralRun treeDecls grounded tsizeBody tsizeBody [treeTy] (.sym "Number") 3)
        (nodeA leafA leafA) = {num 6} ∧
      twiceBody (structuralRun treeDecls grounded tsizeBody tsizeBody [treeTy] (.sym "Number") 3)
        (nodeA leafA (num 7)) = 0 ∧
      structuralRun treeDecls grounded tsizeBody tsizeBody [treeTy] (.sym "Number") 3 =
        protocolRun treeDecls grounded tsizeBody tsizeRow 3 := by
  have treeAcc : MachineAccepts treeDecls [treeTy] [fullTree 1] :=
    .cons (.inr (.inl ⟨tree_structural, walk_count (walk_fullTree 1)⟩)) .nil
  have three : versionRun tsizeBody 3 [fullTree 1] = {num 3} := by simpa using tsize_version 1 1
  have bad := node_count_zero leafA (num 7) (.inr (num_not_tree 7))
  refine ⟨?_, ?_, structuralRun_oracle (tsize_hyps grounded) 3⟩
  · show ((structuralRun treeDecls grounded tsizeBody tsizeBody [treeTy] (.sym "Number") 3
      [fullTree 1]).bind fun a => (structuralRun treeDecls grounded tsizeBody tsizeBody [treeTy]
        (.sym "Number") 3 [fullTree 1]).bind fun b => plus a b) = _
    rw [structuralRun, if_pos treeAcc, three]
    simp [plus]
  · unfold twiceBody
    rw [structuralRun, if_neg (tree_bad_rejected _ _ (.inr (num_not_tree 7))),
      tree_protocol_zero grounded _ _ 2 _ bad, Multiset.zero_bind]

/-- `(= (tag $t) 1)` at `(: tag (-> Tree Number))`. -/
def tagEqs : List Equation := [⟨[.var "t"], .const (num 1)⟩]

abbrev tagBody : (List Atom → Multiset Atom) → List Atom → Multiset Atom :=
  fun o => equationsBody env tagEqs ⟨o, noCallee⟩

theorem tag_body (o : List Atom → Multiset Atom) (v : Atom) : tagBody o [v] = {num 1} := by
  unfold tagBody equationsBody
  rw [show ((tagEqs : List Equation) : Multiset Equation) =
    (⟨[.var "t"], .const (num 1)⟩ : Equation) ::ₘ 0 from rfl, Multiset.cons_bind, Multiset.zero_bind,
    add_zero]
  have m1 : Pat.matchAll [.var "t"] [v] = some [("t", v)] := by
    simp [Pat.matchAll, Pat.match]
  simp only [m1, Expr.eval]

theorem tag_accepted (res : String → Ty Empty) (ent : String → List (Ty Empty)) :
    ∀ eq ∈ tagEqs, Accepted treeDecls res ent [treeTy] (.sym "Number") eq := by
  intro eq heq
  simp only [tagEqs, List.mem_singleton] at heq
  subst heq
  exact ⟨by simp [Pat.varsAll, Pat.vars], rfl, .const, .const (count_int treeDecls 1)⟩

/-- **The check at a call from outside is needed**: `tag`'s version answers `1` on
`(Node 1 2)`, which is no `Tree`, where the protocol answers nothing; the machine
checks the argument, declines, and answers nothing. -/
theorem tag_needs_check (grounded : String → Bool) :
    versionRun tagBody 1 [nodeA (num 1) (num 2)] = {num 1} ∧
      protocolRun treeDecls grounded tagBody tsizeRow 1 [nodeA (num 1) (num 2)] = 0 ∧
      structuralRun treeDecls grounded tagBody tagBody [treeTy] (.sym "Number") 1
        [nodeA (num 1) (num 2)] = 0 := by
  have bad := node_count_zero (num 1) (num 2) (.inl (num_not_tree 1))
  refine ⟨tag_body _ _, tree_protocol_zero grounded _ _ 0 _ bad, ?_⟩
  rw [structuralRun, if_neg (tree_bad_rejected _ _ (.inl (num_not_tree 1)))]
  exact tree_protocol_zero grounded _ _ 0 _ bad

/-- `(= (mkbad $n) (if (== $n 0) Leaf 5))`. -/
def mkbadEqs : List Equation :=
  [⟨[.var "n"], .ifE (.prim "==" [.var "n", .const (num 0)]) (.const leafA) (.const (num 5))⟩]

abbrev mkbadBody : (List Atom → Multiset Atom) → List Atom → Multiset Atom :=
  fun o => equationsBody env mkbadEqs ⟨o, noCallee⟩

theorem mkbad_body (o : List Atom → Multiset Atom) (n : ℤ) :
    mkbadBody o [num n] = if n = 0 then {leafA} else {num 5} := by
  unfold mkbadBody equationsBody
  rw [show ((mkbadEqs : List Equation) : Multiset Equation) =
    (⟨[.var "n"], .ifE (.prim "==" [.var "n", .const (num 0)]) (.const leafA) (.const (num 5))⟩ :
      Equation) ::ₘ 0 from rfl, Multiset.cons_bind, Multiset.zero_bind, add_zero]
  have m1 : Pat.matchAll [.var "n"] [num n] = some [("n", num n)] := by
    simp [Pat.matchAll, Pat.match]
  have ln : List.lookup "n" [("n", num n)] = some (num n) := rfl
  simp only [m1, Expr.eval, Expr.evalAll, ln, Multiset.singleton_bind, Multiset.map_singleton]
  by_cases hn : n = 0
  · subst hn
    simp [env, ops, numEq, truth]
  · simp [env, ops, numEq, truth, hn]

/-- **A structural range no version proves is not admitted** (`mkbad`): `5` is no
`Tree`, so the analysis does not accept the equation at the range `Tree`. -/
theorem mkbad_not_accepted (res : String → Ty Empty) (ent : String → List (Ty Empty)) :
    ¬ ∀ eq ∈ mkbadEqs, Accepted treeDecls res ent [.sym "Number"] treeTy eq := by
  intro h
  have acc := h _ (List.mem_singleton_self _)
  have hres := acc.result
  cases hres with
  | ifE _ he =>
      cases he with
      | const hc =>
          rw [num_not_tree] at hc
          exact absurd hc (by decide)

/-- **`mkbad` keeps its range check**: unchecked, `(mkbad 1)` would answer `5`; its
protocol answers nothing there and `Leaf` at `0`, so `(tsize (mkbad 0))` answers `1`
and `(tsize (mkbad 1))` nothing. -/
theorem mkbad_answers (grounded : String → Bool) :
    versionRun mkbadBody 1 [num 1] = {num 5} ∧
      protocolRun treeDecls grounded mkbadBody mkRow 1 [num 1] = 0 ∧
      protocolRun treeDecls grounded mkbadBody mkRow 1 [num 0] = {leafA} ∧
      ((protocolRun treeDecls grounded mkbadBody mkRow 1 [num 0]).bind fun t =>
        structuralRun treeDecls grounded tsizeBody tsizeBody [treeTy] (.sym "Number") 1 [t]) = {num 1} ∧
      ((protocolRun treeDecls grounded mkbadBody mkRow 1 [num 1]).bind fun t =>
        structuralRun treeDecls grounded tsizeBody tsizeBody [treeTy] (.sym "Number") 1 [t]) = 0 := by
  have none1 : protocolRun treeDecls grounded mkbadBody mkRow 1 [num 1] = 0 := by
    simp only [protocolRun]
    rw [chainCall_closed, argCount_number, one_nsmul, mkbad_body, if_neg (by decide)]
    simp only [if_pos tree_guarded, Multiset.singleton_bind]
    rw [guardCount_of_not_meta (by simp [MetaName]), num_not_tree, zero_nsmul]
  have leaf0 : protocolRun treeDecls grounded mkbadBody mkRow 1 [num 0] = {leafA} := by
    simp only [protocolRun]
    rw [chainCall_closed, argCount_number, one_nsmul, mkbad_body, if_pos rfl]
    simp only [if_pos tree_guarded, Multiset.singleton_bind]
    rw [guardCount_of_not_meta (by simp [MetaName]), leaf_tree, one_nsmul]
  have leafAcc : MachineAccepts treeDecls [treeTy] [leafA] :=
    .cons (.inr (.inl ⟨tree_structural, leaf_tree⟩)) .nil
  refine ⟨?_, none1, leaf0, ?_, ?_⟩
  · show mkbadBody (versionRun mkbadBody 0) [num 1] = _
    rw [mkbad_body, if_neg (by decide)]
  · rw [leaf0, Multiset.singleton_bind, structuralRun, if_pos leafAcc]
    exact tsize_version 0 0
  · rw [none1, Multiset.zero_bind]

/-! ### A parameter the protocol does not check -/

/-- `%Undefined%`. -/
abbrev undefTy : Ty Empty := .sym "%Undefined%"

/-- **An unchecked parameter asks nothing**: a number meets the entry fact at
`%Undefined%`, though the relation does not type it there. -/
theorem unchecked_entry (grounded : String → Bool) :
    EntryFacts treeDecls grounded [undefTy] [num 5] ∧ ¬ Holds treeDecls grounded (num 5) undefTy := by
  refine ⟨.cons (fun hg => absurd hg (by decide)) .nil, fun h => ?_⟩
  have := h.count (by simp [MetaName])
  rw [count_class treeDecls (g := .int 5) rfl] at this
  exact absurd this (by decide)

/-- `(= (tagged Leaf $w) 1)` and `(= (tagged (Node $l $r) $w) (+ (tagged $l $w) (tagged $r $w)))`. -/
def taggedEqs : List Equation :=
  [⟨[.const leafA, .var "w"], .const (num 1)⟩,
   ⟨[.ctor "Node" [.var "l", .var "r"], .var "w"],
     .prim "+" [.self [.var "l", .var "w"], .self [.var "r", .var "w"]]⟩]

/-- **`tagged` is accepted**: its calls to itself meet `Tree` at the tree and are
asked nothing at `%Undefined%`, where `$w` has no fact. -/
theorem tagged_accepted (res : String → Ty Empty) (ent : String → List (Ty Empty)) :
    ∀ eq ∈ taggedEqs, Accepted treeDecls res ent [treeTy, undefTy] (.sym "Number") eq := by
  intro eq heq
  simp only [taggedEqs, List.mem_cons, List.not_mem_nil, or_false] at heq
  rcases heq with rfl | rfl
  · exact ⟨by simp [Pat.varsAll, Pat.vars], rfl, .const, .const (count_int treeDecls 1)⟩
  · refine ⟨by simp [Pat.varsAll, Pat.vars], rfl, .prim fun e he => ?_, .prim rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    have args : ∀ y ∈ ["l", "r"], CallsOK treeDecls res ent
        (eqFacts treeDecls [treeTy, undefTy] ⟨[.ctor "Node" [.var "l", .var "r"], .var "w"],
          .prim "+" [.self [.var "l", .var "w"], .self [.var "r", .var "w"]]⟩)
        (.sym "Number") ([treeTy, undefTy].map Ty.lift) (.self [.var y, .var "w"]) := by
      intro y hy
      refine CallsOK.selfGuarded (fun e he => ?_) (.cons (fun _ => .var ⟨treeTy, .ctor "Node" [.var "l", .var "r"],
        by simp, by decide, node_fact y (by simpa using hy)⟩) (.cons (fun hg => absurd hg (by decide)) .nil))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact .var
    rcases he with rfl | rfl
    · exact args "l" (by simp)
    · exact args "r" (by simp)

abbrev taggedBody : (List Atom → Multiset Atom) → List Atom → Multiset Atom :=
  fun o => equationsBody env taggedEqs ⟨o, noCallee⟩

theorem taggedEqs_eq : ((taggedEqs : List Equation) : Multiset Equation) =
    (⟨[.const leafA, .var "w"], .const (num 1)⟩ : Equation) ::ₘ
      (⟨[.ctor "Node" [.var "l", .var "r"], .var "w"],
        .prim "+" [.self [.var "l", .var "w"], .self [.var "r", .var "w"]]⟩ : Equation) ::ₘ 0 := rfl

theorem tagged_body_leaf (o : List Atom → Multiset Atom) (w : Atom) : taggedBody o [leafA, w] = {num 1} := by
  unfold taggedBody equationsBody
  rw [taggedEqs_eq, Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
  have m1 : Pat.matchAll [.const leafA, .var "w"] [leafA, w] = some [("w", w)] := by
    simp [Pat.matchAll, Pat.match]
  have m2 : Pat.matchAll [.ctor "Node" [.var "l", .var "r"], .var "w"] [leafA, w] = none := by
    simp [Pat.matchAll, Pat.match]
  simp only [m1, m2, Expr.eval, add_zero]

theorem tagged_body_node (o : List Atom → Multiset Atom) (l r w : Atom) :
    taggedBody o [nodeA l r, w] = (o [l, w]).bind fun a => (o [r, w]).bind fun b => plus a b := by
  unfold taggedBody equationsBody
  rw [taggedEqs_eq, Multiset.cons_bind, Multiset.cons_bind, Multiset.zero_bind, add_zero]
  have m1 : Pat.matchAll [.const leafA, .var "w"] [nodeA l r, w] = none := by
    simp [Pat.matchAll, Pat.match]
  have m2 : Pat.matchAll [.ctor "Node" [.var "l", .var "r"], .var "w"] [nodeA l r, w] =
      some [("l", l), ("r", r), ("w", w)] := by
    simp [Pat.matchAll, Pat.match]
  have ll : List.lookup "l" [("l", l), ("r", r), ("w", w)] = some l := rfl
  have lr : List.lookup "r" [("l", l), ("r", r), ("w", w)] = some r := rfl
  have lw : List.lookup "w" [("l", l), ("r", r), ("w", w)] = some w := rfl
  simp only [m1, m2, zero_add, Expr.eval, Expr.evalAll, ll, lr, lw, Multiset.singleton_bind,
    Multiset.map_singleton, Multiset.bind_map, Multiset.bind_assoc]
  simp [env, ops]

/-- `tagged`'s version on the full tree of depth `k`, whatever the second
argument: its `2^k` leaves. -/
theorem tagged_version : ∀ k m : ℕ, ∀ w : Atom,
    versionRun taggedBody (k + 1 + m) [fullTree k, w] = {num (2 ^ k)}
  | 0, m, w => by
      rw [show 0 + 1 + m = m + 1 by omega]
      exact tagged_body_leaf _ _
  | k + 1, m, w => by
      rw [show k + 1 + 1 + m = (k + 1 + m) + 1 by omega]
      show taggedBody (versionRun taggedBody (k + 1 + m)) [nodeA (fullTree k) (fullTree k), w] = _
      rw [tagged_body_node, tagged_version k m w]
      simp only [Multiset.singleton_bind, plus]
      congr 3
      ring

theorem tagged_hyps (grounded : String → Bool) :
    VersionHyps (Γ := treeDecls) (grounded := grounded) taggedBody taggedBody [treeTy, undefTy]
      (.sym "Number") :=
  accepted_versionHyps (res := noRes) (ent := noEnt) treeDecls_functional number_guarded
    (tagged_accepted _ _) (env_ok grounded noRes) noCallee noCallee (fun _ _ _ => rfl)
    (fun _ _ _ r hr => absurd hr (Multiset.notMem_zero r))

abbrev taggedRow : Ty String := arrow ([treeTy, undefTy].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift

/-- **A `%Undefined%` position beside a structural one** (`(tagged (mk 3) anything)`):
the machine checks the tree at `Tree` and nothing at `%Undefined%`, runs the version,
and answers `8` once, as the protocol does. -/
theorem tagged_mk (grounded : String → Bool) :
    ((structuralRun treeDecls grounded mkBody mkBody [.sym "Number"] treeTy 4 [num 3]).bind fun t =>
        structuralRun treeDecls grounded taggedBody taggedBody [treeTy, undefTy] (.sym "Number") 4
          [t, sym "anything"]) = {num 8} ∧
      ((protocolRun treeDecls grounded mkBody mkRow 4 [num 3]).bind fun t =>
        protocolRun treeDecls grounded taggedBody taggedRow 4 [t, sym "anything"]) = {num 8} := by
  have hmk : versionRun mkBody 4 [num 3] = {fullTree 3} := by simpa using mk_version 3 0
  have htg : versionRun taggedBody 4 [fullTree 3, sym "anything"] = {num 8} := by
    simpa using tagged_version 3 0 (sym "anything")
  have mkAcc : MachineAccepts treeDecls [.sym "Number"] [num 3] :=
    .cons (.inl ⟨"Number", rfl, .inl rfl, rfl⟩) .nil
  have treeAcc : MachineAccepts treeDecls [treeTy, undefTy] [fullTree 3, sym "anything"] :=
    .cons (.inr (.inl ⟨tree_structural, walk_count (walk_fullTree 3)⟩)) (.cons (.inr (.inr (by decide))) .nil)
  have machine : ((structuralRun treeDecls grounded mkBody mkBody [.sym "Number"] treeTy 4 [num 3]).bind
      fun t => structuralRun treeDecls grounded taggedBody taggedBody [treeTy, undefTy] (.sym "Number") 4
        [t, sym "anything"]) = {num 8} := by
    rw [structuralRun, if_pos mkAcc, hmk, Multiset.singleton_bind, structuralRun, if_pos treeAcc, htg]
  refine ⟨machine, ?_⟩
  rw [← structuralRun_oracle (mk_hyps grounded) 4, ← structuralRun_oracle (tagged_hyps grounded) 4]
  exact machine

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls
