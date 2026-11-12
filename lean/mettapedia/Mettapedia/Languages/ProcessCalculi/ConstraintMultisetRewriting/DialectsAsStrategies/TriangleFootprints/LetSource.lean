import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.LetPlain

/-!
# HE's `let` with a variable pattern: every derivation publishes the template's answers

HE's `let` is `(= (let $pattern $atom $template) (unify $atom $pattern $template Empty))` with
`(: let (-> Atom %Undefined% Atom %Undefined%))`; `unify` is the minimal instruction declared
`(-> Atom Atom Atom Atom %Undefined%)`. This module assembles the whole source path of
`(let $x d b)`, from HE's completed relation at a frame with empty bindings (HE's entry is one), for a
data value `d` and a template `b` whose one variable is `x`:

1. admission of `let`'s closed arrow on the open arguments `$x`, `d`, `b`
   (`LetPlain.wildcard_selection`): one activation with the frame's bindings;
2. the operator's cast against its arrow, the delivery of `$x` and `b` under `Atom` and the cast of
   `d` under `%Undefined%` (`cast_keeps`): the call value is the plain value of `(let $x d b)`;
3. the query of `let`'s row (`let_frontier_fresh`): one work, whose fresh names are outside the call;
4. the producer and return boundaries, then the evaluation of the body read at the work's frame;
5. admission of `unify`'s closed arrow on the read arguments (a data atom, a variable, a variable or
   expression, and `Empty`, by the models of the work's bindings), the deliveries under `Atom`;
6. the embedded invocation of `unify` (`unify_minimal_source`): the failure branch is ruled out,
   since a model of the work's bindings solves `$x = d` (`solvable`), so every derivation takes the
   success rule, at a candidate frame with a plain environment;
7. the evaluation of the then-branch read at the candidate frame: it is the plain value of the
   template's instance `b[x := d]` (`read_forced`, `LetPlain.read_plain`), whose derivations are
   determined by hypothesis (the instance contract), and the publications above it.

`let_source`: **every derivation publishes the answers of `b[x := d]`**. The instance contract is
met by the settling class with `if` nodes (`LetEveryRun`).

## Controls

* `Controls.instance_five` (positive): the instance of `(pair $x $x)` at `5` is `(pair 5 5)`.
* `Controls.var_not_solvable` (negative, `solvable` has content): bindings that hold `$x := 7` have no
  model sending `x` to `5`; there the failure branch of `unify` applies and `let` publishes nothing.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace LetSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel
  UnifyCandidateRel UnifyNoMatchRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (TypeBindingSatisfied
  applyTypeValuation renameTypeVars)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (MatchRel MatchListAccRel MergeRel
  equalityGroundedSemantic AtomOccurs)
open ServiceFootprints EntryToQuery AnswerBags EveryRun
open LetPlain (Plain PlainEnv letArrow unifyArrow)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-! ## The program, the call and the instance -/

/-- `(let $x a b)`. -/
abbrev letCall (x : String) (a b : Atom) : Atom := .expression [.symbol "let", .var x, a, b]

/-- `(unify $a $p $t Empty)` with the names of a fresh copy of `let`'s row. -/
abbrev unifyBody (a p t : String) : Atom :=
  .expression [.symbol "unify", .var a, .var p, .var t, Atom.empty]

/-- **The instance of a template whose one variable `x` is bound to `d`.** -/
def inst (x : String) (d b : Atom) : Atom :=
  applyTypeValuation (fun y => if y = x then d else .var y) b

/-- **A program carrying HE's `let`**: `let`'s two stdlib declarations and its row, followed by rows
with no other `let` equation of arity three; `let` and `unify` keep their arrows, `Empty` is
undeclared, and no expression is declared. -/
structure LetProgram (atoms : List Atom) : Prop where
  rows : ∃ rest, atoms = LetFrontier.letRows ++ rest ∧ ∀ row ∈ rest, LetFrontier.Foreign "let" 3 row
  letTypes : StorageTypesRel (Space.ofList atoms) (.symbol "let") [letArrow]
  unifyTypes : StorageTypesRel (Space.ofList atoms) (.symbol "unify") [unifyArrow]
  emptyTypes : StorageTypesRel (Space.ofList atoms) Atom.empty [Atom.undefinedType]
  exprTypes : ∀ (head : Atom) (tail : List Atom),
    StorageTypesRel (Space.ofList atoms) (.expression (head :: tail)) [Atom.undefinedType]

/-- **The parts of `(let $x d b)`**: a data value with one closed stored type, and a template that is
an expression whose only variable is `x`. -/
structure LetCall (atoms : List Atom) (x : String) (d b : Atom) : Prop where
  data : DataAtom d
  typed : ∃ T, StorageTypesRel (Space.ofList atoms) d [T] ∧ TypeSubst.typeVars T = []
  onlyX : ∀ y ∈ TypeSubst.typeVars b, y = x
  expression : ∃ h t, b = .expression (h :: t)

/-- **The instance contract**: the facts of a body, answerable answers, and determinism of HE's
completed relation on the scoped lookup at every frame. -/
structure InstanceSource (dispatch : GroundedDispatch) (policy : Policy) (atoms : List Atom)
    (t : Atom) (L : List Atom) : Prop where
  facts : BodyFacts t
  clean : ∀ a ∈ L, Answerable a
  determined : DeterminedUnder dispatch Completed.scopedLookup policy atoms t L

/-! ## Models of a template with one variable -/

theorem inst_of_model {x : String} {d b : Atom} (onlyX : ∀ y ∈ TypeSubst.typeVars b, y = x)
    {v : String → Atom} (vx : v x = d) : applyTypeValuation v b = inst x d b := by
  unfold inst
  apply Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.applyTypeValuation_congr_of_typeVars
  intro y member
  rw [onlyX y member, vx]
  simp

theorem fixed_of_model {x : String} {b : Atom} (onlyX : ∀ y ∈ TypeSubst.typeVars b, y = x)
    {v : String → Atom} (vx : v x = .var x) : applyTypeValuation v b = b := by
  have same : applyTypeValuation v b = applyTypeValuation (fun name => .var name) b := by
    apply Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.applyTypeValuation_congr_of_typeVars
    intro y member
    rw [onlyX y member, vx]
  rw [same, Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Theory.applyTypeValuation_var_identity]

theorem ground_apply {d : Atom} (data : DataAtom d) (v : String → Atom) : applyTypeValuation v d = d := by
  cases data <;> simp [applyTypeValuation]

/-- A valuation keeps `Empty` and error heads, so an atom some valuation sends to a term that is
neither is neither. -/
theorem not_stopped_of_apply {e c : Atom} {m : String → Atom} (sees : applyTypeValuation m e = c)
    (notStopped : ¬ IsEmptyOrErrorRel c) : ¬ IsEmptyOrErrorRel e := by
  rintro (same | ⟨tail, same⟩)
  · subst same
    apply notStopped
    left
    simpa [applyTypeValuation, Atom.empty] using sees.symm
  · subst same
    apply notStopped
    right
    exact ⟨_, by simpa [applyTypeValuation] using sees.symm⟩

theorem var_not_stopped (z : String) : ¬ IsEmptyOrErrorRel (.var z) := by
  rintro (same | ⟨tail, same⟩)
  · simp [Atom.empty] at same
  · cases same

/-- An atom every model of a record sends where `x` goes, at a record with a model fixing `x`, is a
variable. -/
theorem var_of_sees {e : Atom} {x : String} {m : String → Atom} (mx : m x = .var x)
    (sees : applyTypeValuation m e = m x) : ∃ z, e = .var z := by
  rw [mx] at sees
  cases e with
  | var z => exact ⟨z, rfl⟩
  | symbol _ => simp [applyTypeValuation] at sees
  | grounded _ => simp [applyTypeValuation] at sees
  | expression _ => simp [applyTypeValuation] at sees

/-- An atom some model sends to a nonempty expression is a variable or a nonempty expression. -/
theorem var_or_expression {e h : Atom} {t : List Atom} {m : String → Atom}
    (sees : applyTypeValuation m e = .expression (h :: t)) :
    (∃ z, e = .var z) ∨ ∃ h' t', e = .expression (h' :: t') := by
  cases e with
  | var z => exact Or.inl ⟨z, rfl⟩
  | symbol _ => simp [applyTypeValuation] at sees
  | grounded _ => simp [applyTypeValuation] at sees
  | expression items =>
      cases items with
      | nil => simp [applyTypeValuation] at sees
      | cons h' t' => exact Or.inr ⟨h', t', rfl⟩

/-! ## Reads -/

theorem read_erase_of_empty (policy : Policy) (frame : Frame)
    (empty : frame.bindings = Bindings.empty) (v : Entry.Value) :
    (frame.read policy v).erase = v.erase := by
  have model : TypeBindingSatisfied (fun name => .var name) frame.bindings := by
    rw [empty]
    simp [TypeBindingSatisfied, Bindings.empty]
  have same := LetFrontier.read_sound policy frame v model
  simpa only [Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Theory.applyTypeValuation_var_identity]
    using same

/-- **At a frame with empty bindings and a plain environment, the plain value of an atom reads as
itself.** -/
theorem read_ofAtom_of_empty (policy : Policy) (frame : Frame)
    (empty : frame.bindings = Bindings.empty) (plainEnv : PlainEnv frame.environment) (t : Atom) :
    frame.read policy (Entry.Value.ofAtom t) = Entry.Value.ofAtom t := by
  have plain := LetPlain.read_plain policy frame plainEnv (LetPlain.plain_ofAtom t)
  rw [plain, read_erase_of_empty policy frame empty, Entry.Value.erase_ofAtom]

theorem read_active (policy : Policy) (frame : Frame) (children : List Entry.Value) :
    frame.read policy (.expression .active children) =
      .expression .active (children.map (frame.read policy)) := by
  simp only [Completed.Frame.read, Entry.Value.substitute, LetPlain.rebuildStatus_active]
  rfl

theorem read_symbol (policy : Policy) (frame : Frame) (name : String) :
    frame.read policy (.symbol name) = .symbol name := by
  simp [Completed.Frame.read, Entry.Value.substitute]

/-- Every model of a frame sees a read of a read as the value itself. -/
theorem read_read_sound (policy : Policy) (frame : Frame) (u : Entry.Value) {v : String → Atom}
    (model : TypeBindingSatisfied v frame.bindings) :
    applyTypeValuation v (frame.read policy (frame.read policy u)).erase =
      applyTypeValuation v u.erase := by
  rw [LetFrontier.read_sound policy frame _ model, LetFrontier.read_sound policy frame _ model]

/-! ## Casts that keep the frame's bindings -/

theorem singleton_append {T actual : Atom} {earlier later : List Atom}
    (same : [T] = earlier ++ actual :: later) : actual = T := by
  cases earlier with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at same
      exact same.1.symm
  | cons e es =>
      simp only [List.cons_append, List.cons.injEq] at same
      simp at same

/-- **A data atom's cast under a demand that keeps the bindings**: one result, the atom, at a frame
with the same bindings and a plain environment when the frame's is. -/
theorem cast_keeps {space : Space} {live : List Atom} {scope : List String} {a expected T : Atom}
    (data : DataAtom a) (entry : Entry.Rel policy.reentry .active a expected .cast)
    (stored : StorageTypesRel space a [T]) (closedT : TypeSubst.typeVars T = [])
    (keeps : ∀ {b out : Bindings}, TypeMatchRel expected T b out → out = b)
    (accepts : ∀ frame : Frame, ∃ output, policy.matching.Rel expected T frame.bindings output)
    {frame : Frame} {results : List Result}
    (derived : Completed.AtomRel space dispatch Completed.scopedLookup live scope
      (Entry.Value.ofAtom a) expected frame results (policy := policy)) :
    ∃ after : Frame, results = [(Entry.Value.ofAtom a, after)] ∧ after.bindings = frame.bindings ∧
      (PlainEnv frame.environment → PlainEnv after.environment) := by
  have entry' : Entry.Rel policy.reentry (frame.read policy (Entry.Value.ofAtom a)).status
      (frame.read policy (Entry.Value.ofAtom a)).erase expected .cast := by
    simp only [CompleteRun.read_data policy frame data, Entry.Value.erase_ofAtom, data.status]
    exact entry
  cases derived with
  | delivered entered => cases Entry.functional entered entry'
  | cast _ batch related =>
      rw [CompleteRun.read_data policy frame data, Entry.Value.erase_ofAtom] at batch related
      cases batch with
      | success _ _ _ _ =>
          obtain ⟨r, rs, first, rest, rfl⟩ := List.forall₂_cons_left_iff.mp related
          obtain rfl := List.forall₂_nil_left_iff.mp rest
          obtain ⟨rv, rf⟩ := r
          have value : rv = Entry.Value.ofAtom a := by
            have payload := first.payload
            split at payload <;> exact payload
          subst value
          have renewed := first.renewed
          refine ⟨rf, rfl, ?_, fun plain => LetPlain.castRenew_plain renewed plain⟩
          cases renewed with
          | same => rfl
          | matched queried selected _ matched _ =>
              rw [Entry.Value.erase_ofAtom] at queried
              have types := ScopedIf.scoped_closed_answer stored closedT queried
              subst types
              obtain rfl := singleton_append selected
              exact keeps matched.source
      | failure queried rejected =>
          obtain ⟨output, matched⟩ := accepts frame
          have types := ScopedIf.scoped_closed_answer stored closedT queried
          subst types
          exact (rejected T List.mem_cons_self output matched).elim
  | tuple entered => cases Entry.functional entered entry'
  | function entered => cases Entry.functional entered entry'
  | fallback entered => cases Entry.functional entered entry'
  | selectionFailed entered => cases Entry.functional entered entry'

theorem match_symbol_symbol {n : String} {m : Bindings}
    (matched : MatchRel equalityGroundedSemantic (.symbol n) (.symbol n) m) : m = Bindings.empty := by
  cases matched with
  | symSym => rfl

theorem matchList_symbols_out : ∀ (ns : List String) {seed out : Bindings},
    MatchListAccRel equalityGroundedSemantic (ns.map Atom.symbol) (ns.map Atom.symbol) seed out →
      out = seed
  | [], _, _, matched => by cases matched; rfl
  | n :: ns, _, _, matched => by
      simp only [List.map_cons] at matched
      cases matched with
      | cons head merged rest =>
          obtain rfl := match_symbol_symbol head
          obtain rfl := IfEveryRun.merge_empty_out merged
          exact matchList_symbols_out ns rest

/-- **Every match of an expression of symbols with itself keeps the bindings.** -/
theorem symbols_keeps (ns : List String) {b out : Bindings}
    (matched : TypeMatchRel (.expression (ns.map Atom.symbol)) (.expression (ns.map Atom.symbol)) b out) :
    out = b := by
  generalize same : Atom.expression (ns.map Atom.symbol) = A at matched
  cases matched with
  | undefinedLeft => rfl
  | atomLeft => rfl
  | undefinedRight => rfl
  | atomRight => rfl
  | structural _ _ _ _ inner merged =>
      subst same
      cases inner with
      | expression items _ =>
          obtain rfl := matchList_symbols_out ns items
          exact IfEveryRun.merge_empty_out merged

theorem letArrow_keeps {b out : Bindings} (matched : TypeMatchRel letArrow letArrow b out) : out = b := by
  rw [LetPlain.letArrow_symbols] at matched
  exact symbols_keeps _ matched

theorem unifyArrow_keeps {b out : Bindings} (matched : TypeMatchRel unifyArrow unifyArrow b out) :
    out = b := by
  rw [LetPlain.unifyArrow_symbols] at matched
  exact symbols_keeps _ matched

theorem let_data : DataAtom (.symbol "let") := .symbol (by decide) (by decide)

theorem unify_data : DataAtom (.symbol "unify") := .symbol (by decide) (by decide)

theorem arrow_cast_entry {name : String} (notEmpty : name ≠ "Empty") (notError : name ≠ "Error")
    {arrow : Atom} (isExpression : ∃ items, arrow = .expression items) :
    Entry.Rel policy.reentry .active (.symbol name) arrow .cast := by
  obtain ⟨items, rfl⟩ := isExpression
  exact TypedEveryRun.symbol_cast_entry notEmpty notError (by simp [Atom.atomType, Atom.symbolType,
    Atom.variableType])

/-! ## `unify`'s minimal step, keeping its environment -/

/-- **Every derivation of HE's completed relation for a `unify` instruction** is the success rule,
at a candidate frame whose environment the environment unifier reached, or the failure rule. -/
theorem unify_minimal_source {space : Space} {live : List Atom} {scope : List String}
    {caller : Option Atom} {readiness : Entry.Status} {target pattern yes no : Entry.Value}
    {frame : Frame} {results : List Result}
    (derived : Completed.MinimalRel space dispatch Completed.scopedLookup live scope caller
      (.expression readiness [.symbol "unify", target, pattern, yes, no]) frame results
      (policy := policy)) :
    (∃ output : Frame, UnifyCandidateRel target.erase pattern.erase frame.bindings output.bindings ∧
        Entry.Value.UnifyRel policy.rebuilding frame.environment target pattern output.environment ∧
        results = [(output.read policy yes, output)]) ∨
      (UnifyNoMatchRel target.erase pattern.erase frame.bindings ∧ results = [(no, frame)]) := by
  generalize same : Entry.Value.expression readiness [.symbol "unify", target, pattern, yes, no] =
    instruction at derived
  cases derived with
  | data notInstruction =>
      subst same
      simp [Minimal.embeddedInstruction, Entry.Value.erase] at notInstruction
  | unifyYes candidate unified =>
      simp only [Entry.Value.expression.injEq, List.cons.injEq, and_true, true_and] at same
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := same
      exact Or.inl ⟨_, candidate, unified, rfl⟩
  | unifyNo noMatch =>
      simp only [Entry.Value.expression.injEq, List.cons.injEq, and_true, true_and] at same
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := same
      exact Or.inr ⟨noMatch, rfl⟩
  | unifyBadArity badLength =>
      simp only [Entry.Value.expression.injEq, List.cons.injEq, true_and] at same
      obtain ⟨-, rfl⟩ := same
      exact absurd rfl badLength
  | _ => simp at same

/-! ## The call of `unify` -/

theorem unify_value_erase (cA cP cT cE : Entry.Value) :
    (Entry.Value.expression .active [.symbol "unify", cA, cP, cT, cE]).erase =
      .expression [.symbol "unify", cA.erase, cP.erase, cT.erase, cE.erase] := by
  simp [Entry.Value.erase]

theorem unify_not_error (cA cP cT cE : Entry.Value) :
    ¬ IsErrorRel (Entry.Value.expression .active [.symbol "unify", cA, cP, cT, cE]).erase := by
  rw [unify_value_erase]
  rintro ⟨tail, same⟩
  simp at same

theorem unify_embedded (cA cP cT cE : Entry.Value) :
    Minimal.embeddedInstruction
      (Entry.Value.expression .active [.symbol "unify", cA, cP, cT, cE]).erase = true := by
  rw [unify_value_erase]
  rfl

/-- **Every derivation of the call of `unify` on read arguments publishes the instance's answers.**
The models of the frame see the target as `d`, the pattern as `$x` and the then-branch as the
template; one of them sends `x` to `d`, so the failure branch is impossible, and the then-branch reads
at every candidate frame as the plain value of the instance. -/
theorem unify_call_source {atoms : List Atom} {x : String} {d b : Atom} {L : List Atom}
    (onlyX : ∀ y ∈ TypeSubst.typeVars b, y = x)
    (instance' : InstanceSource dispatch policy atoms (inst x d b) L)
    {live : List Atom} {scope : List String} {F : Frame} (plainF : PlainEnv F.environment)
    {cA cP cT cE : Entry.Value} (plainA : Plain cA) (plainP : Plain cP) (plainT : Plain cT)
    (sees : ∀ v, TypeBindingSatisfied v F.bindings →
      applyTypeValuation v cA.erase = d ∧ applyTypeValuation v cP.erase = v x ∧
        applyTypeValuation v cT.erase = applyTypeValuation v b)
    (solvable : ∃ v, TypeBindingSatisfied v F.bindings ∧ v x = d)
    {children : List Result}
    (called : Completed.CallRel (Space.ofList atoms) dispatch Completed.scopedLookup live scope
      (.expression .active [.symbol "unify", cA, cP, cT, cE]) Atom.undefinedType F children
      (policy := policy)) :
    children.map (fun r => r.1.erase) = L := by
  have embedded := unify_embedded cA cP cT cE
  have grounded : ¬ NonGroundedCallRel dispatch
      (Entry.Value.expression .active [.symbol "unify", cA, cP, cT, cE]).erase := by
    intro nonGrounded
    have notInstruction := nonGrounded.2
    rw [embedded] at notInstruction
    cases notInstruction
  cases called with
  | error failed => exact absurd failed (unify_not_error cA cP cT cE)
  | absent _ nonGrounded _ => exact absurd nonGrounded grounded
  | equations _ nonGrounded _ _ _ => exact absurd nonGrounded grounded
  | embedded _ _ _ invocation batch =>
      cases invocation with
      | absent nonGrounded _ => exact absurd nonGrounded grounded
      | equations nonGrounded _ _ _ => exact absurd nonGrounded grounded
      | embedded _ _ minimal =>
          rcases unify_minimal_source minimal with ⟨out, candidate, unified, rfl⟩ | ⟨noMatch, rfl⟩
          · have plainOut : PlainEnv out.environment :=
              LetPlain.unifyRel_plain unified plainA plainP plainF
            have forced : ∀ v, TypeBindingSatisfied v out.bindings →
                applyTypeValuation v cT.erase = inst x d b := by
              intro v model
              obtain ⟨solves, before⟩ := (UnifyCandidateRel.solutions candidate v).mp model
              obtain ⟨isA, isP, isT⟩ := sees v before
              have vx : v x = d := by rw [← isP, ← solves, isA]
              rw [isT, inst_of_model onlyX vx]
            have readT : out.read policy cT = Entry.Value.ofAtom (inst x d b) := by
              rw [LetPlain.read_plain policy out plainOut plainT,
                LetFrontier.read_forced policy out cT _ forced]
            cases batch with
            | cons returned tail =>
                cases tail
                cases returned with
                | returned answered =>
                    rw [readT] at answered
                    cases answered with
                    | notReducible same =>
                        rw [Entry.Value.erase_ofAtom] at same
                        exact absurd same instance'.facts.notRefused
                    | stopped stopped =>
                        rw [Entry.Value.erase_ofAtom] at stopped
                        exact absurd stopped instance'.facts.notStopped
                    | evaluate _ _ evaluated =>
                        simpa using instance'.determined _ _ _ _ evaluated
          · exfalso
            obtain ⟨v, model, vx⟩ := solvable
            obtain ⟨isA, isP, _⟩ := sees v model
            obtain ⟨output, candidate⟩ := (LetFrontier.candidate_iff (target := cA.erase)
              (pattern := cP.erase) (incoming := F.bindings)).mpr ⟨v, model, by rw [isA, isP, vx]⟩
            exact noMatch output candidate

/-! ## The body of `let`'s row: the call of `unify` at the work's frame -/

/-- What the models of the work's frame see: the fresh names of the row and the call's arguments. -/
structure WorkFrame (F : Frame) (x : String) (d b : Atom) (a p t : String) : Prop where
  plain : PlainEnv F.environment
  sees : ∀ v, TypeBindingSatisfied v F.bindings → v a = d ∧ v p = v x ∧ v t = applyTypeValuation v b
  free : ∃ m, TypeBindingSatisfied m F.bindings ∧ m x = .var x
  solvable : ∃ v, TypeBindingSatisfied v F.bindings ∧ v x = d

theorem read_unify_body (policy : Policy) (F : Frame) (a p t : String) :
    F.read policy (F.read policy (Entry.Value.ofAtom (unifyBody a p t))) =
      .expression .active [.symbol "unify", F.read policy (F.read policy (.var a)),
        F.read policy (F.read policy (.var p)), F.read policy (F.read policy (.var t)),
        .symbol "Empty"] := by
  simp only [unifyBody, Atom.empty, Entry.Value.ofAtom, List.map_cons, List.map_nil, read_active,
    read_symbol]

theorem read_read_plain_var (policy : Policy) (F : Frame) (plain : PlainEnv F.environment)
    (name : String) : Plain (F.read policy (F.read policy (.var name))) :=
  LetPlain.read_plain policy F plain (LetPlain.read_plain policy F plain (LetPlain.plain_var name))

/-- **Every derivation of the body of `let`'s work, `(unify $a $p $t Empty)` read at the work's frame,
publishes the instance's answers.** -/
theorem unify_atom_source {atoms : List Atom} (program : LetProgram atoms) {x : String} {d b : Atom}
    (call : LetCall atoms x d b) {L : List Atom}
    (instance' : InstanceSource dispatch policy atoms (inst x d b) L)
    {a p t : String} {G : Frame} (work : WorkFrame G x d b a p t)
    {live : List Atom} {scope : List String} {results : List Result}
    (derived : Completed.AtomRel (Space.ofList atoms) dispatch Completed.scopedLookup live scope
      (G.read policy (Entry.Value.ofAtom (unifyBody a p t))) Atom.undefinedType G results
      (policy := policy)) :
    results.map (fun r => r.1.erase) = L := by
  obtain ⟨wA, hwA⟩ : ∃ w, G.read policy (G.read policy (.var a)) = w := ⟨_, rfl⟩
  obtain ⟨wP, hwP⟩ : ∃ w, G.read policy (G.read policy (.var p)) = w := ⟨_, rfl⟩
  obtain ⟨wT, hwT⟩ : ∃ w, G.read policy (G.read policy (.var t)) = w := ⟨_, rfl⟩
  have readR : G.read policy (G.read policy (Entry.Value.ofAtom (unifyBody a p t))) =
      .expression .active [Entry.Value.ofAtom (.symbol "unify"), wA, wP, wT, .symbol "Empty"] := by
    rw [read_unify_body, hwA, hwP, hwT]
    simp [Entry.Value.ofAtom]
  have plainA : Plain wA := hwA ▸ read_read_plain_var policy G work.plain a
  have plainP : Plain wP := hwP ▸ read_read_plain_var policy G work.plain p
  have plainT : Plain wT := hwT ▸ read_read_plain_var policy G work.plain t
  -- what the models of the work's frame see
  have seesR : ∀ v, TypeBindingSatisfied v G.bindings →
      applyTypeValuation v wA.erase = d ∧ applyTypeValuation v wP.erase = v x ∧
        applyTypeValuation v wT.erase = applyTypeValuation v b := by
    intro v model
    obtain ⟨isA, isP, isT⟩ := work.sees v model
    refine ⟨?_, ?_, ?_⟩
    · rw [← hwA, read_read_sound policy G _ model]
      simpa [Entry.Value.erase, applyTypeValuation] using isA
    · rw [← hwP, read_read_sound policy G _ model]
      simpa [Entry.Value.erase, applyTypeValuation] using isP
    · rw [← hwT, read_read_sound policy G _ model]
      simpa [Entry.Value.erase, applyTypeValuation] using isT
  -- the read arguments' stored types
  obtain ⟨m, mModel, mx⟩ := work.free
  have eraseA : wA.erase = d := by
    rw [← hwA]
    exact LetFrontier.read_forced policy G _ d fun v model => by
      rw [LetFrontier.read_sound policy G _ model]
      simpa [Entry.Value.erase, applyTypeValuation] using (work.sees v model).1
  obtain ⟨zP, eraseP⟩ : ∃ z, wP.erase = .var z :=
    var_of_sees mx (seesR m mModel).2.1
  obtain ⟨h, tl, bShape⟩ := call.expression
  have typesT : StorageTypesRel (Space.ofList atoms) wT.erase [Atom.undefinedType] := by
    have seen := (seesR m mModel).2.2
    rw [fixed_of_model call.onlyX mx, bShape] at seen
    rcases var_or_expression seen with ⟨z, same⟩ | ⟨h', t', same⟩
    · rw [same]; exact .variable _ z
    · rw [same]; exact program.exprTypes h' t'
  have single : LetPlain.SingleTypes (Space.ofList atoms)
      [wA.erase, wP.erase, wT.erase, .symbol "Empty"] := by
    intro arg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · rw [eraseA]; exact call.typed
    · rw [eraseP]; exact ⟨_, .variable _ zP, rfl⟩
    · exact ⟨_, typesT, rfl⟩
    · exact ⟨_, program.emptyTypes, rfl⟩
  have entry : Entry.Rel policy.reentry (G.read policy (G.read policy
        (Entry.Value.ofAtom (unifyBody a p t)))).status
      (G.read policy (G.read policy (Entry.Value.ofAtom (unifyBody a p t)))).erase
      Atom.undefinedType .interpret := by
    have atEmpty := call_entry policy unify_data [wA.erase, wP.erase, wT.erase, Atom.empty]
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom] at atEmpty
    rw [readR]
    simpa [Entry.Value.erase, Entry.Value.status, Entry.Value.ofAtom, Atom.empty] using atEmpty
  have shape : G.read policy (G.read policy (Entry.Value.ofAtom (unifyBody a p t))) =
      .expression .active (Entry.Value.ofAtom (.symbol "unify") :: [wA, wP, wT, .symbol "Empty"]) :=
    readR
  have notStoppedB : ¬ IsEmptyOrErrorRel b :=
    not_stopped_of_apply (m := fun y => if y = x then d else .var y) (c := inst x d b) rfl
      instance'.facts.notStopped
  have selection : ∀ {outcome : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) Completed.scopedLookup policy live scope
        (G.read policy (G.read policy (Entry.Value.ofAtom (unifyBody a p t)))).erase
        (Entry.Value.ofAtom (.symbol "unify")).erase Atom.undefinedType G outcome →
      ∃ (signature : SelectedTypePolicy) (frame : Frame), signature.functionType = unifyArrow ∧
        outcome = .selected signature [frame] ∧ frame.bindings = G.bindings ∧
        (PlainEnv G.environment → PlainEnv frame.environment) := by
    intro outcome chosen
    rw [readR, Entry.Value.erase_ofAtom] at chosen
    simp only [Entry.Value.erase, Entry.Value.erase_ofAtom, List.map_cons, List.map_nil] at chosen
    exact LetPlain.wildcard_selection program.unifyTypes LetPlain.Controls.unifyArrow_closed
      ⟨_, _, LetPlain.unifyPolicy.isFunction⟩ single
      (fun functionType => by
        obtain ⟨args, returned⟩ := LetPlain.unify_projections functionType
        refine ⟨?_, by simp [args], returned⟩
        rw [args]
        intro T member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> exact Or.inr rfl)
      chosen
  have clean := instance'.clean
  cases derived with
  | delivered entered => cases Entry.functional entered entry
  | cast entered => cases Entry.functional entered entry
  | tuple _ shaped occurs _ _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      rw [Entry.Value.erase_ofAtom] at occurs
      have same := Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel.unique occurs
        program.unifyTypes.occurrences
      simp [Atom.undefinedType] at same
  | fallback _ shaped chosen _ _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      obtain ⟨_, _, _, impossible, _⟩ := selection chosen
      cases impossible
  | selectionFailed _ shaped chosen _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      obtain ⟨_, _, _, impossible, _⟩ := selection chosen
      cases impossible
  | function _ shaped chosen invoked priority =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, rfl⟩ := shaped
      obtain ⟨signature, after, functionType, selected, afterBindings, afterPlain⟩ := selection chosen
      simp only [Completed.InvocationSelection.selected.injEq] at selected
      obtain ⟨rfl, rfl⟩ := selected
      have projections := LetPlain.unify_projections functionType
      cases invoked with
      | cons function calls rest =>
          cases rest
          cases function with
          | evaluated _ operatorRel branches =>
              rw [functionType] at operatorRel
              obtain ⟨frU, rfl, frUBindings, frUPlain⟩ := cast_keeps unify_data
                (arrow_cast_entry (by decide) (by decide) ⟨_, rfl⟩) program.unifyTypes
                LetPlain.Controls.unifyArrow_closed unifyArrow_keeps
                (fun frame => ⟨_, Completed.Frame.preserved_type_match policy frame
                  (LetPlain.unifyArrow_matches _)⟩) operatorRel
              have plainU : PlainEnv frU.environment := frUPlain (afterPlain work.plain)
              have bindingsU : frU.bindings = G.bindings := by rw [frUBindings, afterBindings]
              have frModel : TypeBindingSatisfied m frU.bindings := by rw [bindingsU]; exact mModel
              have notStoppedA : ¬ IsEmptyOrErrorRel (frU.read policy wA).erase :=
                not_stopped_of_apply (m := m) (c := d)
                  (by rw [LetFrontier.read_sound policy frU _ frModel]; exact (seesR m mModel).1)
                  call.data.not_stopped
              have notStoppedP : ¬ IsEmptyOrErrorRel (frU.read policy wP).erase :=
                not_stopped_of_apply (m := m) (c := .var x)
                  (by rw [LetFrontier.read_sound policy frU _ frModel, (seesR m mModel).2.1, mx])
                  (var_not_stopped x)
              have notStoppedT : ¬ IsEmptyOrErrorRel (frU.read policy wT).erase :=
                not_stopped_of_apply (m := m) (c := b)
                  (by rw [LetFrontier.read_sound policy frU _ frModel, (seesR m mModel).2.2,
                    fixed_of_model call.onlyX mx])
                  notStoppedB
              rw [projections.1] at branches
              simp only [List.zip_cons_cons, List.zip_nil_right] at branches
              cases branches with
              | stopped stopped _ =>
                  rw [Entry.Value.erase_ofAtom] at stopped
                  exact absurd stopped unify_data.not_stopped
              | continuing _ arguments restBranches =>
                  cases restBranches
                  cases arguments with
                  | cons argA branchesA =>
                      rw [AtomDemands.atom_demand_source argA] at branchesA
                      cases branchesA with
                      | stopped stopped _ => exact absurd stopped.1 notStoppedA
                      | continuing _ argsP restA =>
                          cases restA
                          cases argsP with
                          | cons argP branchesP =>
                              rw [AtomDemands.atom_demand_source argP] at branchesP
                              cases branchesP with
                              | stopped stopped _ => exact absurd stopped.1 notStoppedP
                              | continuing _ argsT restP =>
                                  cases restP
                                  cases argsT with
                                  | cons argT branchesT =>
                                      rw [AtomDemands.atom_demand_source argT] at branchesT
                                      cases branchesT with
                                      | stopped stopped _ => exact absurd stopped.1 notStoppedT
                                      | continuing _ argsE restT =>
                                          cases restT
                                          cases argsE with
                                          | cons argE branchesE =>
                                              rw [AtomDemands.atom_demand_source argE] at branchesE
                                              cases branchesE with
                                              | stopped stopped _ =>
                                                  exact (stopped.2 (by simp [read_symbol])).elim
                                              | continuing _ argsNil restE =>
                                                  cases restE
                                                  cases argsNil
                                                  rw [LetPlain.returnType_undefined projections.2]
                                                    at calls
                                                  simp only [List.map_cons, List.map_nil,
                                                    List.append_nil, Completed.argumentPrepend_packet,
                                                    Completed.functionAssemble,
                                                    Entry.Value.unpackArguments_packet] at calls
                                                  cases calls with
                                                  | cons callRel restCalls =>
                                                      cases restCalls
                                                      simp only [Entry.Value.ofAtom, read_symbol]
                                                        at callRel
                                                      have answered := unify_call_source
                                                        call.onlyX instance' plainU
                                                        (LetPlain.read_plain policy frU plainU plainA)
                                                        (LetPlain.read_plain policy frU plainU plainP)
                                                        (LetPlain.read_plain policy frU plainU plainT)
                                                        (fun v model => by
                                                          have gModel : TypeBindingSatisfied v
                                                              G.bindings := by
                                                            rw [← bindingsU]; exact model
                                                          obtain ⟨isA, isP, isT⟩ := seesR v gModel
                                                          refine ⟨?_, ?_, ?_⟩
                                                          · rw [LetFrontier.read_sound policy frU _
                                                              model, isA]
                                                          · rw [LetFrontier.read_sound policy frU _
                                                              model, isP]
                                                          · rw [LetFrontier.read_sound policy frU _
                                                              model, isT])
                                                        (by rw [bindingsU]; exact work.solvable)
                                                        callRel
                                                      simp only [List.append_nil] at priority
                                                      exact TypedEveryRun.publish_answers answered
                                                        clean priority

/-! ## The query of `let`'s row -/

theorem occurs_letLeft (n : String) (member : n ∈ ["pattern", "atom", "template"]) :
    AtomOccurs LetFrontier.letLeft n := by
  rw [Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide

theorem occurs_letCall (x : String) (d b : Atom) : AtomOccurs (letCall x d b) x :=
  .expression (by simp) (.var x)

/-- **The frontier of `(let $x d b)` on a `let` program**: one work from `let`'s row, freshened by an
injective renaming whose three names are not `x`; its bindings hold exactly when the fresh names equal
`$x`, `d` and `b` and the incoming bindings hold (`LetFrontier.let_frontier`, with the freshness). -/
theorem let_frontier_fresh {rest live : List Atom} {x : String} {d b : Atom} {incoming : Bindings}
    {works : List EquationWork} (foreign : ∀ row ∈ rest, LetFrontier.Foreign "let" 3 row)
    (satisfiable : ∃ m : String → Atom, TypeBindingSatisfied m incoming)
    (frontier : EquationFrontierRel (Space.ofList (LetFrontier.letRows ++ rest)) live (letCall x d b)
      incoming works) :
    ∃ (w : EquationWork) (rename : String → String), works = [w] ∧ Function.Injective rename ∧
      w.pattern = .expression [.symbol "let", .var (rename "pattern"), .var (rename "atom"),
        .var (rename "template")] ∧
      w.body = unifyBody (rename "atom") (rename "pattern") (rename "template") ∧
      (∀ n ∈ ["pattern", "atom", "template"], rename n ≠ x) ∧
      ∀ v : String → Atom, TypeBindingSatisfied v w.bindings ↔
        (v x = v (rename "pattern") ∧ applyTypeValuation v d = v (rename "atom") ∧
          applyTypeValuation v b = v (rename "template")) ∧ TypeBindingSatisfied v incoming := by
  have shaped : LetFrontier.letRows ++ rest = [LetFrontier.letDecl, LetFrontier.unifyDecl] ++
      .expression [.symbol "=", LetFrontier.letLeft, LetFrontier.letRight] :: rest := rfl
  rw [shaped] at frontier
  obtain ⟨w, rfl, wLeft, wRight⟩ := LetFrontier.linear_frontier (pre := [LetFrontier.letDecl,
      LetFrontier.unifyDecl]) (post := rest) (args := [.var x, d, b]) LetFrontier.let_linear rfl
    (fun row member => by
      rcases List.mem_append.mp member with inDecls | inRest
      · exact LetFrontier.decls_foreign row inDecls
      · exact foreign row inRest)
    satisfiable frontier
  obtain ⟨matched, occurrence⟩ := frontier.occurrence (List.mem_singleton_self w)
  obtain ⟨rename, injective, renamedLeft, renamedRight, fresh⟩ := occurrence.selected.1
  have patternEq := Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamedLeft
  have bodyEq := Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamedRight
  rw [wLeft] at patternEq
  rw [wRight] at bodyEq
  refine ⟨w, rename, rfl, injective, ?_, ?_, ?_, fun v => ?_⟩
  · rw [patternEq]
    simp [LetFrontier.letLeft, renameTypeVars]
  · rw [bodyEq]
    simp [LetFrontier.letRight, renameTypeVars, Atom.empty]
  · intro n member same
    apply fresh n (Or.inl (by rw [wLeft]; exact occurs_letLeft n member))
    rw [same]
    exact Or.inl (occurs_letCall x d b)
  · rw [occurrence.solutions v, patternEq]
    simp [LetFrontier.letLeft, renameTypeVars, applyTypeValuation]

theorem unify_body_erase (policy : Policy) (F : Frame) (a p t : String) :
    (F.read policy (Entry.Value.ofAtom (unifyBody a p t))).erase =
      .expression [.symbol "unify", (F.read policy (.var a)).erase, (F.read policy (.var p)).erase,
        (F.read policy (.var t)).erase, .symbol "Empty"] := by
  simp [unifyBody, Atom.empty, Entry.Value.ofAtom, read_active, read_symbol, Entry.Value.erase]

/-- **The frame of `let`'s work**: plain, its models see the fresh names as `d`, `$x` and the
template; one of them fixes `x`, and one sends `x` to `d`. -/
theorem let_work_frame {atoms : List Atom} {x : String} {d b : Atom} (call : LetCall atoms x d b)
    {F output : Frame} (emptyF : F.bindings = Bindings.empty) (plainF : PlainEnv F.environment)
    {rename : String → String} {w : EquationWork}
    (hxp : x ≠ rename "pattern") (hxa : x ≠ rename "atom") (hxt : x ≠ rename "template")
    (hpa : rename "atom" ≠ rename "pattern") (hpt : rename "template" ≠ rename "pattern")
    (hat : rename "template" ≠ rename "atom")
    (solutions : ∀ v : String → Atom, TypeBindingSatisfied v w.bindings ↔
      (v x = v (rename "pattern") ∧ applyTypeValuation v d = v (rename "atom") ∧
        applyTypeValuation v b = v (rename "template")) ∧ TypeBindingSatisfied v F.bindings)
    (sameBindings : output.bindings = w.bindings)
    (unified : Entry.Value.UnifyRel policy.rebuilding F.environment
      (Entry.Value.ofAtom (letCall x d b)) (Entry.Value.ofAtom w.pattern) output.environment) :
    WorkFrame output x d b (rename "atom") (rename "pattern") (rename "template") := by
  refine ⟨LetPlain.unifyRel_plain unified (LetPlain.plain_ofAtom _) (LetPlain.plain_ofAtom _) plainF,
    fun v model => ?_, ?_, ?_⟩
  · rw [sameBindings, solutions v] at model
    obtain ⟨⟨isP, isA, isT⟩, _⟩ := model
    refine ⟨?_, isP.symm, isT.symm⟩
    rw [← isA, ground_apply call.data]
  · refine ⟨fun y => if y = rename "pattern" then .var x
      else if y = rename "atom" then d
      else if y = rename "template" then b else .var y, ?_, ?_⟩
    · rw [sameBindings, solutions]
      refine ⟨⟨by simp [hxp, hxa, hxt], ?_, ?_⟩, ?_⟩
      · simp [hpa, ground_apply call.data]
      · rw [fixed_of_model call.onlyX (by simp [hxp, hxa, hxt])]
        simp [hpt, hat]
      · rw [emptyF]
        simp [TypeBindingSatisfied, Bindings.empty]
    · simp [hxp, hxa, hxt]
  · refine ⟨fun y => if y = rename "pattern" then d
      else if y = rename "atom" then d
      else if y = rename "template" then inst x d b
      else if y = x then d else .var y, ?_, ?_⟩
    · rw [sameBindings, solutions]
      refine ⟨⟨by simp [hxp, hxa, hxt], ?_, ?_⟩, ?_⟩
      · simp [hpa, ground_apply call.data]
      · rw [inst_of_model (d := d) call.onlyX (by simp [hxp, hxa, hxt])]
        simp [hpt, hat]
      · rw [emptyF]
        simp [TypeBindingSatisfied, Bindings.empty]
    · simp [hxp, hxa, hxt]

/-- **Every derivation of the query of `(let $x d b)` at a frame with empty bindings and a plain
environment publishes the instance's answers.** -/
theorem let_query_source {atoms : List Atom} (program : LetProgram atoms) {x : String} {d b : Atom}
    (call : LetCall atoms x d b) {L : List Atom}
    (instance' : InstanceSource dispatch policy atoms (inst x d b) L)
    {live : List Atom} {scope : List String} {F : Frame} (emptyF : F.bindings = Bindings.empty)
    (plainF : PlainEnv F.environment) {children : List Result}
    (called : Completed.CallRel (Space.ofList atoms) dispatch Completed.scopedLookup live scope
      (Entry.Value.ofAtom (letCall x d b)) Atom.undefinedType F children (policy := policy)) :
    children.map (fun r => r.1.erase) = L := by
  have rows := program.rows
  obtain ⟨rest, same, foreign⟩ := rows
  subst same
  have satisfiable : ∃ m : String → Atom, TypeBindingSatisfied m F.bindings :=
    F.certified.satisfiable
  cases called with
  | error failed =>
      rw [Entry.Value.erase_ofAtom] at failed
      obtain ⟨tail, same⟩ := failed
      simp at same
  | embedded _ _ instruction _ _ =>
      rw [Entry.Value.erase_ofAtom] at instruction
      simp [Minimal.embeddedInstruction] at instruction
  | absent _ _ frontier =>
      rw [Entry.Value.erase_ofAtom] at frontier
      obtain ⟨w, _, same, _⟩ := let_frontier_fresh foreign satisfiable frontier
      cases same
  | equations _ _ frontier _ equations =>
      rw [Entry.Value.erase_ofAtom] at frontier
      obtain ⟨w, rename, rfl, injective, _, bodyEq, fresh, solutions⟩ :=
        let_frontier_fresh foreign satisfiable frontier
      have hxp : x ≠ rename "pattern" := fun same => fresh "pattern" (by simp) same.symm
      have hxa : x ≠ rename "atom" := fun same => fresh "atom" (by simp) same.symm
      have hxt : x ≠ rename "template" := fun same => fresh "template" (by simp) same.symm
      have hpa : rename "atom" ≠ rename "pattern" := injective.ne (by decide)
      have hpt : rename "template" ≠ rename "pattern" := injective.ne (by decide)
      have hat : rename "template" ≠ rename "atom" := injective.ne (by decide)
      cases equations with
      | cons sameBindings unified boundary batch later =>
          cases later
          rw [bodyEq] at boundary
          cases boundary with
          | producerFunction pending _ =>
              obtain ⟨⟨inner, same⟩, _⟩ := pending
              rw [unify_body_erase] at same
              simp at same
          | producerRaw _ =>
              cases batch with
              | cons returned tail =>
                  cases tail
                  cases returned with
                  | returned answered =>
                      cases answered with
                      | notReducible same =>
                          rw [unify_body_erase] at same
                          simp [Atom.notReducible] at same
                      | stopped stopped =>
                          rw [unify_body_erase] at stopped
                          rcases stopped with same | ⟨tail, same⟩
                          · simp [Atom.empty] at same
                          · simp at same
                      | evaluate _ _ evaluated =>
                          have work := let_work_frame call emptyF plainF hxp hxa hxt hpa hpt hat
                            solutions sameBindings unified
                          simpa using unify_atom_source program call instance' work evaluated

/-! ## Every derivation of `let` -/

/-- **Every derivation of HE's completed relation for `(let $x d b)`, at a frame with empty bindings
and a plain environment (HE's entry is one), publishes the answers of the instance `b[x := d]`**, on
the scoped lookup, for every policy and dispatch. -/
theorem let_source {atoms : List Atom} (program : LetProgram atoms) {x : String} {d b : Atom}
    (call : LetCall atoms x d b) {L : List Atom}
    (instance' : InstanceSource dispatch policy atoms (inst x d b) L)
    {live : List Atom} {scope : List String} {F : Frame} (emptyF : F.bindings = Bindings.empty)
    (plainF : PlainEnv F.environment) {results : List Result}
    (derived : Completed.AtomRel (Space.ofList atoms) dispatch Completed.scopedLookup live scope
      (Entry.Value.ofAtom (letCall x d b)) Atom.undefinedType F results (policy := policy)) :
    results.map (fun r => r.1.erase) = L := by
  have readC : F.read policy (Entry.Value.ofAtom (letCall x d b)) =
      Entry.Value.ofAtom (letCall x d b) := read_ofAtom_of_empty policy F emptyF plainF _
  have entry : Entry.Rel policy.reentry (F.read policy (Entry.Value.ofAtom (letCall x d b))).status
      (F.read policy (Entry.Value.ofAtom (letCall x d b))).erase Atom.undefinedType .interpret := by
    have atEmpty := call_entry policy let_data [.var x, d, b]
    rw [Completed.Frame.read_empty] at atEmpty
    rw [readC]
    exact atEmpty
  have shape : F.read policy (Entry.Value.ofAtom (letCall x d b)) =
      .expression .active (Entry.Value.ofAtom (.symbol "let") ::
        [Atom.var x, d, b].map Entry.Value.ofAtom) := by
    rw [readC]
    simp only [letCall, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  obtain ⟨Td, typesD, closedD⟩ := call.typed
  obtain ⟨h, tl, bShape⟩ := call.expression
  have single : LetPlain.SingleTypes (Space.ofList atoms) [.var x, d, b] := by
    intro arg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨_, .variable _ x, rfl⟩
    · exact ⟨_, typesD, closedD⟩
    · rw [bShape]; exact ⟨_, program.exprTypes h tl, rfl⟩
  have selection : ∀ {outcome : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) Completed.scopedLookup policy live scope
        (F.read policy (Entry.Value.ofAtom (letCall x d b))).erase
        (Entry.Value.ofAtom (.symbol "let")).erase Atom.undefinedType F outcome →
      ∃ (signature : SelectedTypePolicy) (frame : Frame), signature.functionType = letArrow ∧
        outcome = .selected signature [frame] ∧ frame.bindings = F.bindings ∧
        (PlainEnv F.environment → PlainEnv frame.environment) := by
    intro outcome chosen
    rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosen
    exact LetPlain.wildcard_selection program.letTypes LetPlain.Controls.letArrow_closed
      ⟨_, _, LetPlain.letPolicy.isFunction⟩ single
      (fun functionType => by
        obtain ⟨args, returned⟩ := LetPlain.let_projections functionType
        refine ⟨?_, by simp [args], returned⟩
        rw [args]
        intro T member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl rfl
        · exact Or.inr rfl)
      chosen
  have notStoppedB : ¬ IsEmptyOrErrorRel b :=
    not_stopped_of_apply (m := fun y => if y = x then d else .var y) (c := inst x d b) rfl
      instance'.facts.notStopped
  cases derived with
  | delivered entered => cases Entry.functional entered entry
  | cast entered => cases Entry.functional entered entry
  | tuple _ shaped occurs _ _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      rw [Entry.Value.erase_ofAtom] at occurs
      have same := Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel.unique occurs
        program.letTypes.occurrences
      simp [Atom.undefinedType] at same
  | fallback _ shaped chosen _ _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      obtain ⟨_, _, _, impossible, _⟩ := selection chosen
      cases impossible
  | selectionFailed _ shaped chosen _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      obtain ⟨_, _, _, impossible, _⟩ := selection chosen
      cases impossible
  | function _ shaped chosen invoked priority =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, rfl⟩ := shaped
      obtain ⟨signature, after, functionType, selected, afterBindings, afterPlain⟩ := selection chosen
      simp only [Completed.InvocationSelection.selected.injEq] at selected
      obtain ⟨rfl, rfl⟩ := selected
      have projections := LetPlain.let_projections functionType
      cases invoked with
      | cons function calls rest =>
          cases rest
          cases function with
          | evaluated _ operatorRel branches =>
              rw [functionType] at operatorRel
              obtain ⟨frF, rfl, frFBindings, frFPlain⟩ := cast_keeps let_data
                (arrow_cast_entry (by decide) (by decide) ⟨_, rfl⟩) program.letTypes
                LetPlain.Controls.letArrow_closed letArrow_keeps
                (fun frame => ⟨_, Completed.Frame.preserved_type_match policy frame
                  (LetPlain.letArrow_matches _)⟩) operatorRel
              have emptyFF : frF.bindings = Bindings.empty := by
                rw [frFBindings, afterBindings, emptyF]
              have plainFF : PlainEnv frF.environment := frFPlain (afterPlain plainF)
              have notStoppedX : ¬ IsEmptyOrErrorRel
                  (frF.read policy (Entry.Value.ofAtom (.var x))).erase := by
                rw [read_ofAtom_of_empty policy frF emptyFF plainFF, Entry.Value.erase_ofAtom]
                exact var_not_stopped x
              rw [projections.1] at branches
              simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right]
                at branches
              cases branches with
              | stopped stopped _ =>
                  rw [Entry.Value.erase_ofAtom] at stopped
                  exact absurd stopped let_data.not_stopped
              | continuing _ arguments restBranches =>
                  cases restBranches
                  cases arguments with
                  | cons argX branchesX =>
                      rw [AtomDemands.atom_demand_source argX] at branchesX
                      cases branchesX with
                      | stopped stopped _ => exact absurd stopped.1 notStoppedX
                      | continuing _ argsD restX =>
                          cases restX
                          cases argsD with
                          | cons argD branchesD =>
                              obtain ⟨frD, rfl, frDBindings, frDPlain⟩ := cast_keeps call.data
                                (call.data.entry _) typesD closedD
                                (fun matched => matched.undefined_output)
                                (fun frame => TypedEveryRun.undefined_accepts Td frame) argD
                              have emptyFD : frD.bindings = Bindings.empty := by
                                rw [frDBindings, emptyFF]
                              have plainFD : PlainEnv frD.environment := frDPlain plainFF
                              have notStoppedD : ¬ IsEmptyOrErrorRel (Entry.Value.ofAtom d).erase := by
                                rw [Entry.Value.erase_ofAtom]
                                exact call.data.not_stopped
                              cases branchesD with
                              | stopped stopped _ => exact absurd stopped.1 notStoppedD
                              | continuing _ argsB restD =>
                                  cases restD
                                  cases argsB with
                                  | cons argB branchesB =>
                                      rw [AtomDemands.atom_demand_source argB] at branchesB
                                      cases branchesB with
                                      | stopped stopped _ =>
                                          have readB := read_ofAtom_of_empty policy frD emptyFD
                                            plainFD b
                                          have stoppedB := stopped.1
                                          simp only [readB, Entry.Value.erase_ofAtom] at stoppedB
                                          exact absurd stoppedB notStoppedB
                                      | continuing _ argsNil restB =>
                                          cases restB
                                          cases argsNil
                                          rw [LetPlain.returnType_undefined projections.2] at calls
                                          simp only [List.map_cons, List.map_nil, List.append_nil,
                                            Completed.argumentPrepend_packet,
                                            Completed.functionAssemble,
                                            Entry.Value.unpackArguments_packet] at calls
                                          cases calls with
                                          | cons callRel restCalls =>
                                              cases restCalls
                                              simp only [read_ofAtom_of_empty policy frF emptyFF
                                                plainFF, read_ofAtom_of_empty policy frD emptyFD
                                                plainFD] at callRel
                                              have valueEq : (Entry.Value.expression .active
                                                  [Entry.Value.ofAtom (.symbol "let"),
                                                    Entry.Value.ofAtom (.var x), Entry.Value.ofAtom d,
                                                    Entry.Value.ofAtom b]) =
                                                  Entry.Value.ofAtom (letCall x d b) := by
                                                simp [letCall, Entry.Value.ofAtom]
                                              rw [valueEq] at callRel
                                              have answered := let_query_source program
                                                (call := call) instance' emptyFD plainFD callRel
                                              simp only [List.append_nil] at priority
                                              exact TypedEveryRun.publish_answers answered
                                                instance'.clean priority

/-- **At HE's entry**: every derivation for `(let $x d b)` publishes the instance's answers. -/
theorem let_entry_source {atoms : List Atom} (program : LetProgram atoms) {x : String} {d b : Atom}
    (call : LetCall atoms x d b) {L : List Atom}
    (instance' : InstanceSource dispatch policy atoms (inst x d b) L) {results : List Result}
    (derived : Completed.AtomRel (Space.ofList atoms) dispatch Completed.scopedLookup [] []
      (Entry.Value.ofAtom (letCall x d b)) Atom.undefinedType Completed.Frame.empty results
      (policy := policy)) :
    results.map (fun r => r.1.erase) = L :=
  let_source program call instance' rfl LetPlain.plainEnv_nil derived

/-! ## Controls -/

namespace Controls

open AnswerBags.Controls (app)

/-- **Positive control**: the instance of `(pair $x $x)` at `5` is `(pair 5 5)`. -/
theorem instance_five : inst "x" (.grounded (.int 5)) (app "pair" [.var "x", .var "x"]) =
    app "pair" [.grounded (.int 5), .grounded (.int 5)] := by
  simp [inst, applyTypeValuation, app]

/-- **Negative control, `solvable` has content**: at bindings holding `$x := 7` no model sends `x` to
`5`; there `unify` has no candidate (`LetFrontier.candidate_iff`) and HE's `let` takes the failure
rule. -/
theorem var_not_solvable :
    ¬ ∃ v : String → Atom, TypeBindingSatisfied v ⟨[("x", .grounded (.int 7))], []⟩ ∧
      v "x" = .grounded (.int 5) := by
  rintro ⟨v, model, five⟩
  have seven := model.1 "x" (.grounded (.int 7)) (by simp)
  rw [five] at seven
  simp [applyTypeValuation] at seven

end Controls

#print axioms cast_keeps
#print axioms unify_minimal_source
#print axioms unify_call_source
#print axioms unify_atom_source
#print axioms let_frontier_fresh
#print axioms let_query_source
#print axioms let_source
#print axioms let_entry_source
#print axioms Controls.instance_five
#print axioms Controls.var_not_solvable

end LetSource

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
