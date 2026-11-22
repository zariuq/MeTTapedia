import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.LetPeTTa

/-!
# Plain values on HE's `let` path, and admission against closed arrows with wildcard demands

HE's contextual values carry a readiness mark on every expression node. On the path of `let` from
HE's entry no node is ever marked held: `functionAssemble` builds active nodes, substitution keeps an
active node active under both rebuilding policies, frame renewals unify plain types, and the
environment unifier stores substituted plain values. So every value on that path is the plain value
of its atom, and the template `let` evaluates is read as the plain value of its instance. This module
proves the closure facts once.

* `Plain`, `PlainEnv`: a value equal to the plain value of its erasure; an environment of such values.
* `substitute_plain_value`, `read_plain`: substitution and reads keep plain values plain.
* `unify_plain`: **HE's environment unifier keeps plain environments plain** on plain operands (one
  recursion over its three mutual relations).
* `typeRenew_plain`, `castRenew_plain`: frame renewals keep plain environments.
* `symbols_type_match`: a closed arrow of symbols matches itself and keeps the bindings.
* `wildcard_selection`: **every admission of a call against a closed arrow whose demands are `Atom`
  or `%Undefined%` keeps exactly one activation, with the frame's bindings and a plain environment**,
  when every argument has one closed stored type, on the scoped lookup at any frame; and that
  selection exists (`wildcard_selection_exists`). `let` and `unify` are the two instances used by
  `LetSource` and `LetFine`: one combinator for both closed arrows.

## Controls

* `Controls.held_not_plain` (negative): a held expression is not plain, so `Plain` is a real
  condition.
* `Controls.letArrow_closed`, `Controls.unifyArrow_closed` (positive): both arrows are closed.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace LetPlain

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel FunctionTypeRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (MatchListAccRel MergeRel
  equalityGroundedSemantic semanticLoopFree_empty)

/-! ## Plain values -/

/-- **A plain value**: every expression node is active, so the value is the plain value of its
atom. -/
def Plain (v : Entry.Value) : Prop := v = Entry.Value.ofAtom v.erase

/-- **A plain environment**: every stored value is plain. -/
def PlainEnv (env : Entry.Value.Environment) : Prop := ∀ row ∈ env, Plain row.2

theorem plain_ofAtom (t : Atom) : Plain (Entry.Value.ofAtom t) := by
  unfold Plain
  rw [Entry.Value.erase_ofAtom]

theorem plainEnv_nil : PlainEnv [] := fun _ member => by cases member

theorem eq_of_map_self {α : Type} {f : α → α} : ∀ {l : List α}, l.map f = l → ∀ a ∈ l, f a = a
  | [], _, _, member => by cases member
  | b :: bs, same, a, member => by
      simp only [List.map_cons, List.cons.injEq] at same
      rcases List.mem_cons.mp member with rfl | inner
      · exact same.1
      · exact eq_of_map_self same.2 a inner

/-- An active expression of plain children is plain. -/
theorem plain_expression {children : List Entry.Value} (each : ∀ c ∈ children, Plain c) :
    Plain (.expression .active children) := by
  unfold Plain
  simp only [Entry.Value.erase, Entry.Value.ofAtom, List.map_map]
  congr 1
  conv_lhs => rw [← List.map_id children]
  apply List.map_congr_left
  intro c member
  exact each c member

/-- A plain expression is active, with plain children. -/
theorem Plain.children {s : Entry.Status} {children : List Entry.Value}
    (plain : Plain (.expression s children)) : s = .active ∧ ∀ c ∈ children, Plain c := by
  unfold Plain at plain
  simp only [Entry.Value.erase, Entry.Value.ofAtom, List.map_map,
    Entry.Value.expression.injEq] at plain
  obtain ⟨rfl, same⟩ := plain
  exact ⟨rfl, fun c member => (eq_of_map_self same.symm c member).symm⟩

theorem plain_var (name : String) : Plain (.var name) := by
  simpa [Entry.Value.ofAtom] using plain_ofAtom (.var name)

/-! ## Substitution, reads, and the environment unifier -/

theorem resolve_plain {env : Entry.Value.Environment} (plain : PlainEnv env) (name : String) :
    Plain (Entry.Value.resolve env name) := by
  unfold Entry.Value.resolve
  induction env with
  | nil => exact plain_var name
  | cons row rest ih =>
      obtain ⟨key, value⟩ := row
      by_cases same : name = key
      · subst same
        simpa [List.lookup] using plain _ List.mem_cons_self
      · have different : (name == key) = false := by simpa using same
        simp only [List.lookup, different]
        exact ih (fun r member => plain r (List.mem_cons_of_mem _ member))

theorem rebuildStatus_active (policy : Entry.RebuildPolicy) (before after : Atom) :
    Entry.Value.rebuildStatus policy .active before after = .active := by
  cases policy <;> simp [Entry.Value.rebuildStatus]

/-- **Substituting plain values into the plain value of an atom gives a plain value.** -/
theorem substitute_plain (policy : Entry.RebuildPolicy) (env : String → Entry.Value)
    (plainEnv : ∀ name, Plain (env name)) (t : Atom) :
    Plain (Entry.Value.substitute policy env (Entry.Value.ofAtom t)) := by
  induction t using Atom.rec (motive_2 := fun items =>
      ∀ c ∈ (items.map Entry.Value.ofAtom).map (Entry.Value.substitute policy env), Plain c) with
  | symbol name => simpa [Entry.Value.ofAtom, Entry.Value.substitute] using plain_ofAtom (.symbol name)
  | var name => simpa [Entry.Value.ofAtom, Entry.Value.substitute] using plainEnv name
  | grounded g => simpa [Entry.Value.ofAtom, Entry.Value.substitute] using plain_ofAtom (.grounded g)
  | expression items ih =>
      simp only [Entry.Value.ofAtom, Entry.Value.substitute, rebuildStatus_active]
      exact plain_expression ih
  | nil =>
      rename_i c member
      simp at member
  | cons head tail first rest =>
      rename_i c member
      simp only [List.map_cons, List.mem_cons] at member
      rcases member with rfl | inner
      · exact first
      · exact rest c inner

theorem substitute_plain_value (policy : Entry.RebuildPolicy) (env : String → Entry.Value)
    (plainEnv : ∀ name, Plain (env name)) {v : Entry.Value} (plain : Plain v) :
    Plain (Entry.Value.substitute policy env v) := by
  rw [plain]
  exact substitute_plain policy env plainEnv v.erase

/-- **A read through a frame with a plain environment keeps a plain value plain.** -/
theorem read_plain (policy : Policy) (frame : Frame) (plainEnv : PlainEnv frame.environment)
    {v : Entry.Value} (plain : Plain v) : Plain (frame.read policy v) :=
  substitute_plain_value policy.rebuilding _ (resolve_plain plainEnv) plain

theorem bind_plain (policy : Entry.RebuildPolicy) {env : Entry.Value.Environment}
    (plainEnv : PlainEnv env) (name : String) {value : Entry.Value} (plain : Plain value) :
    PlainEnv (Entry.Value.bind policy env name value) := by
  have resolved : Plain (Entry.Value.substitute policy (Entry.Value.resolve env) value) :=
    substitute_plain_value policy _ (resolve_plain plainEnv) plain
  have single : PlainEnv [(name, Entry.Value.substitute policy (Entry.Value.resolve env) value)] := by
    intro row member
    rw [List.mem_singleton] at member
    subst member
    exact resolved
  intro row member
  simp only [Entry.Value.bind, List.mem_cons, List.mem_map, List.mem_filter] at member
  rcases member with rfl | ⟨old, ⟨inEnv, _⟩, rfl⟩
  · exact resolved
  · exact substitute_plain_value policy _ (resolve_plain single) (plainEnv old inEnv)

/-- **HE's environment unifier keeps plain environments plain on plain operands**, for the applied
step, the materialized step and lists of children. -/
theorem unify_plain (policy : Entry.RebuildPolicy) :
    (∀ {environment output left right},
      Entry.Value.AppliedUnifyRel policy environment left right output →
        Plain left → Plain right → PlainEnv environment → PlainEnv output) ∧
    (∀ {environment output left right},
      Entry.Value.UnifyRel policy environment left right output →
        Plain left → Plain right → PlainEnv environment → PlainEnv output) ∧
    (∀ {environment output lefts rights},
      Entry.Value.UnifyListRel policy environment lefts rights output →
        (∀ c ∈ lefts, Plain c) → (∀ c ∈ rights, Plain c) → PlainEnv environment →
          PlainEnv output) := by
  let applied := fun environment left right output
      (_ : Entry.Value.AppliedUnifyRel policy environment left right output) =>
    Plain left → Plain right → PlainEnv environment → PlainEnv output
  let ordinary := fun environment left right output
      (_ : Entry.Value.UnifyRel policy environment left right output) =>
    Plain left → Plain right → PlainEnv environment → PlainEnv output
  let many := fun environment lefts rights output
      (_ : Entry.Value.UnifyListRel policy environment lefts rights output) =>
    (∀ c ∈ lefts, Plain c) → (∀ c ∈ rights, Plain c) → PlainEnv environment → PlainEnv output
  have identical {environment left right} (same : left.erase = right.erase) :
      applied environment left right environment (.identical same) :=
    fun _ _ plainEnv => plainEnv
  have bindLeft {environment name right} (absent : name ∉ TypeSubst.typeVars right.erase) :
      applied environment (.var name) right (Entry.Value.bind policy environment name right)
        (.bindLeft absent) :=
    fun _ plainRight plainEnv => bind_plain policy plainEnv name plainRight
  have bindRight {environment left name} (nonvar : ∀ other, left.erase ≠ .var other)
      (absent : name ∉ TypeSubst.typeVars left.erase) :
      applied environment left (.var name) (Entry.Value.bind policy environment name left)
        (.bindRight nonvar absent) :=
    fun plainLeft _ plainEnv => bind_plain policy plainEnv name plainLeft
  have expression {environment output left right earlier later}
      (children : Entry.Value.UnifyListRel policy environment left right output)
      (ih : many environment left right output children) :
      applied environment (.expression earlier left) (.expression later right) output
        (.expression children) :=
    fun plainLeft plainRight plainEnv =>
      ih plainLeft.children.2 plainRight.children.2 plainEnv
  have materialized {environment output left right}
      (derived : Entry.Value.AppliedUnifyRel policy environment
        (Entry.Value.substitute policy (Entry.Value.resolve environment) left)
        (Entry.Value.substitute policy (Entry.Value.resolve environment) right) output)
      (ih : applied environment _ _ output derived) :
      ordinary environment left right output (.ordinary derived) :=
    fun plainLeft plainRight plainEnv =>
      ih (substitute_plain_value policy _ (resolve_plain plainEnv) plainLeft)
        (substitute_plain_value policy _ (resolve_plain plainEnv) plainRight) plainEnv
  have nil (environment : Entry.Value.Environment) :
      many environment [] [] environment (.nil environment) :=
    fun _ _ plainEnv => plainEnv
  have cons {environment next output left right lefts rights}
      (head : Entry.Value.UnifyRel policy environment left right next)
      (tail : Entry.Value.UnifyListRel policy next lefts rights output)
      (ih : ordinary environment left right next head) (it : many next lefts rights output tail) :
      many environment (left :: lefts) (right :: rights) output (.cons head tail) :=
    fun plainLefts plainRights plainEnv =>
      it (fun c member => plainLefts c (List.mem_cons_of_mem _ member))
        (fun c member => plainRights c (List.mem_cons_of_mem _ member))
        (ih (plainLefts _ List.mem_cons_self) (plainRights _ List.mem_cons_self) plainEnv)
  exact ⟨fun derived => Entry.Value.AppliedUnifyRel.rec
      (motive_1 := applied) (motive_2 := ordinary) (motive_3 := many)
      identical bindLeft bindRight expression materialized nil cons derived,
    fun derived => Entry.Value.UnifyRel.rec
      (motive_1 := applied) (motive_2 := ordinary) (motive_3 := many)
      identical bindLeft bindRight expression materialized nil cons derived,
    fun derived => Entry.Value.UnifyListRel.rec
      (motive_1 := applied) (motive_2 := ordinary) (motive_3 := many)
      identical bindLeft bindRight expression materialized nil cons derived⟩

theorem unifyRel_plain {policy : Entry.RebuildPolicy} {environment output : Entry.Value.Environment}
    {left right : Entry.Value} (unified : Entry.Value.UnifyRel policy environment left right output)
    (plainLeft : Plain left) (plainRight : Plain right) (plainEnv : PlainEnv environment) :
    PlainEnv output :=
  (unify_plain policy).2.1 unified plainLeft plainRight plainEnv

/-! ## Frame renewals -/

theorem typeRenew_plain {policy : Policy} {expected actual : Atom} {before after : Frame}
    (renewed : Completed.Frame.TypeRenewRel policy expected actual before after)
    (plain : PlainEnv before.environment) : PlainEnv after.environment := by
  cases renewed with
  | unchanged => exact plain
  | unified _ unified => exact unifyRel_plain unified (plain_ofAtom _) (plain_ofAtom _) plain

theorem castRenew_plain {policy : Policy}
    {lookup : Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeLookupRel}
    {original expected : Atom} {before after : Frame}
    (renewed : Completed.Frame.CastRenewRel policy lookup original expected before after)
    (plain : PlainEnv before.environment) : PlainEnv after.environment := by
  cases renewed with
  | same => exact plain
  | matched _ _ _ _ unified => exact unifyRel_plain unified (plain_ofAtom _) (plain_ofAtom _) plain

/-- A renewal under a wildcard demand keeps the bindings. -/
theorem typeRenew_bindings {policy : Policy} {expected actual : Atom} {before after : Frame}
    (renewed : Completed.Frame.TypeRenewRel policy expected actual before after)
    (wildcard : expected = Atom.undefinedType ∨ expected = Atom.atomType) :
    after.bindings = before.bindings :=
  renewed.source.wildcard_output (by rcases wildcard with same | same <;> simp [same])

/-! ## Closed arrows of symbols -/

theorem symbols_match_acc : ∀ ns : List String,
    MatchListAccRel equalityGroundedSemantic (ns.map Atom.symbol) (ns.map Atom.symbol)
      Bindings.empty Bindings.empty
  | [] => .nil
  | n :: ns => .cons (.symSym n semanticLoopFree_empty)
      (MergeRel.mk (order := [])
        (by simp [Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.constraints, Bindings.empty]) .nil)
      (symbols_match_acc ns)

/-- **An expression of symbols matches itself and keeps the bindings.** -/
theorem symbols_type_match (ns : List String) (b : Bindings) :
    TypeMatchRel (.expression (ns.map Atom.symbol)) (.expression (ns.map Atom.symbol)) b b :=
  .structural (by simp [Atom.undefinedType]) (by simp [Atom.atomType])
    (by simp [Atom.undefinedType]) (by simp [Atom.atomType])
    (.expression (symbols_match_acc ns) semanticLoopFree_empty)
    (MergeRel.mk (order := [])
      (by simp [Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.constraints, Bindings.empty]) .nil)

/-- `(-> Atom %Undefined% Atom %Undefined%)`, the arrow of `let` (`LetFrontier.letDecl`). -/
abbrev letArrow : Atom :=
  .expression [.symbol "->", .symbol "Atom", Atom.undefinedType, .symbol "Atom", Atom.undefinedType]

/-- `(-> Atom Atom Atom Atom %Undefined%)`, the arrow of `unify` (`LetFrontier.unifyDecl`). -/
abbrev unifyArrow : Atom :=
  .expression [.symbol "->", .symbol "Atom", .symbol "Atom", .symbol "Atom", .symbol "Atom",
    Atom.undefinedType]

theorem letArrow_symbols :
    letArrow = .expression (["->", "Atom", "%Undefined%", "Atom", "%Undefined%"].map Atom.symbol) :=
  rfl

theorem unifyArrow_symbols :
    unifyArrow = .expression (["->", "Atom", "Atom", "Atom", "Atom", "%Undefined%"].map Atom.symbol) :=
  rfl

theorem letArrow_matches (b : Bindings) : TypeMatchRel letArrow letArrow b b := by
  rw [letArrow_symbols]
  exact symbols_type_match _ b

theorem unifyArrow_matches (b : Bindings) : TypeMatchRel unifyArrow unifyArrow b b := by
  rw [unifyArrow_symbols]
  exact symbols_type_match _ b

/-- The selected policy of `let`'s arrow. -/
def letPolicy : SelectedTypePolicy :=
  ⟨letArrow, [Atom.atomType, Atom.undefinedType, Atom.atomType], Atom.undefinedType, rfl⟩

/-- The selected policy of `unify`'s arrow. -/
def unifyPolicy : SelectedTypePolicy :=
  ⟨unifyArrow, [Atom.atomType, Atom.atomType, Atom.atomType, Atom.atomType], Atom.undefinedType, rfl⟩

theorem let_projections {signature : SelectedTypePolicy}
    (functionType : signature.functionType = letArrow) :
    signature.argumentTypes = [Atom.atomType, Atom.undefinedType, Atom.atomType] ∧
      signature.returnType = Atom.undefinedType := by
  have shaped : FunctionTypeRel letArrow signature.argumentTypes signature.returnType :=
    functionType ▸ signature.isFunction
  exact Mettapedia.Languages.MeTTa.HE.Spec.Type.FunctionTypeRel.unique shaped letPolicy.isFunction

theorem unify_projections {signature : SelectedTypePolicy}
    (functionType : signature.functionType = unifyArrow) :
    signature.argumentTypes = [Atom.atomType, Atom.atomType, Atom.atomType, Atom.atomType] ∧
      signature.returnType = Atom.undefinedType := by
  have shaped : FunctionTypeRel unifyArrow signature.argumentTypes signature.returnType :=
    functionType ▸ signature.isFunction
  exact Mettapedia.Languages.MeTTa.HE.Spec.Type.FunctionTypeRel.unique shaped unifyPolicy.isFunction

theorem returnType_undefined {signature : SelectedTypePolicy}
    (returned : signature.returnType = Atom.undefinedType) :
    Completed.invocationReturnType signature = Atom.undefinedType := by
  simp [Completed.invocationReturnType, returned, Atom.expressionType]

/-! ## Admission against a closed arrow with wildcard demands -/

/-- Every argument has one closed stored type. -/
def SingleTypes (space : Space) (args : List Atom) : Prop :=
  ∀ a ∈ args, ∃ T, StorageTypesRel space a [T] ∧ TypeSubst.typeVars T = []

/-- Every demand is a wildcard. -/
def Wildcards (Ts : List Atom) : Prop := ∀ T ∈ Ts, T = Atom.undefinedType ∨ T = Atom.atomType

theorem wildcard_match {T : Atom} (wildcard : T = Atom.undefinedType ∨ T = Atom.atomType)
    (actual : Atom) (b : Bindings) : TypeMatchRel T actual b b := by
  rcases wildcard with rfl | rfl
  · exact .undefinedLeft actual b
  · exact .atomLeft actual b

theorem wildcard_accepts (policy : Policy) {T : Atom}
    (wildcard : T = Atom.undefinedType ∨ T = Atom.atomType) (actual : Atom) (frame : Frame) :
    ∃ output, policy.matching.Rel T actual frame.bindings output :=
  ⟨_, Completed.Frame.preserved_type_match policy frame (wildcard_match wildcard actual _)⟩

/-- **The argument checks against wildcard demands keep one frame**, with the bindings and a plain
environment, and report no error. -/
theorem wildcard_arguments {space : Space} {P : List String} {policy : Policy} {expression : Atom} :
    ∀ (args Ts : List Atom) (position : Nat) (before : Frame) (after : List Frame)
      (errors : List Atom),
      SingleTypes space args → Wildcards Ts →
      Completed.ApplicabilityArgumentsRel space (Completed.scopedLookup P space) policy expression
        position args Ts [before] after errors →
      ∃ frame : Frame, after = [frame] ∧ frame.bindings = before.bindings ∧
        (PlainEnv before.environment → PlainEnv frame.environment) ∧ errors = []
  | [], _, _, before, after, errors, _, _, checked => by
      cases checked
      exact ⟨before, rfl, rfl, id, rfl⟩
  | a :: rest, _, position, before, after, errors, single, wild, checked => by
      cases checked with
      | cons head tail =>
          have wildT := wild _ List.mem_cons_self
          cases head with
          | cons queried paired restChecks =>
              cases restChecks
              obtain ⟨A, stored, closedA⟩ := single a List.mem_cons_self
              have same := ScopedIf.scoped_closed_answer stored closedA queried
              subst same
              obtain ⟨check, checks, checked, nilChecks, rfl⟩ := List.forall₂_cons_left_iff.mp paired
              obtain rfl := List.forall₂_nil_left_iff.mp nilChecks
              cases checked with
              | rejected rejectedAll =>
                  obtain ⟨output, matched⟩ := wildcard_accepts policy wildT A before
                  exact (rejectedAll output matched).elim
              | accepted renewed =>
                  simp only [Completed.checkedFrames, Completed.checkedFailures, List.filterMap_cons,
                    List.filterMap_nil, List.map_nil, List.append_nil, List.nil_append] at tail ⊢
                  obtain ⟨frame, rfl, sameBindings, plain, rfl⟩ := wildcard_arguments rest _
                    (position + 1) _ after _
                    (fun b member => single b (List.mem_cons_of_mem _ member))
                    (fun T member => wild T (List.mem_cons_of_mem _ member)) tail
                  refine ⟨frame, rfl, ?_,
                    fun plainBefore => plain (typeRenew_plain renewed plainBefore), rfl⟩
                  rw [sameBindings, typeRenew_bindings renewed wildT]

/-- **The checks of a call against a closed arrow with wildcard demands keep one frame.** -/
theorem wildcard_checks {space : Space} {P : List String} {policy : Policy} {operator : Atom}
    {args : List Atom} {signature : SelectedTypePolicy} {before : Frame} {frames : List Frame}
    {errors : List Atom} (single : SingleTypes space args) (wild : Wildcards signature.argumentTypes)
    (arity : args.length = signature.argumentTypes.length)
    (returned : signature.returnType = Atom.undefinedType)
    (checks : Completed.ApplicationChecksRel space (Completed.scopedLookup P space) policy
      (.expression (operator :: args)) Atom.undefinedType signature before frames errors) :
    ∃ frame : Frame, frames = [frame] ∧ frame.bindings = before.bindings ∧
      (PlainEnv before.environment → PlainEnv frame.environment) := by
  cases checks with
  | wrongArity shaped badArity =>
      simp only [Atom.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl⟩ := shaped
      exact absurd arity badArity
  | checked shaped arguments returnChecks =>
      simp only [Atom.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl⟩ := shaped
      obtain ⟨frame, rfl, sameBindings, plain, _⟩ :=
        wildcard_arguments _ _ 1 before _ _ single wild arguments
      obtain ⟨returnCheck, rest, returnChecked, nilReturn, rfl⟩ :=
        List.forall₂_cons_left_iff.mp returnChecks
      obtain rfl := List.forall₂_nil_left_iff.mp nilReturn
      rw [returned] at returnChecked
      cases returnChecked with
      | rejected rejectedAll =>
          obtain ⟨output, matched⟩ := TypedEveryRun.undefined_accepts Atom.undefinedType frame
          exact (rejectedAll output matched).elim
      | accepted renewed =>
          refine ⟨_, rfl, ?_, fun plainBefore => typeRenew_plain renewed (plain plainBefore)⟩
          rw [typeRenew_bindings renewed (Or.inl rfl), sameBindings]

/-- **Every admission of a call of `f` against its one closed arrow with wildcard demands selects that
arrow with one activation keeping the frame's bindings and a plain environment**, on the scoped lookup
at any frame. -/
theorem wildcard_selection {space : Space} {policy : Policy} {live : List Atom} {scope : List String}
    {f : String} {arrow : Atom} {args : List Atom} {before : Frame}
    {outcome : Completed.InvocationSelection}
    (stored : StorageTypesRel space (.symbol f) [arrow]) (closed : TypeSubst.typeVars arrow = [])
    (isArrow : ∃ domains returned, FunctionTypeRel arrow domains returned)
    (single : SingleTypes space args)
    (shape : ∀ {signature : SelectedTypePolicy}, signature.functionType = arrow →
      Wildcards signature.argumentTypes ∧ args.length = signature.argumentTypes.length ∧
        signature.returnType = Atom.undefinedType)
    (chosen : Completed.InvocationSelectionRel space Completed.scopedLookup policy live scope
      (.expression (.symbol f :: args)) (.symbol f) Atom.undefinedType before outcome) :
    ∃ (signature : SelectedTypePolicy) (frame : Frame), signature.functionType = arrow ∧
      outcome = .selected signature [frame] ∧ frame.bindings = before.bindings ∧
      (PlainEnv before.environment → PlainEnv frame.environment) := by
  obtain ⟨candidates, queried, scanned⟩ := chosen
  have same := ScopedIf.scoped_closed_answer stored closed queried
  cases scanned with
  | nil => cases same
  | nonFunction notArrow _ =>
      simp only [List.cons.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact absurd isArrow notArrow
  | selected checks _ =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      obtain ⟨wild, arity, returned⟩ := shape functionType
      obtain ⟨frame, rfl, sameBindings, plain⟩ := wildcard_checks single wild arity returned checks
      exact ⟨_, frame, functionType, rfl, sameBindings, plain⟩
  | rejected checks _ =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      obtain ⟨wild, arity, returned⟩ := shape functionType
      obtain ⟨frame, impossible, _⟩ := wildcard_checks single wild arity returned checks
      cases impossible

/-- The argument checks against wildcard demands exist and keep the frame itself. -/
theorem wildcard_arguments_exist {space : Space} {P : List String} (policy : Policy) {expression : Atom}
    (frame : Frame) : ∀ (args Ts : List Atom) (position : Nat), SingleTypes space args →
      Wildcards Ts → args.length = Ts.length →
      Completed.ApplicabilityArgumentsRel space (Completed.scopedLookup P space) policy expression
        position args Ts [frame] [frame] []
  | [], [], _, _, _, _ => .nil
  | [], _ :: _, _, _, _, arity => by simp at arity
  | _ :: _, [], _, _, _, arity => by simp at arity
  | a :: rest, T :: Ts, position, single, wild, arity => by
      obtain ⟨A, stored, closedA⟩ := single a List.mem_cons_self
      have head : Completed.ArgumentChecksRel space (Completed.scopedLookup P space) policy expression
          a T position [frame] [frame] [] :=
        .cons (ScopedIf.scoped_closed_answers stored closedA)
          (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy frame
            (wildcard_match (wild T List.mem_cons_self) A _)))) .nil) .nil
      exact .cons head (wildcard_arguments_exist policy frame rest Ts (position + 1)
        (fun b member => single b (List.mem_cons_of_mem _ member))
        (fun U member => wild U (List.mem_cons_of_mem _ member)) (by simpa using arity))

/-- **The admission against a closed arrow with wildcard demands exists**, selecting the arrow with
the frame itself as its one activation. -/
theorem wildcard_selection_exists {space : Space} (policy : Policy) (live : List Atom)
    (scope : List String) {f : String} (signature : SelectedTypePolicy) {args : List Atom}
    (before : Frame) (stored : StorageTypesRel space (.symbol f) [signature.functionType])
    (closed : TypeSubst.typeVars signature.functionType = []) (single : SingleTypes space args)
    (wild : Wildcards signature.argumentTypes) (arity : args.length = signature.argumentTypes.length)
    (returned : signature.returnType = Atom.undefinedType) :
    Completed.InvocationSelectionRel space Completed.scopedLookup policy live scope
      (.expression (.symbol f :: args)) (.symbol f) Atom.undefinedType before
      (.selected signature [before]) := by
  refine ⟨[signature.functionType], ScopedIf.scoped_closed_answers stored closed, ?_⟩
  have arguments := wildcard_arguments_exist (P := invocationTypeScope scope live
    (.expression (.symbol f :: args)) Atom.undefinedType before.bindings) (space := space)
    (expression := .expression (.symbol f :: args)) policy before args signature.argumentTypes 1
    single wild arity
  have checks := Completed.ApplicationChecksRel.checked (space := space)
    (lookup := Completed.scopedLookup (invocationTypeScope scope live
      (.expression (.symbol f :: args)) Atom.undefinedType before.bindings) space) (policy := policy)
    (expected := Atom.undefinedType) (selected := signature) (before := before)
    (operator := .symbol f) (arguments := args) rfl arguments
    (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy before
      (by rw [returned]; exact .undefinedLeft _ _)))) .nil)
  exact .selected checks (List.cons_ne_nil _ _)

/-! ## Controls -/

namespace Controls

/-- **Negative control**: a held expression is not plain. -/
theorem held_not_plain : ¬ Plain (.expression .held [.symbol "pair"]) := by
  intro plain
  exact absurd plain.children.1 (by decide)

theorem letArrow_closed : TypeSubst.typeVars letArrow = [] := by decide

theorem unifyArrow_closed : TypeSubst.typeVars unifyArrow = [] := by decide

end Controls

#print axioms unify_plain
#print axioms read_plain
#print axioms typeRenew_plain
#print axioms castRenew_plain
#print axioms letArrow_matches
#print axioms unifyArrow_matches
#print axioms wildcard_selection
#print axioms wildcard_selection_exists
#print axioms Controls.held_not_plain

end LetPlain

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
