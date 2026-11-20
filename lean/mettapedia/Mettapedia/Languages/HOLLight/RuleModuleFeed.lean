import Mettapedia.Languages.HOLLight.RuleModuleReader

/-!
# The feed of a compiled reader: pending wrappers, the HOLR loop, promises, the record table

The HOLR stream reader, a rule module compiled to C, feeds the records it reads to the compiled HOL
Light kernel module while the module runs (`rc_feed.c`, with the HOL description `hlm_feed.c`).
This file states and proves the four contracts that feed rests on.

* **Pending wrappers; stop and resume** (`rc_pend_push`, `rc_pend_apply`, `RC_STOPPED`,
  `rc_resume`).  A rule whose last two steps are `t := J(args)` and the tail call `W(..., t, ...)`
  (`t` at position `k` and nowhere else) is compiled as: push a frame (`W`, `k`, `W`'s other
  arguments), then tail-call `J`.  What the compiled code of a judgment does on its arguments is
  modelled by what its one applicable rule does at its end (`TailStep`: a value or a failure, a
  tail call, or a frame pushed and a tail call); frames are any type with how one is applied
  (`apply`; the C's frames are `RcPend`, applied by `RcPend.apply`).  The rules' meaning is the
  nested evaluation (`Eval`); the compiled code pushes frames as it runs (`Run`), and whoever made
  the call applies the frames above its mark to the run's value, the newest first, a failure
  dropping the rest (`applyFrames`, `Closed`).  The two agree, failures included (`run_eval`,
  `eval_run`, `closed_iff_eval`); both are deterministic (`Run.functional`, `Eval.functional`).  A
  run may stop on entering the safepoint (`RunS`); its arguments and its frames are its whole
  state, so a run resumed from them as often as it stops (`Session`) is the run without the stops
  (`session_iff_run`, `resume_same`).  A host may also take the frames out at every stop and resume
  with the frames below them only (`FeedSession`, as `rc_feed.c` does); the frames it took, applied
  at the end, give the rules' value of the entry (`feedSession_run`, `feed_eval`).  When every frame
  conses its element onto every value `D h xs t` the loop can end with, the frames applied to the
  loop's own value `D h rs t` give `D h (x1 :: ... :: xn :: rs) t`, `x1 ... xn` their elements the
  oldest first (`applyFrames_consLaw`; for the C's frames read out as `rf_take` reads them,
  `rcPend_takeOut`; with the feed, `feed_eval_consLaw`).
* **The HOLR reader's loop** (modules `HOLRRecords`, `HOLRTrailer`).  The judgments `HOLRLoop`,
  `HOLRControl`, `RecordCarry`, `StreamPush` and the trailer's `EndCount`, `EndChecksum`,
  `EndCountCheck`, `EndHash`, `EndChecksumCheck`, `EndTrailing` are transcribed one constructor per
  rule, named after the rule's label, the premises the nested calls in call-by-value order (as in
  `RuleModuleReader`); so are `ReadWordLE64` (with `ReadFixedLE`, `FixedJoin`), the schema list
  (`HOLRSchema`, one value: `holrSchema_iff`) and `ReadRecord` with the field decoder of
  `ByteRecords` (`SelectRecord`, `RecordFields`, `DecodeFields`, `FieldCarry`, `FieldPush`,
  `ReadOperand`, `OperandWord`, `CountValues`, `CountValuesBound`, `ReadValues`, `OperandBytes`,
  `OperandWords`, `OperandPairs`, `ReadWords`, `WordsCarry`, `WordsPush`, `ReadPairs`,
  `PairsFirst`, `PairsSecond`, `PairsPush`, with their refusal rules).  `NatCompare`, `PackByte`,
  `NatInc`, `NatPred`, `ReadULEB62`, `FNV`, `TakeBytes`, `NatSubtract`, `ByteLength` and
  `LookupSchema` are `RuleModuleReader`'s.  The loop's judgments take the judgment answering
  `ReadRecord` as a parameter (`RR`), so that their laws hold for any such judgment; the module's
  is `ReadRecord`.  The loop as its compiled code runs it (`RawLoop`: `RecordNext` pushes the
  frame of its `StreamPush`, which holds the record, and tail-calls the loop) ends only with
  `HOLRDecoded header RecordsNil t`, for the loop's header (`RawLoop.decoded`; the trailer:
  `EndCount.decoded`).  The values of `HOLRLoop` are exactly those of the raw loop with its frames
  applied (`holrLoop_iff_raw`), and each is `HOLRDecoded header (RecordsCons r1 (... (RecordsCons rn
  RecordsNil))) t` with `r1 ... rn` the records pushed, the oldest first (`holrLoop_value`, by the
  cons law of `StreamCons`); `StreamBad` and `StreamShort` never apply in the loop
  (`recordNext_streamCons`).  The loop has a value on every input when the judgment answering
  `ReadRecord` gives, on every input the loop gives it, a result of a shape `RecordCarry` has a
  rule for, a decoded record leaving at most the bytes after its opcode (`ReadRecordGives`,
  `holrLoop_total`); the module's `ReadRecord` does (`readRecordGives`, from the totality of each
  judgment of the field decoder with the shapes of its results: `readULEB62_rest`,
  `takeBytes_rest`, `readWords_total`, `readPairs_total`, `readValues_total`, `readOperand_total`,
  `decodeFields_total`, `selectRecord_total`), so the loop has a value on every input
  (`holrLoop_total_readRecord`); the trailer has a value on every state `ReadULEB62` gives
  (`readULEB62_shape`, `endCount_total`).
* **Promises** (`(rep SORT promise)`, `rc_promise_force`, `rc_term_equal`).  A value is an atom, a
  symbolic term, or a promise holding the host's number (`RVal`); the module data a value stands
  for (`MData`, `dataOf`) takes for each promise the data the host promised (`D`).  The host is a
  relation (`force`: asked for a promise, it may build the term anew each time) and its contract a
  structure (`HostContract`: what it gives is never a promise, and stands for the promised data
  each time; `Keeps`: it gives something).  The view of a promise (`TagIs`, `KidIs`:
  `RC_TAG_promise`, `RC_KID_promise`, each read forcing it) is the view of its forced term
  (`tagIs_promise_iff`, `kidIs_promise_iff`) and reads its module data (`TagIs.data`, `KidIs.data`;
  conversely `kidIs_of_data`).  `rc_term_equal` as the C computes it (`TermEqual`: the identity
  test, both sides forced when either is a promise, atoms by their representation's test, terms by
  constructor, arity and children, the last child first, stopping at the first difference) answers
  `true` exactly on equal module data (`TermEqual.sound`) and has an answer on every pair
  (`termEqual_total`).  Hence a computation that reads values only through views and compares them
  with `rc_term_equal` (`Prog`; run on the C's values, `RunV`) computes on module data
  (`RunV.data`, `RunD.toRunV`, `RunD.functional`), and gives the same result, as module data, on a
  promise as on the term it promises (`runV_same`, `runV_promise`).
* **The record table** (`hol_stream_records`, the schema, the HOL Light module's record
  constructors).  The opcodes (`HolrOp.code`), the table (`holStreamRecords`), the constructors'
  child sorts (`HolRecordCtor.childSorts`) and the schema are transcribed.  By `decide`: the table
  names every opcode of the schema exactly once and nothing else, each constructor once
  (`holStreamRecords_opcodes`); for every row the reader's `LookupSchema` finds the opcode's layout,
  and the constructor's children are, one per field and in order, of the sort the field's kind
  requires: a word a numeral (`Nat`), bytes a name (`Str`), a list of words an id list (`Ids`), a
  list of pairs an id-pair list (`IdPairs`) (`holStreamRecords_fields`, `holStreamRecords_arity`).
  `rf_child` is modelled on its loop (`rfScan`, `rfChild`, over the sorts' representations and data
  constructors): it builds numerals as immediates, names as interned byte strings, id lists one
  number per cell and id-pair lists two per cell (`rfChild_feedSorts`), each from the operand kind
  of the field that requires the sort (`rfChild_fieldSort`), so `rf_build`'s checks pass on every
  row (`holStreamRecords_build`).
* **The probes.**  The compiled reader pushes frames at three rules: `StreamRead` and `FileRead`
  (below the loop, not on the feed's entry `ReadHOLRPrefix`) and `RecordNext`, which pushes
  `StreamPush` with the record at position `0` and the hole at `1`, then tail-calls `HOLRLoop`, the
  safepoint; its `StreamPush` and `HOLRControl` follow the transcribed rules.  The compiled HOL Light
  module, fed by the reader through these frames, gives the native replay's verdict on the eight
  fixture streams of its tests (accepted, refused, and malformed for bad magic, bad checksum,
  trailing bytes, truncation).  The reader called through its entry (the frames applied there)
  gives the native scanner's observation (the header, every record in order, the end) on the same
  eight streams and on 1,172 corruptions of two of them.  The transcriptions of the opcodes, the
  table, the schema, the constructors' child sorts and the sorts' representations and data
  constructors were compared, by a script, with their sources and with the compiled module's own
  tables (`rc_ctor_arity`, `rc_ctor_asort`, `rc_ctor_judgment`, `rc_sort_rep`): all agree.

What the models leave out.

* Pending wrappers.  `prog` is a function: the compiled judgments are deterministic (the decision
  DAG selects at most one rule, which the compiler's validator checks).  A rule's premises before
  its last call are inside its step; that none of them reaches the safepoint is the compiler's
  check (`check_safepoint`), trusted, as is that a wrapper never reaches it.  A wrapper's value is a
  function (`call`): `rc_call` applies whatever frames the call leaves.  Values are abstract: the
  frame stack's storage (`rc_pend_grow`), the collector (frames and safepoint arguments are roots;
  it moves values, it does not change them), the trace and running out of memory are not modelled.
  The checks `rc_feed.c` makes at a stop (every frame the wrapper's, the element not the hole) are
  hypotheses of `rcPend_takeOut`; a failed check stops the run.
* The loop.  `CodecState` is transcribed with the constructors the loop, the trailer and
  `ReadRecord` produce or match.  That the generated loop runs as `RawLoop` is what the compiler
  emits (checked by its validator and the probes), not proved.
* Promises.  Values are trees, not words: the identity test is allowed on equal values only (one
  word, one value); the atoms' test is a parameter, its exactness (`Atoms.Exact`) the contract of
  the atoms' own representations.  The C's explicit stack is modelled by recursion in the order it
  pops the pairs.  That the generated code reads values only through views, `rc_term_equal` and the
  builders is how `rulec` emits it, not proved.
* The table.  `rf_child`'s loop is modelled as the C runs it: a list sort must have exactly one
  constructor without children and one cell, a second of either (or any other constructor, for
  the cell) refusing its slot for good.

Notes for proving here: the mutually inductive judgments are handled by mutual structural recursion
on their derivations (term-mode `match` with all indices as patterns); the `induction` tactic does
not take mutual inductive types.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RuleModuleFeed

open RuleModuleReader

/-! ## Pending wrappers -/

section Pending

universe u v w x y z

variable {J : Type u} {V : Type v} {F : Type w}

/-- `rc_pend_apply`: the frames above a caller's mark (a list, the newest first) applied to a run's
value, the newest first; each gives its wrapper's value with the value in its hole (`apply`), and
after a failure (`none`) the remaining frames are dropped. -/
def applyFrames (apply : F → V → Option V) : List F → Option V → Option V
  | [], v => v
  | f :: fs, v => applyFrames apply fs (v.bind (apply f))

@[simp] theorem applyFrames_nil (apply : F → V → Option V) (v : Option V) :
    applyFrames apply [] v = v := rfl

@[simp] theorem applyFrames_cons (apply : F → V → Option V) (f : F) (fs : List F) (v : Option V) :
    applyFrames apply (f :: fs) v = applyFrames apply fs (v.bind (apply f)) := rfl

theorem applyFrames_append (apply : F → V → Option V) :
    ∀ (fs gs : List F) (v : Option V),
      applyFrames apply (fs ++ gs) v = applyFrames apply gs (applyFrames apply fs v)
  | [], _, _ => rfl
  | f :: fs, gs, v => applyFrames_append apply fs gs (v.bind (apply f))

/-- A failure drops every frame: the caller's value is a failure. -/
@[simp] theorem applyFrames_none (apply : F → V → Option V) :
    ∀ fs : List F, applyFrames apply fs none = none
  | [] => rfl
  | _ :: fs => applyFrames_none apply fs

/-- A frame as `rc_pend_push` stores it (`RcPend`): the wrapper, the position `k` of the value it
waits for, and the wrapper's arguments (the slot at `k` unused until the frame is applied). -/
structure RcPend (W : Type x) (V : Type v) where
  /-- The wrapper (`RcPend.w`). -/
  w : W
  /-- The position of the value the frame waits for (`RcPend.k`). -/
  k : Nat
  /-- The wrapper's arguments (`RcPend.a`, `RcPend.n` of them). -/
  args : List V

/-- How `rc_pend_apply` applies one frame: the value is written into the slot at `k`
(`f.a[f.k] = v`) and the wrapper is called on the arguments (`rc_call`, which itself applies
whatever that call leaves pending, so that `call` is the wrapper's whole value). -/
def RcPend.apply {W : Type x} (call : W → List V → Option V) (f : RcPend W V) (v : V) : Option V :=
  call f.w (f.args.set f.k v)

/-- What the compiled code of a judgment does on its arguments, as the one rule that applies
decides it (the compiled judgments are deterministic: their rules do not overlap, and the
compiler's decision DAG, checked by its validator, selects at most one): it ends with a value or a
failure (`ret`), makes its last call a tail call (`tail`), or pushes a frame and tail-calls the
judgment whose value the frame waits for (`pend`).  The rule's other premises (calls that are not
tail calls, each of which applies the frames its callee leaves) are inside the step. -/
inductive TailStep (J : Type u) (V : Type v) (F : Type w) : Type (max u v w)
  /-- The rule's value, or its failure (`none`). -/
  | ret (v : Option V)
  /-- A tail call. -/
  | tail (j : J) (args : List V)
  /-- A pending wrapper: the frame `f` pushed, then the tail call. -/
  | pend (f : F) (j : J) (args : List V)

section Machine

variable (prog : J → List V → TailStep J V F) (apply : F → V → Option V)

/-- The rules' meaning: the nested evaluation.  A rule `t := J(args); W(..., t, ...)` gives its
wrapper's value on the value of the wrapped call, and fails when that call fails. -/
inductive Eval : J → List V → Option V → Prop
  /-- The rule ends with its value or its failure. -/
  | ret {j : J} {a : List V} {v : Option V} : prog j a = .ret v → Eval j a v
  /-- The rule's tail call. -/
  | tail {j : J} {a : List V} {j' : J} {a' : List V} {v : Option V} :
      prog j a = .tail j' a' → Eval j' a' v → Eval j a v
  /-- The wrapper `W(..., J(args), ...)`. -/
  | pend {j : J} {a : List V} {f : F} {j' : J} {a' : List V} {v : Option V} :
      prog j a = .pend f j' a' → Eval j' a' v → Eval j a (v.bind (apply f))

/-- The compiled code: tail calls, and frames pushed onto the stack of pending frames (a list, the
newest first); the run's own value and the stack it leaves. -/
inductive Run : J → List V → List F → Option V → List F → Prop
  /-- The rule ends: the run's value, the stack as it is. -/
  | ret {j : J} {a : List V} {fs : List F} {v : Option V} : prog j a = .ret v → Run j a fs v fs
  /-- A tail call. -/
  | tail {j : J} {a : List V} {j' : J} {a' : List V} {fs : List F} {v : Option V} {fs' : List F} :
      prog j a = .tail j' a' → Run j' a' fs v fs' → Run j a fs v fs'
  /-- `rc_pend_push`, then the tail call. -/
  | pend {j : J} {a : List V} {f : F} {j' : J} {a' : List V} {fs : List F} {v : Option V}
      {fs' : List F} :
      prog j a = .pend f j' a' → Run j' a' (f :: fs) v fs' → Run j a fs v fs'

/-- A call that is not a tail call, and the host's entry `rc_call`: the run from the caller's
stack `fs`, then the frames it pushed above the caller's mark applied (`RC_CLOSED`,
`rc_pend_unwind`). -/
def Closed (fs : List F) (j : J) (a : List V) (v : Option V) : Prop :=
  ∃ v₀ new, Run prog j a fs v₀ (new ++ fs) ∧ applyFrames apply new v₀ = v

variable {prog apply}

/-- A run only pushes, and never reads the frames below its start: the stack it leaves is the
frames it pushed (the newest first) over the stack it started with, and from any other stack it
gives the same value and pushes the same frames. -/
theorem Run.frames {j : J} {a : List V} {fs : List F} {v : Option V} {fs' : List F}
    (h : Run prog j a fs v fs') : ∃ new, fs' = new ++ fs ∧ ∀ gs, Run prog j a gs v (new ++ gs) := by
  induction h with
  | ret hp => exact ⟨[], rfl, fun _ => .ret hp⟩
  | tail hp _ ih =>
    obtain ⟨new, e, hr⟩ := ih
    exact ⟨new, e, fun gs => .tail hp (hr gs)⟩
  | @pend j a f j' a' fs v fs' hp _ ih =>
    obtain ⟨new, e, hr⟩ := ih
    refine ⟨new ++ [f], by simp [e], fun gs => .pend hp ?_⟩
    rw [List.append_assoc]
    exact hr (f :: gs)

/-- **Pending wrappers compute the rules' meaning.**  The frames a run pushes, applied to the run's
value the newest first, give the value of the nested evaluation, failures included. -/
theorem run_eval {j : J} {a : List V} {fs : List F} {v : Option V} {fs' : List F}
    (h : Run prog j a fs v fs') :
    ∃ new, fs' = new ++ fs ∧ Eval prog apply j a (applyFrames apply new v) := by
  induction h with
  | ret hp => exact ⟨[], rfl, .ret hp⟩
  | tail hp _ ih =>
    obtain ⟨new, e, he⟩ := ih
    exact ⟨new, e, .tail hp he⟩
  | @pend j a f j' a' fs v fs' hp _ ih =>
    obtain ⟨new, e, he⟩ := ih
    refine ⟨new ++ [f], by simp [e], ?_⟩
    rw [applyFrames_append]
    exact .pend hp he

/-- Conversely, every value of the nested evaluation is the value a run gives with its frames
applied, from any stack. -/
theorem eval_run {j : J} {a : List V} {v : Option V} (h : Eval prog apply j a v) :
    ∀ fs : List F, ∃ v₀ new, Run prog j a fs v₀ (new ++ fs) ∧ applyFrames apply new v₀ = v := by
  induction h with
  | ret hp => exact fun fs => ⟨_, [], .ret hp, rfl⟩
  | tail hp _ ih =>
    intro fs
    obtain ⟨v₀, new, hr, e⟩ := ih fs
    exact ⟨v₀, new, .tail hp hr, e⟩
  | @pend j a f j' a' v hp _ ih =>
    intro fs
    obtain ⟨v₀, new, hr, e⟩ := ih (f :: fs)
    refine ⟨v₀, new ++ [f], ?_, ?_⟩
    · rw [List.append_assoc]
      exact .pend hp hr
    · rw [applyFrames_append, e]
      rfl

/-- **A closed call computes the rules' meaning**, from any caller's stack. -/
theorem closed_iff_eval {fs : List F} {j : J} {a : List V} {v : Option V} :
    Closed prog apply fs j a v ↔ Eval prog apply j a v := by
  constructor
  · rintro ⟨v₀, new, hr, rfl⟩
    obtain ⟨new', e, he⟩ := run_eval (apply := apply) hr
    have : new = new' := List.append_cancel_right e
    subst this
    exact he
  · intro h
    exact eval_run h fs

/-- The compiled code is deterministic: one value and one stack. -/
theorem Run.functional {j : J} {a : List V} {fs : List F} {v v' : Option V} {fs' fs'' : List F}
    (h : Run prog j a fs v fs') (h' : Run prog j a fs v' fs'') : v = v' ∧ fs' = fs'' := by
  induction h generalizing v' fs'' with
  | ret hp =>
    cases h' with
    | ret hp' => rw [hp] at hp'; cases hp'; exact ⟨rfl, rfl⟩
    | tail hp' _ => rw [hp] at hp'; cases hp'
    | pend hp' _ => rw [hp] at hp'; cases hp'
  | tail hp _ ih =>
    cases h' with
    | ret hp' => rw [hp] at hp'; cases hp'
    | tail hp' h'' => rw [hp] at hp'; cases hp'; exact ih h''
    | pend hp' _ => rw [hp] at hp'; cases hp'
  | pend hp _ ih =>
    cases h' with
    | ret hp' => rw [hp] at hp'; cases hp'
    | tail hp' _ => rw [hp] at hp'; cases hp'
    | pend hp' h'' => rw [hp] at hp'; cases hp'; exact ih h''

/-- The nested evaluation is deterministic. -/
theorem Eval.functional {j : J} {a : List V} {v v' : Option V} (h : Eval prog apply j a v)
    (h' : Eval prog apply j a v') : v = v' := by
  induction h generalizing v' with
  | ret hp =>
    cases h' with
    | ret hp' => rw [hp] at hp'; cases hp'; rfl
    | tail hp' _ => rw [hp] at hp'; cases hp'
    | pend hp' _ => rw [hp] at hp'; cases hp'
  | tail hp _ ih =>
    cases h' with
    | ret hp' => rw [hp] at hp'; cases hp'
    | tail hp' h'' => rw [hp] at hp'; cases hp'; exact ih h''
    | pend hp' _ => rw [hp] at hp'; cases hp'
  | pend hp _ ih =>
    cases h' with
    | ret hp' => rw [hp] at hp'; cases hp'
    | tail hp' _ => rw [hp] at hp'; cases hp'
    | pend hp' h'' => rw [hp] at hp'; cases hp'; rw [ih h'']

/-! ### Stop and resume at the safepoint -/

/-- What a run that may stop at the safepoint comes to. -/
inductive Outcome (V : Type v) (F : Type w) : Type (max v w)
  /-- It ended, with its value and the stack it left. -/
  | ended (v : Option V) (frames : List F)
  /-- It stopped on entering the safepoint (`RC_STOPPED`): the safepoint's arguments
  (`rc_roots`) and the stack. -/
  | stopped (args : List V) (frames : List F)

variable (prog) (sp : J)

/-- The compiled code with its safepoint `sp`: on entering it the host may stop the run
(`rc_stop_hook`), which then returns `RC_STOPPED` keeping the safepoint's arguments and the
frames.  Only tail calls and pending-wrapper calls lead to the safepoint (the compiler rejects any
other call of a judgment that reaches it), so these two are the whole state of a stopped run. -/
inductive RunS : J → List V → List F → Outcome V F → Prop
  /-- The host stops the run on entering the safepoint. -/
  | stop {a : List V} {fs : List F} : RunS sp a fs (.stopped a fs)
  /-- The rule ends. -/
  | ret {j : J} {a : List V} {fs : List F} {v : Option V} :
      prog j a = .ret v → RunS j a fs (.ended v fs)
  /-- A tail call. -/
  | tail {j : J} {a : List V} {j' : J} {a' : List V} {fs : List F} {o : Outcome V F} :
      prog j a = .tail j' a' → RunS j' a' fs o → RunS j a fs o
  /-- A pending wrapper. -/
  | pend {j : J} {a : List V} {f : F} {j' : J} {a' : List V} {fs : List F} {o : Outcome V F} :
      prog j a = .pend f j' a' → RunS j' a' (f :: fs) o → RunS j a fs o

/-- A run with its stops and resumptions (`rc_call`, then `rc_resume` from the saved arguments with
the frames kept, as often as it stops) until it ends. -/
inductive Session : J → List V → List F → Option V → List F → Prop
  /-- The run ends. -/
  | ended {j : J} {a : List V} {fs : List F} {v : Option V} {fs' : List F} :
      RunS prog sp j a fs (.ended v fs') → Session j a fs v fs'
  /-- The run stops; it is resumed from the safepoint. -/
  | resumed {j : J} {a : List V} {fs : List F} {a' : List V} {fs' : List F} {v : Option V}
      {fs'' : List F} :
      RunS prog sp j a fs (.stopped a' fs') → Session sp a' fs' v fs'' → Session j a fs v fs''

/-- A run as `rc_feed.c` drives it over the base stack `base`: at each stop the frames above the
base are taken out (`rf_take`) and dropped (`pend_drop`), and the run resumes from the safepoint
with the base stack; the index lists every frame taken, the newest first. -/
inductive FeedSession (base : List F) : J → List V → Option V → List F → Prop
  /-- The run ends; the frames it left above the base are taken. -/
  | ended {j : J} {a : List V} {v : Option V} {new : List F} :
      RunS prog sp j a base (.ended v (new ++ base)) → FeedSession base j a v new
  /-- The run stops; the frames above the base are taken; it resumes over the base. -/
  | resumed {j : J} {a : List V} {a' : List V} {taken : List F} {v : Option V} {new : List F} :
      RunS prog sp j a base (.stopped a' (taken ++ base)) → FeedSession base sp a' v new →
        FeedSession base j a v (new ++ taken)

variable {prog sp}

theorem RunS.toRun_of_ended {j : J} {a : List V} {fs : List F} {o : Outcome V F}
    (h : RunS prog sp j a fs o) : ∀ {v : Option V} {fs' : List F}, o = .ended v fs' →
      Run prog j a fs v fs' := by
  induction h with
  | stop => intro v fs' e; cases e
  | ret hp => intro v fs' e; cases e; exact .ret hp
  | tail hp _ ih => intro v fs' e; exact .tail hp (ih e)
  | pend hp _ ih => intro v fs' e; exact .pend hp (ih e)

/-- A stopped run, resumed from its saved state, is the run that did not stop. -/
theorem RunS.toRun_of_stopped {j : J} {a : List V} {fs : List F} {o : Outcome V F}
    (h : RunS prog sp j a fs o) : ∀ {a' : List V} {fs' : List F}, o = .stopped a' fs' →
      ∀ {v : Option V} {fs'' : List F}, Run prog sp a' fs' v fs'' → Run prog j a fs v fs'' := by
  induction h with
  | stop => intro a' fs' e v fs'' hr; cases e; exact hr
  | ret _ => intro a' fs' e; cases e
  | tail hp _ ih => intro a' fs' e v fs'' hr; exact .tail hp (ih e hr)
  | pend hp _ ih => intro a' fs' e v fs'' hr; exact .pend hp (ih e hr)

theorem Run.toRunS {j : J} {a : List V} {fs : List F} {v : Option V} {fs' : List F}
    (h : Run prog j a fs v fs') : RunS prog sp j a fs (.ended v fs') := by
  induction h with
  | ret hp => exact .ret hp
  | tail hp _ ih => exact .tail hp ih
  | pend hp _ ih => exact .pend hp ih

/-- **Stopping and resuming changes nothing.**  A run with any stops and resumptions ends with the
value and the frames of the run without them, and conversely. -/
theorem session_iff_run {j : J} {a : List V} {fs : List F} {v : Option V} {fs' : List F} :
    Session prog sp j a fs v fs' ↔ Run prog j a fs v fs' := by
  constructor
  · intro h
    induction h with
    | ended h => exact h.toRun_of_ended rfl
    | resumed hs _ ih => exact hs.toRun_of_stopped rfl ih
  · intro h
    exact .ended h.toRunS

/-- The value and the frames after a resumption are those of the run without the stop. -/
theorem resume_same {j : J} {a : List V} {fs : List F} {a' : List V} {fs' : List F}
    {v w : Option V} {fs'' gs : List F} (hstop : RunS prog sp j a fs (.stopped a' fs'))
    (hres : Run prog sp a' fs' v fs'') (hrun : Run prog j a fs w gs) : v = w ∧ fs'' = gs :=
  (hstop.toRun_of_stopped rfl hres).functional hrun

/-- A run that the feed drives, its frames taken out at every stop, is the run without the stops,
with every frame it pushed: those taken. -/
theorem feedSession_run {base : List F} {j : J} {a : List V} {v : Option V} {all : List F}
    (h : FeedSession prog sp base j a v all) : Run prog j a base v (all ++ base) := by
  induction h with
  | ended h => exact h.toRun_of_ended rfl
  | @resumed j a a' taken v new hs _ ih =>
    obtain ⟨new', e, hr⟩ := ih.frames
    have : new = new' := List.append_cancel_right e
    subst this
    rw [List.append_assoc]
    exact hs.toRun_of_stopped rfl (hr (taken ++ base))

/-- **The feed computes the rules' value.**  The host calls the entry `j` (`rc_call`); the run stops
where the loop starts, with the frames `base` below it; from then on the host takes the frames
above `base` out at every stop and resumes; when the run ends with `v`, it applies `base`
(`rc_pend_apply` from the stop mark).  The frames taken (`all`, the newest first) applied to `v`,
and then `base`, give the rules' value of the entry. -/
theorem feed_eval {j : J} {a a0 : List V} {base : List F} {v : Option V} {all : List F}
    (hfirst : RunS prog sp j a [] (.stopped a0 base)) (hfeed : FeedSession prog sp base sp a0 v all) :
    Eval prog apply j a (applyFrames apply base (applyFrames apply all v)) := by
  have hr : Run prog j a [] v (all ++ base) := hfirst.toRun_of_stopped rfl (feedSession_run hfeed)
  obtain ⟨new, e, he⟩ := run_eval (apply := apply) hr
  rw [List.append_nil] at e
  subst e
  rwa [applyFrames_append] at he

end Machine

/-! ### Taking the frames out -/

/-- **Taking the frames out.**  When every frame `f` conses its element `elem f` onto every value
`D h xs t` the loop can end with (`apply f (D h xs t) = D h (elem f :: xs) t`), the frames (the
newest first) applied to `D h xs t` give `D h (x1 :: ... :: xn :: xs) t`, `x1 ... xn` their
elements the oldest first. -/
theorem applyFrames_consLaw {X : Type x} {H : Type y} {T : Type z} (apply : F → V → Option V)
    (D : H → List X → T → V) (elem : F → X)
    (law : ∀ f h xs t, apply f (D h xs t) = some (D h (elem f :: xs) t)) :
    ∀ (fs : List F) (h : H) (xs : List X) (t : T),
      applyFrames apply fs (some (D h xs t)) = some (D h ((fs.map elem).reverse ++ xs) t)
  | [], _, _, _ => rfl
  | f :: fs, h, xs, t => by
    rw [applyFrames_cons]
    show applyFrames apply fs (apply f (D h xs t)) = _
    rw [law, applyFrames_consLaw apply D elem law fs h (elem f :: xs) t]
    simp

/-- `rf_take`: the elements at position `e` of the frames' arguments, the frames listed the newest
first, read the oldest first; `none` when a frame has no argument at `e`. -/
def takeOut {W : Type x} (e : Nat) : List (RcPend W V) → Option (List V)
  | [] => some []
  | f :: fs => (takeOut e fs).bind fun xs => f.args[e]?.map fun x => xs ++ [x]

/-- The cons law of a wrapper `w` (`StreamCons` for the HOLR reader): on every argument list of its
arity `n` with an element `x` at position `e` and a value `D h xs t` at the hole `k`, the wrapper's
value is `D h (x :: xs) t`. -/
def ConsLaw {W : Type x} {H : Type y} {T : Type z} (call : W → List V → Option V) (w : W)
    (n e k : Nat) (D : H → List V → T → V) : Prop :=
  ∀ (args : List V) (x : V) (h : H) (xs : List V) (t : T),
    args.length = n → args[e]? = some x → args[k]? = some (D h xs t) →
      call w args = some (D h (x :: xs) t)

/-- **Taking the elements out of the C's frames** (`rf_take`).  If every frame is the wrapper's with
its hole at `k` and `n` arguments (`rc_feed.c` checks this at every stop), the element's position
`e` is not the hole, and the wrapper satisfies its cons law, then the frames applied to `D h rs t`
give `D h (xs ++ rs) t`, `xs` the elements taken out, the oldest first. -/
theorem rcPend_takeOut {W : Type x} {H : Type y} {T : Type z} {call : W → List V → Option V}
    {w : W} {n e k : Nat} {D : H → List V → T → V} (law : ConsLaw call w n e k D) (hek : e ≠ k)
    (hk : k < n) (fs : List (RcPend W V)) (hf : ∀ f ∈ fs, f.w = w ∧ f.k = k ∧ f.args.length = n)
    {xs : List V} (hx : takeOut e fs = some xs) (h : H) (rs : List V) (t : T) :
    applyFrames (RcPend.apply call) fs (some (D h rs t)) = some (D h (xs ++ rs) t) := by
  induction fs generalizing xs rs with
  | nil =>
    simp only [takeOut, Option.some.injEq] at hx
    subst hx
    rfl
  | cons f fs ih =>
    simp only [takeOut, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
    obtain ⟨ys, hys, x, hxe, rfl⟩ := hx
    obtain ⟨hw, hkf, hn⟩ := hf f (List.mem_cons_self ..)
    have hcall : RcPend.apply call f (D h rs t) = some (D h (x :: rs) t) := by
      unfold RcPend.apply
      rw [hw, hkf]
      apply law
      · rw [List.length_set, hn]
      · rw [List.getElem?_set_ne (Ne.symm hek)]
        exact hxe
      · rw [List.getElem?_set_self (by rw [hn]; exact hk)]
    rw [applyFrames_cons]
    show applyFrames (RcPend.apply call) fs (RcPend.apply call f (D h rs t)) = _
    rw [hcall, ih (fun g hg => hf g (List.mem_cons_of_mem _ hg)) hys (x :: rs)]
    simp

/-- The feed's soundness with the cons law: the entry's value is `D h (xs ++ rs) t`, `xs` the
elements of every frame taken, the oldest first, when the loop ends with `D h rs t` and no frame
lies below it. -/
theorem feed_eval_consLaw {X : Type x} {H : Type y} {T : Type z}
    {prog : J → List V → TailStep J V F} {apply : F → V → Option V} {sp : J}
    (D : H → List X → T → V) (elem : F → X)
    (law : ∀ f h xs t, apply f (D h xs t) = some (D h (elem f :: xs) t))
    {j : J} {a a0 : List V} {all : List F} {h : H} {rs : List X} {t : T}
    (hfirst : RunS prog sp j a [] (.stopped a0 []))
    (hfeed : FeedSession prog sp [] sp a0 (some (D h rs t)) all) :
    Eval prog apply j a (some (D h ((all.map elem).reverse ++ rs) t)) := by
  have he := feed_eval (apply := apply) hfirst hfeed
  rwa [applyFrames_consLaw apply D elem law, applyFrames_nil] at he

end Pending

/-! ## The HOLR reader's loop and trailer -/

/-! ### The data -/

/-- Sort `HOLRReason`. -/
inductive Reason
  /-- `BadMagic`. -/
  | badMagic
  /-- `BadHeader`. -/
  | badHeader
  /-- `BadVersion`. -/
  | badVersion
  /-- `BadOpcode`. -/
  | badOpcode
  /-- `BadCount`. -/
  | badCount
  /-- `BadChecksum`. -/
  | badChecksum
  /-- `TrailingBytes`. -/
  | trailingBytes
  /-- `MissingEnd`. -/
  | missingEnd
  /-- `Truncated`. -/
  | truncated
  /-- `IntegerEncoding`. -/
  | integerEncoding
  /-- `FieldLimit`. -/
  | fieldLimit
  deriving DecidableEq, Repr

/-- Sort `HOLRTerminal`. -/
inductive Terminal
  /-- `HOLRPrefixOK`. -/
  | prefixOK
  /-- `HOLRPrefixError`. -/
  | prefixError (r : Reason)
  /-- `HOLRPrefixIncomplete`. -/
  | prefixIncomplete
  deriving DecidableEq, Repr

/-- Sort `HOLRHeader`. -/
inductive Header
  /-- `HOLRHeaderBytes`: the kernel id, the version, the profile, the policy, the flags. -/
  | headerBytes (kernel : Bytes) (version profile policy flags : BinNat)
  deriving DecidableEq, Repr

/-- Sort `WordList`. -/
inductive WordList
  /-- `WordsNil`. -/
  | nil
  /-- `WordsCons`. -/
  | cons (n : BinNat) (rest : WordList)
  deriving DecidableEq, Repr

/-- Sort `Pair`. -/
inductive Pair
  /-- `BPair`. -/
  | pair (first second : BinNat)
  deriving DecidableEq, Repr

/-- Sort `PairList`. -/
inductive PairList
  /-- `PairsNil`. -/
  | nil
  /-- `PairsCons`. -/
  | cons (p : Pair) (rest : PairList)
  deriving DecidableEq, Repr

/-- Sort `Operand`. -/
inductive Operand
  /-- `BWord`. -/
  | word (n : BinNat)
  /-- `BBytes`. -/
  | bytes (b : Bytes)
  /-- `BWords`. -/
  | words (ws : WordList)
  /-- `BPairs`. -/
  | pairs (ps : PairList)
  deriving DecidableEq, Repr

/-- Sort `Operands`. -/
inductive Operands
  /-- `OperandsNil`. -/
  | nil
  /-- `OperandsCons`. -/
  | cons (o : Operand) (rest : Operands)
  deriving DecidableEq, Repr

/-- Sort `Record`. -/
inductive Record
  /-- `BRecord`: the opcode and the operands. -/
  | bRecord (op : Byte) (fields : Operands)
  deriving DecidableEq, Repr

/-- Sort `Records`. -/
inductive Records
  /-- `RecordsNil`. -/
  | nil
  /-- `RecordsCons`. -/
  | cons (r : Record) (rest : Records)
  deriving DecidableEq, Repr

/-- The records of a list, in its order: `RecordsCons r1 (... (RecordsCons rn RecordsNil))`. -/
def Records.ofList : List Record → Records
  | [] => .nil
  | r :: rs => .cons r (Records.ofList rs)

/-- Sort `CodecState`: the constructors that the loop, the trailer and `ReadRecord` produce or
match (the sort's constructors that are judgments are not data). -/
inductive State
  /-- `DecodedWord`. -/
  | decodedWord (n : BinNat) (rest : Bytes)
  /-- `NeedInput`. -/
  | needInput
  /-- `BadInteger`. -/
  | badInteger
  /-- `LimitExceeded`. -/
  | limitExceeded
  /-- `Taken`. -/
  | taken (pre rest : Bytes)
  /-- `RecordDecoded`. -/
  | recordDecoded (r : Record) (rest : Bytes)
  /-- `UnknownOpcode`. -/
  | unknownOpcode (op : Byte)
  /-- `HOLRDecoded`: the header, the records, the terminal. -/
  | holrDecoded (h : Header) (rs : Records) (t : Terminal)
  /-- `HOLRMalformed`. -/
  | holrMalformed (r : Reason)
  /-- `FieldsDecoded`. -/
  | fieldsDecoded (fields : Operands) (rest : Bytes)
  /-- `OperandDecoded`. -/
  | operandDecoded (o : Operand) (rest : Bytes)
  /-- `WordsDecoded`. -/
  | wordsDecoded (ws : WordList) (rest : Bytes)
  /-- `PairsDecoded`. -/
  | pairsDecoded (ps : PairList) (rest : Bytes)
  deriving DecidableEq, Repr

/-- The same constructor of `CodecState`, from the part of the sort that `RuleModuleReader`
transcribes. -/
def State.ofCodec : CodecState → State
  | .decodedWord n rest => .decodedWord n rest
  | .needInput => .needInput
  | .badInteger => .badInteger
  | .limitExceeded => .limitExceeded
  | .taken pre rest => .taken pre rest

/-- The literal of `LoopSelect`, as the rule writes it: `127`, the opcode `END`. -/
def lit127 : BinNat :=
  .bit .bit1 (.bit .bit1 (.bit .bit1 (.bit .bit1 (.bit .bit1 (.bit .bit1 (.bit .bit1 .zero))))))

theorem lit127_eq : lit127 = BinNat.ofNat 127 := by decide

/-- The literal of `LoopLess` and `LoopGreater`, as the rules write it (`NatBit Bit0` twenty times
over `NatBit Bit1 NatZero`): `2 ^ 20`, the bound of `ReadRecord`'s counts. -/
def recordLimit : BinNat := BinNat.ofBits (List.replicate 20 Bit.bit0 ++ [Bit.bit1])

theorem recordLimit_eq : recordLimit = BinNat.ofNat 1048576 := by decide

/-! ### The schema (`HOLRSchema`) -/

/-- The schemas of `SchemaPart0` (the opcodes `0x01` ... `0x07`, `0x10`) before `tail`. -/
def holrSchemaPart0 (tail : Schemas) : Schemas :=
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit0 .bit0 .bit0 .bit0 .bit0 .bit1) (.fieldNext .bytes .fieldsEnd)) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit0 .bit0 .bit0 .bit0 .bit1 .bit0) (.fieldNext .word .fieldsEnd)) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit0 .bit0 .bit0 .bit0 .bit1 .bit1) (.fieldNext .word (.fieldNext .words .fieldsEnd))) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit0 .bit0 .bit0 .bit1 .bit0 .bit0) (.fieldNext .word (.fieldNext .word .fieldsEnd))) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit0 .bit0 .bit0 .bit1 .bit0 .bit1) (.fieldNext .word (.fieldNext .word .fieldsEnd))) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit0 .bit0 .bit0 .bit1 .bit1 .bit0) (.fieldNext .word (.fieldNext .word .fieldsEnd))) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit0 .bit0 .bit0 .bit1 .bit1 .bit1) (.fieldNext .word (.fieldNext .word .fieldsEnd))) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit0 .bit1 .bit0 .bit0 .bit0 .bit0) (.fieldNext .word .fieldsEnd)) <|
  tail

/-- The schemas of `SchemaPart1` (the opcodes `0x11` ... `0x18`) before `tail`. -/
def holrSchemaPart1 (tail : Schemas) : Schemas :=
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit0 .bit1 .bit0 .bit0 .bit0 .bit1) (.fieldNext .word (.fieldNext .word .fieldsEnd))) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit0 .bit1 .bit0 .bit0 .bit1 .bit0) (.fieldNext .word (.fieldNext .word .fieldsEnd))) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit0 .bit1 .bit0 .bit0 .bit1 .bit1) (.fieldNext .word (.fieldNext .word .fieldsEnd))) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit0 .bit1 .bit0 .bit1 .bit0 .bit0) (.fieldNext .word .fieldsEnd)) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit0 .bit1 .bit0 .bit1 .bit0 .bit1) (.fieldNext .word .fieldsEnd)) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit0 .bit1 .bit0 .bit1 .bit1 .bit0) (.fieldNext .word (.fieldNext .word .fieldsEnd))) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit0 .bit1 .bit0 .bit1 .bit1 .bit1) (.fieldNext .word (.fieldNext .word .fieldsEnd))) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit0 .bit1 .bit1 .bit0 .bit0 .bit0) (.fieldNext .pairs (.fieldNext .word .fieldsEnd))) <|
  tail

/-- The schemas of `SchemaPart2` (the opcodes `0x19`, `0x20` ... `0x25`, `0x30`) before `tail`. -/
def holrSchemaPart2 (tail : Schemas) : Schemas :=
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit0 .bit1 .bit1 .bit0 .bit0 .bit1) (.fieldNext .pairs (.fieldNext .word .fieldsEnd))) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit1 .bit0 .bit0 .bit0 .bit0 .bit0) (.fieldNext .word (.fieldNext .word .fieldsEnd))) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit1 .bit0 .bit0 .bit0 .bit0 .bit1) (.fieldNext .word (.fieldNext .word .fieldsEnd))) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit1 .bit0 .bit0 .bit0 .bit1 .bit0) (.fieldNext .word .fieldsEnd)) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit1 .bit0 .bit0 .bit0 .bit1 .bit1) (.fieldNext .word .fieldsEnd)) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit1 .bit0 .bit0 .bit1 .bit0 .bit0) (.fieldNext .word (.fieldNext .word (.fieldNext .word (.fieldNext .word .fieldsEnd))))) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit1 .bit0 .bit0 .bit1 .bit0 .bit1) (.fieldNext .word .fieldsEnd)) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit1 .bit1 .bit0 .bit0 .bit0 .bit0) (.fieldNext .word (.fieldNext .words (.fieldNext .word .fieldsEnd)))) <|
  tail

/-- The schemas of `SchemaPart3` (the opcodes `0x35`, `0x34`, `0x33`, `0x31`, `0x32`, `0x40`,
`0x41`, `0x42`), ending the list. -/
def holrSchemaPart3 : Schemas :=
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit1 .bit1 .bit0 .bit1 .bit0 .bit1) (.fieldNext .word (.fieldNext .words (.fieldNext .word .fieldsEnd)))) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit1 .bit1 .bit0 .bit1 .bit0 .bit0) (.fieldNext .word (.fieldNext .words .fieldsEnd))) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit1 .bit1 .bit0 .bit0 .bit1 .bit1) .fieldsEnd) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit1 .bit1 .bit0 .bit0 .bit0 .bit1) (.fieldNext .word (.fieldNext .word .fieldsEnd))) <|
  .cons (.recordSchema (.byte8 .bit0 .bit0 .bit1 .bit1 .bit0 .bit0 .bit1 .bit0) (.fieldNext .word .fieldsEnd)) <|
  .cons (.recordSchema (.byte8 .bit0 .bit1 .bit0 .bit0 .bit0 .bit0 .bit0 .bit0) (.fieldNext .word .fieldsEnd)) <|
  .cons (.recordSchema (.byte8 .bit0 .bit1 .bit0 .bit0 .bit0 .bit0 .bit0 .bit1) (.fieldNext .word .fieldsEnd)) <|
  .cons (.recordSchema (.byte8 .bit0 .bit1 .bit0 .bit0 .bit0 .bit0 .bit1 .bit0) (.fieldNext .word .fieldsEnd)) <|
  .nil

/-- `HOLRSchemaTail3`. -/
inductive HOLRSchemaTail3 : Schemas → Prop
  /-- `SchemaPart3: (HOLRSchemaTail3) ~> (SchemasCons ... (SchemasNil));` -/
  | schemaPart3 : HOLRSchemaTail3 holrSchemaPart3

/-- `HOLRSchemaTail2`. -/
inductive HOLRSchemaTail2 : Schemas → Prop
  /-- `SchemaPart2: (HOLRSchemaTail2) ~> (SchemasCons ... (HOLRSchemaTail3));` -/
  | schemaPart2 {tail : Schemas} : HOLRSchemaTail3 tail → HOLRSchemaTail2 (holrSchemaPart2 tail)

/-- `HOLRSchemaTail1`. -/
inductive HOLRSchemaTail1 : Schemas → Prop
  /-- `SchemaPart1: (HOLRSchemaTail1) ~> (SchemasCons ... (HOLRSchemaTail2));` -/
  | schemaPart1 {tail : Schemas} : HOLRSchemaTail2 tail → HOLRSchemaTail1 (holrSchemaPart1 tail)

/-- `HOLRSchema`. -/
inductive HOLRSchema : Schemas → Prop
  /-- `SchemaPart0: (HOLRSchema) ~> (SchemasCons ... (HOLRSchemaTail1));` -/
  | schemaPart0 {tail : Schemas} : HOLRSchemaTail1 tail → HOLRSchema (holrSchemaPart0 tail)

/-- The schema list of HOLR v1, what the rules of `HOLRSchema` give. -/
def holrSchema : Schemas := holrSchemaPart0 (holrSchemaPart1 (holrSchemaPart2 holrSchemaPart3))

/-- **`HOLRSchema`** has exactly one value, `holrSchema`. -/
theorem holrSchema_iff {s : Schemas} : HOLRSchema s ↔ s = holrSchema := by
  constructor
  · intro h
    cases h with
    | schemaPart0 h₁ =>
      cases h₁ with
      | schemaPart1 h₂ =>
        cases h₂ with
        | schemaPart2 h₃ =>
          cases h₃
          rfl
  · rintro rfl
    exact .schemaPart0 (.schemaPart1 (.schemaPart2 .schemaPart3))

/-! ### `ReadWordLE64` (module `ByteArithmetic`, theory `FixedWords`) -/

/-- `FixedJoin`: no rule for a state other than `DecodedWord` and `NeedInput`. -/
inductive FixedJoin : Byte → CodecState → CodecState → Prop
  /-- `FixedPack: (FixedJoin b (DecodedWord n rest)) ~> (DecodedWord (PackByte b n) rest);` -/
  | fixedPack {b : Byte} {n : BinNat} {rest : Bytes} {p : BinNat} :
      PackByte b n p → FixedJoin b (.decodedWord n rest) (.decodedWord p rest)
  /-- `FixedPropagate: (FixedJoin b (NeedInput)) ~> (NeedInput);` -/
  | fixedPropagate {b : Byte} : FixedJoin b .needInput .needInput

/-- `ReadFixedLE`. -/
inductive ReadFixedLE : BinNat → Bytes → CodecState → Prop
  /-- `FixedEmpty: (ReadFixedLE (NatZero) xs) ~> (DecodedWord (NatZero) xs);` -/
  | fixedEmpty {xs : Bytes} : ReadFixedLE .zero xs (.decodedWord .zero xs)
  /-- `FixedShort: (ReadFixedLE (NatBit bit n) (BNil)) ~> (NeedInput);` -/
  | fixedShort {bit : Bit} {n : BinNat} : ReadFixedLE (.bit bit n) .nil .needInput
  /-- `FixedByte: (ReadFixedLE (NatBit bit n) (BCons b xs)) ~> (FixedJoin b (ReadFixedLE (NatPred
  (NatBit bit n)) xs));` -/
  | fixedByte {bit : Bit} {n : BinNat} {b : Byte} {xs : Bytes} {p : BinNat} {s r : CodecState} :
      NatPred (.bit bit n) p → ReadFixedLE p xs s → FixedJoin b s r →
        ReadFixedLE (.bit bit n) (.cons b xs) r

/-- `ReadWordLE64`. -/
inductive ReadWordLE64 : Bytes → CodecState → Prop
  /-- `Word64: (ReadWordLE64 xs) ~> (ReadFixedLE (NatBit (Bit0) (NatBit (Bit0) (NatBit (Bit0)
  (NatBit (Bit1) (NatZero))))) xs);` -/
  | word64 {xs : Bytes} {r : CodecState} :
      ReadFixedLE (.bit .bit0 (.bit .bit0 (.bit .bit0 (.bit .bit1 .zero)))) xs r → ReadWordLE64 xs r

/-- `ReadFixedLE` on a canonical numeral has a value on every byte string, `DecodedWord` or
`NeedInput`. -/
theorem readFixedLE_total (xs : Bytes) : ∀ {n : BinNat}, n.Canonical →
    ∃ r, ReadFixedLE n xs r ∧ (r = .needInput ∨ ∃ m rest, r = .decodedWord m rest) := by
  induction xs with
  | nil =>
    intro n _
    cases n with
    | zero => exact ⟨_, .fixedEmpty, .inr ⟨_, _, rfl⟩⟩
    | bit b m => exact ⟨_, .fixedShort, .inl rfl⟩
  | cons b xs ih =>
    intro n hn
    cases n with
    | zero => exact ⟨_, .fixedEmpty, .inr ⟨_, _, rfl⟩⟩
    | bit bit m =>
      obtain ⟨p, hp⟩ := natPred_total (hn.val_pos (fun h => by cases h))
      have hpc : p.Canonical := canonical_natPred hn (natPred_iff_fn.mp hp)
      obtain ⟨s, hs, hshape⟩ := ih hpc
      rcases hshape with rfl | ⟨m', rest, rfl⟩
      · exact ⟨_, .fixedByte hp hs .fixedPropagate, .inl rfl⟩
      · obtain ⟨q, hq⟩ := packByte_total b m'
        exact ⟨_, .fixedByte hp hs (.fixedPack hq), .inr ⟨_, _, rfl⟩⟩

/-- `ReadWordLE64` has a value on every byte string, `DecodedWord` or `NeedInput`. -/
theorem readWordLE64_total (xs : Bytes) :
    ∃ r, ReadWordLE64 xs r ∧ (r = .needInput ∨ ∃ m rest, r = .decodedWord m rest) := by
  obtain ⟨r, hr, hshape⟩ := readFixedLE_total xs
    (n := .bit .bit0 (.bit .bit0 (.bit .bit0 (.bit .bit1 .zero)))) (by decide)
  exact ⟨r, .word64 hr, hshape⟩

/-- `ReadULEB62` never gives `Taken` (nor `LimitExceeded`). -/
theorem readULEB62_shape {xs : Bytes} {s : CodecState} (h : ReadULEB62 xs s) :
    s = .needInput ∨ s = .badInteger ∨ ∃ m rest, s = .decodedWord m rest := by
  rw [readULEB62_iff] at h
  subst h
  cases lebSpec 8 (xs.toList.map Byte.val) with
  | needInput => exact .inl rfl
  | badInteger => exact .inr (.inl rfl)
  | decoded v k => exact .inr (.inr ⟨_, _, rfl⟩)

/-! ### The trailer (module `HOLRTrailer`) -/

/-- `EndTrailing`. -/
inductive EndTrailing : Header → Bytes → State → Prop
  /-- `EndTrailingEmpty: (EndTrailing header (BNil)) ~> (HOLRDecoded header (RecordsNil)
  (HOLRPrefixOK));` -/
  | endTrailingEmpty {header : Header} : EndTrailing header .nil (.holrDecoded header .nil .prefixOK)
  /-- `EndTrailingMore: (EndTrailing header (BCons b rest)) ~> (HOLRDecoded header (RecordsNil)
  (HOLRPrefixError (TrailingBytes)));` -/
  | endTrailingMore {header : Header} {b : Byte} {rest : Bytes} :
      EndTrailing header (.cons b rest) (.holrDecoded header .nil (.prefixError .trailingBytes))

/-- `EndChecksumCheck`. -/
inductive EndChecksumCheck : Cmp → Header → Bytes → State → Prop
  /-- `EndChecksumLess: (EndChecksumCheck (Less) header rest) ~> (HOLRDecoded header (RecordsNil)
  (HOLRPrefixError (BadChecksum)));` -/
  | endChecksumLess {header : Header} {rest : Bytes} :
      EndChecksumCheck .less header rest (.holrDecoded header .nil (.prefixError .badChecksum))
  /-- `EndChecksumGreater: (EndChecksumCheck (Greater) header rest) ~> (HOLRDecoded header
  (RecordsNil) (HOLRPrefixError (BadChecksum)));` -/
  | endChecksumGreater {header : Header} {rest : Bytes} :
      EndChecksumCheck .greater header rest (.holrDecoded header .nil (.prefixError .badChecksum))
  /-- `EndChecksumEqual: (EndChecksumCheck (Equal) header rest) ~> (EndTrailing header rest);` -/
  | endChecksumEqual {header : Header} {rest : Bytes} {r : State} :
      EndTrailing header rest r → EndChecksumCheck .equal header rest r

/-- `EndHash`. -/
inductive EndHash : Header → BinNat → Bytes → State → State → Prop
  /-- `EndHashRead: (EndHash header sum rest (Taken prefix ignored)) ~> (EndChecksumCheck
  (NatCompare sum (FNV prefix)) header rest);` -/
  | endHashRead {header : Header} {sum : BinNat} {rest pre ignored : Bytes} {f : BinNat} {o : Cmp}
      {r : State} :
      FNV pre f → NatCompare sum f o → EndChecksumCheck o header rest r →
        EndHash header sum rest (.taken pre ignored) r
  /-- `EndHashNeedInput: (EndHash header sum rest (NeedInput)) ~> (HOLRDecoded header (RecordsNil)
  (HOLRPrefixIncomplete));` -/
  | endHashNeedInput {header : Header} {sum : BinNat} {rest : Bytes} :
      EndHash header sum rest .needInput (.holrDecoded header .nil .prefixIncomplete)
  /-- `EndHashBadInteger: (EndHash header sum rest (BadInteger)) ~> (HOLRDecoded header
  (RecordsNil) (HOLRPrefixError (IntegerEncoding)));` -/
  | endHashBadInteger {header : Header} {sum : BinNat} {rest : Bytes} :
      EndHash header sum rest .badInteger (.holrDecoded header .nil (.prefixError .integerEncoding))
  /-- `EndHashLimitExceeded: (EndHash header sum rest (LimitExceeded)) ~> (HOLRDecoded header
  (RecordsNil) (HOLRPrefixError (FieldLimit)));` -/
  | endHashLimitExceeded {header : Header} {sum : BinNat} {rest : Bytes} :
      EndHash header sum rest .limitExceeded (.holrDecoded header .nil (.prefixError .fieldLimit))

/-- `EndCountCheck`. -/
inductive EndCountCheck : Cmp → Bytes → Header → Bytes → BinNat → Bytes → State → Prop
  /-- `EndCountLess: (EndCountCheck (Less) full header suffix sum rest) ~> (HOLRDecoded header
  (RecordsNil) (HOLRPrefixError (BadCount)));` -/
  | endCountLess {full : Bytes} {header : Header} {suffix : Bytes} {sum : BinNat} {rest : Bytes} :
      EndCountCheck .less full header suffix sum rest
        (.holrDecoded header .nil (.prefixError .badCount))
  /-- `EndCountGreater: (EndCountCheck (Greater) full header suffix sum rest) ~> (HOLRDecoded
  header (RecordsNil) (HOLRPrefixError (BadCount)));` -/
  | endCountGreater {full : Bytes} {header : Header} {suffix : Bytes} {sum : BinNat}
      {rest : Bytes} :
      EndCountCheck .greater full header suffix sum rest
        (.holrDecoded header .nil (.prefixError .badCount))
  /-- `EndCountEqual: (EndCountCheck (Equal) full header suffix sum rest) ~> (EndHash header sum
  rest (TakeBytes (NatSubtract (ByteLength full) (ByteLength suffix)) full));` -/
  | endCountEqual {full : Bytes} {header : Header} {suffix : Bytes} {sum : BinNat} {rest : Bytes}
      {lf ls d : BinNat} {s : CodecState} {r : State} :
      ByteLength full lf → ByteLength suffix ls → NatSubtract lf ls d → TakeBytes d full s →
        EndHash header sum rest (.ofCodec s) r → EndCountCheck .equal full header suffix sum rest r

/-- `EndChecksum`. -/
inductive EndChecksum : Bytes → Header → BinNat → BinNat → Bytes → State → State → Prop
  /-- `EndChecksumRead: (EndChecksum full header count claimed suffix (DecodedWord sum rest)) ~>
  (EndCountCheck (NatCompare count claimed) full header suffix sum rest);` -/
  | endChecksumRead {full : Bytes} {header : Header} {count claimed : BinNat} {suffix : Bytes}
      {sum : BinNat} {rest : Bytes} {o : Cmp} {r : State} :
      NatCompare count claimed o → EndCountCheck o full header suffix sum rest r →
        EndChecksum full header count claimed suffix (.decodedWord sum rest) r
  /-- `EndChecksumNeedInput: (EndChecksum full header count claimed suffix (NeedInput)) ~>
  (HOLRDecoded header (RecordsNil) (HOLRPrefixIncomplete));` -/
  | endChecksumNeedInput {full : Bytes} {header : Header} {count claimed : BinNat}
      {suffix : Bytes} :
      EndChecksum full header count claimed suffix .needInput
        (.holrDecoded header .nil .prefixIncomplete)
  /-- `EndChecksumBadInteger: (EndChecksum full header count claimed suffix (BadInteger)) ~>
  (HOLRDecoded header (RecordsNil) (HOLRPrefixError (IntegerEncoding)));` -/
  | endChecksumBadInteger {full : Bytes} {header : Header} {count claimed : BinNat}
      {suffix : Bytes} :
      EndChecksum full header count claimed suffix .badInteger
        (.holrDecoded header .nil (.prefixError .integerEncoding))
  /-- `EndChecksumLimitExceeded: (EndChecksum full header count claimed suffix (LimitExceeded)) ~>
  (HOLRDecoded header (RecordsNil) (HOLRPrefixError (FieldLimit)));` -/
  | endChecksumLimitExceeded {full : Bytes} {header : Header} {count claimed : BinNat}
      {suffix : Bytes} :
      EndChecksum full header count claimed suffix .limitExceeded
        (.holrDecoded header .nil (.prefixError .fieldLimit))

/-- `EndCount`. -/
inductive EndCount : Bytes → Header → BinNat → Bytes → State → State → Prop
  /-- `EndCountRead: (EndCount full header count suffix (DecodedWord claimed rest)) ~> (EndChecksum
  full header count claimed suffix (ReadWordLE64 rest));` -/
  | endCountRead {full : Bytes} {header : Header} {count : BinNat} {suffix : Bytes}
      {claimed : BinNat} {rest : Bytes} {s : CodecState} {r : State} :
      ReadWordLE64 rest s → EndChecksum full header count claimed suffix (.ofCodec s) r →
        EndCount full header count suffix (.decodedWord claimed rest) r
  /-- `EndCountNeedInput: (EndCount full header count suffix (NeedInput)) ~> (HOLRDecoded header
  (RecordsNil) (HOLRPrefixIncomplete));` -/
  | endCountNeedInput {full : Bytes} {header : Header} {count : BinNat} {suffix : Bytes} :
      EndCount full header count suffix .needInput (.holrDecoded header .nil .prefixIncomplete)
  /-- `EndCountBadInteger: (EndCount full header count suffix (BadInteger)) ~> (HOLRDecoded header
  (RecordsNil) (HOLRPrefixError (IntegerEncoding)));` -/
  | endCountBadInteger {full : Bytes} {header : Header} {count : BinNat} {suffix : Bytes} :
      EndCount full header count suffix .badInteger
        (.holrDecoded header .nil (.prefixError .integerEncoding))
  /-- `EndCountLimitExceeded: (EndCount full header count suffix (LimitExceeded)) ~> (HOLRDecoded
  header (RecordsNil) (HOLRPrefixError (FieldLimit)));` -/
  | endCountLimitExceeded {full : Bytes} {header : Header} {count : BinNat} {suffix : Bytes} :
      EndCount full header count suffix .limitExceeded
        (.holrDecoded header .nil (.prefixError .fieldLimit))

/-- Every value of `EndTrailing` is `HOLRDecoded header RecordsNil t`. -/
theorem EndTrailing.decoded {header : Header} {rest : Bytes} {r : State}
    (h : EndTrailing header rest r) : ∃ t, r = .holrDecoded header .nil t := by
  cases h <;> exact ⟨_, rfl⟩

theorem EndChecksumCheck.decoded {o : Cmp} {header : Header} {rest : Bytes} {r : State}
    (h : EndChecksumCheck o header rest r) : ∃ t, r = .holrDecoded header .nil t := by
  cases h with
  | endChecksumEqual h => exact h.decoded
  | _ => exact ⟨_, rfl⟩

theorem EndHash.decoded {header : Header} {sum : BinNat} {rest : Bytes} {s r : State}
    (h : EndHash header sum rest s r) : ∃ t, r = .holrDecoded header .nil t := by
  cases h with
  | endHashRead _ _ h => exact h.decoded
  | _ => exact ⟨_, rfl⟩

theorem EndCountCheck.decoded {o : Cmp} {full : Bytes} {header : Header} {suffix : Bytes}
    {sum : BinNat} {rest : Bytes} {r : State} (h : EndCountCheck o full header suffix sum rest r) :
    ∃ t, r = .holrDecoded header .nil t := by
  cases h with
  | endCountEqual _ _ _ _ h => exact h.decoded
  | _ => exact ⟨_, rfl⟩

theorem EndChecksum.decoded {full : Bytes} {header : Header} {count claimed : BinNat}
    {suffix : Bytes} {s r : State} (h : EndChecksum full header count claimed suffix s r) :
    ∃ t, r = .holrDecoded header .nil t := by
  cases h with
  | endChecksumRead _ h => exact h.decoded
  | _ => exact ⟨_, rfl⟩

/-- **The trailer ends the stream with no records**: every value of `EndCount` is
`HOLRDecoded header RecordsNil t`. -/
theorem EndCount.decoded {full : Bytes} {header : Header} {count : BinNat} {suffix : Bytes}
    {s r : State} (h : EndCount full header count suffix s r) :
    ∃ t, r = .holrDecoded header .nil t := by
  cases h with
  | endCountRead _ h => exact h.decoded
  | _ => exact ⟨_, rfl⟩

theorem endTrailing_total (header : Header) (rest : Bytes) : ∃ r, EndTrailing header rest r := by
  cases rest with
  | nil => exact ⟨_, .endTrailingEmpty⟩
  | cons b rest => exact ⟨_, .endTrailingMore⟩

theorem endChecksumCheck_total (o : Cmp) (header : Header) (rest : Bytes) :
    ∃ r, EndChecksumCheck o header rest r := by
  cases o with
  | less => exact ⟨_, .endChecksumLess⟩
  | equal =>
    obtain ⟨r, h⟩ := endTrailing_total header rest
    exact ⟨r, .endChecksumEqual h⟩
  | greater => exact ⟨_, .endChecksumGreater⟩

theorem endHash_total (header : Header) (sum : BinNat) (rest : Bytes) {s : CodecState}
    (hs : ∀ m rest', s ≠ .decodedWord m rest') : ∃ r, EndHash header sum rest (.ofCodec s) r := by
  cases s with
  | decodedWord m rest' => exact absurd rfl (hs m rest')
  | needInput => exact ⟨_, .endHashNeedInput⟩
  | badInteger => exact ⟨_, .endHashBadInteger⟩
  | limitExceeded => exact ⟨_, .endHashLimitExceeded⟩
  | taken pre ignored =>
    obtain ⟨f, hf⟩ := fnv_total pre
    obtain ⟨o, ho⟩ := natCompare_total sum f
    obtain ⟨r, hr⟩ := endChecksumCheck_total o header rest
    exact ⟨r, .endHashRead hf ho hr⟩

theorem endCountCheck_total (o : Cmp) (full : Bytes) (header : Header) (suffix : Bytes)
    (sum : BinNat) (rest : Bytes) : ∃ r, EndCountCheck o full header suffix sum rest r := by
  cases o with
  | less => exact ⟨_, .endCountLess⟩
  | greater => exact ⟨_, .endCountGreater⟩
  | equal =>
    have hlf : ByteLength full (BinNat.ofNat full.toList.length) := byteLength_iff.mpr rfl
    have hls : ByteLength suffix (BinNat.ofNat suffix.toList.length) := byteLength_iff.mpr rfl
    have hd : NatSubtract (BinNat.ofNat full.toList.length) (BinNat.ofNat suffix.toList.length)
        (BinNat.ofNat (full.toList.length - suffix.toList.length)) := natSubtract_iff.mpr rfl
    have ht : TakeBytes (BinNat.ofNat (full.toList.length - suffix.toList.length)) full
        (takeSpec (full.toList.length - suffix.toList.length) full) := takeBytes_iff.mpr rfl
    have hshape : ∀ m rest', takeSpec (full.toList.length - suffix.toList.length) full ≠
        .decodedWord m rest' := by
      intro m rest' e
      unfold takeSpec at e
      split at e <;> cases e
    obtain ⟨r, hr⟩ := endHash_total header sum rest hshape
    exact ⟨r, .endCountEqual hlf hls hd ht hr⟩

theorem endChecksum_total (full : Bytes) (header : Header) (count claimed : BinNat)
    (suffix : Bytes) {s : CodecState} (hs : ∀ pre rest, s ≠ .taken pre rest) :
    ∃ r, EndChecksum full header count claimed suffix (.ofCodec s) r := by
  cases s with
  | decodedWord sum rest =>
    obtain ⟨o, ho⟩ := natCompare_total count claimed
    obtain ⟨r, hr⟩ := endCountCheck_total o full header suffix sum rest
    exact ⟨r, .endChecksumRead ho hr⟩
  | needInput => exact ⟨_, .endChecksumNeedInput⟩
  | badInteger => exact ⟨_, .endChecksumBadInteger⟩
  | limitExceeded => exact ⟨_, .endChecksumLimitExceeded⟩
  | taken pre rest => exact absurd rfl (hs pre rest)

/-- **The trailer has a value** on every state but `Taken`, in particular on every state
`ReadULEB62` gives. -/
theorem endCount_total (full : Bytes) (header : Header) (count : BinNat) (suffix : Bytes)
    {s : CodecState} (hs : ∀ pre rest, s ≠ .taken pre rest) :
    ∃ r, EndCount full header count suffix (.ofCodec s) r := by
  cases s with
  | decodedWord claimed rest =>
    obtain ⟨s', hs', hshape⟩ := readWordLE64_total rest
    have hnt : ∀ pre rest', s' ≠ .taken pre rest' := by
      intro pre rest' e
      subst e
      rcases hshape with h | ⟨m, r', h⟩ <;> cases h
    obtain ⟨r, hr⟩ := endChecksum_total full header count claimed suffix hnt
    exact ⟨r, .endCountRead hs' hr⟩
  | needInput => exact ⟨_, .endCountNeedInput⟩
  | badInteger => exact ⟨_, .endCountBadInteger⟩
  | limitExceeded => exact ⟨_, .endCountLimitExceeded⟩
  | taken pre rest => exact absurd rfl (hs pre rest)

/-! ### The loop (module `HOLRRecords`) -/

/-- `StreamPush`: no rule for a state other than `HOLRDecoded`, `HOLRMalformed` and `NeedInput`. -/
inductive StreamPush : Record → State → State → Prop
  /-- `StreamCons: (StreamPush record (HOLRDecoded header records terminal)) ~> (HOLRDecoded header
  (RecordsCons record records) terminal);` -/
  | streamCons {record : Record} {header : Header} {records : Records} {terminal : Terminal} :
      StreamPush record (.holrDecoded header records terminal)
        (.holrDecoded header (.cons record records) terminal)
  /-- `StreamBad: (StreamPush record (HOLRMalformed reason)) ~> (HOLRMalformed reason);` -/
  | streamBad {record : Record} {reason : Reason} :
      StreamPush record (.holrMalformed reason) (.holrMalformed reason)
  /-- `StreamShort: (StreamPush record (NeedInput)) ~> (NeedInput);` -/
  | streamShort {record : Record} : StreamPush record .needInput .needInput

/-- What the rules of `StreamPush` compute; `none` where no rule applies. -/
def streamPush (record : Record) : State → Option State
  | .holrDecoded header records terminal => some (.holrDecoded header (.cons record records) terminal)
  | .holrMalformed reason => some (.holrMalformed reason)
  | .needInput => some .needInput
  | _ => none

theorem streamPush_iff_fn {record : Record} {s r : State} :
    StreamPush record s r ↔ streamPush record s = some r := by
  constructor
  · rintro (_ | _ | _) <;> rfl
  · intro h
    cases s <;> simp only [streamPush, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      constructor

mutual

/-- `HOLRLoop`, the reader's loop over the records (the safepoint of the compiled reader).
`ReadRecord` is the parameter `RR`. -/
inductive HOLRLoop (RR : BinNat → Schemas → Bytes → State → Prop) :
    Bytes → Header → BinNat → Bytes → State → Prop
  /-- `LoopEmpty: (HOLRLoop full header count (BNil)) ~> (HOLRDecoded header (RecordsNil)
  (HOLRPrefixError (MissingEnd)));` -/
  | loopEmpty {full : Bytes} {header : Header} {count : BinNat} :
      HOLRLoop RR full header count .nil (.holrDecoded header .nil (.prefixError .missingEnd))
  /-- `LoopSelect: (HOLRLoop full header count (BCons op rest)) ~> (HOLRControl (NatCompare
  (PackByte op (NatZero)) (127)) full header count (BCons op rest));` with the literal as the rule
  writes it (`lit127`). -/
  | loopSelect {full : Bytes} {header : Header} {count : BinNat} {op : Byte} {rest : Bytes}
      {n : BinNat} {o : Cmp} {r : State} :
      PackByte op .zero n → NatCompare n lit127 o →
        HOLRControl RR o full header count (.cons op rest) r →
        HOLRLoop RR full header count (.cons op rest) r

/-- `HOLRControl`. -/
inductive HOLRControl (RR : BinNat → Schemas → Bytes → State → Prop) :
    Cmp → Bytes → Header → BinNat → Bytes → State → Prop
  /-- `LoopLess: (HOLRControl (Less) full header count xs) ~> (RecordCarry full header count
  (ReadRecord (2^20) (HOLRSchema) xs));` with the literal as the rule writes it
  (`recordLimit`). -/
  | loopLess {full : Bytes} {header : Header} {count : BinNat} {xs : Bytes} {sch : Schemas}
      {s r : State} :
      HOLRSchema sch → RR recordLimit sch xs s → RecordCarry RR full header count s r →
        HOLRControl RR .less full header count xs r
  /-- `LoopGreater: (HOLRControl (Greater) full header count xs) ~> (RecordCarry full header count
  (ReadRecord (2^20) (HOLRSchema) xs));` -/
  | loopGreater {full : Bytes} {header : Header} {count : BinNat} {xs : Bytes} {sch : Schemas}
      {s r : State} :
      HOLRSchema sch → RR recordLimit sch xs s → RecordCarry RR full header count s r →
        HOLRControl RR .greater full header count xs r
  /-- `LoopEnd: (HOLRControl (Equal) full header count (BCons op rest)) ~> (EndCount full header
  count (BCons op rest) (ReadULEB62 rest));` -/
  | loopEnd {full : Bytes} {header : Header} {count : BinNat} {op : Byte} {rest : Bytes}
      {s : CodecState} {r : State} :
      ReadULEB62 rest s → EndCount full header count (.cons op rest) (.ofCodec s) r →
        HOLRControl RR .equal full header count (.cons op rest) r

/-- `RecordCarry`. -/
inductive RecordCarry (RR : BinNat → Schemas → Bytes → State → Prop) :
    Bytes → Header → BinNat → State → State → Prop
  /-- `RecordNext: (RecordCarry full header count (RecordDecoded record rest)) ~> (StreamPush record
  (HOLRLoop full header (NatInc count) rest));` -/
  | recordNext {full : Bytes} {header : Header} {count : BinNat} {record : Record} {rest : Bytes}
      {c : BinNat} {s r : State} :
      NatInc count c → HOLRLoop RR full header c rest s → StreamPush record s r →
        RecordCarry RR full header count (.recordDecoded record rest) r
  /-- `RecordBad: (RecordCarry full header count (UnknownOpcode op)) ~> (HOLRDecoded header
  (RecordsNil) (HOLRPrefixError (BadOpcode)));` -/
  | recordBad {full : Bytes} {header : Header} {count : BinNat} {op : Byte} :
      RecordCarry RR full header count (.unknownOpcode op)
        (.holrDecoded header .nil (.prefixError .badOpcode))
  /-- `RecordCarryNeedInput: (RecordCarry full header count (NeedInput)) ~> (HOLRDecoded header
  (RecordsNil) (HOLRPrefixIncomplete));` -/
  | recordCarryNeedInput {full : Bytes} {header : Header} {count : BinNat} :
      RecordCarry RR full header count .needInput (.holrDecoded header .nil .prefixIncomplete)
  /-- `RecordCarryBadInteger: (RecordCarry full header count (BadInteger)) ~> (HOLRDecoded header
  (RecordsNil) (HOLRPrefixError (IntegerEncoding)));` -/
  | recordCarryBadInteger {full : Bytes} {header : Header} {count : BinNat} :
      RecordCarry RR full header count .badInteger
        (.holrDecoded header .nil (.prefixError .integerEncoding))
  /-- `RecordCarryLimitExceeded: (RecordCarry full header count (LimitExceeded)) ~> (HOLRDecoded
  header (RecordsNil) (HOLRPrefixError (FieldLimit)));` -/
  | recordCarryLimitExceeded {full : Bytes} {header : Header} {count : BinNat} :
      RecordCarry RR full header count .limitExceeded
        (.holrDecoded header .nil (.prefixError .fieldLimit))

end

mutual

/-- The loop as its compiled code runs it: `RecordNext` pushes the frame of its `StreamPush` (the
record) and tail-calls `HOLRLoop` (the generated code: `rc_pend_push(StreamPush, 1, 2, {record,
_})`, then the tail call); the index lists the records of the frames the run pushed, the oldest
first, and the value is the run's own value, its frames taken. -/
inductive RawLoop (RR : BinNat → Schemas → Bytes → State → Prop) :
    Bytes → Header → BinNat → Bytes → List Record → State → Prop
  /-- `LoopEmpty`. -/
  | loopEmpty {full : Bytes} {header : Header} {count : BinNat} :
      RawLoop RR full header count .nil [] (.holrDecoded header .nil (.prefixError .missingEnd))
  /-- `LoopSelect`. -/
  | loopSelect {full : Bytes} {header : Header} {count : BinNat} {op : Byte} {rest : Bytes}
      {n : BinNat} {o : Cmp} {rs : List Record} {r : State} :
      PackByte op .zero n → NatCompare n lit127 o →
        RawControl RR o full header count (.cons op rest) rs r →
        RawLoop RR full header count (.cons op rest) rs r

/-- `HOLRControl` as its compiled code runs it. -/
inductive RawControl (RR : BinNat → Schemas → Bytes → State → Prop) :
    Cmp → Bytes → Header → BinNat → Bytes → List Record → State → Prop
  /-- `LoopLess`. -/
  | loopLess {full : Bytes} {header : Header} {count : BinNat} {xs : Bytes} {sch : Schemas}
      {s : State} {rs : List Record} {r : State} :
      HOLRSchema sch → RR recordLimit sch xs s → RawCarry RR full header count s rs r →
        RawControl RR .less full header count xs rs r
  /-- `LoopGreater`. -/
  | loopGreater {full : Bytes} {header : Header} {count : BinNat} {xs : Bytes} {sch : Schemas}
      {s : State} {rs : List Record} {r : State} :
      HOLRSchema sch → RR recordLimit sch xs s → RawCarry RR full header count s rs r →
        RawControl RR .greater full header count xs rs r
  /-- `LoopEnd`. -/
  | loopEnd {full : Bytes} {header : Header} {count : BinNat} {op : Byte} {rest : Bytes}
      {s : CodecState} {r : State} :
      ReadULEB62 rest s → EndCount full header count (.cons op rest) (.ofCodec s) r →
        RawControl RR .equal full header count (.cons op rest) [] r

/-- `RecordCarry` as its compiled code runs it. -/
inductive RawCarry (RR : BinNat → Schemas → Bytes → State → Prop) :
    Bytes → Header → BinNat → State → List Record → State → Prop
  /-- `RecordNext`: the frame of `StreamPush record` pushed, then the tail call of `HOLRLoop`. -/
  | recordNext {full : Bytes} {header : Header} {count : BinNat} {record : Record} {rest : Bytes}
      {c : BinNat} {rs : List Record} {s : State} :
      NatInc count c → RawLoop RR full header c rest rs s →
        RawCarry RR full header count (.recordDecoded record rest) (record :: rs) s
  /-- `RecordBad`. -/
  | recordBad {full : Bytes} {header : Header} {count : BinNat} {op : Byte} :
      RawCarry RR full header count (.unknownOpcode op) []
        (.holrDecoded header .nil (.prefixError .badOpcode))
  /-- `RecordCarryNeedInput`. -/
  | recordCarryNeedInput {full : Bytes} {header : Header} {count : BinNat} :
      RawCarry RR full header count .needInput [] (.holrDecoded header .nil .prefixIncomplete)
  /-- `RecordCarryBadInteger`. -/
  | recordCarryBadInteger {full : Bytes} {header : Header} {count : BinNat} :
      RawCarry RR full header count .badInteger []
        (.holrDecoded header .nil (.prefixError .integerEncoding))
  /-- `RecordCarryLimitExceeded`. -/
  | recordCarryLimitExceeded {full : Bytes} {header : Header} {count : BinNat} :
      RawCarry RR full header count .limitExceeded []
        (.holrDecoded header .nil (.prefixError .fieldLimit))

end

section Loop

variable {RR : BinNat → Schemas → Bytes → State → Prop}

mutual

/-- **The loop's own value ends the stream with no records**: every value of the loop as its
compiled code runs it (its frames taken) is `HOLRDecoded header RecordsNil t`, for the loop's
header. -/
theorem RawLoop.decoded : ∀ {full : Bytes} {header : Header} {count : BinNat} {xs : Bytes}
    {rs : List Record} {v : State}, RawLoop RR full header count xs rs v →
      ∃ t, v = .holrDecoded header .nil t
  | _, _, _, _, _, _, .loopEmpty => ⟨_, rfl⟩
  | _, _, _, _, _, _, .loopSelect _ _ h => RawControl.decoded h

theorem RawControl.decoded : ∀ {o : Cmp} {full : Bytes} {header : Header} {count : BinNat}
    {xs : Bytes} {rs : List Record} {v : State}, RawControl RR o full header count xs rs v →
      ∃ t, v = .holrDecoded header .nil t
  | _, _, _, _, _, _, _, .loopLess _ _ h => RawCarry.decoded h
  | _, _, _, _, _, _, _, .loopGreater _ _ h => RawCarry.decoded h
  | _, _, _, _, _, _, _, .loopEnd _ h => h.decoded

theorem RawCarry.decoded : ∀ {full : Bytes} {header : Header} {count : BinNat} {s : State}
    {rs : List Record} {v : State}, RawCarry RR full header count s rs v →
      ∃ t, v = .holrDecoded header .nil t
  | _, _, _, _, _, _, .recordNext _ h => RawLoop.decoded h
  | _, _, _, _, _, _, .recordBad => ⟨_, rfl⟩
  | _, _, _, _, _, _, .recordCarryNeedInput => ⟨_, rfl⟩
  | _, _, _, _, _, _, .recordCarryBadInteger => ⟨_, rfl⟩
  | _, _, _, _, _, _, .recordCarryLimitExceeded => ⟨_, rfl⟩

end

mutual

/-- Every value of the loop is the value of the loop as its compiled code runs it with the frames
it pushed applied (`StreamPush` of each record, the newest first). -/
theorem HOLRLoop.toRaw : ∀ {full : Bytes} {header : Header} {count : BinNat} {xs : Bytes}
    {v : State}, HOLRLoop RR full header count xs v →
      ∃ rs v₀, RawLoop RR full header count xs rs v₀ ∧
        applyFrames streamPush rs.reverse (some v₀) = some v
  | _, _, _, _, _, .loopEmpty => ⟨[], _, .loopEmpty, rfl⟩
  | _, _, _, _, _, .loopSelect h₁ h₂ h => by
    obtain ⟨rs, v₀, hr, e⟩ := HOLRControl.toRaw h
    exact ⟨rs, v₀, .loopSelect h₁ h₂ hr, e⟩

theorem HOLRControl.toRaw : ∀ {o : Cmp} {full : Bytes} {header : Header} {count : BinNat}
    {xs : Bytes} {v : State}, HOLRControl RR o full header count xs v →
      ∃ rs v₀, RawControl RR o full header count xs rs v₀ ∧
        applyFrames streamPush rs.reverse (some v₀) = some v
  | _, _, _, _, _, _, .loopLess h₁ h₂ h => by
    obtain ⟨rs, v₀, hr, e⟩ := RecordCarry.toRaw h
    exact ⟨rs, v₀, .loopLess h₁ h₂ hr, e⟩
  | _, _, _, _, _, _, .loopGreater h₁ h₂ h => by
    obtain ⟨rs, v₀, hr, e⟩ := RecordCarry.toRaw h
    exact ⟨rs, v₀, .loopGreater h₁ h₂ hr, e⟩
  | _, _, _, _, _, _, .loopEnd h₁ h₂ => ⟨[], _, .loopEnd h₁ h₂, rfl⟩

theorem RecordCarry.toRaw : ∀ {full : Bytes} {header : Header} {count : BinNat} {s : State}
    {v : State}, RecordCarry RR full header count s v →
      ∃ rs v₀, RawCarry RR full header count s rs v₀ ∧
        applyFrames streamPush rs.reverse (some v₀) = some v
  | _, _, _, _, _, @RecordCarry.recordNext _ _ _ _ record _ _ _ _ h₁ h₂ h₃ => by
    obtain ⟨rs, v₀, hr, e⟩ := HOLRLoop.toRaw h₂
    refine ⟨record :: rs, v₀, .recordNext h₁ hr, ?_⟩
    rw [List.reverse_cons, applyFrames_append, e]
    exact streamPush_iff_fn.mp h₃
  | _, _, _, _, _, .recordBad => ⟨[], _, .recordBad, rfl⟩
  | _, _, _, _, _, .recordCarryNeedInput => ⟨[], _, .recordCarryNeedInput, rfl⟩
  | _, _, _, _, _, .recordCarryBadInteger => ⟨[], _, .recordCarryBadInteger, rfl⟩
  | _, _, _, _, _, .recordCarryLimitExceeded => ⟨[], _, .recordCarryLimitExceeded, rfl⟩

end

mutual

/-- Conversely, the loop as its compiled code runs it, with the frames it pushed applied, gives a
value of the loop. -/
theorem RawLoop.toLoop : ∀ {full : Bytes} {header : Header} {count : BinNat} {xs : Bytes}
    {rs : List Record} {v₀ : State}, RawLoop RR full header count xs rs v₀ →
      ∀ {v : State}, applyFrames streamPush rs.reverse (some v₀) = some v →
        HOLRLoop RR full header count xs v
  | _, _, _, _, _, _, .loopEmpty => fun e => by
    simp only [List.reverse_nil, applyFrames_nil, Option.some.injEq] at e
    subst e
    exact .loopEmpty
  | _, _, _, _, _, _, .loopSelect h₁ h₂ h => fun e => .loopSelect h₁ h₂ (RawControl.toLoop h e)

theorem RawControl.toLoop : ∀ {o : Cmp} {full : Bytes} {header : Header} {count : BinNat}
    {xs : Bytes} {rs : List Record} {v₀ : State}, RawControl RR o full header count xs rs v₀ →
      ∀ {v : State}, applyFrames streamPush rs.reverse (some v₀) = some v →
        HOLRControl RR o full header count xs v
  | _, _, _, _, _, _, _, .loopLess h₁ h₂ h => fun e => .loopLess h₁ h₂ (RawCarry.toLoop h e)
  | _, _, _, _, _, _, _, .loopGreater h₁ h₂ h => fun e => .loopGreater h₁ h₂ (RawCarry.toLoop h e)
  | _, _, _, _, _, _, _, .loopEnd h₁ h₂ => fun e => by
    simp only [List.reverse_nil, applyFrames_nil, Option.some.injEq] at e
    subst e
    exact .loopEnd h₁ h₂

theorem RawCarry.toLoop : ∀ {full : Bytes} {header : Header} {count : BinNat} {s : State}
    {rs : List Record} {v₀ : State}, RawCarry RR full header count s rs v₀ →
      ∀ {v : State}, applyFrames streamPush rs.reverse (some v₀) = some v →
        RecordCarry RR full header count s v
  | _, _, _, _, _, _, @RawCarry.recordNext _ _ _ _ record _ _ rs _ h₁ h => fun e => by
    rw [List.reverse_cons, applyFrames_append] at e
    obtain ⟨s, hs, hv⟩ := Option.bind_eq_some_iff.mp e
    exact .recordNext h₁ (RawLoop.toLoop h hs) (streamPush_iff_fn.mpr hv)
  | _, _, _, _, _, _, .recordBad => fun e => by
    simp only [List.reverse_nil, applyFrames_nil, Option.some.injEq] at e
    subst e
    exact .recordBad
  | _, _, _, _, _, _, .recordCarryNeedInput => fun e => by
    simp only [List.reverse_nil, applyFrames_nil, Option.some.injEq] at e
    subst e
    exact .recordCarryNeedInput
  | _, _, _, _, _, _, .recordCarryBadInteger => fun e => by
    simp only [List.reverse_nil, applyFrames_nil, Option.some.injEq] at e
    subst e
    exact .recordCarryBadInteger
  | _, _, _, _, _, _, .recordCarryLimitExceeded => fun e => by
    simp only [List.reverse_nil, applyFrames_nil, Option.some.injEq] at e
    subst e
    exact .recordCarryLimitExceeded

end

/-- **The loop's frames compute the loop.**  The values of `HOLRLoop` are exactly the values of the
loop as its compiled code runs it, with the frames it pushed (`StreamPush` of each record)
applied, the newest first. -/
theorem holrLoop_iff_raw {full : Bytes} {header : Header} {count : BinNat} {xs : Bytes}
    {v : State} :
    HOLRLoop RR full header count xs v ↔
      ∃ rs v₀, RawLoop RR full header count xs rs v₀ ∧
        applyFrames streamPush rs.reverse (some v₀) = some v :=
  ⟨HOLRLoop.toRaw, fun ⟨_, _, hr, e⟩ => hr.toLoop e⟩

/-- The cons law of `StreamPush` (rule `StreamCons`) on the values the loop ends with. -/
theorem streamPush_consLaw (record : Record) (header : Header) (rs : List Record)
    (t : Terminal) :
    streamPush record (.holrDecoded header (Records.ofList rs) t) =
      some (.holrDecoded header (Records.ofList (record :: rs)) t) := rfl

/-- **The loop's value.**  Every value of `HOLRLoop` is `HOLRDecoded header (RecordsCons r1 (...
(RecordsCons rn RecordsNil))) t`, for the loop's header, where `r1 ... rn` are the records
`RecordNext` pushed, the oldest first, and `HOLRDecoded header RecordsNil t` is the value of the
loop as its compiled code runs it. -/
theorem holrLoop_value {full : Bytes} {header : Header} {count : BinNat} {xs : Bytes} {v : State}
    (h : HOLRLoop RR full header count xs v) :
    ∃ rs t, RawLoop RR full header count xs rs (.holrDecoded header .nil t) ∧
      v = .holrDecoded header (Records.ofList rs) t := by
  obtain ⟨rs, v₀, hr, e⟩ := h.toRaw
  obtain ⟨t, rfl⟩ := hr.decoded
  refine ⟨rs, t, hr, ?_⟩
  have hc := applyFrames_consLaw streamPush
    (fun (h : Header) (xs : List Record) (t : Terminal) => State.holrDecoded h (Records.ofList xs) t)
    id (fun f h xs t => streamPush_consLaw f h xs t) rs.reverse header [] t
  rw [List.map_id, List.reverse_reverse, List.append_nil] at hc
  exact (Option.some.inj (e.symm.trans hc))

/-- `StreamBad` and `StreamShort` never apply in the loop: the value `RecordNext` gives to
`StreamPush` is a `HOLRDecoded`, so `StreamCons` applies. -/
theorem recordNext_streamCons {full : Bytes} {header : Header} {c : BinNat} {rest : Bytes}
    {s : State} {record : Record} {r : State} (hl : HOLRLoop RR full header c rest s)
    (hp : StreamPush record s r) :
    ∃ rs t, s = .holrDecoded header rs t ∧ r = .holrDecoded header (.cons record rs) t := by
  obtain ⟨rs, t, _, rfl⟩ := holrLoop_value hl
  cases hp
  exact ⟨_, _, rfl, rfl⟩

/-- What the loop needs of `ReadRecord` (the parameter `RR`) to have a value: on every input the
loop gives it (an opcode and the rest, with the limit `2^20` and the schema list), a result of one
of the shapes `RecordCarry` has a rule for, a decoded record leaving at most the bytes after its
opcode. -/
def ReadRecordGives (RR : BinNat → Schemas → Bytes → State → Prop) : Prop :=
  ∀ (op : Byte) (rest : Bytes), ∃ s, RR recordLimit holrSchema (.cons op rest) s ∧
    ((∃ (record : Record) (rest' : Bytes), s = .recordDecoded record rest' ∧
        rest'.toList.length ≤ rest.toList.length) ∨
      (∃ op' : Byte, s = .unknownOpcode op') ∨ s = .needInput ∨ s = .badInteger ∨
      s = .limitExceeded)

/-- **The loop has a value** on every input, when `ReadRecord` gives its results as
`ReadRecordGives` says. -/
theorem holrLoop_total (hRR : ReadRecordGives RR) (full : Bytes) (header : Header) :
    ∀ (xs : Bytes) (count : BinNat), ∃ v, HOLRLoop RR full header count xs v := by
  suffices H : ∀ (n : Nat) (xs : Bytes), xs.toList.length = n → ∀ count : BinNat,
      ∃ v, HOLRLoop RR full header count xs v from
    fun xs count => H _ xs rfl count
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xs hn count
    cases xs with
    | nil => exact ⟨_, .loopEmpty⟩
    | cons op rest =>
      obtain ⟨o, ho⟩ := natCompare_total (packByte op .zero) lit127
      have carry : ∃ s r, RR recordLimit holrSchema (.cons op rest) s ∧
          RecordCarry RR full header count s r := by
        obtain ⟨s, hs, hshape⟩ := hRR op rest
        rcases hshape with ⟨record, rest', rfl, hlen⟩ | ⟨op', rfl⟩ | rfl | rfl | rfl
        · have hlt : rest'.toList.length < n := by
            rw [← hn, Bytes.toList_cons, List.length_cons]
            omega
          obtain ⟨v', hv'⟩ := ih _ hlt rest' rfl (natInc count)
          obtain ⟨rs, t, _, rfl⟩ := holrLoop_value hv'
          exact ⟨_, _, hs, .recordNext (natInc_iff_fn.mpr rfl) hv' .streamCons⟩
        · exact ⟨_, _, hs, .recordBad⟩
        · exact ⟨_, _, hs, .recordCarryNeedInput⟩
        · exact ⟨_, _, hs, .recordCarryBadInteger⟩
        · exact ⟨_, _, hs, .recordCarryLimitExceeded⟩
      have hctl : ∃ v, HOLRControl RR o full header count (.cons op rest) v := by
        cases o with
        | less =>
          obtain ⟨s, r, hs, hc⟩ := carry
          exact ⟨r, .loopLess (holrSchema_iff.mpr rfl) hs hc⟩
        | greater =>
          obtain ⟨s, r, hs, hc⟩ := carry
          exact ⟨r, .loopGreater (holrSchema_iff.mpr rfl) hs hc⟩
        | equal =>
          obtain ⟨s, hs⟩ := readULEB62_total rest
          have hnt : ∀ pre rest', s ≠ .taken pre rest' := by
            intro pre rest' e
            subst e
            rcases readULEB62_shape hs with h | h | ⟨m, r', h⟩ <;> cases h
          obtain ⟨r, hr⟩ := endCount_total full header count (.cons op rest) hnt
          exact ⟨r, .loopEnd hs hr⟩
      obtain ⟨v, hv⟩ := hctl
      exact ⟨v, .loopSelect (packByte_iff_fn.mpr rfl) ho hv⟩

end Loop

/-! ### `ReadRecord` (module `ByteRecords`, theory `Records`) -/

/-- `RecordFields`. -/
inductive RecordFields : Byte → State → State → Prop
  /-- `RecordMake: (RecordFields op (FieldsDecoded fields rest)) ~> (RecordDecoded (BRecord op
  fields) rest);` -/
  | recordMake {op : Byte} {fields : Operands} {rest : Bytes} :
      RecordFields op (.fieldsDecoded fields rest) (.recordDecoded (.bRecord op fields) rest)
  /-- `RecordFieldsNeedInput: (RecordFields op (NeedInput)) ~> (NeedInput);` -/
  | recordFieldsNeedInput {op : Byte} : RecordFields op .needInput .needInput
  /-- `RecordFieldsBadInteger: (RecordFields op (BadInteger)) ~> (BadInteger);` -/
  | recordFieldsBadInteger {op : Byte} : RecordFields op .badInteger .badInteger
  /-- `RecordFieldsLimitExceeded: (RecordFields op (LimitExceeded)) ~> (LimitExceeded);` -/
  | recordFieldsLimitExceeded {op : Byte} : RecordFields op .limitExceeded .limitExceeded

/-- `FieldPush`. -/
inductive FieldPush : Operand → State → State → Prop
  /-- `FieldsCons: (FieldPush value (FieldsDecoded values rest)) ~> (FieldsDecoded (OperandsCons
  value values) rest);` -/
  | fieldsCons {value : Operand} {values : Operands} {rest : Bytes} :
      FieldPush value (.fieldsDecoded values rest) (.fieldsDecoded (.cons value values) rest)
  /-- `FieldPushNeedInput: (FieldPush value (NeedInput)) ~> (NeedInput);` -/
  | fieldPushNeedInput {value : Operand} : FieldPush value .needInput .needInput
  /-- `FieldPushBadInteger: (FieldPush value (BadInteger)) ~> (BadInteger);` -/
  | fieldPushBadInteger {value : Operand} : FieldPush value .badInteger .badInteger
  /-- `FieldPushLimitExceeded: (FieldPush value (LimitExceeded)) ~> (LimitExceeded);` -/
  | fieldPushLimitExceeded {value : Operand} : FieldPush value .limitExceeded .limitExceeded

/-- `OperandWord`. -/
inductive OperandWord : State → State → Prop
  /-- `WordValue: (OperandWord (DecodedWord n rest)) ~> (OperandDecoded (BWord n) rest);` -/
  | wordValue {n : BinNat} {rest : Bytes} :
      OperandWord (.decodedWord n rest) (.operandDecoded (.word n) rest)
  /-- `OperandWordNeedInput: (OperandWord (NeedInput)) ~> (NeedInput);` -/
  | operandWordNeedInput : OperandWord .needInput .needInput
  /-- `OperandWordBadInteger: (OperandWord (BadInteger)) ~> (BadInteger);` -/
  | operandWordBadInteger : OperandWord .badInteger .badInteger
  /-- `OperandWordLimitExceeded: (OperandWord (LimitExceeded)) ~> (LimitExceeded);` -/
  | operandWordLimitExceeded : OperandWord .limitExceeded .limitExceeded

/-- `OperandBytes`. -/
inductive OperandBytes : State → State → Prop
  /-- `BytesValue: (OperandBytes (Taken bytes rest)) ~> (OperandDecoded (BBytes bytes) rest);` -/
  | bytesValue {bytes rest : Bytes} :
      OperandBytes (.taken bytes rest) (.operandDecoded (.bytes bytes) rest)
  /-- `OperandBytesNeedInput: (OperandBytes (NeedInput)) ~> (NeedInput);` -/
  | operandBytesNeedInput : OperandBytes .needInput .needInput
  /-- `OperandBytesBadInteger: (OperandBytes (BadInteger)) ~> (BadInteger);` -/
  | operandBytesBadInteger : OperandBytes .badInteger .badInteger
  /-- `OperandBytesLimitExceeded: (OperandBytes (LimitExceeded)) ~> (LimitExceeded);` -/
  | operandBytesLimitExceeded : OperandBytes .limitExceeded .limitExceeded

/-- `OperandWords`. -/
inductive OperandWords : State → State → Prop
  /-- `WordsValue: (OperandWords (WordsDecoded words rest)) ~> (OperandDecoded (BWords words)
  rest);` -/
  | wordsValue {words : WordList} {rest : Bytes} :
      OperandWords (.wordsDecoded words rest) (.operandDecoded (.words words) rest)
  /-- `OperandWordsNeedInput: (OperandWords (NeedInput)) ~> (NeedInput);` -/
  | operandWordsNeedInput : OperandWords .needInput .needInput
  /-- `OperandWordsBadInteger: (OperandWords (BadInteger)) ~> (BadInteger);` -/
  | operandWordsBadInteger : OperandWords .badInteger .badInteger
  /-- `OperandWordsLimitExceeded: (OperandWords (LimitExceeded)) ~> (LimitExceeded);` -/
  | operandWordsLimitExceeded : OperandWords .limitExceeded .limitExceeded

/-- `OperandPairs`. -/
inductive OperandPairs : State → State → Prop
  /-- `PairsValue: (OperandPairs (PairsDecoded pairs rest)) ~> (OperandDecoded (BPairs pairs)
  rest);` -/
  | pairsValue {pairs : PairList} {rest : Bytes} :
      OperandPairs (.pairsDecoded pairs rest) (.operandDecoded (.pairs pairs) rest)
  /-- `OperandPairsNeedInput: (OperandPairs (NeedInput)) ~> (NeedInput);` -/
  | operandPairsNeedInput : OperandPairs .needInput .needInput
  /-- `OperandPairsBadInteger: (OperandPairs (BadInteger)) ~> (BadInteger);` -/
  | operandPairsBadInteger : OperandPairs .badInteger .badInteger
  /-- `OperandPairsLimitExceeded: (OperandPairs (LimitExceeded)) ~> (LimitExceeded);` -/
  | operandPairsLimitExceeded : OperandPairs .limitExceeded .limitExceeded

/-- `WordsPush`. -/
inductive WordsPush : BinNat → State → State → Prop
  /-- `WordsConsValue: (WordsPush value (WordsDecoded values rest)) ~> (WordsDecoded (WordsCons
  value values) rest);` -/
  | wordsConsValue {value : BinNat} {values : WordList} {rest : Bytes} :
      WordsPush value (.wordsDecoded values rest) (.wordsDecoded (.cons value values) rest)
  /-- `WordsPushNeedInput: (WordsPush value (NeedInput)) ~> (NeedInput);` -/
  | wordsPushNeedInput {value : BinNat} : WordsPush value .needInput .needInput
  /-- `WordsPushBadInteger: (WordsPush value (BadInteger)) ~> (BadInteger);` -/
  | wordsPushBadInteger {value : BinNat} : WordsPush value .badInteger .badInteger
  /-- `WordsPushLimitExceeded: (WordsPush value (LimitExceeded)) ~> (LimitExceeded);` -/
  | wordsPushLimitExceeded {value : BinNat} : WordsPush value .limitExceeded .limitExceeded

/-- `PairsPush`. -/
inductive PairsPush : Pair → State → State → Prop
  /-- `PairsConsValue: (PairsPush pair (PairsDecoded pairs rest)) ~> (PairsDecoded (PairsCons pair
  pairs) rest);` -/
  | pairsConsValue {pair : Pair} {pairs : PairList} {rest : Bytes} :
      PairsPush pair (.pairsDecoded pairs rest) (.pairsDecoded (.cons pair pairs) rest)
  /-- `PairsPushNeedInput: (PairsPush pair (NeedInput)) ~> (NeedInput);` -/
  | pairsPushNeedInput {pair : Pair} : PairsPush pair .needInput .needInput
  /-- `PairsPushBadInteger: (PairsPush pair (BadInteger)) ~> (BadInteger);` -/
  | pairsPushBadInteger {pair : Pair} : PairsPush pair .badInteger .badInteger
  /-- `PairsPushLimitExceeded: (PairsPush pair (LimitExceeded)) ~> (LimitExceeded);` -/
  | pairsPushLimitExceeded {pair : Pair} : PairsPush pair .limitExceeded .limitExceeded

mutual

/-- `ReadWords`. -/
inductive ReadWords : BinNat → Bytes → State → Prop
  /-- `WordsEnd: (ReadWords (NatZero) xs) ~> (WordsDecoded (WordsNil) xs);` -/
  | wordsEnd {xs : Bytes} : ReadWords .zero xs (.wordsDecoded .nil xs)
  /-- `WordsRead: (ReadWords (NatBit bit n) xs) ~> (WordsCarry (NatPred (NatBit bit n)) (ReadULEB62
  xs));` -/
  | wordsRead {bit : Bit} {n : BinNat} {xs : Bytes} {p : BinNat} {s : CodecState} {r : State} :
      NatPred (.bit bit n) p → ReadULEB62 xs s → WordsCarry p (.ofCodec s) r →
        ReadWords (.bit bit n) xs r

/-- `WordsCarry`. -/
inductive WordsCarry : BinNat → State → State → Prop
  /-- `WordsNext: (WordsCarry n (DecodedWord value rest)) ~> (WordsPush value (ReadWords n
  rest));` -/
  | wordsNext {n value : BinNat} {rest : Bytes} {s r : State} :
      ReadWords n rest s → WordsPush value s r → WordsCarry n (.decodedWord value rest) r
  /-- `WordsCarryNeedInput: (WordsCarry n (NeedInput)) ~> (NeedInput);` -/
  | wordsCarryNeedInput {n : BinNat} : WordsCarry n .needInput .needInput
  /-- `WordsCarryBadInteger: (WordsCarry n (BadInteger)) ~> (BadInteger);` -/
  | wordsCarryBadInteger {n : BinNat} : WordsCarry n .badInteger .badInteger
  /-- `WordsCarryLimitExceeded: (WordsCarry n (LimitExceeded)) ~> (LimitExceeded);` -/
  | wordsCarryLimitExceeded {n : BinNat} : WordsCarry n .limitExceeded .limitExceeded

end

mutual

/-- `ReadPairs`. -/
inductive ReadPairs : BinNat → Bytes → State → Prop
  /-- `PairsEnd: (ReadPairs (NatZero) xs) ~> (PairsDecoded (PairsNil) xs);` -/
  | pairsEnd {xs : Bytes} : ReadPairs .zero xs (.pairsDecoded .nil xs)
  /-- `PairsRead: (ReadPairs (NatBit bit n) xs) ~> (PairsFirst (NatPred (NatBit bit n)) (ReadULEB62
  xs));` -/
  | pairsRead {bit : Bit} {n : BinNat} {xs : Bytes} {p : BinNat} {s : CodecState} {r : State} :
      NatPred (.bit bit n) p → ReadULEB62 xs s → PairsFirst p (.ofCodec s) r →
        ReadPairs (.bit bit n) xs r

/-- `PairsFirst`. -/
inductive PairsFirst : BinNat → State → State → Prop
  /-- `PairsReadSecond: (PairsFirst n (DecodedWord first rest)) ~> (PairsSecond n first (ReadULEB62
  rest));` -/
  | pairsReadSecond {n first : BinNat} {rest : Bytes} {s : CodecState} {r : State} :
      ReadULEB62 rest s → PairsSecond n first (.ofCodec s) r →
        PairsFirst n (.decodedWord first rest) r
  /-- `PairsFirstNeedInput: (PairsFirst n (NeedInput)) ~> (NeedInput);` -/
  | pairsFirstNeedInput {n : BinNat} : PairsFirst n .needInput .needInput
  /-- `PairsFirstBadInteger: (PairsFirst n (BadInteger)) ~> (BadInteger);` -/
  | pairsFirstBadInteger {n : BinNat} : PairsFirst n .badInteger .badInteger
  /-- `PairsFirstLimitExceeded: (PairsFirst n (LimitExceeded)) ~> (LimitExceeded);` -/
  | pairsFirstLimitExceeded {n : BinNat} : PairsFirst n .limitExceeded .limitExceeded

/-- `PairsSecond`. -/
inductive PairsSecond : BinNat → BinNat → State → State → Prop
  /-- `PairsNext: (PairsSecond n first (DecodedWord second rest)) ~> (PairsPush (BPair first
  second) (ReadPairs n rest));` -/
  | pairsNext {n first second : BinNat} {rest : Bytes} {s r : State} :
      ReadPairs n rest s → PairsPush (.pair first second) s r →
        PairsSecond n first (.decodedWord second rest) r
  /-- `PairsSecondNeedInput: (PairsSecond n first (NeedInput)) ~> (NeedInput);` -/
  | pairsSecondNeedInput {n first : BinNat} : PairsSecond n first .needInput .needInput
  /-- `PairsSecondBadInteger: (PairsSecond n first (BadInteger)) ~> (BadInteger);` -/
  | pairsSecondBadInteger {n first : BinNat} : PairsSecond n first .badInteger .badInteger
  /-- `PairsSecondLimitExceeded: (PairsSecond n first (LimitExceeded)) ~> (LimitExceeded);` -/
  | pairsSecondLimitExceeded {n first : BinNat} :
      PairsSecond n first .limitExceeded .limitExceeded

end

/-- `ReadValues`: no rule for `WordField` (only the counted kinds are counted). -/
inductive ReadValues : FieldKind → BinNat → Bytes → State → Prop
  /-- `ValuesBytes: (ReadValues (BytesField) n xs) ~> (OperandBytes (TakeBytes n xs));` -/
  | valuesBytes {n : BinNat} {xs : Bytes} {s : CodecState} {r : State} :
      TakeBytes n xs s → OperandBytes (.ofCodec s) r → ReadValues .bytes n xs r
  /-- `ValuesWords: (ReadValues (WordsField) n xs) ~> (OperandWords (ReadWords n xs));` -/
  | valuesWords {n : BinNat} {xs : Bytes} {s r : State} :
      ReadWords n xs s → OperandWords s r → ReadValues .words n xs r
  /-- `ValuesPairs: (ReadValues (PairsField) n xs) ~> (OperandPairs (ReadPairs n xs));` -/
  | valuesPairs {n : BinNat} {xs : Bytes} {s r : State} :
      ReadPairs n xs s → OperandPairs s r → ReadValues .pairs n xs r

/-- `CountValuesBound`. -/
inductive CountValuesBound : Cmp → FieldKind → BinNat → Bytes → State → Prop
  /-- `CountSmall: (CountValuesBound (Less) kind n rest) ~> (ReadValues kind n rest);` -/
  | countSmall {kind : FieldKind} {n : BinNat} {rest : Bytes} {r : State} :
      ReadValues kind n rest r → CountValuesBound .less kind n rest r
  /-- `CountEqual: (CountValuesBound (Equal) kind n rest) ~> (ReadValues kind n rest);` -/
  | countEqual {kind : FieldKind} {n : BinNat} {rest : Bytes} {r : State} :
      ReadValues kind n rest r → CountValuesBound .equal kind n rest r
  /-- `CountLarge: (CountValuesBound (Greater) kind n rest) ~> (LimitExceeded);` -/
  | countLarge {kind : FieldKind} {n : BinNat} {rest : Bytes} :
      CountValuesBound .greater kind n rest .limitExceeded

/-- `CountValues`. -/
inductive CountValues : BinNat → FieldKind → State → State → Prop
  /-- `CountValue: (CountValues limit kind (DecodedWord n rest)) ~> (CountValuesBound (NatCompare n
  limit) kind n rest);` -/
  | countValue {limit : BinNat} {kind : FieldKind} {n : BinNat} {rest : Bytes} {o : Cmp}
      {r : State} :
      NatCompare n limit o → CountValuesBound o kind n rest r →
        CountValues limit kind (.decodedWord n rest) r
  /-- `CountValuesNeedInput: (CountValues limit kind (NeedInput)) ~> (NeedInput);` -/
  | countValuesNeedInput {limit : BinNat} {kind : FieldKind} :
      CountValues limit kind .needInput .needInput
  /-- `CountValuesBadInteger: (CountValues limit kind (BadInteger)) ~> (BadInteger);` -/
  | countValuesBadInteger {limit : BinNat} {kind : FieldKind} :
      CountValues limit kind .badInteger .badInteger
  /-- `CountValuesLimitExceeded: (CountValues limit kind (LimitExceeded)) ~> (LimitExceeded);` -/
  | countValuesLimitExceeded {limit : BinNat} {kind : FieldKind} :
      CountValues limit kind .limitExceeded .limitExceeded

/-- `ReadOperand`. -/
inductive ReadOperand : BinNat → FieldKind → Bytes → State → Prop
  /-- `ReadOne: (ReadOperand limit (WordField) xs) ~> (OperandWord (ReadULEB62 xs));` -/
  | readOne {limit : BinNat} {xs : Bytes} {s : CodecState} {r : State} :
      ReadULEB62 xs s → OperandWord (.ofCodec s) r → ReadOperand limit .word xs r
  /-- `ReadBytes: (ReadOperand limit (BytesField) xs) ~> (CountValues limit (BytesField) (ReadULEB62
  xs));` -/
  | readBytes {limit : BinNat} {xs : Bytes} {s : CodecState} {r : State} :
      ReadULEB62 xs s → CountValues limit .bytes (.ofCodec s) r → ReadOperand limit .bytes xs r
  /-- `ReadMany: (ReadOperand limit (WordsField) xs) ~> (CountValues limit (WordsField) (ReadULEB62
  xs));` -/
  | readMany {limit : BinNat} {xs : Bytes} {s : CodecState} {r : State} :
      ReadULEB62 xs s → CountValues limit .words (.ofCodec s) r → ReadOperand limit .words xs r
  /-- `ReadPairList: (ReadOperand limit (PairsField) xs) ~> (CountValues limit (PairsField)
  (ReadULEB62 xs));` -/
  | readPairList {limit : BinNat} {xs : Bytes} {s : CodecState} {r : State} :
      ReadULEB62 xs s → CountValues limit .pairs (.ofCodec s) r → ReadOperand limit .pairs xs r

mutual

/-- `DecodeFields`. -/
inductive DecodeFields : BinNat → FieldLayout → Bytes → State → Prop
  /-- `FieldsEmpty: (DecodeFields limit (FieldsEnd) xs) ~> (FieldsDecoded (OperandsNil) xs);` -/
  | fieldsEmpty {limit : BinNat} {xs : Bytes} :
      DecodeFields limit .fieldsEnd xs (.fieldsDecoded .nil xs)
  /-- `FieldsMore: (DecodeFields limit (FieldNext kind tailfields) xs) ~> (FieldCarry limit
  tailfields (ReadOperand limit kind xs));` -/
  | fieldsMore {limit : BinNat} {kind : FieldKind} {tailfields : FieldLayout} {xs : Bytes}
      {s r : State} :
      ReadOperand limit kind xs s → FieldCarry limit tailfields s r →
        DecodeFields limit (.fieldNext kind tailfields) xs r

/-- `FieldCarry`. -/
inductive FieldCarry : BinNat → FieldLayout → State → State → Prop
  /-- `FieldsNext: (FieldCarry limit tailfields (OperandDecoded value rest)) ~> (FieldPush value
  (DecodeFields limit tailfields rest));` -/
  | fieldsNext {limit : BinNat} {tailfields : FieldLayout} {value : Operand} {rest : Bytes}
      {s r : State} :
      DecodeFields limit tailfields rest s → FieldPush value s r →
        FieldCarry limit tailfields (.operandDecoded value rest) r
  /-- `FieldCarryNeedInput: (FieldCarry limit tailfields (NeedInput)) ~> (NeedInput);` -/
  | fieldCarryNeedInput {limit : BinNat} {tailfields : FieldLayout} :
      FieldCarry limit tailfields .needInput .needInput
  /-- `FieldCarryBadInteger: (FieldCarry limit tailfields (BadInteger)) ~> (BadInteger);` -/
  | fieldCarryBadInteger {limit : BinNat} {tailfields : FieldLayout} :
      FieldCarry limit tailfields .badInteger .badInteger
  /-- `FieldCarryLimitExceeded: (FieldCarry limit tailfields (LimitExceeded)) ~>
  (LimitExceeded);` -/
  | fieldCarryLimitExceeded {limit : BinNat} {tailfields : FieldLayout} :
      FieldCarry limit tailfields .limitExceeded .limitExceeded

end

/-- `SelectRecord`. -/
inductive SelectRecord : BinNat → Byte → Bytes → FoundLayout → State → Prop
  /-- `RecordKnown: (SelectRecord limit op rest (FoundLayout fields)) ~> (RecordFields op
  (DecodeFields limit fields rest));` -/
  | recordKnown {limit : BinNat} {op : Byte} {rest : Bytes} {fields : FieldLayout} {s r : State} :
      DecodeFields limit fields rest s → RecordFields op s r →
        SelectRecord limit op rest (.foundLayout fields) r
  /-- `RecordUnknown: (SelectRecord limit op rest (NoLayout)) ~> (UnknownOpcode op);` -/
  | recordUnknown {limit : BinNat} {op : Byte} {rest : Bytes} :
      SelectRecord limit op rest .noLayout (.unknownOpcode op)

/-- `ReadRecord`. -/
inductive ReadRecord : BinNat → Schemas → Bytes → State → Prop
  /-- `RecordEmpty: (ReadRecord limit schemas (BNil)) ~> (NeedInput);` -/
  | recordEmpty {limit : BinNat} {schemas : Schemas} : ReadRecord limit schemas .nil .needInput
  /-- `RecordStart: (ReadRecord limit schemas (BCons op rest)) ~> (SelectRecord limit op rest
  (LookupSchema op schemas));` -/
  | recordStart {limit : BinNat} {schemas : Schemas} {op : Byte} {rest : Bytes}
      {found : FoundLayout} {r : State} :
      LookupSchema op schemas found → SelectRecord limit op rest found r →
        ReadRecord limit schemas (.cons op rest) r

/-- `ReadULEB62` gives `NeedInput`, `BadInteger`, or a canonical numeral and a rest no longer than
its input. -/
theorem readULEB62_rest {xs : Bytes} {s : CodecState} (h : ReadULEB62 xs s) :
    s = .needInput ∨ s = .badInteger ∨
      ∃ v rest, s = .decodedWord (BinNat.ofNat v) rest ∧ rest.toList.length ≤ xs.toList.length := by
  rw [readULEB62_iff] at h
  subst h
  cases lebSpec 8 (xs.toList.map Byte.val) with
  | needInput => exact .inl rfl
  | badInteger => exact .inr (.inl rfl)
  | decoded v k =>
    refine .inr (.inr ⟨v, _, rfl, ?_⟩)
    simp only [Bytes.toList_ofList, List.length_drop]
    omega

/-- `TakeBytes` on a canonical count gives `NeedInput`, or the bytes taken and a rest no longer
than its input. -/
theorem takeBytes_rest (k : Nat) (xs : Bytes) :
    ∃ s, TakeBytes (BinNat.ofNat k) xs s ∧
      (s = .needInput ∨ ∃ pre rest, s = .taken pre rest ∧ rest.toList.length ≤ xs.toList.length) := by
  refine ⟨_, takeBytes_iff.mpr rfl, ?_⟩
  unfold takeSpec
  split
  · refine .inr ⟨_, _, rfl, ?_⟩
    simp only [Bytes.toList_ofList, List.length_drop]
    omega
  · exact .inl rfl

/-- `ReadWords` has a value on every canonical count and input: `NeedInput`, `BadInteger`, or the
words and a rest no longer than the input. -/
theorem readWords_total : ∀ (k : Nat) (xs : Bytes), ∃ s, ReadWords (BinNat.ofNat k) xs s ∧
    (s = .needInput ∨ s = .badInteger ∨
      ∃ ws rest, s = .wordsDecoded ws rest ∧ rest.toList.length ≤ xs.toList.length)
  | 0, _ => ⟨_, .wordsEnd, .inr (.inr ⟨_, _, rfl, Nat.le_refl _⟩)⟩
  | k + 1, xs => by
    have hp : NatPred (BinNat.ofNat (k + 1)) (BinNat.ofNat k) := natPred_iff.mpr ⟨by omega, by simp⟩
    obtain ⟨s0, hs0⟩ := readULEB62_total xs
    have hcarry : ∃ r, WordsCarry (BinNat.ofNat k) (.ofCodec s0) r ∧
        (r = .needInput ∨ r = .badInteger ∨
          ∃ ws rest, r = .wordsDecoded ws rest ∧ rest.toList.length ≤ xs.toList.length) := by
      rcases readULEB62_rest hs0 with rfl | rfl | ⟨v, rest0, rfl, hlen0⟩
      · exact ⟨_, .wordsCarryNeedInput, .inl rfl⟩
      · exact ⟨_, .wordsCarryBadInteger, .inr (.inl rfl)⟩
      · obtain ⟨s1, hs1, hshape1⟩ := readWords_total k rest0
        rcases hshape1 with rfl | rfl | ⟨ws, rest1, rfl, hlen1⟩
        · exact ⟨_, .wordsNext hs1 .wordsPushNeedInput, .inl rfl⟩
        · exact ⟨_, .wordsNext hs1 .wordsPushBadInteger, .inr (.inl rfl)⟩
        · exact ⟨_, .wordsNext hs1 .wordsConsValue,
            .inr (.inr ⟨_, _, rfl, Nat.le_trans hlen1 hlen0⟩)⟩
    obtain ⟨r, hr, hshape⟩ := hcarry
    rw [BinNat.ofNat_of_ne_zero (by omega : k + 1 ≠ 0)] at hp ⊢
    exact ⟨r, .wordsRead hp hs0 hr, hshape⟩

/-- `ReadPairs` has a value on every canonical count and input: `NeedInput`, `BadInteger`, or the
pairs and a rest no longer than the input. -/
theorem readPairs_total : ∀ (k : Nat) (xs : Bytes), ∃ s, ReadPairs (BinNat.ofNat k) xs s ∧
    (s = .needInput ∨ s = .badInteger ∨
      ∃ ps rest, s = .pairsDecoded ps rest ∧ rest.toList.length ≤ xs.toList.length)
  | 0, _ => ⟨_, .pairsEnd, .inr (.inr ⟨_, _, rfl, Nat.le_refl _⟩)⟩
  | k + 1, xs => by
    have hp : NatPred (BinNat.ofNat (k + 1)) (BinNat.ofNat k) := natPred_iff.mpr ⟨by omega, by simp⟩
    obtain ⟨s0, hs0⟩ := readULEB62_total xs
    have hfirst : ∃ r, PairsFirst (BinNat.ofNat k) (.ofCodec s0) r ∧
        (r = .needInput ∨ r = .badInteger ∨
          ∃ ps rest, r = .pairsDecoded ps rest ∧ rest.toList.length ≤ xs.toList.length) := by
      rcases readULEB62_rest hs0 with rfl | rfl | ⟨first, rest0, rfl, hlen0⟩
      · exact ⟨_, .pairsFirstNeedInput, .inl rfl⟩
      · exact ⟨_, .pairsFirstBadInteger, .inr (.inl rfl)⟩
      · obtain ⟨s1, hs1⟩ := readULEB62_total rest0
        rcases readULEB62_rest hs1 with rfl | rfl | ⟨second, rest1, rfl, hlen1⟩
        · exact ⟨_, .pairsReadSecond hs1 .pairsSecondNeedInput, .inl rfl⟩
        · exact ⟨_, .pairsReadSecond hs1 .pairsSecondBadInteger, .inr (.inl rfl)⟩
        · obtain ⟨s2, hs2, hshape2⟩ := readPairs_total k rest1
          rcases hshape2 with rfl | rfl | ⟨ps, rest2, rfl, hlen2⟩
          · exact ⟨_, .pairsReadSecond hs1 (.pairsNext hs2 .pairsPushNeedInput), .inl rfl⟩
          · exact ⟨_, .pairsReadSecond hs1 (.pairsNext hs2 .pairsPushBadInteger), .inr (.inl rfl)⟩
          · exact ⟨_, .pairsReadSecond hs1 (.pairsNext hs2 .pairsConsValue),
              .inr (.inr ⟨_, _, rfl, Nat.le_trans hlen2 (Nat.le_trans hlen1 hlen0)⟩)⟩
    obtain ⟨r, hr, hshape⟩ := hfirst
    rw [BinNat.ofNat_of_ne_zero (by omega : k + 1 ≠ 0)] at hp ⊢
    exact ⟨r, .pairsRead hp hs0 hr, hshape⟩

/-- `ReadValues` has a value on every counted kind, canonical count and input: `NeedInput`,
`BadInteger`, or the operand and a rest no longer than the input. -/
theorem readValues_total {kind : FieldKind} (hk : kind ≠ .word) (k : Nat) (xs : Bytes) :
    ∃ r, ReadValues kind (BinNat.ofNat k) xs r ∧
      (r = .needInput ∨ r = .badInteger ∨
        ∃ o rest, r = .operandDecoded o rest ∧ rest.toList.length ≤ xs.toList.length) := by
  cases kind with
  | word => exact absurd rfl hk
  | bytes =>
    obtain ⟨s, hs, hshape⟩ := takeBytes_rest k xs
    rcases hshape with rfl | ⟨pre, rest, rfl, hlen⟩
    · exact ⟨_, .valuesBytes hs .operandBytesNeedInput, .inl rfl⟩
    · exact ⟨_, .valuesBytes hs .bytesValue, .inr (.inr ⟨_, _, rfl, hlen⟩)⟩
  | words =>
    obtain ⟨s, hs, hshape⟩ := readWords_total k xs
    rcases hshape with rfl | rfl | ⟨ws, rest, rfl, hlen⟩
    · exact ⟨_, .valuesWords hs .operandWordsNeedInput, .inl rfl⟩
    · exact ⟨_, .valuesWords hs .operandWordsBadInteger, .inr (.inl rfl)⟩
    · exact ⟨_, .valuesWords hs .wordsValue, .inr (.inr ⟨_, _, rfl, hlen⟩)⟩
  | pairs =>
    obtain ⟨s, hs, hshape⟩ := readPairs_total k xs
    rcases hshape with rfl | rfl | ⟨ps, rest, rfl, hlen⟩
    · exact ⟨_, .valuesPairs hs .operandPairsNeedInput, .inl rfl⟩
    · exact ⟨_, .valuesPairs hs .operandPairsBadInteger, .inr (.inl rfl)⟩
    · exact ⟨_, .valuesPairs hs .pairsValue, .inr (.inr ⟨_, _, rfl, hlen⟩)⟩

/-- `ReadOperand` has a value on every kind and input: a refusal, or the operand and a rest no
longer than the input. -/
theorem readOperand_total (limit : BinNat) (kind : FieldKind) (xs : Bytes) :
    ∃ r, ReadOperand limit kind xs r ∧
      (r = .needInput ∨ r = .badInteger ∨ r = .limitExceeded ∨
        ∃ o rest, r = .operandDecoded o rest ∧ rest.toList.length ≤ xs.toList.length) := by
  obtain ⟨s, hs⟩ := readULEB62_total xs
  have count : ∀ {kind : FieldKind}, kind ≠ .word → ∃ r, CountValues limit kind (.ofCodec s) r ∧
      (r = .needInput ∨ r = .badInteger ∨ r = .limitExceeded ∨
        ∃ o rest, r = .operandDecoded o rest ∧ rest.toList.length ≤ xs.toList.length) := by
    intro kind hk
    rcases readULEB62_rest hs with rfl | rfl | ⟨v, rest, rfl, hlen⟩
    · exact ⟨_, .countValuesNeedInput, .inl rfl⟩
    · exact ⟨_, .countValuesBadInteger, .inr (.inl rfl)⟩
    · obtain ⟨o, ho⟩ := natCompare_total (BinNat.ofNat v) limit
      have small : ∃ r, ReadValues kind (BinNat.ofNat v) rest r ∧
          (r = .needInput ∨ r = .badInteger ∨ r = .limitExceeded ∨
            ∃ o rest', r = .operandDecoded o rest' ∧ rest'.toList.length ≤ xs.toList.length) := by
        obtain ⟨r, hr, hshape⟩ := readValues_total hk v rest
        refine ⟨r, hr, ?_⟩
        rcases hshape with rfl | rfl | ⟨o', rest', rfl, hlen'⟩
        · exact .inl rfl
        · exact .inr (.inl rfl)
        · exact .inr (.inr (.inr ⟨_, _, rfl, Nat.le_trans hlen' hlen⟩))
      cases o with
      | less =>
        obtain ⟨r, hr, hshape⟩ := small
        exact ⟨r, .countValue ho (.countSmall hr), hshape⟩
      | equal =>
        obtain ⟨r, hr, hshape⟩ := small
        exact ⟨r, .countValue ho (.countEqual hr), hshape⟩
      | greater => exact ⟨_, .countValue ho .countLarge, .inr (.inr (.inl rfl))⟩
  cases kind with
  | word =>
    rcases readULEB62_rest hs with rfl | rfl | ⟨v, rest, rfl, hlen⟩
    · exact ⟨_, .readOne hs .operandWordNeedInput, .inl rfl⟩
    · exact ⟨_, .readOne hs .operandWordBadInteger, .inr (.inl rfl)⟩
    · exact ⟨_, .readOne hs .wordValue, .inr (.inr (.inr ⟨_, _, rfl, hlen⟩))⟩
  | bytes =>
    obtain ⟨r, hr, hshape⟩ := count (kind := .bytes) nofun
    exact ⟨r, .readBytes hs hr, hshape⟩
  | words =>
    obtain ⟨r, hr, hshape⟩ := count (kind := .words) nofun
    exact ⟨r, .readMany hs hr, hshape⟩
  | pairs =>
    obtain ⟨r, hr, hshape⟩ := count (kind := .pairs) nofun
    exact ⟨r, .readPairList hs hr, hshape⟩

/-- `DecodeFields` has a value on every layout and input: a refusal, or the operands and a rest no
longer than the input. -/
theorem decodeFields_total (limit : BinNat) : ∀ (fields : FieldLayout) (xs : Bytes),
    ∃ r, DecodeFields limit fields xs r ∧
      (r = .needInput ∨ r = .badInteger ∨ r = .limitExceeded ∨
        ∃ ops rest, r = .fieldsDecoded ops rest ∧ rest.toList.length ≤ xs.toList.length)
  | .fieldsEnd, _ => ⟨_, .fieldsEmpty, .inr (.inr (.inr ⟨_, _, rfl, Nat.le_refl _⟩))⟩
  | .fieldNext kind tail, xs => by
    obtain ⟨s, hs, hshape⟩ := readOperand_total limit kind xs
    rcases hshape with rfl | rfl | rfl | ⟨value, rest, rfl, hlen⟩
    · exact ⟨_, .fieldsMore hs .fieldCarryNeedInput, .inl rfl⟩
    · exact ⟨_, .fieldsMore hs .fieldCarryBadInteger, .inr (.inl rfl)⟩
    · exact ⟨_, .fieldsMore hs .fieldCarryLimitExceeded, .inr (.inr (.inl rfl))⟩
    · obtain ⟨s1, hs1, hshape1⟩ := decodeFields_total limit tail rest
      rcases hshape1 with rfl | rfl | rfl | ⟨ops, rest1, rfl, hlen1⟩
      · exact ⟨_, .fieldsMore hs (.fieldsNext hs1 .fieldPushNeedInput), .inl rfl⟩
      · exact ⟨_, .fieldsMore hs (.fieldsNext hs1 .fieldPushBadInteger), .inr (.inl rfl)⟩
      · exact ⟨_, .fieldsMore hs (.fieldsNext hs1 .fieldPushLimitExceeded),
          .inr (.inr (.inl rfl))⟩
      · exact ⟨_, .fieldsMore hs (.fieldsNext hs1 .fieldsCons),
          .inr (.inr (.inr ⟨_, _, rfl, Nat.le_trans hlen1 hlen⟩))⟩

/-- `SelectRecord` has a value on every layout found or not: a refusal, `UnknownOpcode`, or the
record and a rest no longer than the input after the opcode. -/
theorem selectRecord_total (limit : BinNat) (op : Byte) (rest : Bytes) (found : FoundLayout) :
    ∃ r, SelectRecord limit op rest found r ∧
      (r = .needInput ∨ r = .badInteger ∨ r = .limitExceeded ∨ r = .unknownOpcode op ∨
        ∃ record rest', r = .recordDecoded record rest' ∧
          rest'.toList.length ≤ rest.toList.length) := by
  cases found with
  | noLayout => exact ⟨_, .recordUnknown, .inr (.inr (.inr (.inl rfl)))⟩
  | foundLayout fields =>
    obtain ⟨s, hs, hshape⟩ := decodeFields_total limit fields rest
    rcases hshape with rfl | rfl | rfl | ⟨ops, rest', rfl, hlen⟩
    · exact ⟨_, .recordKnown hs .recordFieldsNeedInput, .inl rfl⟩
    · exact ⟨_, .recordKnown hs .recordFieldsBadInteger, .inr (.inl rfl)⟩
    · exact ⟨_, .recordKnown hs .recordFieldsLimitExceeded, .inr (.inr (.inl rfl))⟩
    · exact ⟨_, .recordKnown hs .recordMake, .inr (.inr (.inr (.inr ⟨_, _, rfl, hlen⟩)))⟩

/-- **`ReadRecord` gives what the loop needs**: on every opcode and rest, a result of a shape
`RecordCarry` has a rule for, a decoded record leaving at most the bytes after its opcode. -/
theorem readRecordGives : ReadRecordGives ReadRecord := by
  intro op rest
  obtain ⟨found, hfound⟩ := lookupSchema_total op holrSchema
  obtain ⟨r, hr, hshape⟩ := selectRecord_total recordLimit op rest found
  refine ⟨r, .recordStart hfound hr, ?_⟩
  rcases hshape with rfl | rfl | rfl | rfl | ⟨record, rest', rfl, hlen⟩
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr (.inl rfl)))
  · exact .inr (.inr (.inr (.inr rfl)))
  · exact .inr (.inl ⟨_, rfl⟩)
  · exact .inl ⟨_, _, rfl, hlen⟩

/-- **The HOLR reader's loop has a value on every input**, with the module's own `ReadRecord`. -/
theorem holrLoop_total_readRecord (full : Bytes) (header : Header) (xs : Bytes) (count : BinNat) :
    ∃ v, HOLRLoop ReadRecord full header count xs v :=
  holrLoop_total readRecordGives full header xs count

/-! ## Promised values -/

section Promise

universe uA uB uL

/-- A value as the compiled code holds it, for the comparison of values and the views of promised
sorts: an atom (an immediate or a foreign value, read through its own representation), a symbolic
term (its constructor and its children), or a promise (`RC_PROMISE`,
foreign tag 6) holding the number the host gave it. -/
inductive RVal (A : Type uA) (L : Type uL) : Type (max uA uL)
  /-- An atom. -/
  | atom (x : A)
  /-- A symbolic term. -/
  | node (c : L) (kids : List (RVal A L))
  /-- A promise. -/
  | promise (p : Nat)

/-- Module data: the terms the values stand for, over the data the atoms stand for. -/
inductive MData (B : Type uB) (L : Type uL) : Type (max uB uL)
  /-- The datum of an atom. -/
  | atom (x : B)
  /-- A term: its constructor and its children. -/
  | node (c : L) (kids : List (MData B L))

variable {A : Type uA} {B : Type uB} {L : Type uL}

/-- `RC_IS_PROMISE`. -/
def RVal.isPromise : RVal A L → Bool
  | .promise _ => true
  | _ => false

/-- The representations of the atoms: the datum each atom stands for, and a test on two atoms that
are not the same word (`rc_term_equal` answers `false`: immediates are numbers, and the stores of
foreign values intern them). -/
structure Atoms (A : Type uA) (B : Type uB) where
  /-- The datum an atom stands for. -/
  datum : A → B
  /-- The test on two atoms that are different words. -/
  test : A → A → Bool

/-- The atoms' test decides equality of their data: the contract of the atoms' own representations
(one word per number, one object per value of an interning store). -/
def Atoms.Exact (R : Atoms A B) : Prop := ∀ x y, R.test x y = true ↔ R.datum x = R.datum y

mutual

/-- The module data a value stands for, a promise `p` standing for `D p`. -/
def dataOf (R : Atoms A B) (D : Nat → MData B L) : RVal A L → MData B L
  | .atom x => .atom (R.datum x)
  | .node c kids => .node c (dataOfList R D kids)
  | .promise p => D p

/-- `dataOf` on a list of values. -/
def dataOfList (R : Atoms A B) (D : Nat → MData B L) : List (RVal A L) → List (MData B L)
  | [] => []
  | x :: xs => dataOf R D x :: dataOfList R D xs

end

theorem dataOfList_eq_map (R : Atoms A B) (D : Nat → MData B L) :
    ∀ xs : List (RVal A L), dataOfList R D xs = xs.map (dataOf R D)
  | [] => by rw [dataOfList, List.map_nil]
  | x :: xs => by rw [dataOfList, dataOfList_eq_map R D xs, List.map_cons]

@[simp] theorem dataOf_atom (R : Atoms A B) (D : Nat → MData B L) (x : A) :
    dataOf R D (.atom x : RVal A L) = .atom (R.datum x) := by
  rw [dataOf]

@[simp] theorem dataOf_node (R : Atoms A B) (D : Nat → MData B L) (c : L) (kids : List (RVal A L)) :
    dataOf R D (.node c kids) = .node c (kids.map (dataOf R D)) := by
  rw [dataOf, dataOfList_eq_map]

@[simp] theorem dataOf_promise (R : Atoms A B) (D : Nat → MData B L) (p : Nat) :
    dataOf R D (.promise p : RVal A L) = D p := by
  rw [dataOf]

/-- **The host's contract for its promises** (`rc_promise_hook`; `rc_rt.h`, `rc_feed.h`): asked for
the promise `p`, the host gives a term, never a promise, and it stands for the same module data
`D p` each time it is asked (the host may build the term anew).  `force p v`: asked for `p`, the
host may give `v`. -/
structure HostContract (R : Atoms A B) (force : Nat → RVal A L → Prop) (D : Nat → MData B L) :
    Prop where
  /-- What the host gives is never a promise (`rc_promise_force` stops the run otherwise). -/
  notPromise : ∀ p v, force p v → v.isPromise = false
  /-- What the host gives stands for the promised data, each time. -/
  sameData : ∀ p v, force p v → dataOf R D v = D p

/-- The host keeps every promise it made: asked for it, it gives a term (otherwise
`rc_promise_force` stops the run). -/
def Keeps (force : Nat → RVal A L → Prop) : Prop := ∀ p, ∃ v, force p v

/-- `rc_promised`: a promise forced through the host, any other value as it is. -/
inductive Promised (force : Nat → RVal A L → Prop) : RVal A L → RVal A L → Prop
  /-- A promise: what the host gives for it. -/
  | promise {p : Nat} {v : RVal A L} : force p v → Promised force (.promise p) v
  /-- An atom, as it is. -/
  | atom {x : A} : Promised force (.atom x) (.atom x)
  /-- A term, as it is. -/
  | node {c : L} {kids : List (RVal A L)} : Promised force (.node c kids) (.node c kids)

variable {R : Atoms A B} {force : Nat → RVal A L → Prop} {D : Nat → MData B L}

/-- Forcing keeps the module data. -/
theorem Promised.dataOf_eq (hc : HostContract R force D) {x y : RVal A L}
    (h : Promised force x y) : dataOf R D y = dataOf R D x := by
  cases h with
  | promise hf => rw [dataOf_promise]; exact hc.sameData _ _ hf
  | atom => rfl
  | node => rfl

theorem Promised.isPromise_false (hc : HostContract R force D) {x y : RVal A L}
    (h : Promised force x y) : y.isPromise = false := by
  cases h with
  | promise hf => exact hc.notPromise _ _ hf
  | atom => rfl
  | node => rfl

theorem promised_exists (hk : Keeps force) (x : RVal A L) : ∃ y, Promised force x y := by
  cases x with
  | atom x => exact ⟨_, .atom⟩
  | node c kids => exact ⟨_, .node⟩
  | promise p =>
    obtain ⟨v, hv⟩ := hk p
    exact ⟨v, .promise hv⟩

/-- A forced value whose module data is a term is that term's constructor over children standing
for its children. -/
theorem Promised.eq_node (hc : HostContract R force D) {x y : RVal A L} (h : Promised force x y)
    {c : L} {ks : List (MData B L)} (hd : dataOf R D x = .node c ks) :
    ∃ kids, y = .node c kids ∧ kids.map (dataOf R D) = ks := by
  have hy := h.dataOf_eq hc
  have hp := h.isPromise_false hc
  rw [hd] at hy
  cases y with
  | atom a => rw [dataOf_atom] at hy; cases hy
  | node c' kids =>
    rw [dataOf_node] at hy
    injection hy with h1 h2
    subst h1
    exact ⟨kids, rfl, h2⟩
  | promise q => cases hp

/-- A forced value whose module data is an atom's datum is an atom with that datum. -/
theorem Promised.eq_atom (hc : HostContract R force D) {x y : RVal A L} (h : Promised force x y)
    {d : B} (hd : dataOf R D x = .atom d) : ∃ a, y = .atom a ∧ R.datum a = d := by
  have hy := h.dataOf_eq hc
  have hp := h.isPromise_false hc
  rw [hd] at hy
  cases y with
  | atom a =>
    rw [dataOf_atom] at hy
    injection hy with h1
    exact ⟨a, rfl, h1⟩
  | node c' kids => rw [dataOf_node] at hy; cases hy
  | promise q => cases hp

/-! ### The views -/

/-- `RC_TAG_promise`: the constructor read from a value, forced if a promise. -/
def TagIs (force : Nat → RVal A L → Prop) (x : RVal A L) (c : L) : Prop :=
  ∃ kids, Promised force x (.node c kids)

/-- `RC_KID_promise`: child `i` read from a value, forced (again) if a promise. -/
def KidIs (force : Nat → RVal A L → Prop) (x : RVal A L) (i : Nat) (y : RVal A L) : Prop :=
  ∃ c kids, Promised force x (.node c kids) ∧ kids[i]? = some y

/-- **The view of a promise is the view of its forced term**: its constructor. -/
theorem tagIs_promise_iff (hc : HostContract R force D) {p : Nat} {c : L} :
    TagIs force (.promise p) c ↔ ∃ v, force p v ∧ TagIs force v c := by
  constructor
  · rintro ⟨kids, h⟩
    cases h with
    | promise hf => exact ⟨_, hf, kids, .node⟩
  · rintro ⟨v, hf, kids, h⟩
    cases h with
    | promise _ => exact absurd (hc.notPromise _ _ hf) (by simp [RVal.isPromise])
    | node => exact ⟨kids, .promise hf⟩

/-- **The view of a promise is the view of its forced term**: its children. -/
theorem kidIs_promise_iff (hc : HostContract R force D) {p : Nat} {i : Nat} {y : RVal A L} :
    KidIs force (.promise p) i y ↔ ∃ v, force p v ∧ KidIs force v i y := by
  constructor
  · rintro ⟨c, kids, h, hi⟩
    cases h with
    | promise hf => exact ⟨_, hf, c, kids, .node, hi⟩
  · rintro ⟨v, hf, c, kids, h, hi⟩
    cases h with
    | promise _ => exact absurd (hc.notPromise _ _ hf) (by simp [RVal.isPromise])
    | node => exact ⟨c, kids, .promise hf, hi⟩

/-- The constructor a view reads is the constructor of the value's module data. -/
theorem TagIs.data (hc : HostContract R force D) {x : RVal A L} {c : L} (h : TagIs force x c) :
    ∃ ks, dataOf R D x = .node c ks := by
  obtain ⟨kids, hp⟩ := h
  exact ⟨_, (hp.dataOf_eq hc).symm.trans (dataOf_node R D c kids)⟩

/-- The child a view reads stands for the child of the value's module data. -/
theorem KidIs.data (hc : HostContract R force D) {x : RVal A L} {i : Nat} {y : RVal A L}
    (h : KidIs force x i y) :
    ∃ c ks, dataOf R D x = .node c ks ∧ ks[i]? = some (dataOf R D y) := by
  obtain ⟨c, kids, hp, hi⟩ := h
  refine ⟨c, kids.map (dataOf R D), (hp.dataOf_eq hc).symm.trans (dataOf_node R D c kids), ?_⟩
  rw [List.getElem?_map, hi]
  rfl

/-- Conversely, a value whose module data is a term has that view, when the host keeps its
promises. -/
theorem kidIs_of_data (hc : HostContract R force D) (hk : Keeps force) {x : RVal A L} {c : L}
    {ks : List (MData B L)} (hd : dataOf R D x = .node c ks) :
    TagIs force x c ∧ ∀ {i : Nat} {d : MData B L}, ks[i]? = some d →
      ∃ y, KidIs force x i y ∧ dataOf R D y = d := by
  obtain ⟨y, hy⟩ := promised_exists hk x
  obtain ⟨kids, rfl, hks⟩ := hy.eq_node hc hd
  refine ⟨⟨kids, hy⟩, fun {i d} hi => ?_⟩
  rw [← hks, List.getElem?_map] at hi
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp hi
  exact ⟨z, ⟨c, kids, hy, hz⟩, rfl⟩

/-! ### Equality (`rc_term_equal`) -/

mutual

/-- `rc_term_equal` on a pair of values, as the C computes it: the same word is the same value; a
promise on either side is forced (`rc_promised`, both sides) and the forced values are compared;
otherwise the values are compared as they are. -/
inductive TermEqual (R : Atoms A B) (force : Nat → RVal A L → Prop) :
    RVal A L → RVal A L → Bool → Prop
  /-- `x == y`: one word, one value. -/
  | same {x : RVal A L} : TermEqual R force x x true
  /-- A promise on either side: both read through `rc_promised`, then compared. -/
  | forced {x y x' y' : RVal A L} {b : Bool} :
      (x.isPromise = true ∨ y.isPromise = true) → Promised force x x' → Promised force y y' →
        TermEqualTerms R force x' y' b → TermEqual R force x y b
  /-- No promise. -/
  | terms {x y : RVal A L} {b : Bool} :
      x.isPromise = false → y.isPromise = false → TermEqualTerms R force x y b →
        TermEqual R force x y b

/-- The comparison of two values that are not promises. -/
inductive TermEqualTerms (R : Atoms A B) (force : Nat → RVal A L → Prop) :
    RVal A L → RVal A L → Bool → Prop
  /-- `x == y` after forcing. -/
  | same {x : RVal A L} : TermEqualTerms R force x x true
  /-- Two atoms: the atoms' test. -/
  | atoms {x y : A} : TermEqualTerms R force (.atom x) (.atom y) (R.test x y)
  /-- An atom and a term differ. -/
  | atomNode {x : A} {c : L} {kids : List (RVal A L)} :
      TermEqualTerms R force (.atom x) (.node c kids) false
  /-- A term and an atom differ. -/
  | nodeAtom {c : L} {kids : List (RVal A L)} {x : A} :
      TermEqualTerms R force (.node c kids) (.atom x) false
  /-- Two terms of different constructors or numbers of children differ. -/
  | nodeMismatch {c c' : L} {kids kids' : List (RVal A L)} :
      (c ≠ c' ∨ kids.length ≠ kids'.length) →
        TermEqualTerms R force (.node c kids) (.node c' kids') false
  /-- Two terms of one constructor: their children, pair by pair. -/
  | nodes {c : L} {kids kids' : List (RVal A L)} {b : Bool} :
      kids.length = kids'.length → TermEqualKids R force kids.reverse kids'.reverse b →
        TermEqualTerms R force (.node c kids) (.node c kids') b

/-- The pairs of children, in the order the C's stack pops them (the last child first, each with
all it holds before the next), stopping at the first pair that differs. -/
inductive TermEqualKids (R : Atoms A B) (force : Nat → RVal A L → Prop) :
    List (RVal A L) → List (RVal A L) → Bool → Prop
  /-- No more pairs. -/
  | nil : TermEqualKids R force [] [] true
  /-- A pair that differs ends the comparison. -/
  | differ {x y : RVal A L} {xs ys : List (RVal A L)} :
      TermEqual R force x y false → TermEqualKids R force (x :: xs) (y :: ys) false
  /-- A pair that agrees, then the rest. -/
  | agree {x y : RVal A L} {xs ys : List (RVal A L)} {b : Bool} :
      TermEqual R force x y true → TermEqualKids R force xs ys b →
        TermEqualKids R force (x :: xs) (y :: ys) b

end

mutual

/-- **`rc_term_equal` is equality of module data**: whatever the host gives for the promises it
forces, the answer is `true` exactly when the two values stand for the same module data. -/
theorem TermEqual.sound (hR : R.Exact) (hc : HostContract R force D) :
    ∀ {x y : RVal A L} {b : Bool}, TermEqual R force x y b →
      (b = true ↔ dataOf R D x = dataOf R D y)
  | _, _, _, .same => by simp
  | _, _, _, .forced _ hx hy h => by
    rw [← hx.dataOf_eq hc, ← hy.dataOf_eq hc]
    exact TermEqualTerms.sound hR hc h
  | _, _, _, .terms _ _ h => TermEqualTerms.sound hR hc h

theorem TermEqualTerms.sound (hR : R.Exact) (hc : HostContract R force D) :
    ∀ {x y : RVal A L} {b : Bool}, TermEqualTerms R force x y b →
      (b = true ↔ dataOf R D x = dataOf R D y)
  | _, _, _, .same => by simp
  | _, _, _, .atoms => by
    rw [dataOf_atom, dataOf_atom, MData.atom.injEq]
    exact hR _ _
  | _, _, _, .atomNode => by simp
  | _, _, _, .nodeAtom => by simp
  | _, _, _, .nodeMismatch h => by
    rw [dataOf_node, dataOf_node]
    constructor
    · intro e
      cases e
    · intro e
      injection e with e1 e2
      rcases h with h | h
      · exact absurd e1 h
      · exact absurd (by simpa using congrArg List.length e2) h
  | _, _, _, .nodes _ h => by
    rw [TermEqualKids.sound hR hc h, dataOf_node, dataOf_node, MData.node.injEq, List.map_reverse,
      List.map_reverse, List.reverse_inj]
    simp

theorem TermEqualKids.sound (hR : R.Exact) (hc : HostContract R force D) :
    ∀ {xs ys : List (RVal A L)} {b : Bool}, TermEqualKids R force xs ys b →
      (b = true ↔ xs.map (dataOf R D) = ys.map (dataOf R D))
  | _, _, _, .nil => by simp
  | _, _, _, @TermEqualKids.differ _ _ _ _ _ x y xs ys h => by
    have hne : dataOf R D x ≠ dataOf R D y := fun e =>
      absurd ((TermEqual.sound hR hc h).mpr e) (by decide)
    rw [List.map_cons, List.map_cons]
    constructor
    · intro e
      cases e
    · intro e
      injection e with e1 _
      exact absurd e1 hne
  | _, _, _, .agree h hs => by
    have h1 := (TermEqual.sound hR hc h).mp rfl
    rw [List.map_cons, List.map_cons, List.cons.injEq, h1, TermEqualKids.sound hR hc hs]
    simp

end

mutual

/-- The size of module data. -/
def MData.size : MData B L → Nat
  | .atom _ => 1
  | .node _ kids => MData.sizeList kids + 1

/-- The sizes of a list of module data, summed. -/
def MData.sizeList : List (MData B L) → Nat
  | [] => 0
  | k :: ks => MData.size k + MData.sizeList ks

end

theorem MData.size_le_sizeList : ∀ {ks : List (MData B L)} {k : MData B L}, k ∈ ks →
    k.size ≤ MData.sizeList ks
  | [], _, h => nomatch h
  | k' :: ks, k, h => by
    rw [MData.sizeList]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := MData.size_le_sizeList h
      omega

/-- **`rc_term_equal` has an answer** on every pair of values, when the host keeps its promises and
its contract (the module data are finite terms, so the comparison ends). -/
theorem termEqual_total (hc : HostContract R force D) (hk : Keeps force) (x y : RVal A L) :
    ∃ b, TermEqual R force x y b := by
  suffices H : ∀ (n : Nat) (x y : RVal A L), (dataOf R D x).size < n →
      ∃ b, TermEqual R force x y b from H _ x y (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro x y h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    have kidsEx : ∀ (xs ys : List (RVal A L)), xs.length = ys.length →
        (∀ k ∈ xs, (dataOf R D k).size < n) → ∃ b, TermEqualKids R force xs ys b := by
      intro xs
      induction xs with
      | nil =>
        intro ys hl _
        cases ys with
        | nil => exact ⟨_, .nil⟩
        | cons _ _ => simp at hl
      | cons x xs ihx =>
        intro ys hl hs
        cases ys with
        | nil => simp at hl
        | cons y ys =>
          obtain ⟨b0, h0⟩ := ih x y (hs x (List.mem_cons_self ..))
          cases b0 with
          | false => exact ⟨_, .differ h0⟩
          | true =>
            obtain ⟨b, hb⟩ := ihx ys (by simpa using hl)
              (fun k hk => hs k (List.mem_cons_of_mem _ hk))
            exact ⟨b, .agree h0 hb⟩
    have terms : ∀ x' y' : RVal A L, x'.isPromise = false → y'.isPromise = false →
        (dataOf R D x').size < n + 1 → ∃ b, TermEqualTerms R force x' y' b := by
      intro x' y' hx' hy' hs
      cases x' with
      | promise _ => cases hx'
      | atom a =>
        cases y' with
        | atom a' => exact ⟨_, .atoms⟩
        | node c kids => exact ⟨_, .atomNode⟩
        | promise _ => cases hy'
      | node c kids =>
        cases y' with
        | atom a' => exact ⟨_, .nodeAtom⟩
        | promise _ => cases hy'
        | node c' kids' =>
          by_cases hm : c = c' ∧ kids.length = kids'.length
          · obtain ⟨rfl, hlen⟩ := hm
            have hkids : ∀ k ∈ kids.reverse, (dataOf R D k).size < n := by
              intro k hk
              have hle := MData.size_le_sizeList (List.mem_map_of_mem (f := dataOf R D)
                (List.mem_reverse.mp hk))
              rw [dataOf_node, MData.size] at hs
              omega
            obtain ⟨b, hb⟩ := kidsEx kids.reverse kids'.reverse (by simpa using hlen) hkids
            exact ⟨b, .nodes hlen hb⟩
          · refine ⟨_, .nodeMismatch ?_⟩
            by_cases h1 : c = c'
            · exact .inr (fun h2 => hm ⟨h1, h2⟩)
            · exact .inl h1
    intro x y hs
    by_cases hp : x.isPromise = true ∨ y.isPromise = true
    · obtain ⟨x', hx'⟩ := promised_exists hk x
      obtain ⟨y', hy'⟩ := promised_exists hk y
      obtain ⟨b, hb⟩ := terms x' y' (hx'.isPromise_false hc) (hy'.isPromise_false hc)
        (by rw [hx'.dataOf_eq hc]; exact hs)
      exact ⟨b, .forced hp hx' hy' hb⟩
    · have hx : x.isPromise = false := by
        cases h : x.isPromise
        · rfl
        · exact absurd (.inl h) hp
      have hy : y.isPromise = false := by
        cases h : y.isPromise
        · rfl
        · exact absurd (.inr h) hp
      obtain ⟨b, hb⟩ := terms x y hx hy hs
      exact ⟨b, .terms hx hy hb⟩

/-! ### Computations that read values only through views -/

/-- A computation of compiled rules over values held in registers (its arguments, then each value
it reads or builds, in order): it reads the head of a register (`RC_TAG`: a term's constructor, or
an atom's datum through the atom's own representation), reads a child of a register into a new
register (`RC_KID`), compares two registers (`rc_term_equal`), builds a term or an atom into a new
register (`RC_MK`), and ends with a register's value or with no result.  The continuations may be
any functions of what was read. -/
inductive Prog (A : Type uA) (B : Type uB) (L : Type uL) : Type (max uA uB uL)
  /-- The value of register `i`. -/
  | ret (i : Nat)
  /-- No result. -/
  | fail
  /-- Read the head of register `i`. -/
  | head (i : Nat) (k : B ⊕ L → Prog A B L)
  /-- Read child `j` of register `i` into a new register. -/
  | kid (i j : Nat) (k : Prog A B L)
  /-- Compare registers `i` and `j`. -/
  | eq (i j : Nat) (k : Bool → Prog A B L)
  /-- Build the term of constructor `c` over the registers `is` into a new register. -/
  | mk (c : L) (is : List Nat) (k : Prog A B L)
  /-- Build the atom `x` into a new register. -/
  | mkAtom (x : A) (k : Prog A B L)

/-- The registers `is`, if all exist. -/
def getRegs {X : Type _} (regs : List X) : List Nat → Option (List X)
  | [] => some []
  | i :: is => regs[i]?.bind fun x => (getRegs regs is).map (x :: ·)

theorem getRegs_map {X : Type _} {Y : Type _} (f : X → Y) (regs : List X) :
    ∀ is : List Nat, getRegs (regs.map f) is = (getRegs regs is).map (List.map f)
  | [] => rfl
  | i :: is => by
    simp only [getRegs, List.getElem?_map, getRegs_map f regs is]
    cases regs[i]? <;> cases getRegs regs is <;> simp

/-- A computation on the C's values: each read of a promise forces it through the host. -/
inductive RunV (R : Atoms A B) (force : Nat → RVal A L → Prop) :
    Prog A B L → List (RVal A L) → Option (RVal A L) → Prop
  /-- The value of register `i`. -/
  | ret {i : Nat} {regs : List (RVal A L)} {v : RVal A L} :
      regs[i]? = some v → RunV R force (.ret i) regs (some v)
  /-- No result. -/
  | fail {regs : List (RVal A L)} : RunV R force .fail regs none
  /-- The head of an atom: its datum. -/
  | headAtom {i : Nat} {k : B ⊕ L → Prog A B L} {regs : List (RVal A L)} {x : RVal A L} {a : A}
      {out : Option (RVal A L)} :
      regs[i]? = some x → Promised force x (.atom a) → RunV R force (k (.inl (R.datum a))) regs out →
        RunV R force (.head i k) regs out
  /-- The head of a term: its constructor (`RC_TAG_promise`). -/
  | headNode {i : Nat} {k : B ⊕ L → Prog A B L} {regs : List (RVal A L)} {x : RVal A L} {c : L}
      {kids : List (RVal A L)} {out : Option (RVal A L)} :
      regs[i]? = some x → Promised force x (.node c kids) → RunV R force (k (.inr c)) regs out →
        RunV R force (.head i k) regs out
  /-- A child (`RC_KID_promise`, forcing again). -/
  | kid {i j : Nat} {k : Prog A B L} {regs : List (RVal A L)} {x : RVal A L} {c : L}
      {kids : List (RVal A L)} {y : RVal A L} {out : Option (RVal A L)} :
      regs[i]? = some x → Promised force x (.node c kids) → kids[j]? = some y →
        RunV R force k (regs ++ [y]) out → RunV R force (.kid i j k) regs out
  /-- A comparison (`rc_term_equal`). -/
  | eq {i j : Nat} {k : Bool → Prog A B L} {regs : List (RVal A L)} {x y : RVal A L} {b : Bool}
      {out : Option (RVal A L)} :
      regs[i]? = some x → regs[j]? = some y → TermEqual R force x y b →
        RunV R force (k b) regs out → RunV R force (.eq i j k) regs out
  /-- A term built. -/
  | mk {c : L} {is : List Nat} {k : Prog A B L} {regs : List (RVal A L)} {xs : List (RVal A L)}
      {out : Option (RVal A L)} :
      getRegs regs is = some xs → RunV R force k (regs ++ [.node c xs]) out →
        RunV R force (.mk c is k) regs out
  /-- An atom built. -/
  | mkAtom {x : A} {k : Prog A B L} {regs : List (RVal A L)} {out : Option (RVal A L)} :
      RunV R force k (regs ++ [.atom x]) out → RunV R force (.mkAtom x k) regs out

/-- The same computation on module data. -/
inductive RunD (R : Atoms A B) : Prog A B L → List (MData B L) → Option (MData B L) → Prop
  /-- The value of register `i`. -/
  | ret {i : Nat} {regs : List (MData B L)} {d : MData B L} :
      regs[i]? = some d → RunD R (.ret i) regs (some d)
  /-- No result. -/
  | fail {regs : List (MData B L)} : RunD R .fail regs none
  /-- The head of an atom's datum. -/
  | headAtom {i : Nat} {k : B ⊕ L → Prog A B L} {regs : List (MData B L)} {d : B}
      {out : Option (MData B L)} :
      regs[i]? = some (.atom d) → RunD R (k (.inl d)) regs out → RunD R (.head i k) regs out
  /-- The head of a term. -/
  | headNode {i : Nat} {k : B ⊕ L → Prog A B L} {regs : List (MData B L)} {c : L}
      {ks : List (MData B L)} {out : Option (MData B L)} :
      regs[i]? = some (.node c ks) → RunD R (k (.inr c)) regs out → RunD R (.head i k) regs out
  /-- A child. -/
  | kid {i j : Nat} {k : Prog A B L} {regs : List (MData B L)} {c : L} {ks : List (MData B L)}
      {d : MData B L} {out : Option (MData B L)} :
      regs[i]? = some (.node c ks) → ks[j]? = some d → RunD R k (regs ++ [d]) out →
        RunD R (.kid i j k) regs out
  /-- A comparison: equality of the data. -/
  | eq {i j : Nat} {k : Bool → Prog A B L} {regs : List (MData B L)} {d e : MData B L} {b : Bool}
      {out : Option (MData B L)} :
      regs[i]? = some d → regs[j]? = some e → (b = true ↔ d = e) → RunD R (k b) regs out →
        RunD R (.eq i j k) regs out
  /-- A term built. -/
  | mk {c : L} {is : List Nat} {k : Prog A B L} {regs : List (MData B L)} {ds : List (MData B L)}
      {out : Option (MData B L)} :
      getRegs regs is = some ds → RunD R k (regs ++ [.node c ds]) out → RunD R (.mk c is k) regs out
  /-- An atom built. -/
  | mkAtom {x : A} {k : Prog A B L} {regs : List (MData B L)} {out : Option (MData B L)} :
      RunD R k (regs ++ [.atom (R.datum x)]) out → RunD R (.mkAtom x k) regs out

/-- A computation on module data has at most one result. -/
theorem RunD.functional {p : Prog A B L} {regs : List (MData B L)} {out out' : Option (MData B L)}
    (h : RunD R p regs out) (h' : RunD R p regs out') : out = out' := by
  induction h generalizing out' with
  | ret hi =>
    cases h' with
    | ret hi' => rw [hi] at hi'; cases hi'; rfl
  | fail => cases h'; rfl
  | headAtom hi _ ih =>
    cases h' with
    | headAtom hi' h'' => rw [hi] at hi'; cases hi'; exact ih h''
    | headNode hi' _ => rw [hi] at hi'; cases hi'
  | headNode hi _ ih =>
    cases h' with
    | headAtom hi' _ => rw [hi] at hi'; cases hi'
    | headNode hi' h'' => rw [hi] at hi'; cases hi'; exact ih h''
  | kid hi hj _ ih =>
    cases h' with
    | kid hi' hj' h'' =>
      rw [hi] at hi'
      cases hi'
      rw [hj] at hj'
      cases hj'
      exact ih h''
  | @eq i j k regs d e b out hi hj hb _ ih =>
    cases h' with
    | @eq _ _ _ _ d' e' b' _ hi' hj' hb' h'' =>
      rw [hi] at hi'
      cases hi'
      rw [hj] at hj'
      cases hj'
      have : b = b' := Bool.eq_iff_iff.mpr (hb.trans hb'.symm)
      subst this
      exact ih h''
  | mk hg _ ih =>
    cases h' with
    | mk hg' h'' => rw [hg] at hg'; cases hg'; exact ih h''
  | mkAtom _ ih =>
    cases h' with
    | mkAtom h'' => exact ih h''

/-- **A computation that reads values only through views computes on module data**: run on the C's
values, forcing promises as it reads them, it gives a result whose module data is the result of
the same computation on the module data of its arguments. -/
theorem RunV.data (hR : R.Exact) (hc : HostContract R force D) {p : Prog A B L}
    {regs : List (RVal A L)} {out : Option (RVal A L)} (h : RunV R force p regs out) :
    RunD R p (regs.map (dataOf R D)) (out.map (dataOf R D)) := by
  induction h with
  | ret hi => exact .ret (by simp [List.getElem?_map, hi])
  | fail => exact .fail
  | @headAtom i k regs x a out hi hp _ ih =>
    have hx : dataOf R D x = .atom (R.datum a) := by rw [← hp.dataOf_eq hc, dataOf_atom]
    exact .headAtom (by simp [List.getElem?_map, hi, hx]) ih
  | @headNode i k regs x c kids out hi hp _ ih =>
    have hx : dataOf R D x = .node c (kids.map (dataOf R D)) := by
      rw [← hp.dataOf_eq hc, dataOf_node]
    exact .headNode (ks := kids.map (dataOf R D)) (by simp [List.getElem?_map, hi, hx]) ih
  | @kid i j k regs x c kids y out hi hp hj _ ih =>
    have hx : dataOf R D x = .node c (kids.map (dataOf R D)) := by
      rw [← hp.dataOf_eq hc, dataOf_node]
    refine .kid (c := c) (ks := kids.map (dataOf R D)) (d := dataOf R D y)
      (by simp [List.getElem?_map, hi, hx]) (by simp [List.getElem?_map, hj]) ?_
    simpa [List.map_append] using ih
  | eq hi hj he _ ih =>
    exact .eq (by simp [List.getElem?_map, hi]) (by simp [List.getElem?_map, hj])
      (TermEqual.sound hR hc he) ih
  | @mk c is k regs xs out hg _ ih =>
    refine .mk (by rw [getRegs_map, hg]; rfl) ?_
    simpa [List.map_append] using ih
  | mkAtom _ ih =>
    exact .mkAtom (by simpa [List.map_append] using ih)

/-- Conversely, every result of a computation on module data is, as module data, a result of the
same computation on any values standing for its arguments, when the host keeps its promises. -/
theorem RunD.toRunV (hR : R.Exact) (hc : HostContract R force D) (hk : Keeps force)
    {p : Prog A B L} {dregs : List (MData B L)} {out' : Option (MData B L)} (h : RunD R p dregs out') :
    ∀ regs : List (RVal A L), regs.map (dataOf R D) = dregs →
      ∃ out, RunV R force p regs out ∧ out.map (dataOf R D) = out' := by
  induction h with
  | ret hi =>
    intro regs hregs
    subst hregs
    rw [List.getElem?_map] at hi
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hi
    exact ⟨_, .ret hv, rfl⟩
  | fail => intro regs _; exact ⟨_, .fail, rfl⟩
  | headAtom hi _ ih =>
    intro regs hregs
    subst hregs
    rw [List.getElem?_map] at hi
    obtain ⟨x, hx, hxd⟩ := Option.map_eq_some_iff.mp hi
    obtain ⟨y, hy⟩ := promised_exists hk x
    obtain ⟨a, rfl, ha⟩ := hy.eq_atom hc hxd
    obtain ⟨out, hrun, hout⟩ := ih regs rfl
    refine ⟨out, .headAtom hx hy ?_, hout⟩
    rw [ha]
    exact hrun
  | headNode hi _ ih =>
    intro regs hregs
    subst hregs
    rw [List.getElem?_map] at hi
    obtain ⟨x, hx, hxd⟩ := Option.map_eq_some_iff.mp hi
    obtain ⟨y, hy⟩ := promised_exists hk x
    obtain ⟨kids, rfl, _⟩ := hy.eq_node hc hxd
    obtain ⟨out, hrun, hout⟩ := ih regs rfl
    exact ⟨out, .headNode hx hy hrun, hout⟩
  | kid hi hj _ ih =>
    intro regs hregs
    subst hregs
    rw [List.getElem?_map] at hi
    obtain ⟨x, hx, hxd⟩ := Option.map_eq_some_iff.mp hi
    obtain ⟨y, hy⟩ := promised_exists hk x
    obtain ⟨kids, rfl, hks⟩ := hy.eq_node hc hxd
    rw [← hks, List.getElem?_map] at hj
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp hj
    obtain ⟨out, hrun, hout⟩ := ih (regs ++ [z]) (by simp)
    exact ⟨out, .kid hx hy hz hrun, hout⟩
  | eq hi hj hb _ ih =>
    intro regs hregs
    subst hregs
    rw [List.getElem?_map] at hi hj
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hi
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hj
    obtain ⟨b', hb'⟩ := termEqual_total hc hk x y
    have : b' = _ := Bool.eq_iff_iff.mpr ((TermEqual.sound hR hc hb').trans hb.symm)
    subst this
    obtain ⟨out, hrun, hout⟩ := ih regs rfl
    exact ⟨out, .eq hx hy hb' hrun, hout⟩
  | @mk c is k dregs ds out hg _ ih =>
    intro regs hregs
    subst hregs
    rw [getRegs_map] at hg
    obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.mp hg
    obtain ⟨out, hrun, hout⟩ := ih (regs ++ [.node c xs]) (by simp)
    exact ⟨out, .mk hxs hrun, hout⟩
  | @mkAtom x k dregs out _ ih =>
    intro regs hregs
    subst hregs
    obtain ⟨out', hrun, hout⟩ := ih (regs ++ [.atom x]) (by simp)
    exact ⟨out', .mkAtom hrun, hout⟩

/-- **Values with the same module data give the same results.**  A computation that reads values
only through views and compares them with `rc_term_equal` gives, as module data, the same result
on any two argument lists that stand for the same module data. -/
theorem runV_same (hR : R.Exact) (hc : HostContract R force D) {p : Prog A B L}
    {regs regs' : List (RVal A L)} (hd : regs.map (dataOf R D) = regs'.map (dataOf R D))
    {out out' : Option (RVal A L)} (h : RunV R force p regs out) (h' : RunV R force p regs' out') :
    out.map (dataOf R D) = out'.map (dataOf R D) := by
  have e := h.data hR hc
  rw [hd] at e
  exact RunD.functional e (h'.data hR hc)

/-- **A promise and the term it promises give the same result**: a computation that reads values
only through views gives, as module data, the same result on a promise as on any term the host
gives for it. -/
theorem runV_promise (hR : R.Exact) (hc : HostContract R force D) {p : Prog A B L} {q : Nat}
    {v : RVal A L} (hv : force q v) {out out' : Option (RVal A L)}
    (h : RunV R force p [.promise q] out) (h' : RunV R force p [v] out') :
    out.map (dataOf R D) = out'.map (dataOf R D) :=
  runV_same hR hc (by simp [hc.sameData _ _ hv]) h h'

end Promise

/-! ## The record table of the HOL Light module against the HOLR schema -/

/-- The opcodes of HOLR v1, by name (the enumeration of `hol_replay.h`). -/
inductive HolrOp
  | NAME | TYVAR | TYAPP | VAR | CONST | COMB | ABS
  | REFL | TRANS | MK_COMB | ABS_RULE | BETA | ASSUME | EQ_MP | DEDUCT | INST_TYPE | INST
  | NEW_TYPE | NEW_CONSTANT | NEW_AXIOM | NEW_DEFINITION | NEW_TYPEDEF | POLICY
  | EXPECT | LABEL | EMIT | EXPECT_REFUSED | EXPECT_AXIOMS | EXPECT_ALPHA
  | DROP_TYPE | DROP_TERM | DROP_THM
  | END
  deriving DecidableEq, Repr

/-- The number of each opcode (`HOLR_NAME = 0x01`, ...). -/
def HolrOp.code : HolrOp → Nat
  | .NAME => 0x01
  | .TYVAR => 0x02
  | .TYAPP => 0x03
  | .VAR => 0x04
  | .CONST => 0x05
  | .COMB => 0x06
  | .ABS => 0x07
  | .REFL => 0x10
  | .TRANS => 0x11
  | .MK_COMB => 0x12
  | .ABS_RULE => 0x13
  | .BETA => 0x14
  | .ASSUME => 0x15
  | .EQ_MP => 0x16
  | .DEDUCT => 0x17
  | .INST_TYPE => 0x18
  | .INST => 0x19
  | .NEW_TYPE => 0x20
  | .NEW_CONSTANT => 0x21
  | .NEW_AXIOM => 0x22
  | .NEW_DEFINITION => 0x23
  | .NEW_TYPEDEF => 0x24
  | .POLICY => 0x25
  | .EXPECT => 0x30
  | .LABEL => 0x31
  | .EMIT => 0x32
  | .EXPECT_REFUSED => 0x33
  | .EXPECT_AXIOMS => 0x34
  | .EXPECT_ALPHA => 0x35
  | .DROP_TYPE => 0x40
  | .DROP_TERM => 0x41
  | .DROP_THM => 0x42
  | .END => 0x7f

/-- The record constructors of the HOL Light module (sort `Record`: `"holr:NAME"`, ...). -/
inductive HolRecordCtor
  | NAME | TYVAR | TYAPP | VAR | CONST | COMB | ABS | REFL | TRANS | MK_COMB | ABS_RULE | BETA
  | ASSUME | EQ_MP | DEDUCT_ANTISYM_RULE | INST_TYPE | INST | NEW_TYPE | NEW_CONSTANT | NEW_AXIOM
  | NEW_DEFINITION | NEW_TYPEDEF | POLICY | EXPECT | EXPECT_ALPHA | EXPECT_AXIOMS | EXPECT_REFUSED
  | LABEL | EMIT | DROP_TYPE | DROP_TERM | DROP_THM
  deriving DecidableEq, Repr

/-- The sorts of the HOL Light module that the record constructors' children have, closed under
the children of their data constructors: `Nat`, `Str`, `Ids`, `IdPairs`, `Byte`, `Nib`. -/
inductive FeedSort
  /-- `Nat`, the numerals. -/
  | nat
  /-- `Str`, the names. -/
  | str
  /-- `Ids`, the id lists. -/
  | ids
  /-- `IdPairs`, the id-pair lists. -/
  | idPairs
  /-- `Byte`. -/
  | byte
  /-- `Nib`. -/
  | nib
  deriving DecidableEq, Repr

/-- The sorts of each record constructor's children, in order (the module's grammar:
`"holr:TYAPP". n:Nat, args:Ids |- ...`, ...). -/
def HolRecordCtor.childSorts : HolRecordCtor → List FeedSort
  | .NAME => [.str]
  | .TYVAR => [.nat]
  | .TYAPP => [.nat, .ids]
  | .VAR => [.nat, .nat]
  | .CONST => [.nat, .nat]
  | .COMB => [.nat, .nat]
  | .ABS => [.nat, .nat]
  | .REFL => [.nat]
  | .TRANS => [.nat, .nat]
  | .MK_COMB => [.nat, .nat]
  | .ABS_RULE => [.nat, .nat]
  | .BETA => [.nat]
  | .ASSUME => [.nat]
  | .EQ_MP => [.nat, .nat]
  | .DEDUCT_ANTISYM_RULE => [.nat, .nat]
  | .INST_TYPE => [.idPairs, .nat]
  | .INST => [.idPairs, .nat]
  | .NEW_TYPE => [.nat, .nat]
  | .NEW_CONSTANT => [.nat, .nat]
  | .NEW_AXIOM => [.nat]
  | .NEW_DEFINITION => [.nat]
  | .NEW_TYPEDEF => [.nat, .nat, .nat, .nat]
  | .POLICY => [.nat]
  | .EXPECT => [.nat, .ids, .nat]
  | .EXPECT_ALPHA => [.nat, .ids, .nat]
  | .EXPECT_AXIOMS => [.nat, .ids]
  | .EXPECT_REFUSED => []
  | .LABEL => [.nat, .nat]
  | .EMIT => [.nat]
  | .DROP_TYPE => [.nat]
  | .DROP_TERM => [.nat]
  | .DROP_THM => [.nat]

/-- The record table of the HOL Light feed (`hol_stream_records`): the module's constructor for the
reader's records of each opcode, in the order of the C table. -/
def holStreamRecords : List (HolrOp × HolRecordCtor) :=
  [(.NAME, .NAME), (.TYVAR, .TYVAR), (.TYAPP, .TYAPP), (.VAR, .VAR),
   (.CONST, .CONST), (.COMB, .COMB), (.ABS, .ABS),
   (.REFL, .REFL), (.TRANS, .TRANS), (.MK_COMB, .MK_COMB), (.ABS_RULE, .ABS_RULE),
   (.BETA, .BETA), (.ASSUME, .ASSUME), (.EQ_MP, .EQ_MP), (.DEDUCT, .DEDUCT_ANTISYM_RULE),
   (.INST_TYPE, .INST_TYPE), (.INST, .INST),
   (.NEW_TYPE, .NEW_TYPE), (.NEW_CONSTANT, .NEW_CONSTANT), (.NEW_AXIOM, .NEW_AXIOM),
   (.NEW_DEFINITION, .NEW_DEFINITION), (.NEW_TYPEDEF, .NEW_TYPEDEF), (.POLICY, .POLICY),
   (.EXPECT, .EXPECT), (.LABEL, .LABEL), (.EMIT, .EMIT), (.EXPECT_REFUSED, .EXPECT_REFUSED),
   (.EXPECT_AXIOMS, .EXPECT_AXIOMS), (.EXPECT_ALPHA, .EXPECT_ALPHA),
   (.DROP_TYPE, .DROP_TYPE), (.DROP_TERM, .DROP_TERM), (.DROP_THM, .DROP_THM)]

/-- The sort a field kind requires of the constructor's child (`rc_feed.h`): a word a numeral,
bytes a name, a list of words an id list, a list of pairs an id-pair list. -/
def fieldSort : FieldKind → FeedSort
  | .word => .nat
  | .bytes => .str
  | .words => .ids
  | .pairs => .idPairs

/-- The field kinds of a layout, in order. -/
def layoutKinds : FieldLayout → List FieldKind
  | .fieldsEnd => []
  | .fieldNext k rest => k :: layoutKinds rest

/-- The opcodes of a schema list, as numbers, in order. -/
def schemaOpcodes : Schemas → List Nat
  | .nil => []
  | .cons (.recordSchema tag _) rest => tag.val :: schemaOpcodes rest

/-- **The table names every opcode of the schema exactly once, and nothing else**: its opcodes and
the schema's are two lists without repetition with the same members.  (Its constructors are
distinct too.) -/
theorem holStreamRecords_opcodes :
    (holStreamRecords.map (·.1.code)).Nodup ∧ (schemaOpcodes holrSchema).Nodup ∧
      (∀ n ∈ holStreamRecords.map (·.1.code), n ∈ schemaOpcodes holrSchema) ∧
      (∀ n ∈ schemaOpcodes holrSchema, n ∈ holStreamRecords.map (·.1.code)) ∧
      (holStreamRecords.map (·.2)).Nodup := by
  decide

/-- Whether a row's constructor has, child by child, the sorts the schema's fields of its opcode
require (computed). -/
def rowFits (row : HolrOp × HolRecordCtor) : Bool :=
  match findLayout (Byte.ofWord row.1.code) holrSchema with
  | .foundLayout fields => decide ((layoutKinds fields).map fieldSort = row.2.childSorts)
  | .noLayout => false

theorem holStreamRecords_rowFits : ∀ row ∈ holStreamRecords, rowFits row = true := by
  decide

/-- **Each row's constructor has the schema's fields.**  For every row of the table, the reader's
`LookupSchema` finds the opcode's layout in the schema list, and the constructor's children are,
one for each field and in order, of the sort the field's kind requires (so the constructor's arity
is the number of fields). -/
theorem holStreamRecords_fields {op : HolrOp} {c : HolRecordCtor} (h : (op, c) ∈ holStreamRecords) :
    ∃ fields, LookupSchema (Byte.ofWord op.code) holrSchema (.foundLayout fields) ∧
      (layoutKinds fields).map fieldSort = c.childSorts := by
  have hfit := holStreamRecords_rowFits _ h
  unfold rowFits at hfit
  split at hfit
  · rename_i fields hl
    exact ⟨fields, lookupSchema_iff.mpr hl.symm, of_decide_eq_true hfit⟩
  · cases hfit

/-- The arity of each row's constructor is the number of the schema's fields. -/
theorem holStreamRecords_arity {op : HolrOp} {c : HolRecordCtor} (h : (op, c) ∈ holStreamRecords) :
    ∃ fields, LookupSchema (Byte.ofWord op.code) holrSchema (.foundLayout fields) ∧
      (layoutKinds fields).length = c.childSorts.length := by
  obtain ⟨fields, hl, hs⟩ := holStreamRecords_fields h
  exact ⟨fields, hl, by rw [← hs, List.length_map]⟩

/-! ### How the generic feed builds each child (`rf_child`, `rf_build`) -/

/-- The representations of `rulec`: the list `rc_rep.h` that the compiler, the generated table
`rc_sort_rep` and the hosts share by name. -/
inductive Rep
  | symbolic | records | nat | intern | bytes | table | unary | word | binary | slices | promise
  deriving DecidableEq, Repr

/-- A representation whose values are numbers (`rf_child`'s test: `nat`, `unary`, `word`,
`binary`). -/
def Rep.number : Rep → Bool
  | .nat | .unary | .word | .binary => true
  | _ => false

/-- How `rc_feed.c` builds a child from an operand (`rf_child`'s `how`). -/
inductive How
  /-- `RB_IMM`: an immediate natural. -/
  | imm
  /-- `RB_NUMBER`: a number of the sort's representation. -/
  | number
  /-- `RB_IBYTES`: an interned byte string. -/
  | ibytes
  /-- `RB_LIST1`: a list, one number per cell. -/
  | list1
  /-- `RB_LIST2`: a list, two numbers per cell. -/
  | list2
  deriving DecidableEq, Repr

/-- The operand kind each way of building takes (`rf_build`: a word for a number, bytes for a byte
string, a list of words for `RB_LIST1`, a list of pairs for `RB_LIST2`; any other operand is a
refinement violation). -/
def How.takes : How → FieldKind
  | .imm | .number => .word
  | .ibytes => .bytes
  | .list1 => .words
  | .list2 => .pairs

/-- A slot of `rf_child` (`nil[i]`, the list's end; `cons[i]`, its cell): none found yet (`-1`),
one found (by its number of children), or refused (`-2`). -/
inductive Slot
  /-- `-1`: none found yet. -/
  | none
  /-- One found, with its number of children. -/
  | found (arity : Nat)
  /-- `-2`: refused. -/
  | refused
  deriving DecidableEq, Repr

/-- A constructor for a slot: the first one found is kept; a second refuses the slot, and a refused
slot stays refused (`w->nil[i] == -1 ? c : -2`; `w->cons[i] != -1` refuses). -/
def Slot.take (slot : Slot) (arity : Nat) : Slot :=
  match slot with
  | .none => .found arity
  | _ => .refused

/-- Whether a constructor's children are one or two numbers and then the sort itself (`rf_child`'s
`numbers`). -/
def rfNumbers {S : Type} [DecidableEq S] (rep : S → Rep) (s : S) (args : List S) : Bool :=
  (args.length == 2 || args.length == 3) && decide (args.getLast? = some s) &&
    args.dropLast.all fun a => (rep a).number

/-- `rf_child`'s loop over the data constructors of the sort `s` (by their children's sorts), its
slots the list's end and the list's cell: a constructor without children is taken for the end; one
whose children are one or two numbers and then `s` is taken for the cell; any other constructor
refuses the cell.  Exactly one of each is accepted: a second refuses its slot, which stays
refused. -/
def rfScan {S : Type} [DecidableEq S] (rep : S → Rep) (s : S) :
    List (List S) → Slot × Slot → Slot × Slot
  | [], st => st
  | args :: rest, (nil, cons) =>
    if args.isEmpty then rfScan rep s rest (nil.take 0, cons)
    else if rfNumbers rep s args then rfScan rep s rest (nil, cons.take args.length)
    else rfScan rep s rest (nil, .refused)

/-- `rf_child`: how a child of sort `s` holds an operand, from the sort's representation, and for
the other representations from its data constructors (`none`: the feed refuses the table, unless
both slots hold one constructor each). -/
def rfChild {S : Type} [DecidableEq S] (rep : S → Rep) (ctors : S → List (List S)) (s : S) :
    Option How :=
  match rep s with
  | .nat | .unary => some .imm
  | .word | .binary => some .number
  | .bytes | .slices => some .ibytes
  | _ =>
    match rfScan rep s (ctors s) (.none, .none) with
    | (.found _, .found 2) => some .list1
    | (.found _, .found _) => some .list2
    | _ => none

/-- `rc_sort_rep` of the sorts (the module's bindings: `(rep "Nat" nat ...)`, `(rep "Str" bytes
...)`; the others have no `rep` line and are symbolic). -/
def FeedSort.rep : FeedSort → Rep
  | .nat => .nat
  | .str => .bytes
  | .ids => .symbolic
  | .idPairs => .symbolic
  | .byte => .symbolic
  | .nib => .symbolic

/-- The data constructors of each sort, by their children's sorts, in the module's order (its
grammar; constructors of these sorts that are judgments are not data): `"hl:nz"`, `"hl:nb0"`,
`"hl:nb1"`; `"hl:nnil"`, `"hl:ncons"`; `"hl:ids-nil"`, `"hl:ids-cons"`; `"hl:idp-nil"`,
`"hl:idp-cons"`; `"hl:byte"`; `"hl:x0"` ... `"hl:xf"`. -/
def FeedSort.dataCtors : FeedSort → List (List FeedSort)
  | .nat => [[], [.nat], [.nat]]
  | .str => [[], [.byte, .str]]
  | .ids => [[], [.nat, .ids]]
  | .idPairs => [[], [.nat, .nat, .idPairs]]
  | .byte => [[.nib, .nib]]
  | .nib => List.replicate 16 []

/-- `rf_child` on the HOL Light module's child sorts: numerals as immediates, names as interned
byte strings, id lists one number per cell, id-pair lists two per cell. -/
theorem rfChild_feedSorts :
    rfChild FeedSort.rep FeedSort.dataCtors .nat = some .imm ∧
      rfChild FeedSort.rep FeedSort.dataCtors .str = some .ibytes ∧
      rfChild FeedSort.rep FeedSort.dataCtors .ids = some .list1 ∧
      rfChild FeedSort.rep FeedSort.dataCtors .idPairs = some .list2 := by
  decide

/-- The child of the sort a field kind requires is built from exactly that kind of operand. -/
theorem rfChild_fieldSort (k : FieldKind) :
    (rfChild FeedSort.rep FeedSort.dataCtors (fieldSort k)).map How.takes = some k := by
  cases k <;> decide

/-- **The generic feed builds every record of the table**: for every row, the schema's fields of
its opcode, and the operand kinds the feed's way of building each child takes, agree one for one
(`rf_build`'s count check and each child's operand check pass). -/
theorem holStreamRecords_build {op : HolrOp} {c : HolRecordCtor} (h : (op, c) ∈ holStreamRecords) :
    ∃ fields, LookupSchema (Byte.ofWord op.code) holrSchema (.foundLayout fields) ∧
      c.childSorts.map (fun s => (rfChild FeedSort.rep FeedSort.dataCtors s).map How.takes) =
        (layoutKinds fields).map some := by
  obtain ⟨fields, hl, hs⟩ := holStreamRecords_fields h
  refine ⟨fields, hl, ?_⟩
  rw [← hs, List.map_map]
  congr 1
  funext k
  exact rfChild_fieldSort k

/-! ## Examples -/

section Examples

/-! ### Pending wrappers -/

/-- The frames are applied the newest first (`10 * 0 + 1`, then `10 * 1 + 2`). -/
example : applyFrames (fun (f v : Nat) => some (10 * v + f)) [1, 2] (some 0) = some 12 := rfl

/-- A failure drops the frames after it. -/
example :
    applyFrames (fun (f v : Nat) => if f = 2 then none else some (f + v)) [1, 2, 3] (some 0) = none :=
  rfl

/-- `sum n = n + sum (n - 1)`, its `+ n` a pending wrapper: one judgment, the frames numbers. -/
def sumProg : Unit → List Nat → TailStep Unit Nat Nat
  | (), [n] => if n = 0 then .ret (some 0) else .pend n () [n - 1]
  | (), _ => .ret none

/-- The compiled run of `sum 3` pushes `3`, `2`, `1` and ends with `0`. -/
theorem sumRun : Run sumProg () [3] [] (some 0) [1, 2, 3] :=
  .pend rfl (.pend rfl (.pend rfl (.ret rfl)))

/-- The caller applies the frames: `6`, the rules' value. -/
example : Eval sumProg (fun f v => some (f + v)) () [3] (some 6) :=
  closed_iff_eval.mp ⟨some 0, [1, 2, 3], sumRun, rfl⟩

/-- The run stops on entering the safepoint a second time and is resumed from `[2]`, its frame `3`
kept; it ends as the run without the stop. -/
example : Session sumProg () () [3] [] (some 0) [1, 2, 3] :=
  .resumed (.pend rfl .stop) (.ended (.pend rfl (.pend rfl (.ret rfl))))

/-- A host that takes the frames out at that stop (`3`), then at the end (`2`, `1`). -/
example : FeedSession sumProg () [] () [3] (some 0) [1, 2, 3] := by
  have h₁ : RunS sumProg () () [3] [] (.stopped [2] ([3] ++ [])) := .pend rfl .stop
  have h₂ : RunS sumProg () () [2] [] (.ended (some 0) ([1, 2] ++ [])) :=
    .pend rfl (.pend rfl (.ret rfl))
  exact .resumed h₁ (.ended h₂)

/-! ### The loop -/

/-- The loop on an empty input: `MissingEnd`, no records. -/
example (RR : BinNat → Schemas → Bytes → State → Prop) (full : Bytes) (header : Header) :
    HOLRLoop RR full header .zero .nil (.holrDecoded header .nil (.prefixError .missingEnd)) :=
  .loopEmpty

/-- One record of opcode `NAME` (`0x01`), then the end of the input: `StreamPush` conses the record
onto the loop's own value. -/
theorem loop_one_record (full : Bytes) (header : Header) (record : Record) :
    HOLRLoop (fun _ _ xs s => xs = .cons (Byte.ofWord 1) .nil ∧ s = .recordDecoded record .nil)
      full header .zero (.cons (Byte.ofWord 1) .nil)
      (.holrDecoded header (.cons record .nil) (.prefixError .missingEnd)) :=
  .loopSelect (packByte_iff_fn.mpr rfl) (natCompare_iff_fn.mpr (by decide))
    (.loopLess (holrSchema_iff.mpr rfl) ⟨rfl, rfl⟩
      (.recordNext (natInc_iff_fn.mpr rfl) .loopEmpty .streamCons))

/-- The same loop as its compiled code runs it: the frame of the record, and `HOLRDecoded header
RecordsNil (MissingEnd)`. -/
example (full : Bytes) (header : Header) (record : Record) :
    RawLoop (fun _ _ xs s => xs = .cons (Byte.ofWord 1) .nil ∧ s = .recordDecoded record .nil)
      full header .zero (.cons (Byte.ofWord 1) .nil) [record]
      (.holrDecoded header .nil (.prefixError .missingEnd)) :=
  .loopSelect (packByte_iff_fn.mpr rfl) (natCompare_iff_fn.mpr (by decide))
    (.loopLess (holrSchema_iff.mpr rfl) ⟨rfl, rfl⟩ (.recordNext (natInc_iff_fn.mpr rfl) .loopEmpty))

/-- `StreamPush` has no rule on a state the loop never gives it. -/
example (record : Record) (pre rest : Bytes) (r : State) : ¬ StreamPush record (.taken pre rest) r :=
  nofun

/-- No rule of `HOLRControl` takes `Equal` with an empty input (`LoopSelect` never gives it one). -/
example (RR : BinNat → Schemas → Bytes → State → Prop) (full : Bytes) (header : Header)
    (count : BinNat) (r : State) : ¬ HOLRControl RR .equal full header count .nil r :=
  nofun

/-- With a `ReadRecord` that gives no result, the loop has no value on a record's opcode: the
loop's value needs `ReadRecord`'s. -/
example (full : Bytes) (header : Header) (v : State) :
    ¬ HOLRLoop (fun _ _ _ _ => False) full header .zero (.cons (Byte.ofWord 1) .nil) v := by
  intro h
  cases h with
  | loopSelect h1 h2 h3 =>
    cases h3 with
    | loopLess _ h _ => exact h
    | loopGreater _ h _ => exact h
    | loopEnd _ _ =>
      have e := natCompare_iff_fn.mp h2
      rw [packByte_iff_fn.mp h1] at e
      exact absurd e (by decide)

/-! ### `ReadRecord` -/

/-- `TYVAR 5` (bytes `0x02 0x05`): the record of opcode `2` with the word `5`, nothing left. -/
example : ReadRecord recordLimit holrSchema (.cons (Byte.ofWord 2) (.cons (Byte.ofWord 5) .nil))
    (.recordDecoded (.bRecord (Byte.ofWord 2) (.cons (.word (BinNat.ofNat 5)) .nil)) .nil) := by
  have hl : LookupSchema (Byte.ofWord 2) holrSchema (.foundLayout (.fieldNext .word .fieldsEnd)) :=
    lookupSchema_iff.mpr (by decide)
  have hu : ReadULEB62 (.cons (Byte.ofWord 5) .nil) (.decodedWord (BinNat.ofNat 5) .nil) :=
    readULEB62_iff.mpr (by decide)
  exact .recordStart hl
    (.recordKnown (.fieldsMore (.readOne hu .wordValue) (.fieldsNext .fieldsEmpty .fieldsCons))
      .recordMake)

/-- `TYVAR` without its word: `NeedInput`. -/
example : ReadRecord recordLimit holrSchema (.cons (Byte.ofWord 2) .nil) .needInput := by
  have hl : LookupSchema (Byte.ofWord 2) holrSchema (.foundLayout (.fieldNext .word .fieldsEnd)) :=
    lookupSchema_iff.mpr (by decide)
  have hu : ReadULEB62 .nil .needInput := readULEB62_iff.mpr (by decide)
  exact .recordStart hl
    (.recordKnown (.fieldsMore (.readOne hu .operandWordNeedInput) .fieldCarryNeedInput)
      .recordFieldsNeedInput)

/-- `NAME` whose count is `2^20 + 1` (bytes `0x81 0x80 0x40`): `LimitExceeded`. -/
example : ReadRecord recordLimit holrSchema
    (.cons (Byte.ofWord 1) (.cons (Byte.ofWord 0x81) (.cons (Byte.ofWord 0x80)
      (.cons (Byte.ofWord 0x40) .nil)))) .limitExceeded := by
  have hl : LookupSchema (Byte.ofWord 1) holrSchema (.foundLayout (.fieldNext .bytes .fieldsEnd)) :=
    lookupSchema_iff.mpr (by decide)
  have hu : ReadULEB62 (.cons (Byte.ofWord 0x81) (.cons (Byte.ofWord 0x80)
      (.cons (Byte.ofWord 0x40) .nil))) (.decodedWord (BinNat.ofNat 1048577) .nil) :=
    readULEB62_iff.mpr (by decide)
  have ho : NatCompare (BinNat.ofNat 1048577) recordLimit .greater :=
    natCompare_iff_fn.mpr (by decide)
  exact .recordStart hl
    (.recordKnown (.fieldsMore (.readBytes hu (.countValue ho .countLarge)) .fieldCarryLimitExceeded)
      .recordFieldsLimitExceeded)

/-- An opcode outside the schema (`0x08`): `UnknownOpcode`. -/
example : ReadRecord recordLimit holrSchema (.cons (Byte.ofWord 8) .nil)
    (.unknownOpcode (Byte.ofWord 8)) :=
  .recordStart (lookupSchema_iff.mpr (by decide)) .recordUnknown

/-- `ReadValues` has no rule for `WordField`. -/
example (n : BinNat) (xs : Bytes) (r : State) : ¬ ReadValues .word n xs r := nofun

/-! ### Promises -/

/-- Atoms that are numbers, compared by value. -/
def exAtoms : Atoms Nat Nat := ⟨id, fun x y => x == y⟩

theorem exAtoms_exact : exAtoms.Exact := fun x y => by simp [exAtoms]

/-- A host that builds the term of promise `0` anew, either fully or with a promise (`1`) inside. -/
def exForce : Nat → RVal Nat Bool → Prop
  | 0, v => v = .node true [.atom 5] ∨ v = .node true [.promise 1]
  | 1, v => v = .atom 5
  | _, _ => False

/-- The data it promises. -/
def exData : Nat → MData Nat Bool
  | 0 => .node true [.atom 5]
  | 1 => .atom 5
  | _ => .atom 0

theorem exHost : HostContract exAtoms exForce exData where
  notPromise p v h := by
    rcases p with _ | _ | p
    · rcases (h : v = .node true [.atom 5] ∨ v = .node true [.promise 1]) with rfl | rfl <;> rfl
    · obtain rfl : v = .atom 5 := h
      rfl
    · exact (h : False).elim
  sameData p v h := by
    rcases p with _ | _ | p
    · rcases (h : v = .node true [.atom 5] ∨ v = .node true [.promise 1]) with rfl | rfl <;>
        simp [exData, exAtoms]
    · obtain rfl : v = .atom 5 := h
      simp [exData, exAtoms]
    · exact (h : False).elim

/-- Comparing the promise with its term, through the representation with the inner promise: `true`,
as its module data says. -/
example : TermEqual exAtoms exForce (.promise 0) (.node true [.atom 5]) true :=
  .forced (.inl rfl) (.promise (.inr rfl)) .node
    (.nodes rfl (.agree (.forced (.inl rfl) (.promise rfl) .atom .same) .nil))

/-- A host that gives two different data for one promise breaks its contract, and `rc_term_equal`
then answers both ways. -/
def badForce : Nat → RVal Nat Bool → Prop
  | 0, v => v = .atom 1 ∨ v = .atom 2
  | _, _ => False

example : TermEqual exAtoms badForce (.promise 0) (.atom 1) true :=
  .forced (.inl rfl) (.promise (.inl rfl)) .atom .same

example : TermEqual exAtoms badForce (.promise 0) (.atom 1) false :=
  .forced (.inl rfl) (.promise (.inr rfl)) .atom .atoms

example : ¬ ∃ D, HostContract exAtoms badForce D := by
  rintro ⟨D, hc⟩
  have h1 := hc.sameData 0 (.atom 1) (.inl rfl)
  have h2 := hc.sameData 0 (.atom 2) (.inr rfl)
  rw [← h2] at h1
  simp [exAtoms] at h1

/-! ### The record table -/

/-- `INST_TYPE` (`0x18`): a list of pairs and a word; its constructor's children an id-pair list
and a numeral. -/
example : findLayout (Byte.ofWord HolrOp.INST_TYPE.code) holrSchema =
    .foundLayout (.fieldNext .pairs (.fieldNext .word .fieldsEnd)) := by decide
example : HolRecordCtor.INST_TYPE.childSorts = [.idPairs, .nat] := rfl

/-- `DEDUCT` (`0x17`) is the module's `DEDUCT_ANTISYM_RULE`, two words. -/
example : (HolrOp.DEDUCT, HolRecordCtor.DEDUCT_ANTISYM_RULE) ∈ holStreamRecords := by decide
example : findLayout (Byte.ofWord HolrOp.DEDUCT.code) holrSchema =
    .foundLayout (.fieldNext .word (.fieldNext .word .fieldsEnd)) := by decide

/-- `END` (`0x7f`) has no schema and no row: `LoopSelect` sends it to the trailer. -/
example : findLayout (Byte.ofWord HolrOp.END.code) holrSchema = .noLayout := by decide
example : HolrOp.END ∉ holStreamRecords.map (·.1) := by decide

/-- An opcode outside HOLR v1 (`0x08`) has no schema: `ReadRecord` gives `UnknownOpcode`. -/
example : findLayout (Byte.ofWord 0x08) holrSchema = .noLayout := by decide

/-- `rf_child` takes a list sort with one end and one cell, in either order. -/
example : rfChild FeedSort.rep
    (fun s => if s = .ids then [[.nat, .ids], []] else FeedSort.dataCtors s) .ids =
      some .list1 := by decide

/-- It refuses a list sort with two cells. -/
example : rfChild FeedSort.rep
    (fun s => if s = .ids then [[], [.nat, .ids], [.nat, .ids]] else FeedSort.dataCtors s) .ids =
      none := by decide

/-- A refused cell stays refused: a constructor that is not a cell, then a cell. -/
example : rfChild FeedSort.rep
    (fun s => if s = .ids then [[], [.str, .ids], [.nat, .ids]] else FeedSort.dataCtors s) .ids =
      none := by decide

/-- A second constructor without children refuses. -/
example : rfChild FeedSort.rep
    (fun s => if s = .ids then [[], [], [.nat, .ids]] else FeedSort.dataCtors s) .ids =
      none := by decide

/-- A sort without a cell, or without an end, is refused. -/
example : rfChild FeedSort.rep
    (fun s => if s = .ids then [[]] else FeedSort.dataCtors s) .ids = none := by decide
example : rfChild FeedSort.rep
    (fun s => if s = .ids then [[.nat, .ids]] else FeedSort.dataCtors s) .ids = none := by decide

end Examples

end Mettapedia.Languages.HOLLight.RuleModuleFeed

/-! ## Axioms -/

#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.run_eval
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.eval_run
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.closed_iff_eval
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.Run.functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.Eval.functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.session_iff_run
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.resume_same
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.feedSession_run
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.feed_eval
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.applyFrames_consLaw
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.rcPend_takeOut
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.feed_eval_consLaw
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.holrSchema_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.readWordLE64_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.readULEB62_shape
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.EndCount.decoded
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.endCount_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.streamPush_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.RawLoop.decoded
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.holrLoop_iff_raw
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.holrLoop_value
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.recordNext_streamCons
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.holrLoop_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.readULEB62_rest
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.takeBytes_rest
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.readWords_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.readPairs_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.readValues_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.readOperand_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.decodeFields_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.selectRecord_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.readRecordGives
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.holrLoop_total_readRecord
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.lit127_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.recordLimit_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.tagIs_promise_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.kidIs_promise_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.TagIs.data
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.KidIs.data
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.kidIs_of_data
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.TermEqual.sound
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.termEqual_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.RunD.functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.RunV.data
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.RunD.toRunV
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.runV_same
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.runV_promise
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.holStreamRecords_opcodes
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.holStreamRecords_rowFits
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.holStreamRecords_fields
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.holStreamRecords_arity
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.rfChild_feedSorts
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.rfChild_fieldSort
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.holStreamRecords_build
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.sumRun
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.loop_one_record
#print axioms Mettapedia.Languages.HOLLight.RuleModuleFeed.exHost
