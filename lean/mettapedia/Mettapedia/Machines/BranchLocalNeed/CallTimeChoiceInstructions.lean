import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSpec
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSource
import Mathlib.Logic.Relation

/-!
# Explicit instruction rules for the existing call-time-choice source

The source judgments are the independent `CallTimeChoice.Derives` rules.
This continuation representation exposes their recursive calls as separate
work items. No instruction invokes the source interpreter or assumes a
completed source evaluation. Alternatives keep their original input store,
and joins concatenate ordered result occurrences without deduplication.

The finite instruction families use the source's structural data operations:
value/environment lookup, finite rule selection, cell lookup/cache update and
list construction. These operations do not execute a computation. The
comparison concerns complete ordered answers and retained unfinished work;
it does not choose a concurrent scheduling or external-publication policy.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions

open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

inductive Frame where
  | sequence (rest : Comp) (environment : List (Val Nat))
  | commit (cell : Nat)
  | follow
  | later (goal : Goal)
  | append (earlier : List Result)
  | cons (earlier : Result)

inductive Control where
  | task (goal : Goal) (stack : List Frame)
  | returned (results : List Result) (stack : List Frame)

/-- Each constructor is a root instruction schema. Its side conditions
inspect finite data, never the result of a recursive computation. -/
inductive Instruction (P : Program) : Control → Control → Prop where
  | ret (σ : Store) (ρ : List (Val Nat)) (v : VExp) (k : List Frame) :
      Instruction P (.task (.eval σ ρ (.ret v)) k) (.returned [(.ok (v.eval ρ), σ)] k)
  | seq (σ : Store) (ρ : List (Val Nat)) (m n : Comp) (k : List Frame) :
      Instruction P (.task (.eval σ ρ (.seq m n)) k) (.task (.eval σ ρ m) (.sequence n ρ :: k))
  | need (σ : Store) (ρ : List (Val Nat)) (m n : Comp) (k : List Frame) :
      Instruction P (.task (.eval σ ρ (.need m n)) k)
        (.task (.eval (σ.alloc m ρ) (.need σ.cells.length :: ρ) n) k)
  | delay (σ : Store) (ρ : List (Val Nat)) (m n : Comp) (k : List Frame) :
      Instruction P (.task (.eval σ ρ (.delay m n)) k)
        (.task (.eval (σ.alloc m ρ) (.thunk σ.cells.length :: ρ) n) k)
  | force (σ : Store) (ρ : List (Val Nat)) (v : VExp) (k : List Frame) :
      Instruction P (.task (.eval σ ρ (.force v)) k) (.task (.forceVal σ (v.eval ρ)) k)
  | caseConHit (σ : Store) (ρ : List (Val Nat)) (v : VExp) (c n : Nat) (hit miss : Comp)
      (fields : List (Val Nat)) (matched : (v.eval ρ).matchCon c n = some fields) (k : List Frame) :
      Instruction P (.task (.eval σ ρ (.caseCon v c n hit miss)) k) (.task (.eval σ (fields ++ ρ) hit) k)
  | caseConMiss (σ : Store) (ρ : List (Val Nat)) (v : VExp) (c n : Nat) (hit miss : Comp)
      (unmatched : (v.eval ρ).matchCon c n = none) (k : List Frame) :
      Instruction P (.task (.eval σ ρ (.caseCon v c n hit miss)) k) (.task (.eval σ ρ miss) k)
  | caseAppHit (σ : Store) (ρ : List (Val Nat)) (v : VExp) (hit miss : Comp)
      (f x : Val Nat) (matched : (v.eval ρ).matchApp = some (f,x)) (k : List Frame) :
      Instruction P (.task (.eval σ ρ (.caseApp v hit miss)) k) (.task (.eval σ (f :: x :: ρ) hit) k)
  | caseAppMiss (σ : Store) (ρ : List (Val Nat)) (v : VExp) (hit miss : Comp)
      (unmatched : (v.eval ρ).matchApp = none) (k : List Frame) :
      Instruction P (.task (.eval σ ρ (.caseApp v hit miss)) k) (.task (.eval σ ρ miss) k)
  | call (σ : Store) (ρ : List (Val Nat)) (f : Nat) (arguments : List VExp)
      (available : candidates P f arguments.length ≠ []) (k : List Frame) :
      Instruction P (.task (.eval σ ρ (.call f arguments)) k)
        (.task (.alts σ ((candidates P f arguments.length).map fun rule =>
          (rule.body, arguments.map (·.eval ρ)))) k)
  | callNone (σ : Store) (ρ : List (Val Nat)) (f : Nat) (arguments : List VExp)
      (empty : candidates P f arguments.length = []) (k : List Frame) :
      Instruction P (.task (.eval σ ρ (.call f arguments)) k) (.returned [(.fail, σ)] k)
  | callRule (σ : Store) (ρ : List (Val Nat)) (i : Nat) (arguments : List VExp) (rule : Rule)
      (selected : P[i]? = some rule) (arity : rule.arity = arguments.length) (k : List Frame) :
      Instruction P (.task (.eval σ ρ (.callRule i arguments)) k)
        (.task (.eval σ (arguments.map (·.eval ρ)) rule.body) k)
  | callRuleNone (σ : Store) (ρ : List (Val Nat)) (i : Nat) (arguments : List VExp)
      (missing : ∀ rule, P[i]? = some rule → rule.arity ≠ arguments.length) (k : List Frame) :
      Instruction P (.task (.eval σ ρ (.callRule i arguments)) k) (.returned [(.fail, σ)] k)
  | choose (σ : Store) (ρ : List (Val Nat)) (m n : Comp) (k : List Frame) :
      Instruction P (.task (.eval σ ρ (.choose m n)) k)
        (.task (.eval σ ρ m) (.later (.eval σ ρ n) :: k))
  | fail (σ : Store) (ρ : List (Val Nat)) (k : List Frame) :
      Instruction P (.task (.eval σ ρ .fail) k) (.returned [(.fail, σ)] k)
  | emit (σ : Store) (ρ : List (Val Nat)) (event : Nat) (next : Comp) (k : List Frame) :
      Instruction P (.task (.eval σ ρ (.emit event next)) k) (.task (.eval (σ.emit event) ρ next) k)
  | quote (σ : Store) (ρ : List (Val Nat)) (code : Comp) (k : List Frame) :
      Instruction P (.task (.eval σ ρ (.quote code)) k)
        (.returned [(.ok (.code σ.cells.length), σ.alloc code ρ)] k)
  | runCode (σ : Store) (ρ : List (Val Nat)) (v : VExp) (cell : Nat) (record : Suspension)
      (code : v.eval ρ = .code cell) (found : σ.cells[cell]? = some record) (k : List Frame) :
      Instruction P (.task (.eval σ ρ (.run v)) k) (.task (.eval σ record.env record.code) (.follow :: k))
  | runOther (σ : Store) (ρ : List (Val Nat)) (v : VExp)
      (notCode : ∀ cell, v.eval ρ ≠ .code cell) (k : List Frame) :
      Instruction P (.task (.eval σ ρ (.run v)) k)
        (.returned [(.ok (.app (.sym unquoteHead) (v.eval ρ)), σ)] k)
  | prim (σ : Store) (ρ : List (Val Nat)) (operation : Prim) (arguments : List VExp) (k : List Frame) :
      Instruction P (.task (.eval σ ρ (.prim operation arguments)) k)
        (.returned [(primOutcome operation (arguments.map (·.eval ρ)), σ)] k)
  | altsNil (σ : Store) (k : List Frame) :
      Instruction P (.task (.alts σ []) k) (.returned [] k)
  | altsCons (σ : Store) (code : Comp) (env : List (Val Nat))
      (remaining : List (Comp × List (Val Nat))) (k : List Frame) :
      Instruction P (.task (.alts σ ((code,env) :: remaining)) k)
        (.task (.eval σ env code) (.later (.alts σ remaining) :: k))
  | seqKNil (code : Comp) (env : List (Val Nat)) (k : List Frame) :
      Instruction P (.task (.seqK code env []) k) (.returned [] k)
  | seqKOk (code : Comp) (env : List (Val Nat)) (value : Val Nat) (σ : Store)
      (remaining : List Result) (k : List Frame) :
      Instruction P (.task (.seqK code env ((.ok value,σ) :: remaining)) k)
        (.task (.eval σ (value :: env) code) (.later (.seqK code env remaining) :: k))
  | seqKStop (code : Comp) (env : List (Val Nat)) (outcome : Outcome) (σ : Store)
      (remaining : List Result) (stopped : outcome.isOk = false) (k : List Frame) :
      Instruction P (.task (.seqK code env ((outcome,σ) :: remaining)) k)
        (.task (.seqK code env remaining) (.cons (outcome,σ) :: k))
  | forceWhnf (σ : Store) (value : Val Nat) (ready : value.isCell = false) (k : List Frame) :
      Instruction P (.task (.forceVal σ value) k) (.returned [(.ok value,σ)] k)
  | forceDone (σ : Store) (cell : Nat) (record : Suspension) (value : Val Nat)
      (found : σ.cells[cell]? = some record) (done : record.memo = .done value) (k : List Frame) :
      Instruction P (.task (.forceVal σ (.need cell)) k) (.task (.forceVal σ value) k)
  | forceBlackhole (σ : Store) (cell : Nat) (record : Suspension)
      (found : σ.cells[cell]? = some record) (busy : record.memo = .evaluating) (k : List Frame) :
      Instruction P (.task (.forceVal σ (.need cell)) k) (.returned [(.blackhole,σ)] k)
  | forcePending (σ : Store) (cell : Nat) (record : Suspension)
      (found : σ.cells[cell]? = some record) (pending : record.memo = .pending) (k : List Frame) :
      Instruction P (.task (.forceVal σ (.need cell)) k)
        (.task (.eval (σ.setMemo cell .evaluating) record.env record.code) (.commit cell :: k))
  | forceThunk (σ : Store) (cell : Nat) (record : Suspension)
      (found : σ.cells[cell]? = some record) (k : List Frame) :
      Instruction P (.task (.forceVal σ (.thunk cell)) k) (.task (.eval σ record.env record.code) (.follow :: k))
  | commitNil (cell : Nat) (k : List Frame) :
      Instruction P (.task (.commitK cell []) k) (.returned [] k)
  | commitOk (cell : Nat) (value : Val Nat) (σ : Store) (remaining : List Result) (k : List Frame) :
      Instruction P (.task (.commitK cell ((.ok value,σ) :: remaining)) k)
        (.task (.forceVal (σ.setMemo cell (.done value)) value) (.later (.commitK cell remaining) :: k))
  | commitStop (cell : Nat) (outcome : Outcome) (σ : Store) (remaining : List Result)
      (stopped : outcome.isOk = false) (k : List Frame) :
      Instruction P (.task (.commitK cell ((outcome,σ) :: remaining)) k)
        (.task (.commitK cell remaining) (.cons (outcome,σ.setMemo cell .pending) :: k))
  | followNil (k : List Frame) : Instruction P (.task (.followK []) k) (.returned [] k)
  | followOk (value : Val Nat) (σ : Store) (remaining : List Result) (k : List Frame) :
      Instruction P (.task (.followK ((.ok value,σ) :: remaining)) k)
        (.task (.forceVal σ value) (.later (.followK remaining) :: k))
  | followStop (outcome : Outcome) (σ : Store) (remaining : List Result)
      (stopped : outcome.isOk = false) (k : List Frame) :
      Instruction P (.task (.followK ((outcome,σ) :: remaining)) k)
        (.task (.followK remaining) (.cons (outcome,σ) :: k))
  | sequenceReturn (results : List Result) (code : Comp) (env : List (Val Nat)) (k : List Frame) :
      Instruction P (.returned results (.sequence code env :: k)) (.task (.seqK code env results) k)
  | commitReturn (results : List Result) (cell : Nat) (k : List Frame) :
      Instruction P (.returned results (.commit cell :: k)) (.task (.commitK cell results) k)
  | followReturn (results : List Result) (k : List Frame) :
      Instruction P (.returned results (.follow :: k)) (.task (.followK results) k)
  | laterReturn (results : List Result) (goal : Goal) (k : List Frame) :
      Instruction P (.returned results (.later goal :: k)) (.task goal (.append results :: k))
  | appendReturn (first second : List Result) (k : List Frame) :
      Instruction P (.returned second (.append first :: k)) (.returned (first ++ second) k)
  | consReturn (first : Result) (remaining : List Result) (k : List Frame) :
      Instruction P (.returned remaining (.cons first :: k)) (.returned (first :: remaining) k)

abbrev Path (program : Program) := Relation.ReflTransGen (Instruction program)

/-- Every independently derived result list is produced by the explicit
instructions under any already retained return stack. -/
theorem source_realized {P : Program} {goal : Goal} {results : List Result}
    (derived : Derives P goal results) :
    ∀ stack, Path P (.task goal stack) (.returned results stack) := by
  induction derived with
  | ret => intro k; exact .single (.ret _ _ _ _)
  | seq first second firstIH secondIH =>
      intro k
      exact (Relation.ReflTransGen.single (.seq _ _ _ _ _)).trans
        ((firstIH _).trans ((Relation.ReflTransGen.single (.sequenceReturn _ _ _ _)).trans (secondIH k)))
  | need body ih => intro k; exact (Relation.ReflTransGen.single (.need _ _ _ _ _)).trans (ih k)
  | delay body ih => intro k; exact (Relation.ReflTransGen.single (.delay _ _ _ _ _)).trans (ih k)
  | force body ih => intro k; exact (Relation.ReflTransGen.single (.force _ _ _ _)).trans (ih k)
  | caseConHit matched body ih => intro k; exact (Relation.ReflTransGen.single (.caseConHit _ _ _ _ _ _ _ _ matched _)).trans (ih k)
  | caseConMiss unmatched body ih => intro k; exact (Relation.ReflTransGen.single (.caseConMiss _ _ _ _ _ _ _ unmatched _)).trans (ih k)
  | caseAppHit matched body ih => intro k; exact (Relation.ReflTransGen.single (.caseAppHit _ _ _ _ _ _ _ matched _)).trans (ih k)
  | caseAppMiss unmatched body ih => intro k; exact (Relation.ReflTransGen.single (.caseAppMiss _ _ _ _ _ unmatched _)).trans (ih k)
  | call available body ih => intro k; exact (Relation.ReflTransGen.single (.call _ _ _ _ available _)).trans (ih k)
  | callNone empty => intro k; exact .single (.callNone _ _ _ _ empty _)
  | callRule selected arity body ih => intro k; exact (Relation.ReflTransGen.single (.callRule _ _ _ _ _ selected arity _)).trans (ih k)
  | callRuleNone missing => intro k; exact .single (.callRuleNone _ _ _ _ missing _)
  | choose first second firstIH secondIH =>
      intro k
      exact (Relation.ReflTransGen.single (.choose _ _ _ _ _)).trans
        ((firstIH _).trans ((Relation.ReflTransGen.single (.laterReturn _ _ _)).trans
          ((secondIH _).trans (.single (.appendReturn _ _ _)))))
  | fail => intro k; exact .single (.fail _ _ _)
  | emit body ih => intro k; exact (Relation.ReflTransGen.single (.emit _ _ _ _ _)).trans (ih k)
  | quote => intro k; exact .single (.quote _ _ _ _)
  | runCode code found first second firstIH secondIH =>
      intro k
      exact (Relation.ReflTransGen.single (.runCode _ _ _ _ _ code found _)).trans
        ((firstIH _).trans ((Relation.ReflTransGen.single (.followReturn _ _)).trans (secondIH k)))
  | runOther notCode => intro k; exact .single (.runOther _ _ _ notCode _)
  | prim => intro k; exact .single (.prim _ _ _ _ _)
  | altsNil => intro k; exact .single (.altsNil _ _)
  | altsCons first second firstIH secondIH =>
      intro k
      exact (Relation.ReflTransGen.single (.altsCons _ _ _ _ _)).trans
        ((firstIH _).trans ((Relation.ReflTransGen.single (.laterReturn _ _ _)).trans
          ((secondIH _).trans (.single (.appendReturn _ _ _)))))
  | seqKNil => intro k; exact .single (.seqKNil _ _ _)
  | seqKOk first second firstIH secondIH =>
      intro k
      exact (Relation.ReflTransGen.single (.seqKOk _ _ _ _ _ _)).trans
        ((firstIH _).trans ((Relation.ReflTransGen.single (.laterReturn _ _ _)).trans
          ((secondIH _).trans (.single (.appendReturn _ _ _)))))
  | seqKStop stopped body ih =>
      intro k
      exact (Relation.ReflTransGen.single (.seqKStop _ _ _ _ _ stopped _)).trans
        ((ih _).trans (.single (.consReturn _ _ _)))
  | forceWhnf ready => intro k; exact .single (.forceWhnf _ _ ready _)
  | forceDone found done body ih => intro k; exact (Relation.ReflTransGen.single (.forceDone _ _ _ _ found done _)).trans (ih k)
  | forceBlackhole found busy => intro k; exact .single (.forceBlackhole _ _ _ found busy _)
  | forcePending found pending first second firstIH secondIH =>
      intro k
      exact (Relation.ReflTransGen.single (.forcePending _ _ _ found pending _)).trans
        ((firstIH _).trans ((Relation.ReflTransGen.single (.commitReturn _ _ _)).trans (secondIH k)))
  | forceThunk found first second firstIH secondIH =>
      intro k
      exact (Relation.ReflTransGen.single (.forceThunk _ _ _ found _)).trans
        ((firstIH _).trans ((Relation.ReflTransGen.single (.followReturn _ _)).trans (secondIH k)))
  | commitNil => intro k; exact .single (.commitNil _ _)
  | commitOk first second firstIH secondIH =>
      intro k
      exact (Relation.ReflTransGen.single (.commitOk _ _ _ _ _)).trans
        ((firstIH _).trans ((Relation.ReflTransGen.single (.laterReturn _ _ _)).trans
          ((secondIH _).trans (.single (.appendReturn _ _ _)))))
  | commitStop stopped body ih =>
      intro k
      exact (Relation.ReflTransGen.single (.commitStop _ _ _ _ stopped _)).trans
        ((ih _).trans (.single (.consReturn _ _ _)))
  | followNil => intro k; exact .single (.followNil _)
  | followOk first second firstIH secondIH =>
      intro k
      exact (Relation.ReflTransGen.single (.followOk _ _ _ _)).trans
        ((firstIH _).trans ((Relation.ReflTransGen.single (.laterReturn _ _ _)).trans
          ((secondIH _).trans (.single (.appendReturn _ _ _)))))
  | followStop stopped body ih =>
      intro k
      exact (Relation.ReflTransGen.single (.followStop _ _ _ stopped _)).trans
        ((ih _).trans (.single (.consReturn _ _ _)))

/-- The retained continuation is interpreted using independent source
judgments. This invariant is not used to admit an instruction. -/
inductive Continues (P : Program) : List Frame → List Result → List Result → Prop where
  | nil (results : List Result) : Continues P [] results results
  | sequence {rest : Comp} {env : List (Val Nat)} {k : List Frame} {input middle result : List Result} :
      Derives P (.seqK rest env input) middle → Continues P k middle result →
      Continues P (.sequence rest env :: k) input result
  | commit {cell : Nat} {k : List Frame} {input middle result : List Result} :
      Derives P (.commitK cell input) middle → Continues P k middle result →
      Continues P (.commit cell :: k) input result
  | follow {k : List Frame} {input middle result : List Result} :
      Derives P (.followK input) middle → Continues P k middle result →
      Continues P (.follow :: k) input result
  | later {goal : Goal} {k : List Frame} {input suffix result : List Result} :
      Derives P goal suffix → Continues P k (input ++ suffix) result →
      Continues P (.later goal :: k) input result
  | append {k : List Frame} {first second result : List Result} :
      Continues P k (first ++ second) result → Continues P (.append first :: k) second result
  | cons {k : List Frame} {first : Result} {remaining result : List Result} :
      Continues P k (first :: remaining) result → Continues P (.cons first :: k) remaining result

def Meaning (P : Program) : Control → List Result → Prop
  | .task goal stack, final => ∃ middle, Derives P goal middle ∧ Continues P stack middle final
  | .returned results stack, final => Continues P stack results final

/-- Any source meaning of a successor reconstructs the predecessor's
source derivation. Failure branches and branch-specific stores are retained. -/
theorem instruction_reflects_meaning {P : Program} {before after : Control}
    (instruction : Instruction P before after) (result : List Result)
    (meaning : Meaning P after result) : Meaning P before result := by
  cases instruction with
  | ret => exact ⟨_, .ret, meaning⟩
  | seq =>
      obtain ⟨first, derived, continued⟩ := meaning
      cases continued with
      | sequence next rest => exact ⟨_, .seq derived next, rest⟩
  | need => obtain ⟨_, derived, rest⟩ := meaning; exact ⟨_, .need derived, rest⟩
  | delay => obtain ⟨_, derived, rest⟩ := meaning; exact ⟨_, .delay derived, rest⟩
  | force => obtain ⟨_, derived, rest⟩ := meaning; exact ⟨_, .force derived, rest⟩
  | caseConHit _ _ _ _ _ _ _ _ matched =>
      obtain ⟨_, derived, rest⟩ := meaning; exact ⟨_, .caseConHit matched derived, rest⟩
  | caseConMiss _ _ _ _ _ _ _ unmatched =>
      obtain ⟨_, derived, rest⟩ := meaning; exact ⟨_, .caseConMiss unmatched derived, rest⟩
  | caseAppHit _ _ _ _ _ _ _ matched =>
      obtain ⟨_, derived, rest⟩ := meaning; exact ⟨_, .caseAppHit matched derived, rest⟩
  | caseAppMiss _ _ _ _ _ unmatched =>
      obtain ⟨_, derived, rest⟩ := meaning; exact ⟨_, .caseAppMiss unmatched derived, rest⟩
  | call _ _ _ _ available => obtain ⟨_, derived, rest⟩ := meaning; exact ⟨_, .call available derived, rest⟩
  | callNone _ _ _ _ empty => exact ⟨_, .callNone empty, meaning⟩
  | callRule _ _ _ _ _ selected arity =>
      obtain ⟨_, derived, rest⟩ := meaning; exact ⟨_, .callRule selected arity derived, rest⟩
  | callRuleNone _ _ _ _ missing => exact ⟨_, .callRuleNone missing, meaning⟩
  | choose =>
      obtain ⟨first, derived, continued⟩ := meaning
      cases continued with
      | later next rest => exact ⟨_, .choose derived next, rest⟩
  | fail => exact ⟨_, .fail, meaning⟩
  | emit => obtain ⟨_, derived, rest⟩ := meaning; exact ⟨_, .emit derived, rest⟩
  | quote => exact ⟨_, .quote, meaning⟩
  | runCode _ _ _ _ _ code found =>
      obtain ⟨first, derived, continued⟩ := meaning
      cases continued with
      | follow next rest => exact ⟨_, .runCode code found derived next, rest⟩
  | runOther _ _ _ notCode => exact ⟨_, .runOther notCode, meaning⟩
  | prim => exact ⟨_, .prim, meaning⟩
  | altsNil => exact ⟨_, .altsNil, meaning⟩
  | altsCons =>
      obtain ⟨first, derived, continued⟩ := meaning
      cases continued with
      | later next rest => exact ⟨_, .altsCons derived next, rest⟩
  | seqKNil => exact ⟨_, .seqKNil, meaning⟩
  | seqKOk =>
      obtain ⟨first, derived, continued⟩ := meaning
      cases continued with
      | later next rest => exact ⟨_, .seqKOk derived next, rest⟩
  | seqKStop _ _ _ _ _ stopped =>
      obtain ⟨remaining, derived, continued⟩ := meaning
      cases continued with
      | cons rest => exact ⟨_, .seqKStop stopped derived, rest⟩
  | forceWhnf _ _ ready => exact ⟨_, .forceWhnf ready, meaning⟩
  | forceDone _ _ _ _ found done => obtain ⟨_, derived, rest⟩ := meaning; exact ⟨_, .forceDone found done derived, rest⟩
  | forceBlackhole _ _ _ found busy => exact ⟨_, .forceBlackhole found busy, meaning⟩
  | forcePending _ _ _ found pending =>
      obtain ⟨first, derived, continued⟩ := meaning
      cases continued with
      | commit next rest => exact ⟨_, .forcePending found pending derived next, rest⟩
  | forceThunk _ _ _ found =>
      obtain ⟨first, derived, continued⟩ := meaning
      cases continued with
      | follow next rest => exact ⟨_, .forceThunk found derived next, rest⟩
  | commitNil => exact ⟨_, .commitNil, meaning⟩
  | commitOk =>
      obtain ⟨first, derived, continued⟩ := meaning
      cases continued with
      | later next rest => exact ⟨_, .commitOk derived next, rest⟩
  | commitStop _ _ _ _ stopped =>
      obtain ⟨remaining, derived, continued⟩ := meaning
      cases continued with
      | cons rest => exact ⟨_, .commitStop stopped derived, rest⟩
  | followNil => exact ⟨_, .followNil, meaning⟩
  | followOk =>
      obtain ⟨first, derived, continued⟩ := meaning
      cases continued with
      | later next rest => exact ⟨_, .followOk derived next, rest⟩
  | followStop _ _ _ stopped =>
      obtain ⟨remaining, derived, continued⟩ := meaning
      cases continued with
      | cons rest => exact ⟨_, .followStop stopped derived, rest⟩
  | sequenceReturn => obtain ⟨_, derived, rest⟩ := meaning; exact .sequence derived rest
  | commitReturn => obtain ⟨_, derived, rest⟩ := meaning; exact .commit derived rest
  | followReturn => obtain ⟨_, derived, rest⟩ := meaning; exact .follow derived rest
  | laterReturn =>
      obtain ⟨_, derived, continued⟩ := meaning
      cases continued with
      | append rest => exact .later derived rest
  | appendReturn => exact .append meaning
  | consReturn => exact .cons meaning

theorem path_reflects_meaning {P : Program} {before after : Control}
    (path : Path P before after) (result : List Result) (meaning : Meaning P after result) :
    Meaning P before result := by
  induction path with
  | refl => exact meaning
  | tail previous instruction ih => exact ih (instruction_reflects_meaning instruction result meaning)

/-- Complete ordered observations agree with the independent source,
including every result's exact branch store and emitted-event sequence. -/
theorem source_iff_instruction_path (P : Program) (goal : Goal) (results : List Result) :
    Derives P goal results ↔ Path P (.task goal []) (.returned results []) := by
  constructor
  · intro derived; exact source_realized derived []
  · intro path
    obtain ⟨middle, derived, continued⟩ := path_reflects_meaning path results (Continues.nil results)
    cases continued
    exact derived

/-- Execute one instruction. Missing referenced cells retain a suspended
control; they do not become a completed empty answer list. -/
def next (P : Program) : Control → Option Control
  | .returned _ [] => none
  | .returned results (.sequence rest env :: k) => some (.task (.seqK rest env results) k)
  | .returned results (.commit cell :: k) => some (.task (.commitK cell results) k)
  | .returned results (.follow :: k) => some (.task (.followK results) k)
  | .returned results (.later goal :: k) => some (.task goal (.append results :: k))
  | .returned results (.append first :: k) => some (.returned (first ++ results) k)
  | .returned results (.cons first :: k) => some (.returned (first :: results) k)
  | .task (.eval σ ρ code) k => match code with
    | .ret v => some (.returned [(.ok (v.eval ρ),σ)] k)
    | .seq first rest => some (.task (.eval σ ρ first) (.sequence rest ρ :: k))
    | .need producer body => some (.task (.eval (σ.alloc producer ρ) (.need σ.cells.length :: ρ) body) k)
    | .delay producer body => some (.task (.eval (σ.alloc producer ρ) (.thunk σ.cells.length :: ρ) body) k)
    | .force value => some (.task (.forceVal σ (value.eval ρ)) k)
    | .caseCon value name arity hit miss =>
        match (value.eval ρ).matchCon name arity with
        | some fields => some (.task (.eval σ (fields ++ ρ) hit) k)
        | none => some (.task (.eval σ ρ miss) k)
    | .caseApp value hit miss =>
        match (value.eval ρ).matchApp with
        | some (f,x) => some (.task (.eval σ (f :: x :: ρ) hit) k)
        | none => some (.task (.eval σ ρ miss) k)
    | .call function arguments =>
        match candidates P function arguments.length with
        | [] => some (.returned [(.fail,σ)] k)
        | branches => some (.task (.alts σ (branches.map fun rule => (rule.body, arguments.map (·.eval ρ)))) k)
    | .callRule index arguments =>
        match P[index]? with
        | some rule => if rule.arity = arguments.length then
            some (.task (.eval σ (arguments.map (·.eval ρ)) rule.body) k)
          else some (.returned [(.fail,σ)] k)
        | none => some (.returned [(.fail,σ)] k)
    | .choose first second => some (.task (.eval σ ρ first) (.later (.eval σ ρ second) :: k))
    | .fail => some (.returned [(.fail,σ)] k)
    | .emit event rest => some (.task (.eval (σ.emit event) ρ rest) k)
    | .quote body => some (.returned [(.ok (.code σ.cells.length),σ.alloc body ρ)] k)
    | .run value => match value.eval ρ with
      | .code cell => match σ.cells[cell]? with
        | some record => some (.task (.eval σ record.env record.code) (.follow :: k))
        | none => none
      | other => some (.returned [(.ok (.app (.sym unquoteHead) other),σ)] k)
    | .prim operation arguments => some (.returned [(primOutcome operation (arguments.map (·.eval ρ)),σ)] k)
  | .task (.alts _ []) k => some (.returned [] k)
  | .task (.alts σ ((code,env) :: rest)) k => some (.task (.eval σ env code) (.later (.alts σ rest) :: k))
  | .task (.seqK _ _ []) k => some (.returned [] k)
  | .task (.seqK code env ((.ok value,σ) :: rest)) k =>
      some (.task (.eval σ (value :: env) code) (.later (.seqK code env rest) :: k))
  | .task (.seqK code env ((outcome,σ) :: rest)) k =>
      some (.task (.seqK code env rest) (.cons (outcome,σ) :: k))
  | .task (.forceVal σ value) k => match value with
    | .need cell => match σ.cells[cell]? with
      | none => none
      | some record => match record.memo with
        | .done value => some (.task (.forceVal σ value) k)
        | .evaluating => some (.returned [(.blackhole,σ)] k)
        | .pending => some (.task (.eval (σ.setMemo cell .evaluating) record.env record.code) (.commit cell :: k))
    | .thunk cell => match σ.cells[cell]? with
      | none => none
      | some record => some (.task (.eval σ record.env record.code) (.follow :: k))
    | other => some (.returned [(.ok other,σ)] k)
  | .task (.commitK _ []) k => some (.returned [] k)
  | .task (.commitK cell ((.ok value,σ) :: rest)) k =>
      some (.task (.forceVal (σ.setMemo cell (.done value)) value) (.later (.commitK cell rest) :: k))
  | .task (.commitK cell ((outcome,σ) :: rest)) k =>
      some (.task (.commitK cell rest) (.cons (outcome,σ.setMemo cell .pending) :: k))
  | .task (.followK []) k => some (.returned [] k)
  | .task (.followK ((.ok value,σ) :: rest)) k =>
      some (.task (.forceVal σ value) (.later (.followK rest) :: k))
  | .task (.followK ((outcome,σ) :: rest)) k => some (.task (.followK rest) (.cons (outcome,σ) :: k))

theorem next_complete {P : Program} {before after : Control} (instruction : Instruction P before after) :
    next P before = some after := by
  cases instruction with
  | ret | seq | need | delay | force | choose | fail | emit | quote | prim | altsNil | altsCons
    | seqKNil | seqKOk | commitNil | commitOk | followNil | followOk | sequenceReturn | commitReturn
    | followReturn | laterReturn | appendReturn | consReturn => rfl
  | caseConHit _ _ _ _ _ _ _ _ matched => simp [next, matched]
  | caseConMiss _ _ _ _ _ _ _ unmatched => simp [next, unmatched]
  | caseAppHit _ _ _ _ _ _ _ matched => simp [next, matched]
  | caseAppMiss _ _ _ _ _ unmatched => simp [next, unmatched]
  | call _ _ _ _ available =>
      simp only [next]
  | callNone _ _ _ _ empty => simp [next, empty]
  | callRule _ _ _ _ _ selected arity => simp [next, selected, arity]
  | callRuleNone σ ρ i args missing k =>
      cases selected : P[i]? with
      | none => simp [next, selected]
      | some rule => simp [next, selected, missing rule selected]
  | runCode _ _ _ _ _ code found => simp [next, code, found]
  | runOther σ ρ v notCode k =>
      cases value : v.eval ρ <;> simp [next, value]
      exact False.elim (notCode _ value)
  | seqKStop _ _ outcome _ _ stopped => cases outcome <;> simp_all [Outcome.isOk, next]
  | forceWhnf σ value ready k => cases value <;> simp_all [Val.isCell, next]
  | forceDone _ _ _ _ found done => simp [next, found, done]
  | forceBlackhole _ _ _ found busy => simp [next, found, busy]
  | forcePending _ _ _ found pending => simp [next, found, pending]
  | forceThunk _ _ _ found => simp [next, found]
  | commitStop _ outcome _ _ stopped => cases outcome <;> simp_all [Outcome.isOk, next]
  | followStop outcome _ _ stopped => cases outcome <;> simp_all [Outcome.isOk, next]

theorem next_sound {P : Program} {before after : Control} (computed : next P before = some after) :
    Instruction P before after := by
  have use {target : Control} (instruction : Instruction P before target) : Instruction P before after := by
    have same := Option.some.inj ((next_complete instruction).symm.trans computed)
    exact same ▸ instruction
  cases before with
  | returned results stack =>
      cases stack with
      | nil => simp [next] at computed
      | cons frame rest =>
          cases frame with
          | sequence code env => exact use (.sequenceReturn results code env rest)
          | commit cell => exact use (.commitReturn results cell rest)
          | follow => exact use (.followReturn results rest)
          | later goal => exact use (.laterReturn results goal rest)
          | append earlier => exact use (.appendReturn earlier results rest)
          | cons earlier => exact use (.consReturn earlier results rest)
  | task goal stack =>
      cases goal with
      | eval store env code =>
          cases code with
          | ret value => exact use (.ret store env value stack)
          | seq first rest => exact use (.seq store env first rest stack)
          | need producer body => exact use (.need store env producer body stack)
          | delay producer body => exact use (.delay store env producer body stack)
          | force value => exact use (.force store env value stack)
          | caseCon value name arity hit miss =>
              cases matched : (value.eval env).matchCon name arity with
              | some fields => exact use (.caseConHit store env value name arity hit miss fields matched stack)
              | none => exact use (.caseConMiss store env value name arity hit miss matched stack)
          | caseApp value hit miss =>
              cases matched : (value.eval env).matchApp with
              | some fields => exact use (.caseAppHit store env value hit miss fields.1 fields.2 matched stack)
              | none => exact use (.caseAppMiss store env value hit miss matched stack)
          | call function arguments =>
              by_cases empty : candidates P function arguments.length = []
              · exact use (.callNone store env function arguments empty stack)
              · exact use (.call store env function arguments empty stack)
          | callRule index arguments =>
              cases selected : P[index]? with
              | none => exact use (.callRuleNone store env index arguments (by simp [selected]) stack)
              | some rule =>
                  by_cases arity : rule.arity = arguments.length
                  · exact use (.callRule store env index arguments rule selected arity stack)
                  · apply use (.callRuleNone store env index arguments ?_ stack)
                    intro other found
                    rw [selected] at found
                    cases Option.some.inj found
                    exact arity
          | choose first second => exact use (.choose store env first second stack)
          | fail => exact use (.fail store env stack)
          | emit event rest => exact use (.emit store env event rest stack)
          | quote body => exact use (.quote store env body stack)
          | run value =>
              cases code : value.eval env with
              | code cell =>
                  cases found : store.cells[cell]? with
                  | none => simp [next, code, found] at computed
                  | some record => exact use (.runCode store env value cell record code found stack)
              | sym symbol => exact use (.runOther store env value (by simp [code]) stack)
              | app function argument => exact use (.runOther store env value (by simp [code]) stack)
              | need cell => exact use (.runOther store env value (by simp [code]) stack)
              | thunk cell => exact use (.runOther store env value (by simp [code]) stack)
          | prim operation arguments => exact use (.prim store env operation arguments stack)
      | alts store branches =>
          cases branches with
          | nil => exact use (.altsNil store stack)
          | cons branch rest => exact use (.altsCons store branch.1 branch.2 rest stack)
      | seqK code env results =>
          cases results with
          | nil => exact use (.seqKNil code env stack)
          | cons result rest =>
              rcases result with ⟨outcome,store⟩
              cases outcome with
              | ok value => exact use (.seqKOk code env value store rest stack)
              | fail => exact use (.seqKStop code env .fail store rest rfl stack)
              | blackhole => exact use (.seqKStop code env .blackhole store rest rfl stack)
      | forceVal store value =>
          cases value with
          | sym symbol => exact use (.forceWhnf store (.sym symbol) rfl stack)
          | app function argument => exact use (.forceWhnf store (.app function argument) rfl stack)
          | code cell => exact use (.forceWhnf store (.code cell) rfl stack)
          | need cell =>
              cases found : store.cells[cell]? with
              | none => simp [next, found] at computed
              | some record =>
                  cases cache : record.memo with
                  | pending => exact use (.forcePending store cell record found cache stack)
                  | evaluating => exact use (.forceBlackhole store cell record found cache stack)
                  | done value => exact use (.forceDone store cell record value found cache stack)
          | thunk cell =>
              cases found : store.cells[cell]? with
              | none => simp [next, found] at computed
              | some record => exact use (.forceThunk store cell record found stack)
      | commitK cell results =>
          cases results with
          | nil => exact use (.commitNil cell stack)
          | cons result rest =>
              rcases result with ⟨outcome,store⟩
              cases outcome with
              | ok value => exact use (.commitOk cell value store rest stack)
              | fail => exact use (.commitStop cell .fail store rest rfl stack)
              | blackhole => exact use (.commitStop cell .blackhole store rest rfl stack)
      | followK results =>
          cases results with
          | nil => exact use (.followNil stack)
          | cons result rest =>
              rcases result with ⟨outcome,store⟩
              cases outcome with
              | ok value => exact use (.followOk value store rest stack)
              | fail => exact use (.followStop .fail store rest rfl stack)
              | blackhole => exact use (.followStop .blackhole store rest rfl stack)

theorem instruction_iff_next (P : Program) (before after : Control) :
    Instruction P before after ↔ next P before = some after := ⟨next_complete, next_sound⟩

def runFuel (P : Program) : Nat → Control → Control
  | 0, state => state
  | fuel + 1, state => match next P state with
    | none => state
    | some later => runFuel P fuel later

theorem runFuel_add (P : Program) (first second : Nat) (state : Control) :
    runFuel P (first + second) state = runFuel P second (runFuel P first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, runFuel]
  | succ first ih =>
      simp only [Nat.succ_add, runFuel]
      cases selected : next P state with
      | some later => exact ih later
      | none =>
          cases second <;> simp only [runFuel, selected]

/-- An abstract finite instruction path is executable with sufficient fuel;
the runner performs one exposed instruction per recursive call. -/
theorem path_runs {P : Program} {before after : Control} (path : Path P before after) :
    ∃ fuel, runFuel P fuel before = after := by
  induction path with
  | refl => exact ⟨0,rfl⟩
  | tail prior instruction ih =>
      obtain ⟨fuel, reached⟩ := ih
      refine ⟨fuel+1, ?_⟩
      rw [runFuel_add, reached]
      simp only [runFuel, next_complete instruction]

theorem runFuel_has_path (P : Program) (fuel : Nat) (state : Control) :
    Path P state (runFuel P fuel state) := by
  induction fuel generalizing state with
  | zero => exact .refl
  | succ fuel ih =>
      cases selected : next P state with
      | none => simpa only [runFuel, selected] using (Relation.ReflTransGen.refl (a := state))
      | some later =>
          exact (Relation.ReflTransGen.single (next_sound selected)).trans (by simpa only [runFuel, selected] using ih later)

theorem source_iff_executable (P : Program) (goal : Goal) (results : List Result) :
    Derives P goal results ↔ ∃ fuel, runFuel P fuel (.task goal []) = .returned results [] := by
  constructor
  · intro derived; exact path_runs (source_realized derived [])
  · rintro ⟨fuel,reached⟩
    exact (source_iff_instruction_path P goal results).mpr (reached ▸ runFuel_has_path P fuel (.task goal []))

/-- Entering an authored computation or forcing a value is source work.
Return frames and finite result-list traversal are administrative work. -/
def sourceWork : Control → Bool
  | .task (.eval _ _ _) _ | .task (.forceVal _ _) _ => true
  | _ => false

def Frame.launches : Frame → Nat
  | .sequence _ _ | .commit _ | .follow | .later _ => 1
  | .append _ | .cons _ => 0

def launches : List Frame → Nat
  | [] => 0
  | frame :: rest => frame.launches + launches rest

def pendingRows : Goal → Nat
  | .alts _ branches => branches.length
  | .seqK _ _ results | .commitK _ results | .followK results => results.length
  | .eval _ _ _ | .forceVal _ _ => 0

def administrativeRank : Control → Nat × Nat
  | .task goal stack => (launches stack, 2 * pendingRows goal + 1 + stack.length)
  | .returned _ stack => (launches stack, stack.length)

/-- Between source-work boundaries, an instruction strictly decreases a
lexicographic natural-number rank. Returning into another continuation can
expose a long result list, but consumes one of the finitely many launch frames. -/
theorem administrative_decreases {P : Program} {before after : Control}
    (instruction : Instruction P before after)
    (beforeAdministrative : sourceWork before = false) (afterAdministrative : sourceWork after = false) :
    Prod.Lex (· < ·) (· < ·) (administrativeRank after) (administrativeRank before) := by
  cases instruction <;> simp_all only [sourceWork, Bool.true_eq_false]
  all_goals
    simp only [administrativeRank, launches, Frame.launches, pendingRows,
      List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_zero]
    first
    | exact Prod.Lex.left _ _ (by omega)
    | exact Prod.Lex.right _ (by omega)

/-- No infinite sequence consists solely of instruction bookkeeping. This
does not assert termination of recursively defined source computations. -/
theorem administrative_wellFounded (P : Program) :
    WellFounded (fun after before => Instruction P before after ∧
      sourceWork before = false ∧ sourceWork after = false) := by
  exact Subrelation.wf (r := InvImage (Prod.Lex (· < ·) (· < ·)) administrativeRank)
    (fun {_ _} step => administrative_decreases step.1 step.2.1 step.2.2)
    (InvImage.wf administrativeRank (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf))

/-- Consume the existing source translation for each declared argument
profile. Its source observation already uses `Derives`; the new result is
the actual finite instruction execution, not a redefinition of that source. -/
theorem source_expression_iff_executable (profile : Profile) (program : SProgram)
    (expression : Expr) (results : List Result) :
    SourceObserves profile program expression results ↔
      ∃ fuel, runFuel (observed (program.toCore profile)) fuel
        (.task (.eval Store.empty [] (observe (expression.toCore profile id))) []) = .returned results [] :=
  source_iff_executable _ _ results

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions
