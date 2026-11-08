import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.UnifyingFrames
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RefinedUninterpreted
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.UninterpretedLocalMultiplicity

/-!
# Captured parameter frames for uninterpreted source regions

Prefix and suffix parameters are captured outside the logical substitution,
not inserted under source-local names into that substitution. The source
lowering inserts captured value recipes at recursive call sites. Its exact
correspondence is proved for ground frames, using the general support theorem
as the reason those captures cannot change. Open frames require a separate
support-scoped effect admission and are not silently treated as ground.

Groundness here is that of the encoded first-order Atom model. It does not
certify absence of hidden native closure/seal/resource dependencies. Such
native values require explicit admission exclusions or a codec exposing their
captured ports, as distinguished by `Machines.CapturedBindingProjection`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.CapturedUninterpretedRegions

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open UnifyingRegions UnifyingFrames

def GroundFrame (values : List Atom) : Prop := ∀ value ∈ values, support value = ∅

theorem subst_ground {value : Atom} (ground : support value = ∅) (σ : Substitution) :
    substA σ value = value := by
  have encoded : Mettapedia.Logic.LP.Subst.applyTerm
      (fun x => UnifyAtoms.encode (σ x) : Mettapedia.Logic.LP.Subst UnifyAtoms.sig)
      (UnifyAtoms.encode value) = UnifyAtoms.encode value := by
    apply Mettapedia.Logic.LP.Subst.applyTerm_eq_self
    intro x member
    change x ∈ support value at member
    rw [ground] at member
    exact False.elim (Finset.notMem_empty x member)
  have decoded := congrArg UnifyAtoms.decode encoded
  have commutes := UnifyAtoms.decode_applyTerm (fun x => UnifyAtoms.encode (σ x)) value
  have eq := commutes.symm.trans (decoded.trans (UnifyAtoms.decode_encode value))
  have maps : (fun x => UnifyAtoms.decode (UnifyAtoms.encode (σ x))) = σ :=
    funext fun x => UnifyAtoms.decode_encode (σ x)
  rw [maps] at eq
  exact eq

theorem GroundFrame.subst {values : List Atom} (ground : GroundFrame values) (σ : Substitution) :
    values.map (substA σ) = values := by
  calc
    _ = values.map id := List.map_congr_left fun value member => subst_ground (ground value member) σ
    _ = values := by simp

def captureOracle (pre post : List Atom) (oracle : SelfOracle) : SelfOracle :=
  fun args => oracle (pre ++ args ++ post)

mutual
/-- Insert an explicit captured frame around recursive arguments in the
existing source syntax. Unsupported forms are left for the same fallback. -/
def liftFrame (pre post : List Atom) : Expr → Expr
  | .ctor c args => .ctor c (liftFrameAll pre post args)
  | .self args => .self (pre.map Expr.const ++ liftFrameAll pre post args ++ post.map Expr.const)
  | .letE p val body => .letE p (liftFrame pre post val) (liftFrame pre post body)
  | .ifE c t e => .ifE (liftFrame pre post c) (liftFrame pre post t) (liftFrame pre post e)
  | e => e

def liftFrameAll (pre post : List Atom) : List Expr → List Expr
  | [] => []
  | e :: es => liftFrame pre post e :: liftFrameAll pre post es
end

theorem evalAll_constants (fallback : Fallback) (oracle : SelfOracle) (values : List Atom)
    (σ : Substitution) :
    evalAllUnifying fallback oracle (values.map Expr.const) σ = {(values, σ)} := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [evalAllUnifying, evalUnifying, ih]

theorem evalAll_append (fallback : Fallback) (oracle : SelfOracle) (left right : List Expr) :
    ∀ σ, evalAllUnifying fallback oracle (left ++ right) σ =
      (evalAllUnifying fallback oracle left σ).bind fun first =>
        (evalAllUnifying fallback oracle right first.2).map fun second =>
          (first.1 ++ second.1, second.2) := by
  induction left with
  | nil => intro σ; simp [evalAllUnifying]
  | cons e es ih =>
      intro σ
      simp only [List.cons_append, evalAllUnifying, ih, Multiset.bind_assoc,
        Multiset.map_bind, Multiset.bind_map, Multiset.map_map]
      rfl

theorem evalAll_captured (fallback : Fallback) (oracle : SelfOracle) (pre post : List Atom)
    (expressions : List Expr) (σ : Substitution) :
    evalAllUnifying fallback oracle (pre.map Expr.const ++ expressions ++ post.map Expr.const) σ =
      (evalAllUnifying fallback oracle expressions σ).map fun out =>
        (pre ++ out.1 ++ post, out.2) := by
  rw [evalAll_append, evalAll_append, evalAll_constants]
  simp [Multiset.singleton_bind, evalAll_constants, Multiset.map_map]

mutual
/-- The captured-frame lowering preserves the full answer/state bag. Its
body is the actual existing expression evaluator, not a replacement oracle. -/
theorem eval_liftFrame (fallback : Fallback) (oracle : SelfOracle) (pre post : List Atom)
    (preGround : GroundFrame pre) (postGround : GroundFrame post) :
    ∀ (e : Expr) (σ : Substitution),
      evalUnifying fallback oracle (liftFrame pre post e) σ =
        evalUnifying fallback (captureOracle pre post oracle) e σ
  | .var _, _ => rfl
  | .const _, _ => rfl
  | .ctor c args, σ => by
      simp only [liftFrame, evalUnifying, evalAll_liftFrame fallback oracle pre post preGround postGround]
  | .self args, σ => by
      simp only [liftFrame, evalUnifying]
      rw [evalAll_captured, evalAll_liftFrame fallback oracle pre post preGround postGround,
        Multiset.bind_map]
      apply Multiset.bind_congr
      intro out _
      simp only [List.map_append, preGround.subst, postGround.subst, captureOracle]
  | .letE p val body, σ => by
      simp only [liftFrame, evalUnifying]
      rw [eval_liftFrame fallback oracle pre post preGround postGround val σ]
      apply Multiset.bind_congr
      intro out _
      cases h : bindPattern out.2 p out.1 with
      | none => rfl
      | some τ => exact eval_liftFrame fallback oracle pre post preGround postGround body τ
  | .ifE c t e, σ => by
      simp only [liftFrame, evalUnifying]
      rw [eval_liftFrame fallback oracle pre post preGround postGround c σ]
      apply Multiset.bind_congr
      intro out _
      split
      · exact eval_liftFrame fallback oracle pre post preGround postGround t out.2
      · exact eval_liftFrame fallback oracle pre post preGround postGround e out.2
  | .empty, _ => rfl
  | .prim _ _, _ => rfl
  | .call _ _, _ => rfl
  | .enter _ _, _ => rfl
  | .caseE _ _ _, _ => rfl
  | .matchE _ _ _, _ => rfl

theorem evalAll_liftFrame (fallback : Fallback) (oracle : SelfOracle) (pre post : List Atom)
    (preGround : GroundFrame pre) (postGround : GroundFrame post) :
    ∀ (es : List Expr) (σ : Substitution),
      evalAllUnifying fallback oracle (liftFrameAll pre post es) σ =
        evalAllUnifying fallback (captureOracle pre post oracle) es σ
  | [], _ => rfl
  | e :: es, σ => by
      simp only [liftFrameAll, evalAllUnifying]
      rw [eval_liftFrame fallback oracle pre post preGround postGround e σ]
      apply Multiset.bind_congr
      intro out _
      rw [evalAll_liftFrame fallback oracle pre post preGround postGround es out.2]
end

/-- Splitting the source argument list retains the captured frame as values,
outside the substitution used for local names. -/
def sourceBody (fallback : Fallback) (parameter : String) (e : Expr) (prefixLength : Nat)
    (oracle : SelfOracle) (args : List Atom) : Multiset Atom :=
  match args.drop prefixLength with
  | [] => 0
  | value :: post =>
      (evalUnifying fallback oracle (liftFrame (args.take prefixLength) post e)
        (initial parameter value)).map observe

theorem sourceBody_split (fallback : Fallback) (parameter : String) (e : Expr)
    (pre post : List Atom) (value : Atom) (oracle : SelfOracle) :
    sourceBody fallback parameter e pre.length oracle (pre ++ value :: post) =
      (evalUnifying fallback oracle (liftFrame pre post e) (initial parameter value)).map observe := by
  simp [sourceBody]

theorem sourceBody_captured (fallback : Fallback) (parameter : String) (e : Expr)
    (pre post : List Atom) (value : Atom) (oracle : SelfOracle)
    (preGround : GroundFrame pre) (postGround : GroundFrame post) :
    sourceBody fallback parameter e pre.length oracle (pre ++ value :: post) =
      body fallback parameter e (captureOracle pre post oracle) [value] := by
  rw [sourceBody_split, eval_liftFrame fallback oracle pre post preGround postGround]
  rfl

def allGround (values : List Atom) : Bool := values.all fun value => support value == ∅

theorem allGround_iff (values : List Atom) : allGround values = true ↔ GroundFrame values := by
  simp [allGround, GroundFrame, List.all_eq_true]

/-- This executable extra gate checks the frame, not merely its declared
types. The active uninterpreted argument may remain open. -/
def frameGate (prefixLength : Nat) (args : List Atom) : Bool :=
  match args.drop prefixLength with
  | [] => false
  | _ :: post => allGround (args.take prefixLength) && allGround post

theorem frameGate_split (pre post : List Atom) (value : Atom) :
    frameGate pre.length (pre ++ value :: post) = true ↔ GroundFrame pre ∧ GroundFrame post := by
  simp [frameGate, allGround_iff]

def Admitted (Γ : Decls) (grounded : String → Bool) (pre post : List (Ty Empty))
    (args : List Atom) : Prop :=
  UnintEntry Γ grounded pre post args ∧ frameGate pre.length args = true

theorem admitted_split {Γ : Decls} {grounded : String → Bool} {pre post : List (Ty Empty)}
    {us ws : List Atom} {value : Atom} (len : pre.length = us.length)
    (allowed : Admitted Γ grounded pre post (us ++ value :: ws)) :
    EntryFacts Γ grounded pre us ∧ Uninterp Γ value ∧ EntryFacts Γ grounded post ws ∧
      GroundFrame us ∧ GroundFrame ws := by
  obtain ⟨before, v, after, shape, beforeLen, beforeTyped, clean, afterTyped⟩ := allowed.1
  have parts := List.append_inj shape (len.symm.trans beforeLen)
  obtain ⟨rfl, rest⟩ := parts
  obtain ⟨rfl, rfl⟩ := List.cons.inj rest
  have gate := allowed.2
  rw [len] at gate
  exact ⟨beforeTyped, clean, afterTyped, (frameGate_split _ _ _).mp gate⟩

theorem admitted_make {Γ : Decls} {grounded : String → Bool} {pre post : List (Ty Empty)}
    {us ws : List Atom} {value : Atom} (len : pre.length = us.length)
    (before : EntryFacts Γ grounded pre us) (clean : Uninterp Γ value)
    (after : EntryFacts Γ grounded post ws) (preGround : GroundFrame us) (postGround : GroundFrame ws) :
    Admitted Γ grounded pre post (us ++ value :: ws) := by
  refine ⟨⟨us, value, ws, rfl, len, before, clean, after⟩, ?_⟩
  rw [len]
  exact (frameGate_split _ _ _).mpr ⟨preGround, postGround⟩

/-- Source admission and return analysis derive the recursive obligations
for arbitrary numbers and types of captured prefix/suffix parameters. -/
theorem analyzed_frame_hyps {Γ : Decls} (grounded : String → Bool) (fallback : Fallback)
    (parameter : String) (pre post : List (Ty Empty)) {e : Expr}
    (accepted : UnifyingRegions.Accepted Γ e) (returns : ReturnsPat (.var parameter) e) :
    RefinedUninterpreted.Hyps Γ grounded pre post (Admitted Γ grounded pre post)
      (sourceBody fallback parameter e pre.length) (sourceBody fallback parameter e pre.length) where
  entry _ allowed := allowed.1
  calls o o' agree cleanOracle args allowed := by
    obtain ⟨us, value, ws, rfl, len, _, _, _⟩ := allowed.1
    obtain ⟨before, cleanValue, after, preGround, postGround⟩ := admitted_split len allowed
    have clean : OracleClean Γ (captureOracle us ws o) := by
      intro v hv r member
      apply cleanOracle (us ++ v :: ws) (admitted_make len before hv after preGround postGround) r
      simpa [captureOracle, List.append_assoc] using member
    have same : UnifyingRegions.Agree Γ (captureOracle us ws o) (captureOracle us ws o') := by
      intro v hv
      simpa [captureOracle, List.append_assoc] using
        agree (us ++ v :: ws) (admitted_make len before hv after preGround postGround)
    rw [len, sourceBody_captured fallback parameter e us ws value o preGround postGround,
      sourceBody_captured fallback parameter e us ws value o' preGround postGround]
    simp only [body]
    rw [accepted_congr fallback _ _ clean same accepted _ (clean_initial parameter cleanValue)]
  results o cleanOracle us value ws len allowed r member := by
    obtain ⟨before, cleanValue, after, preGround, postGround⟩ := admitted_split len allowed
    have clean : OracleClean Γ (captureOracle us ws o) := by
      intro v hv r member
      apply cleanOracle (us ++ v :: ws) (admitted_make len before hv after preGround postGround) r
      simpa [captureOracle, List.append_assoc] using member
    rw [len, sourceBody_captured fallback parameter e us ws value o preGround postGround] at member
    exact body_instance fallback parameter accepted returns _ clean cleanValue r member

theorem source_version_eq_protocol {Γ : Decls} (functional : Functional Γ)
    (grounded : String → Bool) (fallback : Fallback) (parameter typeVariable : String)
    (pre post : List (Ty Empty)) {e : Expr} (accepted : UnifyingRegions.Accepted Γ e)
    (returns : ReturnsPat (.var parameter) e) (fuel : Nat) (args : List Atom)
    (allowed : Admitted Γ grounded pre post args) :
    protocolRun Γ grounded (sourceBody fallback parameter e pre.length)
        (arrow (pre.map Ty.lift ++ .var typeVariable :: post.map Ty.lift) (.var typeVariable)) fuel args =
      versionRun (sourceBody fallback parameter e pre.length) fuel args :=
  RefinedUninterpreted.version_eq_protocol functional typeVariable
    (analyzed_frame_hyps grounded fallback parameter pre post accepted returns) fuel args allowed

/-- The source rule depends on the active value's local typing footprint,
not on uniqueness of declarations elsewhere in the space. -/
theorem source_version_eq_protocol_local {Γ : Decls}
    (grounded : String → Bool) (fallback : Fallback) (parameter typeVariable : String)
    (pre post : List (Ty Empty)) {e : Expr} (accepted : UnifyingRegions.Accepted Γ e)
    (returns : ReturnsPat (.var parameter) e) (fuel : Nat) (args : List Atom)
    (allowed : Admitted Γ grounded pre post args) :
    protocolRun Γ grounded (sourceBody fallback parameter e pre.length)
        (arrow (pre.map Ty.lift ++ .var typeVariable :: post.map Ty.lift) (.var typeVariable)) fuel args =
      versionRun (sourceBody fallback parameter e pre.length) fuel args :=
  UninterpretedLocalMultiplicity.version_eq_protocol_local typeVariable
    (analyzed_frame_hyps grounded fallback parameter pre post accepted returns) fuel args allowed

/-- The ordinary type boundary has established entry facts. The region
offer tests its additional frame condition before entering the fast body. -/
structure CheckedInput (Γ : Decls) (grounded : String → Bool) (pre post : List (Ty Empty)) where
  args : List Atom
  entry : UnintEntry Γ grounded pre post args

noncomputable def offeredRun (Γ : Decls) (grounded : String → Bool) (fallback : Fallback)
    (parameter typeVariable : String) (pre post : List (Ty Empty)) (e : Expr) (fuel : Nat)
    (input : CheckedInput Γ grounded pre post) : Multiset Atom :=
  if frameGate pre.length input.args then
    versionRun (sourceBody fallback parameter e pre.length) fuel input.args
  else
    protocolRun Γ grounded (sourceBody fallback parameter e pre.length)
      (arrow (pre.map Ty.lift ++ .var typeVariable :: post.map Ty.lift) (.var typeVariable)) fuel input.args

/-- A failed frame gate falls back to the canonical protocol; it does not
turn a well-typed open call into an empty answer. -/
theorem offeredRun_eq_protocol {Γ : Decls} (functional : Functional Γ)
    (grounded : String → Bool) (fallback : Fallback) (parameter typeVariable : String)
    (pre post : List (Ty Empty)) {e : Expr} (accepted : UnifyingRegions.Accepted Γ e)
    (returns : ReturnsPat (.var parameter) e) (fuel : Nat)
    (input : CheckedInput Γ grounded pre post) :
    offeredRun Γ grounded fallback parameter typeVariable pre post e fuel input =
      protocolRun Γ grounded (sourceBody fallback parameter e pre.length)
        (arrow (pre.map Ty.lift ++ .var typeVariable :: post.map Ty.lift) (.var typeVariable)) fuel input.args := by
  unfold offeredRun
  split
  · exact (source_version_eq_protocol functional grounded fallback parameter typeVariable
      pre post accepted returns fuel input.args ⟨input.entry, ‹_›⟩).symm
  · rfl

theorem offeredRun_eq_protocol_local {Γ : Decls}
    (grounded : String → Bool) (fallback : Fallback) (parameter typeVariable : String)
    (pre post : List (Ty Empty)) {e : Expr} (accepted : UnifyingRegions.Accepted Γ e)
    (returns : ReturnsPat (.var parameter) e) (fuel : Nat)
    (input : CheckedInput Γ grounded pre post) :
    offeredRun Γ grounded fallback parameter typeVariable pre post e fuel input =
      protocolRun Γ grounded (sourceBody fallback parameter e pre.length)
        (arrow (pre.map Ty.lift ++ .var typeVariable :: post.map Ty.lift) (.var typeVariable)) fuel input.args := by
  unfold offeredRun
  split
  · exact (source_version_eq_protocol_local grounded fallback parameter typeVariable
      pre post accepted returns fuel input.args ⟨input.entry, ‹_›⟩).symm
  · rfl

namespace Controls

def declarations : Decls := fun name => if name = "Known" then [.sym "Tagged"] else []
def known : Atom := .symbol "Known"
def seven : Atom := .grounded (.int 7)
def off : Atom := .grounded (.bool false)
def tagged : Ty Empty := .sym "Tagged"
def number : Ty Empty := .sym "Number"
def program : Expr := UnifyingRegions.Controls.recursiveBody
def fallback : Fallback := fun _ _ => 0

theorem functional : Functional declarations := by
  intro name
  by_cases h : name = "Known" <;> simp [declarations, h]

theorem known_typed (grounded : String → Bool) : Holds declarations grounded known tagged := by
  apply Holds.of_count
  unfold known
  rw [count_symbol_closed declarations "Known" tagged (by rfl)]
  simp

theorem seven_typed (grounded : String → Bool) : Holds declarations grounded seven number := by
  apply Holds.of_count
  unfold seven
  rw [count_class declarations (g := .int 7) (c := "Number") rfl]
  simp [number]

theorem program_accepted : UnifyingRegions.Accepted declarations program :=
  .ifE (.var "argument") (.var "argument")
    (.letE trivial (.self (.const truth trivial)) (.var "argument"))

theorem program_returns : ReturnsPat (.var "argument") program := .ifE .refl (.letE .refl)

theorem typed_entry (grounded : String → Bool) :
    UnintEntry declarations grounded [tagged] [number] [known, off, seven] :=
  ⟨[known], off, [seven], rfl, rfl,
    .cons (fun _ => known_typed grounded) .nil, trivial,
    .cons (fun _ => seven_typed grounded) .nil⟩

theorem computed_gate_passes : frameGate 1 [known, off, seven] = true := by decide +kernel

/-- The recursive source really forwards both captured parameters while
evaluating the active argument through two calls. -/
theorem captured_recursive_execution :
    versionRun (sourceBody fallback "argument" program 1) 2 [known, off, seven] = {off} := by cbv

theorem captured_protocol_every_fuel (grounded : String → Bool) (fuel : Nat) :
    protocolRun declarations grounded (sourceBody fallback "argument" program 1)
        (arrow [tagged.lift, .var "t", number.lift] (.var "t")) fuel [known, off, seven] =
      versionRun (sourceBody fallback "argument" program 1) fuel [known, off, seven] :=
  source_version_eq_protocol functional grounded fallback "argument" "t" [tagged] [number]
    program_accepted program_returns fuel [known, off, seven]
    ⟨typed_entry grounded, computed_gate_passes⟩

/-- A closed type judgment can hold of an open value. Groundness cannot be
silently recovered from that type judgment. -/
theorem typed_open_value (grounded : String → Bool) :
    Holds declarations grounded (.var "open") tagged ∧
      frameGate 1 [.var "open", off, seven] = false := by
  constructor
  · exact Holds.of_count (count_var declarations "open" tagged)
  · decide +kernel

def openInput (grounded : String → Bool) : CheckedInput declarations grounded [tagged] [number] :=
  ⟨[.var "open", off, seven], [.var "open"], off, [seven], rfl, rfl,
    .cons (fun _ => (typed_open_value grounded).1) .nil, trivial,
    .cons (fun _ => seven_typed grounded) .nil⟩

theorem typed_open_frame_uses_canonical (grounded : String → Bool) (fuel : Nat) :
    offeredRun declarations grounded fallback "argument" "t" [tagged] [number] program fuel
        (openInput grounded) =
      protocolRun declarations grounded (sourceBody fallback "argument" program 1)
        (arrow [tagged.lift, .var "t", number.lift] (.var "t")) fuel [.var "open", off, seven] := by
  simp [offeredRun, openInput, (typed_open_value grounded).2]

/-- Opaque declared captures do not become mappings of logical variables. -/
theorem declared_frame_not_in_logical_store :
    initial "argument" off "Known" = .var "Known" ∧
      ¬ Uninterp declarations known := by
  constructor
  · rfl
  · simp [known, declarations, Uninterp, Safe]

def withOverload : Decls := fun name =>
  if name = "unrelated" then [.sym "Number", .sym "String"] else declarations name

theorem overload_not_functional : ¬ Functional withOverload := by
  intro h
  have bad := h "unrelated"
  simp [withOverload] at bad

theorem overload_entry (grounded : String → Bool) :
    UnintEntry withOverload grounded [tagged] [number] [known, off, seven] := by
  have before : Holds withOverload grounded known tagged := by
    apply Holds.of_count
    unfold known
    rw [count_symbol_closed withOverload "Known" tagged (by rfl)]
    simp
  have after : Holds withOverload grounded seven number := by
    apply Holds.of_count
    unfold seven
    rw [count_class withOverload (g := .int 7) (c := "Number") rfl]
    simp [number]
  exact ⟨[known], off, [seven], rfl, rfl, .cons (fun _ => before) .nil, trivial,
    .cons (fun _ => after) .nil⟩

/-- An actual overloaded declaration space supports the same admitted
recursive source region. The closed-frame counts were proved at that space. -/
theorem captured_protocol_with_overload (grounded : String → Bool) (fuel : Nat) :
    ¬ Functional withOverload ∧
      protocolRun withOverload grounded (sourceBody fallback "argument" program 1)
          (arrow [tagged.lift, .var "t", number.lift] (.var "t")) fuel [known, off, seven] =
        versionRun (sourceBody fallback "argument" program 1) fuel [known, off, seven] := by
  refine ⟨overload_not_functional, ?_⟩
  have accepted : UnifyingRegions.Accepted withOverload program :=
    .ifE (.var "argument") (.var "argument")
      (.letE trivial (.self (.const truth trivial)) (.var "argument"))
  exact source_version_eq_protocol_local grounded fallback "argument" "t" [tagged] [number]
    accepted program_returns fuel [known, off, seven] ⟨overload_entry grounded, computed_gate_passes⟩

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.CapturedUninterpretedRegions
