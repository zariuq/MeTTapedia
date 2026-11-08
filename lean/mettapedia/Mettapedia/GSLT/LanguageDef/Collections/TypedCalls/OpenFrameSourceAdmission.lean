import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OpenFrameEffects
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.CapturedUninterpretedRegions

/-!
# Recursive source admission with open retained frames

The source checker bounds local recipes and their unification effects. Open
captured values are allowed outside that scope, and recursive answers remain
inside it. The proof uses the existing substitution-threaded source evaluator
and its captured-frame lowering. It does not identify this sufficient checker
with the native contract analysis.

Support is first-order syntactic support. A native closure, seal or opaque
resource can retain additional dependency ports; a native adapter must expose
those ports in its observation or exclude such values from this contract.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OpenFrameSourceAdmission

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open UnifyingRegions UnifyingFrames OpenFrameEffects CapturedUninterpretedRegions

def Separate (scope : Finset String) (frames : List Atom) : Prop :=
  ∀ value ∈ frames, Disjoint (support value) scope

theorem local_fixes {scope : Finset String} {σ : Substitution} (locality : Local scope σ)
    {value : Atom} (separate : Disjoint (support value) scope) : substA σ value = value := by
  apply subst_fixes
  intro x member
  exact locality.fixes x fun hx => Finset.disjoint_left.mp separate member hx

theorem local_fixes_list {scope : Finset String} {σ : Substitution} (locality : Local scope σ)
    {frames : List Atom} (separate : Separate scope frames) : frames.map (substA σ) = frames := by
  calc
    _ = frames.map id := List.map_congr_left fun value member => local_fixes locality (separate value member)
    _ = frames := by simp

theorem initial_local {scope : Finset String} {parameter : String} (inside : parameter ∈ scope)
    {value : Atom} (supported : support value ⊆ scope) : Local scope (initial parameter value) where
  closed x hx := by
    by_cases eq : x = parameter
    · subst x; simpa only [initial, Function.update_self] using supported
    · simpa only [initial, Function.update_of_ne eq] using (Local.identity scope).closed x hx
  fixes x outside := by
    have different : x ≠ parameter := fun eq => outside (eq ▸ inside)
    simp [initial, different]

theorem evalAll_lift_scoped {Γ : Decls} {scope : Finset String}
    (fallback : Fallback) (oracle : SelfOracle) (pre post : List Atom) (es : List Expr)
    (same : ∀ e ∈ es, ∀ σ, Clean Γ σ → Local scope σ →
      evalUnifying fallback oracle (liftFrame pre post e) σ =
        evalUnifying fallback (captureOracle pre post oracle) e σ)
    (sound : ∀ e ∈ es, ∀ σ, Clean Γ σ → Closed scope σ →
      ∀ out ∈ evalUnifying fallback (captureOracle pre post oracle) e σ,
        ScopedGood Γ scope σ out) :
    ∀ σ, Clean Γ σ → Local scope σ →
      evalAllUnifying fallback oracle (liftFrameAll pre post es) σ =
        evalAllUnifying fallback (captureOracle pre post oracle) es σ := by
  induction es with
  | nil => intro σ _ _; rfl
  | cons e es ih =>
      intro σ clean locality
      simp only [liftFrameAll, evalAllUnifying]
      rw [same e (by simp) σ clean locality]
      apply Multiset.bind_congr
      intro out member
      have good := sound e (by simp) σ clean locality.closed out member
      rw [ih (fun e he => same e (by simp [he]))
        (fun e he => sound e (by simp [he])) out.2 good.clean (good.effect.toLocal locality)]

/-- Open captures are inserted into actual recursive calls without being
changed by local unifiers. The full recipe/state bag is retained. -/
theorem eval_lift_scoped {Γ : Decls} {scope : Finset String}
    (fallback : Fallback) (oracle : SelfOracle) (pre post : List Atom)
    (preSeparate : Separate scope pre) (postSeparate : Separate scope post)
    (oracleGood : ScopedOracle Γ scope (captureOracle pre post oracle))
    {e : Expr} (accepted : UnifyingRegions.Accepted Γ e) (checked : check scope e = true) :
    ∀ σ, Clean Γ σ → Local scope σ →
      evalUnifying fallback oracle (liftFrame pre post e) σ =
        evalUnifying fallback (captureOracle pre post oracle) e σ := by
  induction accepted with
  | var => intro σ _ _; rfl
  | const => intro σ _ _; rfl
  | @ctor c args head parts ih =>
      intro σ clean locality
      have checks := (checkAll_iff scope args).mp checked
      simp only [liftFrame, evalUnifying]
      rw [evalAll_lift_scoped fallback oracle pre post args
        (fun a ha => ih a ha (checks a ha))
        (fun a ha => accepted_scoped fallback _ oracleGood (parts a ha) (checks a ha)) σ clean locality]
  | @self arg argument ih =>
      intro σ clean locality
      have sameAll := evalAll_lift_scoped fallback oracle pre post [arg]
        (fun e he => by simp only [List.mem_singleton] at he; subst e; exact ih checked)
        (fun e he => by
          simp only [List.mem_singleton] at he
          subst e
          exact accepted_scoped fallback _ oracleGood argument checked) σ clean locality
      simp only [liftFrame, evalUnifying]
      rw [evalAll_captured, sameAll, Multiset.bind_map]
      apply Multiset.bind_congr
      intro out member
      have good := evalAll_scoped fallback _ [arg]
        (fun e he => by
          simp only [List.mem_singleton] at he
          subst e
          exact accepted_scoped fallback _ oracleGood argument checked) σ clean locality.closed out member
      have finalLocal := good.effect.toLocal locality
      simp only [List.map_append, local_fixes_list finalLocal preSeparate,
        local_fixes_list finalLocal postSeparate, captureOracle]
  | @letE p val body pattern value result ihv ihb =>
      have checks : (support p.toAtom ⊆ scope ∧ check scope val = true) ∧
          check scope body = true := by simpa only [check, Bool.and_eq_true, decide_eq_true_eq] using checked
      intro σ clean locality
      simp only [liftFrame, evalUnifying]
      rw [ihv checks.1.2 σ clean locality]
      apply Multiset.bind_congr
      intro first member
      have good := accepted_scoped fallback _ oracleGood value checks.1.2 σ clean locality.closed first member
      cases bound : bindPattern first.2 p first.1 with
      | none => rfl
      | some τ =>
          have changed := bindPattern_effect bound (Finset.union_subset
            (subst_support_subset good.closed checks.1.1)
            (subst_support_subset good.closed good.supported))
          exact ihb checks.2 τ (bindPattern_sound good.clean pattern good.data bound).1
            ((good.effect.trans changed).toLocal locality)
  | @ifE c t e condition yes no ihc iht ihe =>
      have checks : (check scope c = true ∧ check scope t = true) ∧ check scope e = true :=
        by simpa only [check, Bool.and_eq_true] using checked
      intro σ clean locality
      simp only [liftFrame, evalUnifying]
      rw [ihc checks.1.1 σ clean locality]
      apply Multiset.bind_congr
      intro first member
      have good := accepted_scoped fallback _ oracleGood condition checks.1.1 σ clean locality.closed first member
      split
      · exact iht checks.1.2 first.2 good.clean (good.effect.toLocal locality)
      · exact ihe checks.2 first.2 good.clean (good.effect.toLocal locality)
  | empty => intro σ _ _; rfl

theorem sourceBody_open {Γ : Decls} {scope : Finset String}
    (fallback : Fallback) (parameter : String) (inside : parameter ∈ scope)
    {e : Expr} (accepted : UnifyingRegions.Accepted Γ e) (checked : check scope e = true)
    (pre post : List Atom) (value : Atom) (oracle : SelfOracle)
    (preSeparate : Separate scope pre) (postSeparate : Separate scope post)
    (clean : Uninterp Γ value) (supported : support value ⊆ scope)
    (oracleGood : ScopedOracle Γ scope (captureOracle pre post oracle)) :
    sourceBody fallback parameter e pre.length oracle (pre ++ value :: post) =
      body fallback parameter e (captureOracle pre post oracle) [value] := by
  rw [sourceBody_split, eval_lift_scoped fallback oracle pre post preSeparate postSeparate
    oracleGood accepted checked _ (clean_initial parameter clean) (initial_local inside supported)]
  rfl

def gate (scope : Finset String) (prefixLength : Nat) (args : List Atom) : Bool :=
  match args.drop prefixLength with
  | [] => false
  | value :: post => decide (support value ⊆ scope) &&
      frameCheck scope Atom.var (args.take prefixLength) && frameCheck scope Atom.var post

theorem id_frameCheck (scope : Finset String) (values : List Atom) :
    frameCheck scope Atom.var values = true ↔ Separate scope values := by
  simp [frameCheck_iff, Separate, observedSupport, substA_var_self]

theorem gate_split (scope : Finset String) (pre post : List Atom) (value : Atom) :
    gate scope pre.length (pre ++ value :: post) = true ↔
      (support value ⊆ scope ∧ Separate scope pre) ∧ Separate scope post := by
  simp [gate, id_frameCheck]

def Admitted (Γ : Decls) (grounded : String → Bool) (pre post : List (Ty Empty))
    (scope : Finset String) (args : List Atom) : Prop :=
  UnintEntry Γ grounded pre post args ∧ gate scope pre.length args = true

theorem admitted_split {Γ : Decls} {grounded : String → Bool} {pre post : List (Ty Empty)}
    {scope : Finset String} {us ws : List Atom} {value : Atom} (len : pre.length = us.length)
    (allowed : Admitted Γ grounded pre post scope (us ++ value :: ws)) :
    EntryFacts Γ grounded pre us ∧ Uninterp Γ value ∧ EntryFacts Γ grounded post ws ∧
      support value ⊆ scope ∧ Separate scope us ∧ Separate scope ws := by
  obtain ⟨before, v, after, shape, beforeLen, beforeTyped, clean, afterTyped⟩ := allowed.1
  have parts := List.append_inj shape (len.symm.trans beforeLen)
  obtain ⟨rfl, rest⟩ := parts
  obtain ⟨rfl, rfl⟩ := List.cons.inj rest
  have checked := allowed.2
  rw [len] at checked
  have fields := (gate_split scope us ws value).mp checked
  exact ⟨beforeTyped, clean, afterTyped, fields.1.1, fields.1.2, fields.2⟩

theorem admitted_make {Γ : Decls} {grounded : String → Bool} {pre post : List (Ty Empty)}
    {scope : Finset String} {us ws : List Atom} {value : Atom} (len : pre.length = us.length)
    (before : EntryFacts Γ grounded pre us) (clean : Uninterp Γ value)
    (after : EntryFacts Γ grounded post ws) (supported : support value ⊆ scope)
    (preSeparate : Separate scope us) (postSeparate : Separate scope ws) :
    Admitted Γ grounded pre post scope (us ++ value :: ws) := by
  refine ⟨⟨us, value, ws, rfl, len, before, clean, after⟩, ?_⟩
  rw [len]
  exact (gate_split scope us ws value).mpr ⟨⟨supported, preSeparate⟩, postSeparate⟩

def OracleOn (Γ : Decls) (grounded : String → Bool) (pre post : List (Ty Empty))
    (scope : Finset String) (oracle : SelfOracle) : Prop :=
  ∀ args, Admitted Γ grounded pre post scope args →
    ∀ result ∈ oracle args, Uninterp Γ result ∧ support result ⊆ scope

theorem oracle_capture {Γ : Decls} {grounded : String → Bool} {pre post : List (Ty Empty)}
    {scope : Finset String} {oracle : SelfOracle} (good : OracleOn Γ grounded pre post scope oracle)
    {us ws : List Atom} (len : pre.length = us.length)
    (before : EntryFacts Γ grounded pre us) (after : EntryFacts Γ grounded post ws)
    (preSeparate : Separate scope us) (postSeparate : Separate scope ws) :
    ScopedOracle Γ scope (captureOracle us ws oracle) := by
  intro value clean supported result member
  apply good _ (admitted_make len before clean after supported preSeparate postSeparate) result
  simpa [captureOracle, List.append_assoc] using member

/-- Returning the active recipe yields a clean instance of that value;
the source analysis also proves its result stays inside the effect scope. -/
theorem source_results {Γ : Decls} {scope : Finset String}
    (grounded : String → Bool) (fallback : Fallback) (parameter : String)
    (inside : parameter ∈ scope) (pre post : List (Ty Empty))
    {e : Expr} (accepted : UnifyingRegions.Accepted Γ e) (checked : check scope e = true)
    (returns : ReturnsPat (.var parameter) e) (oracle : SelfOracle)
    (oracleGood : OracleOn Γ grounded pre post scope oracle)
    (us ws : List Atom) (value : Atom) (len : pre.length = us.length)
    (allowed : Admitted Γ grounded pre post scope (us ++ value :: ws))
    (result : Atom) (member : result ∈ sourceBody fallback parameter e pre.length oracle (us ++ value :: ws)) :
    (∃ delta : Substitution, result = substA delta value ∧ Clean Γ delta) ∧ support result ⊆ scope := by
  obtain ⟨before, clean, after, supported, preSeparate, postSeparate⟩ := admitted_split len allowed
  have oracleScoped := oracle_capture oracleGood len before after preSeparate postSeparate
  rw [len, sourceBody_open fallback parameter inside accepted checked us ws value oracle
    preSeparate postSeparate clean supported oracleScoped] at member
  simp only [body, Multiset.mem_map] at member
  obtain ⟨out, member, rfl⟩ := member
  have good := accepted_scoped fallback _ oracleScoped accepted checked _ (clean_initial parameter clean)
    (initial_local inside supported).closed out member
  have recipe := returns_argument fallback _ parameter returns accepted _ out member
  obtain ⟨delta, safe, extension⟩ := good.extension
  refine ⟨⟨delta, ?_, safe⟩, subst_support_subset good.closed good.supported⟩
  simp only [observe, recipe, substA, extension, compose, initial, Function.update_self]

/-- The source invokes recursive oracles only at calls that satisfy the
same checked domain. Multiplicity is preserved by full multiset equality. -/
theorem source_congr {Γ : Decls} {scope : Finset String}
    (grounded : String → Bool) (fallback : Fallback) (parameter : String)
    (inside : parameter ∈ scope) (pre post : List (Ty Empty))
    {e : Expr} (accepted : UnifyingRegions.Accepted Γ e) (checked : check scope e = true)
    (o o' : SelfOracle) (oracleGood : OracleOn Γ grounded pre post scope o)
    (agree : ∀ args, Admitted Γ grounded pre post scope args → o args = o' args)
    (args : List Atom) (allowed : Admitted Γ grounded pre post scope args) :
    sourceBody fallback parameter e pre.length o args = sourceBody fallback parameter e pre.length o' args := by
  obtain ⟨us, value, ws, rfl, len, _, _, _⟩ := allowed.1
  obtain ⟨before, clean, after, supported, preSeparate, postSeparate⟩ := admitted_split len allowed
  have leftGood := oracle_capture oracleGood len before after preSeparate postSeparate
  have capturedAgree : ∀ v, Uninterp Γ v → support v ⊆ scope →
      captureOracle us ws o [v] = captureOracle us ws o' [v] := by
    intro v hv hs
    simpa [captureOracle, List.append_assoc] using
      agree _ (admitted_make len before hv after hs preSeparate postSeparate)
  have rightGood : ScopedOracle Γ scope (captureOracle us ws o') := by
    intro v hv hs r member
    rw [← capturedAgree v hv hs] at member
    exact leftGood v hv hs r member
  rw [len, sourceBody_open fallback parameter inside accepted checked us ws value o
    preSeparate postSeparate clean supported leftGood,
    sourceBody_open fallback parameter inside accepted checked us ws value o'
    preSeparate postSeparate clean supported rightGood]
  simp only [body]
  rw [accepted_scoped_congr fallback _ _ leftGood capturedAgree accepted checked _
    (clean_initial parameter clean) (initial_local inside supported).closed]

/-- Recursive answers inherit the checked support bound. This is proved
from the source, not assumed of an external whole-program execution. -/
theorem version_results {Γ : Decls} {scope : Finset String}
    (grounded : String → Bool) (fallback : Fallback) (parameter : String)
    (inside : parameter ∈ scope) (pre post : List (Ty Empty))
    {e : Expr} (accepted : UnifyingRegions.Accepted Γ e) (checked : check scope e = true)
    (returns : ReturnsPat (.var parameter) e) :
    ∀ fuel, OracleOn Γ grounded pre post scope (versionRun (sourceBody fallback parameter e pre.length) fuel)
  | 0, _, _, r, member => False.elim (Multiset.notMem_zero r member)
  | fuel + 1, args, allowed, r, member => by
      obtain ⟨us, value, ws, rfl, len, _, clean, _⟩ := allowed.1
      obtain ⟨⟨delta, rfl, safe⟩, supported⟩ := source_results grounded fallback parameter inside pre post
        accepted checked returns _ (version_results grounded fallback parameter inside pre post
          accepted checked returns fuel) us ws value len allowed r member
      exact ⟨uninterp_substA safe value clean, supported⟩

/-- At every recursive fuel, the actual captured source and typed protocol
have exactly the same answer bag. Open disjoint captures and unrelated
overloaded declarations are permitted; no global functionality is assumed. -/
theorem source_version_eq_protocol {Γ : Decls} {scope : Finset String}
    (grounded : String → Bool) (fallback : Fallback) (parameter typeVariable : String)
    (inside : parameter ∈ scope) (pre post : List (Ty Empty))
    {e : Expr} (accepted : UnifyingRegions.Accepted Γ e) (checked : check scope e = true)
    (returns : ReturnsPat (.var parameter) e) :
    ∀ fuel args, Admitted Γ grounded pre post scope args →
      protocolRun Γ grounded (sourceBody fallback parameter e pre.length)
          (arrow (pre.map Ty.lift ++ .var typeVariable :: post.map Ty.lift) (.var typeVariable)) fuel args =
        versionRun (sourceBody fallback parameter e pre.length) fuel args
  | 0, _, _ => rfl
  | fuel + 1, args, allowed => by
      have ih := source_version_eq_protocol grounded fallback parameter typeVariable inside pre post
        accepted checked returns fuel
      have sourceSame := source_congr grounded fallback parameter inside pre post accepted checked _ _
        (fun ws hws r member => by
          rw [ih ws hws] at member
          exact version_results grounded fallback parameter inside pre post accepted checked returns fuel ws hws r member)
        ih args allowed
      obtain ⟨us, value, ws, rfl, len, before, clean, after⟩ := allowed.1
      simp only [protocolRun, versionRun]
      rw [chainCall_congr _ _ sourceSame,
        UninterpretedLocalMultiplicity.pair_protocol_clean _ pre post typeVariable _ us ws value len clean
          (fun r member => (source_results grounded fallback parameter inside pre post accepted checked returns _
            (version_results grounded fallback parameter inside pre post accepted checked returns fuel)
            us ws value len allowed r member).1),
        argCount_of_entryFacts before, argCount_of_entryFacts after, mul_one, one_nsmul]

/-- The existing typed entry boundary precedes the optional dependency
check. A refusal executes the canonical protocol rather than losing answers. -/
noncomputable def offeredRun (Γ : Decls) (grounded : String → Bool) (fallback : Fallback)
    (parameter typeVariable : String) (pre post : List (Ty Empty)) (scope : Finset String)
    (e : Expr) (fuel : Nat) (input : CheckedInput Γ grounded pre post) : Multiset Atom :=
  if gate scope pre.length input.args then
    versionRun (sourceBody fallback parameter e pre.length) fuel input.args
  else
    protocolRun Γ grounded (sourceBody fallback parameter e pre.length)
      (arrow (pre.map Ty.lift ++ .var typeVariable :: post.map Ty.lift) (.var typeVariable)) fuel input.args

theorem offeredRun_eq_protocol {Γ : Decls} {scope : Finset String}
    (grounded : String → Bool) (fallback : Fallback) (parameter typeVariable : String)
    (inside : parameter ∈ scope) (pre post : List (Ty Empty))
    {e : Expr} (accepted : UnifyingRegions.Accepted Γ e) (checked : check scope e = true)
    (returns : ReturnsPat (.var parameter) e) (fuel : Nat)
    (input : CheckedInput Γ grounded pre post) :
    offeredRun Γ grounded fallback parameter typeVariable pre post scope e fuel input =
      protocolRun Γ grounded (sourceBody fallback parameter e pre.length)
        (arrow (pre.map Ty.lift ++ .var typeVariable :: post.map Ty.lift) (.var typeVariable)) fuel input.args := by
  unfold offeredRun
  split
  · exact (source_version_eq_protocol grounded fallback parameter typeVariable inside pre post
      accepted checked returns fuel input.args ⟨input.entry, ‹_›⟩).symm
  · rfl

namespace Controls

def declarations : Decls := CapturedUninterpretedRegions.Controls.withOverload
def fallback : Fallback := fun _ _ => 0
def known : Atom := .symbol "Known"
def one : Atom := .grounded (.int 1)
def input : Atom := .expression [.symbol "pair", .var "left", .var "right"]
def expected : Atom := .expression [.symbol "pair", .var "left", one]
def tagged : Ty Empty := .sym "Tagged"
def scope : Finset String := {"argument", "ignored", "first", "left", "right"}
def pattern : Pat := .ctor "pair" [.var "first", .const one]

/-- The call really recurses, then instantiates an old variable inside the
active argument, while the captured variable remains outside its scope. -/
def program : Expr := .ifE (.var "argument") (.var "argument")
  (.letE (.var "ignored") (.self [.const truth])
    (.letE pattern (.var "argument") (.var "argument")))

theorem pattern_clean : Uninterp declarations pattern.toAtom := by
  simp [pattern, Pat.toAtom, Pat.toAtoms, one, Uninterp, Safe, SafeAll,
    substA, HeadFree, declarations, CapturedUninterpretedRegions.Controls.withOverload,
    CapturedUninterpretedRegions.Controls.declarations]

theorem input_clean : Uninterp declarations input := by
  simp [input, Uninterp, Safe, SafeAll, substA, HeadFree, declarations,
    CapturedUninterpretedRegions.Controls.withOverload, CapturedUninterpretedRegions.Controls.declarations]

theorem program_accepted : UnifyingRegions.Accepted declarations program :=
  .ifE (.var "argument") (.var "argument")
    (.letE trivial (.self (.const truth trivial))
      (.letE pattern_clean (.var "argument") (.var "argument")))

theorem program_returns : ReturnsPat (.var "argument") program := .ifE .refl (.letE (.letE .refl))

theorem program_checked : check scope program = true := by decide +kernel

theorem open_gate_passes : gate scope 1 [.var "open", input, known] = true := by decide +kernel

theorem saved_frame_genuinely_open : support (Atom.var "open") ≠ ∅ := by decide +kernel

theorem open_entry (grounded : String → Bool) :
    UnintEntry declarations grounded [tagged] [tagged] [.var "open", input, known] := by
  have first : Holds declarations grounded (.var "open") tagged :=
    Holds.of_count (count_var declarations "open" tagged)
  have last : Holds declarations grounded known tagged := by
    apply Holds.of_count
    unfold known
    rw [count_symbol_closed declarations "Known" tagged (by rfl)]
    simp
  exact ⟨[.var "open"], input, [known], rfl, rfl, .cons (fun _ => first) .nil,
    input_clean, .cons (fun _ => last) .nil⟩

theorem open_recursive_execution :
    versionRun (sourceBody fallback "argument" program 1) 2 [.var "open", input, known] = {expected} := by
  cbv

/-- The preceding ground-only gate refuses this same input. The new
source-derived contract admits it even in an overloaded declaration space. -/
theorem open_recursive_protocol (grounded : String → Bool) (fuel : Nat) :
    ¬ Functional declarations ∧
      frameGate 1 [.var "open", input, known] = false ∧
      protocolRun declarations grounded (sourceBody fallback "argument" program 1)
          (arrow [tagged.lift, .var "t", tagged.lift] (.var "t")) fuel [.var "open", input, known] =
        versionRun (sourceBody fallback "argument" program 1) fuel [.var "open", input, known] := by
  refine ⟨CapturedUninterpretedRegions.Controls.overload_not_functional, by decide +kernel, ?_⟩
  exact source_version_eq_protocol grounded fallback "argument" "t" (by decide +kernel : "argument" ∈ scope)
    [tagged] [tagged] program_accepted program_checked program_returns fuel _
    ⟨open_entry grounded, open_gate_passes⟩

theorem overlapping_source_frame_rejected : gate scope 1 [.var "right", input, known] = false := by
  decide +kernel

def aliasScope : Finset String := {"source-b", "shared"}
def aliasProgram : Expr := .letE UnifyingFrames.Controls.pattern
  (.const UnifyingFrames.Controls.value) (.var "source-b")

/-- The local source checker and substitution-closure checker both pass.
The observed-frame check alone catches the indirect alias. -/
theorem indirect_alias_gate :
    check aliasScope aliasProgram = true ∧
      closureCheck aliasScope UnifyingFrames.Controls.aliases = true ∧
      Disjoint (support UnifyingFrames.Controls.frame) aliasScope ∧
      frameCheck aliasScope UnifyingFrames.Controls.aliases [UnifyingFrames.Controls.frame] = false := by
  decide +kernel

/-- Ignoring that refusal really changes the saved observation during the
actual expression run, not merely in a hypothetical unifier. -/
theorem indirect_alias_run_changes_saved_value :
    (evalUnifying fallback (fun _ => 0) aliasProgram UnifyingFrames.Controls.aliases).map
        (fun out => substA out.2 UnifyingFrames.Controls.frame) = {UnifyingFrames.Controls.value} ∧
      substA UnifyingFrames.Controls.aliases UnifyingFrames.Controls.frame = .var "shared" := by
  cbv

/-- A source variable whose current image leaves the finite scope is not
admitted just because its source name belongs to that scope. -/
theorem unclosed_alias_rejected :
    closureCheck ({"source-b"} : Finset String) UnifyingFrames.Controls.aliases = false := by
  decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OpenFrameSourceAdmission
