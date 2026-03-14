import Mettapedia.Languages.ProcessCalculi.MORK.WorkQueueOrder

/-!
# MORK: Work-Queue Scheduler Semantics

The faithful abstract semantics of MORK's `metta_calculus(steps)` scheduler.

## Real runtime behaviour (from Rust `metta_calculus` + `transform_multi_multi_o`)

1. **Pop** the next `(exec ...)` fact from the PathMap (sorted by serialized path)
2. **Remove** it from live space
3. **Read copy**: `live_after_remove ∪ {exec_fact}` — re-insert so the rule can match itself
4. **Match** the pattern against the read copy (all matches simultaneously)
5. **Apply** template outputs (add/remove) to live space (NOT to read copy)
6. **Repeat** until no more exec facts or step limit reached

## Design decisions

- **Abstract scheduler key**: we parameterize exec-fact ordering by a `SchedulerKey` function
  rather than committing to exact byte-level PathMap serialization.  A future refinement
  file can connect the abstract key to the concrete shortlex/PathMap order.

- **`ExecFact`**: an exec fact is just an `Atom` in the space that happens to be an
  `(exec loc pattern template)` expression.  We define `ExecFact` as a structured
  extraction from such an atom, mirroring the Rust `destruct!(rt, ("exec" loc pat tpl))`.

- **Read copy**: explicit in the formalization, matching the Rust
  `let mut read_copy = self.btm.clone(); read_copy.insert(add.span(), ());`.

## Relationship to ThreePhaseExec

`ThreePhaseExec.lean` defines a phase-band abstraction (priority ranges 0..31 / 32..63 /
64..95) that is a RESTRICTED VIEW of the scheduler.  The scheduler is the more fundamental
semantic layer.  A future refinement theorem should show that three-phase stepping is a
special case of work-queue execution with phase-aligned priorities.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## Exec fact extraction -/

/-- A structured exec fact extracted from an `(exec (priority name) pattern template)` atom.
    Mirrors the Rust `destruct!(rt, ("exec" loc pat_expr tpl_expr))`. -/
structure ExecFact where
  /-- The original atom in the space (for removal). -/
  atom     : Atom
  /-- The raw location term (for ordering). Preserved from the original atom. -/
  loc      : Atom
  /-- The structured rule extracted from the atom. -/
  rule     : ExecRule
  deriving Repr, DecidableEq

/-- Convert a digit character to its numeric value. -/
private def digitToNat : Char → Nat
  | '0' => 0 | '1' => 1 | '2' => 2 | '3' => 3 | '4' => 4
  | '5' => 5 | '6' => 6 | '7' => 7 | '8' => 8 | '9' => 9
  | _ => 0

/-- Kernel-reducible natural number parser over `List Char`.
    (`String.foldl` is C-backed and does not reduce definitionally.) -/
private def parseNatAux : List Char → Nat → Nat
  | [], acc => acc
  | c :: cs, acc => parseNatAux cs (acc * 10 + digitToNat c)

/-- Parse a numeric string to ℕ (returns 0 on failure). -/
private def parseNat (s : String) : Nat := parseNatAux s.toList 0

/-- Try to extract an `ExecFact` from an atom.
    Recognises the shape `(exec (priority name) (, p₁ ... pₙ) (O s₁ ... sₙ))`.

    This is a simplified extractor that handles the subset of exec atoms used in
    the conformance test suite.  A full extractor would parse arbitrary priority
    terms and sink types. -/
def extractExecFact (a : Atom) : Option ExecFact :=
  match a with
  | .expression (.symbol "exec" :: loc :: patExpr :: tplExpr :: []) =>
    -- Extract priority and name from loc
    let (prio, name) := match loc with
      | .expression [.grounded (.int p), .symbol n] => (p.toNat, n)
      | .expression [.symbol p, .symbol n]          => (parseNat p, n)
      | _ => (0, "unnamed")
    -- Extract pattern atoms (skip the leading `,` functor)
    let patAtoms := match patExpr with
      | .expression (.symbol "," :: rest) => rest
      | _ => []
    -- Extract sinks (skip the leading `O` functor)
    let sinks := match tplExpr with
      | .expression (.symbol "O" :: rest) =>
        rest.filterMap fun s => match s with
          | .expression [.symbol "+", body] => some (.add body)
          | .expression [.symbol "-", body] => some (.remove body)
          | .expression [.symbol "head", body] => some (.head body)
          | _ => none
      | _ => []
    some {
      atom := a
      loc  := loc
      rule := mkExecRule prio name (mkPattern patAtoms) (mkTemplate sinks)
    }
  | _ => none

/-- An exec fact with source-aware input specification. -/
structure SourceExecFact where
  /-- The original exec atom in the space. -/
  atom : Atom
  /-- The location term (priority + name). -/
  loc  : Atom
  /-- The structured source-aware rule. -/
  rule : SourceExecRule
  deriving Repr, DecidableEq

/-- Parse a list of source factors from `(I src₁ src₂ ...)` body. -/
def parseSourceFactors (args : List Atom) : List SourceFactor :=
  args.filterMap fun arg => match arg with
    | .expression [.symbol "BTM", pat] => some (.btm pat)
    | .expression [.symbol "==", pat, witness] => some (.eqConstraint pat witness)
    | .expression [.symbol "!=", pat, witness] => some (.neqConstraint pat witness)
    | _ => none

/-- Parse sinks from a template expression `(O sink₁ ...)`. -/
def parseSinks (tplExpr : Atom) : List Sink :=
  match tplExpr with
  | .expression (.symbol "O" :: rest) =>
    rest.filterMap fun s => match s with
      | .expression [.symbol "+", body] => some (.add body)
      | .expression [.symbol "-", body] => some (.remove body)
      | .expression [.symbol "head", body] => some (.head body)
      | _ => none
  | _ => match tplExpr with
    | .expression (.symbol "," :: rest) =>
      rest.map (.add ·)
    | _ => []

/-- Try to extract a `SourceExecFact` from an atom.
    Recognises both compat-mode `(exec loc (, ...) (O ...))` and
    explicit-source `(exec loc (I ...) (O ...))`.  -/
def extractSourceExecFact (a : Atom) : Option SourceExecFact :=
  match a with
  | .expression (.symbol "exec" :: loc :: inputExpr :: tplExpr :: []) =>
    let (prio, name) := match loc with
      | .expression [.grounded (.int p), .symbol n] => (p.toNat, n)
      | .expression [.symbol p, .symbol n]          => (parseNat p, n)
      | _ => (0, "unnamed")
    let sinks := parseSinks tplExpr
    let input := match inputExpr with
      | .expression (.symbol "I" :: rest) =>
        InputSpec.explicit (parseSourceFactors rest)
      | .expression (.symbol "," :: rest) =>
        InputSpec.compat (mkPattern rest)
      | _ => InputSpec.compat (mkPattern [])
    some {
      atom := a
      loc  := loc
      rule := ⟨prio, name, input, [], mkTemplate sinks⟩
    }
  | _ => none

/-- Convert a `SourceExecFact` to an `ExecFact` when the input is compat-mode. -/
def SourceExecFact.toExecFact? (sef : SourceExecFact) : Option ExecFact :=
  match sef.rule.input with
  | .compat pat => some ⟨sef.atom, sef.loc, mkExecRule sef.rule.priority sef.rule.name pat sef.rule.tmpl⟩
  | .explicit _ => none

/-! ## Abstract scheduler key -/

/-- A scheduler key assigns a lexicographic ordering to exec facts.
    In the real runtime, this is the serialized PathMap path (shortlex byte order).
    We abstract it as a `List ℕ` to avoid committing to byte-level details. -/
class SchedulerKey (α : Type) where
  key : α → List ℕ

/-- Location-based scheduler key: uses `atomKey` on the raw location term.
    Approximates PathMap byte ordering (expressions < symbols < variables,
    shorter before longer, then lexicographic). -/
instance : SchedulerKey ExecFact where
  key ef := atomKey ef.loc

/-- Select the minimum exec fact from a list by scheduler key. -/
def selectNextExec (facts : List ExecFact) : Option ExecFact :=
  facts.foldl (fun best ef =>
    match best with
    | none => some ef
    | some b =>
      if lexLt (SchedulerKey.key ef) (SchedulerKey.key b) then some ef else some b
  ) none

/-! ## Work-queue step -/

/-- Extract all exec facts from a space.
    Scans all atoms, returns those successfully parsed as exec facts. -/
noncomputable def execFactsOfSpace (s : Space) : List ExecFact :=
  s.toList.filterMap extractExecFact

/-- Remove an atom from the space (consume the exec fact from live). -/
def consumeExec (s : Space) (ef : ExecFact) : Space :=
  s.erase ef.atom

/-- Construct the read copy: live space (with exec removed) plus the exec fact re-inserted.
    This is the space against which patterns are matched.

    Mirrors Rust: `let mut read_copy = self.btm.clone(); read_copy.insert(add.span(), ());`
    where `add` is the exec fact that was just removed. -/
def readCopy (s : Space) (ef : ExecFact) : Space :=
  consumeExec s ef ∪ {ef.atom}

/-- Fire all matches of an exec fact's rule against the read copy,
    then apply template outputs to the live space (after exec removal).

    Returns the new live space.

    Key semantic point: matching happens against `readCopy`, but mutations
    apply to `consumeExec s ef` (the live space with exec consumed). -/
noncomputable def fireExecFact (s : Space) (ef : ExecFact) : Space :=
  let live := consumeExec s ef
  let rc := readCopy s ef
  let ms := matchPattern [] rc ef.rule.pat
  -- Apply all match results to the live space
  ms.foldl (fun acc (σ, _consumed) =>
    applySinks acc σ ef.rule.tmpl
  ) live

/-- One step of the work-queue scheduler:
    1. Extract exec facts from the space
    2. Select the one with minimum scheduler key
    3. Consume it from live
    4. Match against read copy
    5. Apply outputs to live

    Returns `none` if no exec facts remain (termination). -/
noncomputable def workQueueStep (s : Space) : Option Space :=
  let facts := execFactsOfSpace s
  match selectNextExec facts with
  | none => none
  | some ef => some (fireExecFact s ef)

/-- Fuel-bounded work-queue execution.
    Mirrors `metta_calculus(steps)` in the Rust runtime.
    Returns `(final_space, steps_taken)`. -/
noncomputable def workQueueRunN : ℕ → Space → Space × ℕ
  | 0, s => (s, 0)
  | fuel + 1, s =>
    match workQueueStep s with
    | none => (s, 0)
    | some s' =>
      let (final, n) := workQueueRunN fuel s'
      (final, n + 1)

/-! ## Source-aware work-queue firing

When exec facts carry `SourceExecRule`s, the firing path uses
`matchInputSpec` instead of `matchPattern`. -/

/-- Consume an atom from the space (generalized: only needs the atom). -/
noncomputable def consumeAtom (s : Space) (a : Atom) : Space := s.erase a

/-- Read copy from consuming an atom. -/
noncomputable def readCopyAtom (s : Space) (a : Atom) : Space :=
  consumeAtom s a ∪ {a}

/-- Fire a source-exec-fact: match its input spec against the read copy,
    then apply template sinks to the live space. -/
noncomputable def fireSourceExecFact (s : Space) (sef : SourceExecFact) : Space :=
  let live := consumeAtom s sef.atom
  let rc := readCopyAtom s sef.atom
  let ms := matchInputSpec [] rc sef.rule.input
  ms.foldl (fun acc (σ, _consumed) =>
    applySinks acc σ sef.rule.tmpl
  ) live

/-! ## Basic structural lemmas -/

/-- The read copy always contains the exec fact itself. -/
theorem readCopy_mem_exec (s : Space) (ef : ExecFact) :
    ef.atom ∈ readCopy s ef := by
  simp [readCopy]

/-- Consuming an exec fact removes it from the space (when present). -/
theorem consumeExec_not_mem (s : Space) (ef : ExecFact) :
    ef.atom ∉ consumeExec s ef := by
  simp [consumeExec]

/-- Consuming an exec fact preserves all other atoms. -/
theorem consumeExec_mem_other (s : Space) (ef : ExecFact) (a : Atom)
    (ha : a ∈ s) (hne : a ≠ ef.atom) :
    a ∈ consumeExec s ef := by
  simp [consumeExec]
  exact ⟨hne, ha⟩

/-- The read copy preserves all non-exec atoms from the original space. -/
theorem readCopy_mem_other (s : Space) (ef : ExecFact) (a : Atom)
    (ha : a ∈ s) (hne : a ≠ ef.atom) :
    a ∈ readCopy s ef := by
  simp [readCopy]
  exact Or.inr (consumeExec_mem_other s ef a ha hne)

/-- If the exec fact was in the space, the read copy has the same elements.
    (Removing then re-inserting = identity on membership.) -/
theorem readCopy_eq_of_mem (s : Space) (ef : ExecFact) (hm : ef.atom ∈ s) :
    readCopy s ef = s := by
  simp [readCopy, consumeExec]
  ext a
  simp [Finset.mem_erase]
  constructor
  · rintro (rfl | ⟨_, ha⟩)
    · exact hm
    · exact ha
  · intro ha
    by_cases h : a = ef.atom
    · left; exact h
    · right; exact ⟨h, ha⟩

/-- `workQueueStep` returns `none` iff no exec facts are in the space. -/
theorem workQueueStep_none_iff (s : Space) :
    workQueueStep s = none ↔ selectNextExec (execFactsOfSpace s) = none := by
  simp [workQueueStep]
  split <;> simp_all

/-- `workQueueRunN 0` is the identity. -/
theorem workQueueRunN_zero (s : Space) :
    workQueueRunN 0 s = (s, 0) := rfl

/-! ## Cardinality lemmas -/

/-- Consuming an exec fact strictly decreases space cardinality. -/
theorem consumeExec_card_lt (s : Space) (ef : ExecFact) (hm : ef.atom ∈ s) :
    (consumeExec s ef).card < s.card := by
  simp only [consumeExec]
  exact Finset.card_erase_lt_of_mem hm

/-- A template is remove-only (no add or head sinks). -/
def Template.isRemoveOnly (tmpl : Template) : Prop :=
  ∀ sink ∈ tmpl.sinks, ∃ a, sink = .remove a

/-- A single remove sink cannot increase space cardinality. -/
private theorem applySink_remove_card_le (s : Space) (σ : Subst) (a : Atom) :
    (applySink s σ (.remove a)).card ≤ s.card := by
  simp only [applySink]
  exact Finset.card_erase_le

/-- Remove-only templates cannot increase space cardinality. -/
theorem applySinks_removeOnly_card_le (s : Space) (σ : Subst) (sinks : List Sink)
    (hro : ∀ sink ∈ sinks, ∃ a, sink = .remove a) :
    (sinks.foldl (applySink · σ) s).card ≤ s.card := by
  induction sinks generalizing s with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    obtain ⟨a, ha⟩ := hro hd (by simp)
    subst ha
    calc (tl.foldl (applySink · σ) (applySink s σ (.remove a))).card
        ≤ (applySink s σ (.remove a)).card :=
          ih _ (fun sink hs => hro sink (List.mem_cons_of_mem _ hs))
      _ ≤ s.card := applySink_remove_card_le s σ a

/-! ## Termination under remove-only templates -/

/-- Under remove-only templates, `fireExecFact` strictly decreases cardinality.
    This guarantees scheduler termination: the space shrinks at every step,
    so the scheduler must halt within `s.card` steps.

    The proof combines:
    - `consumeExec_card_lt`: consuming the exec fact strictly decreases cardinality
    - `applySinks_removeOnly_card_le`: remove-only sinks cannot increase cardinality
    - The foldl over matches only applies `applySinks`, which is also non-increasing -/
theorem fireExecFact_card_lt_of_removeOnly (s : Space) (ef : ExecFact)
    (hm : ef.atom ∈ s)
    (hro : Template.isRemoveOnly ef.rule.tmpl) :
    (fireExecFact s ef).card < s.card := by
  simp only [fireExecFact]
  -- The live space after consuming ef has strictly smaller cardinality
  have hlive : (consumeExec s ef).card < s.card := consumeExec_card_lt s ef hm
  -- Each applySinks with remove-only sinks is non-increasing
  suffices h : ∀ (ms : List (Subst × Finset Atom)) (acc : Space),
      acc.card ≤ (consumeExec s ef).card →
      (ms.foldl (fun a (σ, _) => applySinks a σ ef.rule.tmpl) acc).card ≤
        (consumeExec s ef).card by
    exact Nat.lt_of_le_of_lt (h _ _ le_rfl) hlive
  intro ms
  induction ms with
  | nil => intro acc hacc; simpa
  | cons m rest ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    apply ih
    calc (applySinks acc m.1 ef.rule.tmpl).card
        = (ef.rule.tmpl.sinks.foldl (applySink · m.1) acc).card := by rfl
      _ ≤ acc.card := applySinks_removeOnly_card_le acc m.1 ef.rule.tmpl.sinks hro
      _ ≤ (consumeExec s ef).card := hacc

/-- `workQueueRunN` takes at most `fuel` steps (general bound). -/
theorem workQueueRunN_steps_le_fuel (fuel : ℕ) (s : Space) :
    (workQueueRunN fuel s).2 ≤ fuel := by
  induction fuel generalizing s with
  | zero => simp [workQueueRunN]
  | succ n ih =>
    simp only [workQueueRunN]
    match workQueueStep s with
    | none => simp
    | some s' =>
      simp only
      exact Nat.succ_le_succ (ih s')

/-! ## Computable reference scheduler

The spec-level `workQueueStep` uses `Finset.toList` and is noncomputable.
For conformance testing, we mirror the scheduler over `List Atom`. -/

namespace WQComputable

open Conformance.Computable (CSpace cmatchPattern capplySinks cmatchAtom cmatchAtomList
  cmatchInputSpec)

/-- Extract exec facts from a computable (List Atom) space. -/
def cExecFacts (s : List Atom) : List ExecFact :=
  s.filterMap extractExecFact

/-- Consume an exec fact from a computable space (removes first occurrence). -/
def cConsumeExec (s : List Atom) (ef : ExecFact) : List Atom :=
  s.erase ef.atom

/-- Computable read copy: remove exec fact, then re-add it at the head. -/
def cReadCopy (s : List Atom) (ef : ExecFact) : List Atom :=
  ef.atom :: cConsumeExec s ef

/-- Fire all matches of an exec fact against the read copy,
    applying template outputs to the live space. -/
def cFireExecFact (s : List Atom) (ef : ExecFact) : List Atom :=
  let live := cConsumeExec s ef
  let rc := cReadCopy s ef
  let ms := cmatchPattern [] rc ef.rule.pat
  ms.foldl (fun acc (σ, _consumed) =>
    capplySinks acc σ ef.rule.tmpl
  ) live

/-- One computable work-queue step. -/
def cWorkQueueStep (s : List Atom) : Option (List Atom) :=
  match selectNextExec (cExecFacts s) with
  | none => none
  | some ef => some (cFireExecFact s ef)

/-- Fuel-bounded computable work-queue execution. -/
def cWorkQueueRunN : ℕ → List Atom → List Atom × ℕ
  | 0, s => (s, 0)
  | fuel + 1, s =>
    match cWorkQueueStep s with
    | none => (s, 0)
    | some s' =>
      let (final, n) := cWorkQueueRunN fuel s'
      (final, n + 1)

/-- Computable: extract all source-exec-facts from a list space. -/
def cSourceExecFacts (s : List Atom) : List SourceExecFact :=
  s.filterMap extractSourceExecFact

/-- Computable: fire a source-exec-fact against the read copy. -/
def cFireSourceExecFact (s : List Atom) (sef : SourceExecFact) : List Atom :=
  let live := s.erase sef.atom
  let rc := sef.atom :: live
  let ms := cmatchInputSpec [] rc sef.rule.input
  ms.foldl (fun acc (σ, _consumed) =>
    capplySinks acc σ sef.rule.tmpl
  ) live

end WQComputable

/-! ## Scheduler correspondence

The computable `cWorkQueueStep` and the spec-level `workQueueStep` compute
the same result (up to `toFinset`) when exec-fact extraction produces the
same elements.  The key invariant: `selectNextExec` picks the minimum by
`lexLt`, which is permutation-invariant. -/

section SchedulerCorrespondence

open WQComputable

/-- Key injectivity: no two distinct exec facts share the same scheduler key. -/
def KeyInjective (l : List ExecFact) : Prop :=
  ∀ a b, a ∈ l → b ∈ l → SchedulerKey.key a = SchedulerKey.key b → a = b

/-- The fold step function for `selectNextExec`. -/
private def sneFold (best : Option ExecFact) (ef : ExecFact) : Option ExecFact :=
  match best with
  | none => some ef
  | some b => if lexLt (SchedulerKey.key ef) (SchedulerKey.key b) then some ef else some b

@[simp] private theorem sneFold_none (ef : ExecFact) : sneFold none ef = some ef := rfl
@[simp] private theorem sneFold_some (b ef : ExecFact) :
    sneFold (some b) ef = if lexLt (SchedulerKey.key ef) (SchedulerKey.key b) then some ef else some b := rfl

/-- Helper: the foldl step picks the minimum by lexLt. Two adjacent elements
    can be swapped without changing the result, provided distinct keys.

    This is the key commutativity lemma for permutation invariance of `selectNextExec`. -/
private theorem sneFold_comm (x y : ExecFact)
    (hdist : SchedulerKey.key x ≠ SchedulerKey.key y ∨ x = y)
    (init : Option ExecFact) :
    sneFold (sneFold init x) y = sneFold (sneFold init y) x := by
  cases init with
  | none =>
    dsimp only [sneFold]
    cases hyx : lexLt (SchedulerKey.key y) (SchedulerKey.key x) <;>
    cases hxy : lexLt (SchedulerKey.key x) (SchedulerKey.key y) <;>
    simp_all
    · exact hdist.elim (absurd (lexLt_eq_of_not_both _ _ hxy hyx)) id
    · exact absurd (lexLt_asymm _ _ hyx) (by simp [hxy])
  | some b =>
    dsimp only [sneFold]
    cases hxb : lexLt (SchedulerKey.key x) (SchedulerKey.key b) <;>
    cases hyb : lexLt (SchedulerKey.key y) (SchedulerKey.key b) <;>
    cases hyx : lexLt (SchedulerKey.key y) (SchedulerKey.key x) <;>
    cases hxy : lexLt (SchedulerKey.key x) (SchedulerKey.key y) <;>
    simp_all <;>
    first
    | (rw [lexLt_asymm _ _ hxy] at hyx; exact Bool.noConfusion hyx)
    | (rw [lexLt_trans _ _ _ hxy hyb] at hxb; exact Bool.noConfusion hxb)
    | (rw [lexLt_trans _ _ _ hyx hxb] at hyb; exact Bool.noConfusion hyb)
    | (exact hdist.elim (absurd (lexLt_eq_of_not_both _ _ hxy hyx)) id)

/-- Helper: foldl with `sneFold` is permutation-invariant under key injectivity. -/
private theorem selectNextExec_foldl_perm_aux
    (l₁ l₂ : List ExecFact) (hp : l₁.Perm l₂)
    (hinj : KeyInjective l₁)
    (init : Option ExecFact) :
    l₁.foldl sneFold init = l₂.foldl sneFold init := by
  induction hp generalizing init with
  | nil => rfl
  | cons x _ ih =>
    simp only [List.foldl]
    apply ih
    intro a b ha hb
    exact hinj a b (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb)
  | swap x y l =>
    simp only [List.foldl]
    have hdist : SchedulerKey.key x ≠ SchedulerKey.key y ∨ x = y := by
      by_cases h : SchedulerKey.key x = SchedulerKey.key y
      · right
        exact hinj x y (by simp) (by simp) h
      · left; exact h
    rw [sneFold_comm x y hdist init]
  | trans hp1 hp2 ih1 ih2 =>
    rename_i la lb lc
    have hinj_mid : KeyInjective lb := by
      intro a b ha hb
      exact hinj a b (hp1.mem_iff.mpr ha) (hp1.mem_iff.mpr hb)
    exact (ih1 hinj init).trans (ih2 hinj_mid init)

/-- `selectNextExec` is permutation-invariant under key injectivity:
    reordering the input list does not change which exec fact is selected,
    provided all exec facts have distinct scheduler keys. -/
theorem selectNextExec_perm (l₁ l₂ : List ExecFact) (hp : l₁.Perm l₂)
    (hinj : KeyInjective l₁) :
    selectNextExec l₁ = selectNextExec l₂ := by
  unfold selectNextExec
  exact selectNextExec_foldl_perm_aux l₁ l₂ hp hinj none

/-- Under `Nodup`, the computable exec-fact list is a permutation of the
    spec-level exec-fact list.  This bridges `cExecFacts s` (computable) with
    `execFactsOfSpace s.toFinset` (noncomputable, uses `Finset.toList`). -/
theorem cExecFacts_perm_execFacts (s : List Atom) (hnd : s.Nodup) :
    (cExecFacts s).Perm (execFactsOfSpace s.toFinset) := by
  unfold cExecFacts execFactsOfSpace
  exact (List.toFinset_toList hnd).filterMap extractExecFact |>.symm

/-- The computable scheduler selects the same exec fact as the spec-level
    scheduler, provided the input space has no duplicates and all exec facts
    have distinct scheduler keys. -/
theorem cWorkQueueStep_selectExec_eq (s : List Atom) (hnd : s.Nodup)
    (hinj : KeyInjective (cExecFacts s)) :
    selectNextExec (cExecFacts s) = selectNextExec (execFactsOfSpace s.toFinset) := by
  exact selectNextExec_perm _ _ (cExecFacts_perm_execFacts s hnd) hinj

/-- `extractExecFact` preserves the original atom in the `.atom` field. -/
theorem extractExecFact_atom (a : Atom) (ef : ExecFact)
    (h : extractExecFact a = some ef) : ef.atom = a := by
  unfold extractExecFact at h
  split at h
  · simp at h; exact congr_arg ExecFact.atom h.symm
  · simp at h

/-- Two atoms extracting to the same ExecFact must be identical. -/
theorem extractExecFact_injective (a₁ a₂ : Atom) (ef : ExecFact)
    (h1 : extractExecFact a₁ = some ef) (h2 : extractExecFact a₂ = some ef) :
    a₁ = a₂ :=
  (extractExecFact_atom a₁ ef h1).symm.trans (extractExecFact_atom a₂ ef h2)

/-! ## cConsumeExec / cReadCopy correspondence -/

/-- List erase = Finset erase under Nodup. -/
theorem cConsumeExec_toFinset (s : List Atom) (ef : ExecFact) (hnd : s.Nodup) :
    (cConsumeExec s ef).toFinset = consumeExec s.toFinset ef := by
  simp only [cConsumeExec, consumeExec]
  ext x
  simp only [List.mem_toFinset, Finset.mem_erase]
  constructor
  · intro hx
    exact ⟨fun heq => absurd (heq ▸ hx) (List.Nodup.not_mem_erase hnd),
           List.mem_of_mem_erase hx⟩
  · intro ⟨hne, hx_mem⟩
    exact (List.mem_erase_of_ne hne).mpr hx_mem

/-- Computable read copy = spec read copy under Nodup. -/
theorem cReadCopy_toFinset (s : List Atom) (ef : ExecFact) (hnd : s.Nodup) :
    (cReadCopy s ef).toFinset = readCopy s.toFinset ef := by
  simp only [cReadCopy, readCopy]
  rw [List.toFinset_cons, cConsumeExec_toFinset s ef hnd]
  ext x; simp [Finset.mem_insert]

/-! ## cFireExecFact correspondence (single-match case)

The general multi-match case requires tracking `NodupSafe` through each foldl
step (the accumulator changes after each sink application) and aligning the
order of match results between computable and spec levels.  The single-match
case avoids both issues: foldl over a singleton is just one application.

This covers the common case in MORK: a rule with a conjunctive pattern that
matches at most one way against the space. -/

open Conformance.Computable (cmatchPattern capplySinks)
open Conformance (NodupSafe FoldNodupSafe foldl_capplySinks_toFinset)

/-- Single-match correspondence: when the computable matcher returns exactly one
    result, `cFireExecFact` and `fireExecFact` agree at the `toFinset` level.

    The key precondition is that the spec-level matcher also returns exactly one
    result that corresponds to the computable result. This is ensured by
    `hmatch_spec_eq` which states the spec match result is the singleton list
    containing the `toFinset`-lifted computable result. -/
theorem cFireExecFact_toFinset_single (s : List Atom) (ef : ExecFact)
    (hnd : s.Nodup) (hm : ef.atom ∈ s)
    (σ : Subst) (consumed : List Atom)
    (hmatch_c : cmatchPattern [] (cReadCopy s ef) ef.rule.pat = [(σ, consumed)])
    (hmatch_spec_eq : matchPattern [] s.toFinset ef.rule.pat = [(σ, consumed.toFinset)])
    (hsafe : NodupSafe (cConsumeExec s ef) σ ef.rule.tmpl.sinks) :
    (cFireExecFact s ef).toFinset = fireExecFact s.toFinset ef := by
  simp only [cFireExecFact, fireExecFact]
  rw [hmatch_c, List.foldl_cons, List.foldl_nil]
  rw [readCopy_eq_of_mem s.toFinset ef (by rwa [List.mem_toFinset])]
  rw [hmatch_spec_eq, List.foldl_cons, List.foldl_nil]
  -- Goal: (capplySinks (cConsumeExec s ef) σ ef.rule.tmpl).toFinset =
  --       applySinks (consumeExec s.toFinset ef) σ ef.rule.tmpl
  have h := Conformance.capplySinks_toFinset_safe (cConsumeExec s ef) σ ef.rule.tmpl hsafe
  rw [h, cConsumeExec_toFinset s ef hnd]

/-- No-match case: when the computable matcher returns no results,
    both `cFireExecFact` and `fireExecFact` reduce to consuming the exec fact. -/
theorem cFireExecFact_toFinset_empty (s : List Atom) (ef : ExecFact)
    (hnd : s.Nodup) (hm : ef.atom ∈ s)
    (hmatch_c : cmatchPattern [] (cReadCopy s ef) ef.rule.pat = [])
    (hmatch_spec_eq : matchPattern [] s.toFinset ef.rule.pat = []) :
    (cFireExecFact s ef).toFinset = fireExecFact s.toFinset ef := by
  simp only [cFireExecFact, fireExecFact]
  rw [hmatch_c, List.foldl_nil]
  rw [readCopy_eq_of_mem s.toFinset ef (by rwa [List.mem_toFinset])]
  rw [hmatch_spec_eq, List.foldl_nil]
  exact cConsumeExec_toFinset s ef hnd

/-! ## General multi-match cFireExecFact correspondence

The general case lifts the single-match theorem to arbitrarily many match results,
requiring explicit alignment of match results (`hcorr`) and `FoldNodupSafe`
throughout the fold.  This covers all MORK rule patterns. -/

/-- General multi-match `cFireExecFact` correspondence.
    Requires that computable and spec matchers return corresponding substitutions
    in the same order, and that `FoldNodupSafe` holds throughout the fold. -/
theorem cFireExecFact_toFinset (s : List Atom) (ef : ExecFact)
    (hnd : s.Nodup) (hm : ef.atom ∈ s)
    (hcorr : let cms := cmatchPattern [] (cReadCopy s ef) ef.rule.pat
             let sms := matchPattern [] s.toFinset ef.rule.pat
             cms.length = sms.length ∧
             ∀ (i : ℕ) (hi_c : i < cms.length) (hi_s : i < sms.length),
               cms[i].1 = sms[i].1)
    (hsafe : FoldNodupSafe (cConsumeExec s ef)
               (cmatchPattern [] (cReadCopy s ef) ef.rule.pat) ef.rule.tmpl) :
    (cFireExecFact s ef).toFinset = fireExecFact s.toFinset ef := by
  simp only [cFireExecFact, fireExecFact]
  rw [readCopy_eq_of_mem s.toFinset ef (by rwa [List.mem_toFinset])]
  exact foldl_capplySinks_toFinset
    (cConsumeExec s ef) (consumeExec s.toFinset ef) ef.rule.tmpl
    (cmatchPattern [] (cReadCopy s ef) ef.rule.pat)
    (matchPattern [] s.toFinset ef.rule.pat)
    (cConsumeExec_toFinset s ef hnd)
    hcorr.1
    hcorr.2
    hsafe

/-! ## Work-queue step correspondence -/

/-- Work-queue step correspondence: if the per-firing invariants hold for the
    selected exec fact, the computable and spec work-queue steps agree. -/
theorem cWorkQueueStep_toFinset (s : List Atom) (hnd : s.Nodup)
    (hinj : KeyInjective (cExecFacts s))
    (hfire : ∀ ef, selectNextExec (cExecFacts s) = some ef →
      ef.atom ∈ s ∧
      (let cms := cmatchPattern [] (cReadCopy s ef) ef.rule.pat
       let sms := matchPattern [] s.toFinset ef.rule.pat
       cms.length = sms.length ∧
       ∀ (i : ℕ) (hi_c : i < cms.length) (hi_s : i < sms.length),
         cms[i].1 = sms[i].1) ∧
      FoldNodupSafe (cConsumeExec s ef)
        (cmatchPattern [] (cReadCopy s ef) ef.rule.pat) ef.rule.tmpl) :
    (cWorkQueueStep s).map List.toFinset = workQueueStep s.toFinset := by
  simp only [cWorkQueueStep, workQueueStep]
  rw [← cWorkQueueStep_selectExec_eq s hnd hinj]
  match h : selectNextExec (cExecFacts s) with
  | none => simp
  | some ef =>
    simp only [Option.map]
    obtain ⟨hm, hcorr, hsafe⟩ := hfire ef h
    exact congrArg some (cFireExecFact_toFinset s ef hnd hm ⟨hcorr.1, hcorr.2⟩ hsafe)

/-! ## Work-queue bounded-run correspondence -/

/-- Invariant for work-queue step correspondence.
    Bundles all per-step requirements: Nodup, KeyInjective, and firing alignment. -/
structure WorkQueueInvariant (s : List Atom) : Prop where
  nodup : s.Nodup
  keyInj : KeyInjective (cExecFacts s)
  fire : ∀ ef, selectNextExec (cExecFacts s) = some ef →
    ef.atom ∈ s ∧
    (let cms := cmatchPattern [] (cReadCopy s ef) ef.rule.pat
     let sms := matchPattern [] s.toFinset ef.rule.pat
     cms.length = sms.length ∧
     ∀ (i : ℕ) (hi_c : i < cms.length) (hi_s : i < sms.length),
       cms[i].1 = sms[i].1) ∧
    FoldNodupSafe (cConsumeExec s ef)
      (cmatchPattern [] (cReadCopy s ef) ef.rule.pat) ef.rule.tmpl

/-- The set of list-spaces reachable from `s₀` in at most `fuel` computable steps. -/
inductive CReachable : ℕ → List Atom → List Atom → Prop where
  | refl : CReachable fuel s s
  | step {fuel s s' s''} :
      cWorkQueueStep s = some s' → CReachable fuel s' s'' →
      CReachable (fuel + 1) s s''

/-- Bounded-run correspondence: if the `WorkQueueInvariant` holds at every
    reachable state, computable and spec schedulers produce corresponding results.

    This makes the invariant-maintenance burden explicit: the caller must show that
    every intermediate state satisfies `WorkQueueInvariant`.  For finite-state MORK
    programs (the common case), this can be verified by exhaustive enumeration. -/
theorem cWorkQueueRunN_toFinset (fuel : ℕ) (s : List Atom)
    (hinv : ∀ s', CReachable fuel s s' → WorkQueueInvariant s') :
    (cWorkQueueRunN fuel s).1.toFinset = (workQueueRunN fuel s.toFinset).1 ∧
    (cWorkQueueRunN fuel s).2 = (workQueueRunN fuel s.toFinset).2 := by
  induction fuel generalizing s with
  | zero => simp [cWorkQueueRunN, workQueueRunN]
  | succ fuel ih =>
    simp only [cWorkQueueRunN, workQueueRunN]
    have winv := hinv s .refl
    have hstep := cWorkQueueStep_toFinset s winv.nodup winv.keyInj winv.fire
    match hc : cWorkQueueStep s with
    | none =>
      simp only [hc] at hstep
      simp only [Option.map] at hstep ⊢
      rw [← hstep]; exact ⟨rfl, rfl⟩
    | some s' =>
      simp only [hc, Option.map] at hstep
      have hspec : workQueueStep s.toFinset = some s'.toFinset := by rw [← hstep]
      simp only [hspec]
      have hinv' : ∀ s'', CReachable fuel s' s'' → WorkQueueInvariant s'' :=
        fun s'' hreach => hinv s'' (.step hc hreach)
      obtain ⟨h1, h2⟩ := ih s' hinv'
      exact ⟨h1, congrArg (· + 1) h2⟩

end SchedulerCorrespondence

/-! ## Conformance canaries

These test the work-queue scheduler against known MORK outputs.
All proofs are `rfl` (kernel-checked). -/

section Canaries

-- API typechecks
#check @extractExecFact
#check @selectNextExec
#check @workQueueStep
#check @workQueueRunN
#check @readCopy_mem_exec
#check @readCopy_eq_of_mem

open WQComputable

/-! ### Canary 1: exec fact extraction

An `(exec (0 process) (, (task $x)) (O (+ (done $x)) (- (task $x))))` atom
is correctly parsed into an `ExecFact`. -/

private def canary1_exec : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "process"],
    .expression [.symbol ",", .expression [.symbol "task", .var "x"]],
    .expression [.symbol "O",
      .expression [.symbol "+", .expression [.symbol "done", .var "x"]],
      .expression [.symbol "-", .expression [.symbol "task", .var "x"]]]]

/-- Exec fact extraction succeeds on a well-formed exec atom. -/
theorem canary1_extract_some :
    (extractExecFact canary1_exec).isSome = true := rfl

/-- Extracted rule has correct name. -/
theorem canary1_name :
    (extractExecFact canary1_exec).map (·.rule.name) = some "process" := rfl

/-- Extracted rule has correct priority. -/
theorem canary1_priority :
    (extractExecFact canary1_exec).map (·.rule.priority) = some 0 := rfl

/-- Non-exec atoms are not extracted. -/
theorem canary1_non_exec :
    extractExecFact (.expression [.symbol "task", .symbol "a"]) = none := rfl

/-! ### Canary 2: Single-step work-queue execution

Space: `(task a)` + the exec rule.
One work-queue step should consume the exec fact, match `(task a)`, and produce `(done a)`.

This tests the full pipeline: extraction → selection → read-copy → match → apply. -/

private def canary2_task : Atom := .expression [.symbol "task", .symbol "a"]

private def canary2_space : List Atom := [canary2_task, canary1_exec]

/-- The work-queue scheduler fires the exec rule and produces `(done a)`. -/
theorem canary2_one_step :
    cWorkQueueStep canary2_space =
      some [.expression [.symbol "done", .symbol "a"]] := rfl

/-! ### Canary 3: Read-copy self-matching

A self-respawning rule pattern-matches its own exec atom via the read copy.

```mm2
(exec (0 self)
  (, (exec (0 self) $ps $cs) (trigger))
  (O (+ (exec (0 self) $ps $cs))
     (+ (fired))
     (- (trigger))))
```

The rule matches itself because the exec atom is re-inserted into the read copy.
Without read-copy, the rule would never match (it was removed from live). -/

private def canary3_exec : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "self"],
    .expression [.symbol ",",
      .expression [.symbol "exec",
        .expression [.symbol "0", .symbol "self"],
        .var "ps", .var "cs"],
      .expression [.symbol "trigger"]],
    .expression [.symbol "O",
      .expression [.symbol "+",
        .expression [.symbol "exec",
          .expression [.symbol "0", .symbol "self"],
          .var "ps", .var "cs"]],
      .expression [.symbol "+", .expression [.symbol "fired"]],
      .expression [.symbol "-", .expression [.symbol "trigger"]]]]

private def canary3_space : List Atom :=
  [canary3_exec, .expression [.symbol "trigger"]]

/-- Read copy contains the exec atom after consumption.
    We extract the exec fact and verify the read copy has it. -/
theorem canary3_readcopy_has_exec :
    match cExecFacts canary3_space with
    | ef :: _ => (cReadCopy canary3_space ef).contains canary3_exec = true
    | [] => False := rfl

/-- The self-referential rule fires and produces `(fired)`, but the respawned exec
    is rejected by `isGroundAtom` because `$ps`/`$cs` substitute to atoms containing
    `.var` nodes. In MORK's byte representation, captured bytes are always ground.
    This is a known modeling gap: coreferential byte-capture is not faithfully
    represented by Lean's `Atom.var` constructor. -/
theorem canary3_coreferential_gap :
    cWorkQueueStep canary3_space =
      some [.expression [.symbol "fired"]] := rfl

/-! ### Canary 4: Priority ordering

Two exec rules at different priorities. The lower-priority rule fires first.
After consuming `(ready)`, the higher-priority rule fires but finds no match. -/

private def canary4_rule0 : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "first"],
    .expression [.symbol ",", .expression [.symbol "ready"]],
    .expression [.symbol "O",
      .expression [.symbol "+", .expression [.symbol "result", .symbol "first"]],
      .expression [.symbol "-", .expression [.symbol "ready"]]]]

private def canary4_rule1 : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "1", .symbol "second"],
    .expression [.symbol ",", .expression [.symbol "ready"]],
    .expression [.symbol "O",
      .expression [.symbol "+", .expression [.symbol "result", .symbol "second"]],
      .expression [.symbol "-", .expression [.symbol "ready"]]]]

private def canary4_space : List Atom :=
  [.expression [.symbol "ready"], canary4_rule1, canary4_rule0]

/-- Priority 0 fires first, producing `(result first)` and consuming `(ready)`. -/
theorem canary4_priority_step1 :
    cWorkQueueStep canary4_space =
      some [canary4_rule1,
            .expression [.symbol "result", .symbol "first"]] := rfl

/-- After both rules are consumed, only the first result remains.
    Priority 1 fired but found no match (ready already consumed). -/
theorem canary4_priority_full :
    cWorkQueueRunN 2 canary4_space =
      ([.expression [.symbol "result", .symbol "first"]], 2) := rfl

/-! ### Canary 5: Conjunctive match via work queue

An exec rule with a conjunctive pattern `(, (left $x) (right $y))` fires
against the read copy. Both data atoms are consumed; only the joined result
remains.  Tests full pipeline: extraction → scheduling → read-copy → match → apply. -/

private def canary5_exec : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "join"],
    .expression [.symbol ",",
      .expression [.symbol "left", .var "x"],
      .expression [.symbol "right", .var "y"]],
    .expression [.symbol "O",
      .expression [.symbol "+", .expression [.symbol "pair", .var "x", .var "y"]],
      .expression [.symbol "-", .expression [.symbol "left", .var "x"]],
      .expression [.symbol "-", .expression [.symbol "right", .var "y"]]]]

private def canary5_space : List Atom :=
  [canary5_exec,
   .expression [.symbol "left", .symbol "a"],
   .expression [.symbol "right", .symbol "b"]]

/-- Full pipeline: exec consumed, conjunctive match fires, result is `(pair a b)`. -/
theorem canary5_conjunctive_wq :
    cWorkQueueStep canary5_space =
      some [.expression [.symbol "pair", .symbol "a", .symbol "b"]] := rfl

/-- `cWorkQueueRunN` terminates after 1 step (no more exec facts). -/
theorem canary5_terminates :
    cWorkQueueRunN 10 canary5_space =
      ([.expression [.symbol "pair", .symbol "a", .symbol "b"]], 1) := rfl

/-! ### Canary 6: Read-copy enables self-matching

The read copy re-inserts the exec atom after consumption, making the consumed
list strictly shorter than the read copy. This is what enables the bootstrap
pattern: the rule can match itself through the read copy. -/

/-- Read copy re-inserts the exec atom: the first extracted exec fact's read copy
    contains the exec fact itself (checked via `List.contains`). -/
theorem canary3_readcopy_contains_exec :
    match cExecFacts canary3_space with
    | ef :: _ => (cReadCopy canary3_space ef).contains ef.atom = true
    | [] => True := rfl

/-! ### Canary 7: Location-based ordering via atomKey

Verify that the scheduler selects exec facts by `atomKey` on the location term,
producing the same results as the old priority-based ordering. -/

/-- Extracted exec fact preserves the raw location term. -/
theorem canary1_loc :
    (extractExecFact canary1_exec).map (·.loc) =
      some (.expression [.symbol "0", .symbol "process"]) := rfl

/-- Priority ordering still works under location-based keys:
    `atomKey (0 first)` < `atomKey (1 second)`. -/
theorem canary4_loc_order :
    lexLt (atomKey (.expression [.symbol "0", .symbol "first"]))
          (atomKey (.expression [.symbol "1", .symbol "second"])) = true := rfl

/-! ### Canary 8: Ground self-respawn

A rule that matches `(trigger)`, removes it, adds `(fired)`, and re-adds itself
as a ground literal (no variables in the re-add sink). This models the ground
self-respawn pattern: the exec atom persists after firing.

Unlike canary 3 (coreferential self-matching via `$ps`/`$cs`), this rule uses
a fully ground `(+)` sink that literally re-adds the entire exec atom. The
exec atom is ground because the pattern only contains `(trigger)` (no variables
captured into the re-add sink).

```mm2
(exec (0 persist)
  (, (trigger))
  (O (+ (fired))
     (- (trigger))
     (+ (exec (0 persist) (, (trigger)) (O (+ (fired)) (- (trigger)) (+ ...))))))
```

We approximate with a simpler ground rule where the re-add is the full exec atom. -/

private def canary8_exec : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "persist"],
    .expression [.symbol ",", .expression [.symbol "trigger"]],
    .expression [.symbol "O",
      .expression [.symbol "+", .expression [.symbol "fired"]],
      .expression [.symbol "-", .expression [.symbol "trigger"]]]]

private def canary8_exec_with_respawn : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "persist"],
    .expression [.symbol ",", .expression [.symbol "trigger"]],
    .expression [.symbol "O",
      .expression [.symbol "+", .expression [.symbol "fired"]],
      .expression [.symbol "-", .expression [.symbol "trigger"]],
      .expression [.symbol "+", canary8_exec]]]

private def canary8_space : List Atom :=
  [canary8_exec_with_respawn, .expression [.symbol "trigger"]]

/-- Ground self-respawn: after one step, `(fired)` is added and the exec atom
    `canary8_exec` is re-added by the ground `(+)` sink.  The re-added exec lacks
    the respawn sink (it's `canary8_exec`, not `canary8_exec_with_respawn`), so this
    models a one-shot ground respawn. -/
theorem canary8_ground_self_respawn :
    cWorkQueueStep canary8_space =
      some [.expression [.symbol "fired"], canary8_exec] := rfl

/-- After a second step, the re-added `canary8_exec` fires but finds no `(trigger)`.
    No match → exec consumed with no replacement.  Only `(fired)` remains. -/
theorem canary8_second_step_no_match :
    cWorkQueueRunN 2 canary8_space =
      ([.expression [.symbol "fired"]], 2) := rfl

/-! ### Canary 9: Source-aware extraction

Verify that `extractSourceExecFact` correctly parses both compat-mode `(, ...)`
and explicit-mode `(I ...)` exec atoms. -/

/-- Compat-mode exec atom extracts with `InputSpec.compat`. -/
theorem canary9_compat_extraction :
    (extractSourceExecFact canary1_exec).isSome = true := rfl

/-- Compat-mode extraction produces a compat InputSpec. -/
theorem canary9_compat_input :
    (extractSourceExecFact canary1_exec).bind
      (fun sef => match sef.rule.input with
        | .compat _ => some true
        | .explicit _ => some false) = some true := rfl

/-- Explicit-mode `(I (BTM pat))` exec atom. -/
private def canary9_explicit_exec : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "src-test"],
    .expression [.symbol "I",
      .expression [.symbol "BTM",
        .expression [.symbol "data", .var "x"]]],
    .expression [.symbol "O",
      .expression [.symbol "+",
        .expression [.symbol "found", .var "x"]]]]

/-- Explicit-mode extracts successfully. -/
theorem canary9_explicit_extraction :
    (extractSourceExecFact canary9_explicit_exec).isSome = true := rfl

/-- Explicit-mode extraction produces an explicit InputSpec. -/
theorem canary9_explicit_input :
    (extractSourceExecFact canary9_explicit_exec).bind
      (fun sef => match sef.rule.input with
        | .compat _ => some false
        | .explicit _ => some true) = some true := rfl

/-! ### Canary 10: Source-aware firing via cFireSourceExecFact

Exercise the full source-aware firing pipeline: extract, match via
`cmatchInputSpec`, apply sinks. -/

/-- Fire the explicit-source rule against a space with `(data hello)`. -/
theorem canary10_source_fire :
    match extractSourceExecFact canary9_explicit_exec with
    | some sef =>
      cFireSourceExecFact
        [canary9_explicit_exec, .expression [.symbol "data", .symbol "hello"]]
        sef =
        [.expression [.symbol "data", .symbol "hello"],
         .expression [.symbol "found", .symbol "hello"]]
    | none => False := rfl

/-- Explicit `(I (BTM ...) (== ...))` exec atom with equality constraint. -/
private def canary10_eq_exec : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "eq-test"],
    .expression [.symbol "I",
      .expression [.symbol "BTM",
        .expression [.symbol "key", .var "k"]],
      .expression [.symbol "==",
        .expression [.symbol "val", .var "k"],
        .var "v"]],
    .expression [.symbol "O",
      .expression [.symbol "+",
        .expression [.symbol "pair", .var "k", .var "v"]],
      .expression [.symbol "-",
        .expression [.symbol "key", .var "k"]]]]

/-- `==` constraint: match `(key k)`, then lookup `(val $k)` in space.
    Space: `[(key a), (val a)]` → binds `k=a`, finds `(val a)`, binds `v=(val a)`.
    Result: `(pair a (val a))` added, `(key a)` removed. -/
theorem canary10_eq_fire :
    match extractSourceExecFact canary10_eq_exec with
    | some sef =>
      cFireSourceExecFact
        [canary10_eq_exec,
         .expression [.symbol "key", .symbol "a"],
         .expression [.symbol "val", .symbol "a"]]
        sef =
        [.expression [.symbol "val", .symbol "a"],
         .expression [.symbol "pair", .symbol "a",
           .expression [.symbol "val", .symbol "a"]]]
    | none => False := rfl

/-- `==` constraint with no match: `(val b)` not in space when `k=a`. -/
theorem canary10_eq_nomatch :
    match extractSourceExecFact canary10_eq_exec with
    | some sef =>
      cFireSourceExecFact
        [canary10_eq_exec,
         .expression [.symbol "key", .symbol "a"],
         .expression [.symbol "val", .symbol "b"]]
        sef =
        [.expression [.symbol "key", .symbol "a"],
         .expression [.symbol "val", .symbol "b"]]
    | none => False := rfl

/-! ### Canary 11: `!=` constraint through cFireSourceExecFact

Exercise `neqConstraint` through the source-aware firing pipeline. -/

/-- `!=` source exec fact (constructed directly to avoid kernel reduction of parser). -/
private def canary11_sef : SourceExecFact where
  atom := .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "neq-wq"],
    .symbol "I-body", .symbol "O-body"]  -- placeholder atom
  loc  := .expression [.symbol "0", .symbol "neq-wq"]
  rule := ⟨0, "neq-wq",
    .explicit [
      .btm (.expression [.symbol "skip", .var "x"]),
      .neqConstraint (.expression [.symbol "data", .var "x"])
                     (.expression [.symbol "data", .var "y"])],
    [],
    mkTemplate [mkAdd (.expression [.symbol "found", .var "y"])]⟩

/-- `!=` through cFireSourceExecFact: skip `(data a)`, match remaining `(data b)`. -/
theorem canary11_neq_fire :
    cFireSourceExecFact
      [canary11_sef.atom,
       .expression [.symbol "skip", .symbol "a"],
       .expression [.symbol "data", .symbol "a"],
       .expression [.symbol "data", .symbol "b"]]
      canary11_sef =
      [.expression [.symbol "skip", .symbol "a"],
       .expression [.symbol "data", .symbol "a"],
       .expression [.symbol "data", .symbol "b"],
       .expression [.symbol "found", .symbol "b"]] := rfl

/-- `!=` with no remaining match: only `(data a)` exists, excluded. -/
theorem canary11_neq_nomatch :
    cFireSourceExecFact
      [canary11_sef.atom,
       .expression [.symbol "skip", .symbol "a"],
       .expression [.symbol "data", .symbol "a"]]
      canary11_sef =
      [.expression [.symbol "skip", .symbol "a"],
       .expression [.symbol "data", .symbol "a"]] := rfl

/-- Extraction roundtrip: `extractSourceExecFact` parses the `!=` source. -/
theorem canary11_extraction_parses :
    (extractSourceExecFact
      (.expression [.symbol "exec",
        .expression [.symbol "0", .symbol "neq-wq"],
        .expression [.symbol "I",
          .expression [.symbol "BTM",
            .expression [.symbol "skip", .var "x"]],
          .expression [.symbol "!=",
            .expression [.symbol "data", .var "x"],
            .expression [.symbol "data", .var "y"]]],
        .expression [.symbol "O",
          .expression [.symbol "+",
            .expression [.symbol "found", .var "y"]]]])).isSome = true := rfl

end Canaries

end Mettapedia.Languages.ProcessCalculi.MORK
