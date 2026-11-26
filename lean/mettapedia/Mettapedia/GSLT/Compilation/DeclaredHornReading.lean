import Mettapedia.GSLT.Compilation.CanonicalHornSemantics

/-! A declared positive Horn fragment has a demand-driven rule-module reading.
Relate the actual occurrence-indexed compiler output to the authored least
model. Finiteness of the text, finiteness of reachable calls and answers, and
bounded work per implementation step are three different assertions. -/
set_option autoImplicit false
namespace Mettapedia.GSLT.Compilation.DeclaredHornReading

open Mettapedia.GSLT.Parsing
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Source)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
open CanonicalHornModule CanonicalHornSemantics ModedRuleModule
open ModuleReading (reading seed valueRow RangeRestricted Demanded Derives)
open SetStoreSyntax (QuantifiedStep QuantifiedTerminal)

/-- Keeping provider roles and rules fixed, adding provider facts cannot
withdraw a positive source answer. This concerns semantic answers, not the
order, cost, or termination of a particular search procedure. -/
theorem source_mono {L : Type} (roles : RelationRoles) (rules : L → HornCertificate.Rule)
    {first next : Set RawAtom} (grows : first ⊆ next) (goal : RawAtom) :
    SourceLeast roles rules first goal → SourceLeast roles rules next goal := by
  intro yes model closed
  apply yes model
  intro label subst body
  apply closed label subst
  intro atom member
  have old := body atom member
  unfold sourceHolds at old ⊢
  cases h : roles (HornUnification.encodeAtom atom).symbol with
  | none => rw [h] at old; exact old
  | some role =>
    rw [h] at old
    cases role with
    | derived => exact old
    | external => exact grows old

/-- There is no transparent/default reading of absence as a positive Horn
goal over the same append-only providers. A complement oracle, an explicitly
closed domain, or a different observation would be a different interface. -/
theorem cannot_read_absence {L : Type} (roles : RelationRoles) (rules : L → HornCertificate.Rule)
    (goal watched : RawAtom) :
    ¬ ∀ facts : Finset RawAtom, SourceLeast roles rules facts goal ↔ watched ∉ facts := by
  intro decides
  have present := source_mono roles rules
    (show (↑(∅ : Finset RawAtom) : Set RawAtom) ⊆ ↑({watched} : Finset RawAtom) by simp)
    goal ((decides ∅).2 (by simp))
  exact (decides {watched}).1 present (Finset.mem_singleton_self _)

/-- No fallback elaborator: a source composition must elaborate, and every
elaborated rule must pass the declared mode and bound-variable checks. -/
theorem admitted_iff {L : Type} (modes : Modes) (sources : List Source)
    (out : List (Clause (Signature L))) :
    compileSource? modes sources = some out ↔ ∃ program,
      CanonicalSourceHornElaboration.elaborateProgram? sources = some program ∧
      compileProgram? modes program = some out := by
  simp [compileSource?, Option.bind_eq_some_iff]

/-- The syntactic boundary within an elaborated module is two-sided. The head
is derived, every premise has a mode, and external tests and final outputs
read only variables bound at the corresponding point in the ordered body. -/
theorem rule_accepted_iff {L : Type} (modes : Modes) (r : HornCertificate.Rule)
    (c : Clause (Signature L)) :
    compileRule? modes r = some c ↔
      lowerCall? modes r.head = some (.intensional c.head) ∧
      r.body.mapM (lowerCall? modes) = some c.body ∧
      loadBody c.head.output c.head.input.freeVars c.body = true := by
  refine ⟨compileRule?_components, ?_⟩
  rintro ⟨hh, hb, safe⟩
  simp [compileRule?, hh, hb, safe]

abbrev Label (p : HornCertificate.Program) := Fin p.length

/-- Give a rule occurrence its own label even when the source repeats the rule. -/
def emitted {p : HornCertificate.Program} {modes : Modes}
    {out : List (Clause (Signature (Label p)))} (ok : compileProgram? modes p = some out)
    (i : Label p) : Clause (Signature (Label p)) :=
  out[i.val]'(by rw [(compileProgram?_length_and_scope modes p ok).1]; exact i.isLt)

theorem emitted_at {p : HornCertificate.Program} {modes : Modes}
    {out : List (Clause (Signature (Label p)))} (ok : compileProgram? modes p = some out)
    (i : Label p) : compileRule? modes p[i.val] = some (emitted ok i) := by
  have hr : p[i.val]? = some p[i.val] := List.getElem?_eq_getElem i.isLt
  have ht : out[i.val]? = some (emitted ok i) :=
    List.getElem?_eq_some_iff.mpr ⟨_, rfl⟩
  simpa only [hr, ht, Option.bind_some] using (compileProgram?_at ok (i := i.val))

/-- Labels may be any finite type indexing the source rule occurrences.
The independent Horn model is linked to the quantified tcalc run by the
compiler result at each label, not by a postulated semantics of a backend. -/
theorem labelled_answers {L : Type} [Fintype L] [DecidableEq L] (modes : Modes)
    (source : L → HornCertificate.Rule) (target : L → Clause (Signature L))
    (compiled : ∀ i, compileRule? modes (source i) = some (target i))
    (timing : SetStore.AskTiming) (facts : Finset RawAtom) (groundFacts : ∀ a ∈ facts, a.isGround)
    (goal : RawAtom) (r : CallRow (Signature L)) (mode : lowerAtom? modes goal = some (.intensional r))
    (gi : r.input.isGround) {after : Finset (Datum L)}
    (run : Relation.ReflTransGen (QuantifiedStep .every timing (reading (lower target)))
      (seed r.input (facts.image wrapAtom)) after)
    (terminal : QuantifiedTerminal .every timing (reading (lower target)) after) :
    valueRow r.input r.output ∈ after ↔ SourceLeast (rolesOf modes) source facts goal := by
  have ground : ∀ a ∈ facts.image (wrapAtom (Labels := L)), a.isGround := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact (wrap_atom_ground_iff _).2 (groundFacts b hb)
  refine (completed_every_answers (σ := signature) (Equiv.refl Nat) timing target _
    (fun i => compileRule?_rangeRestricted (compiled i)) _ _ gi ground run terminal).trans ?_
  simpa only [Finset.coe_image] using least_iff_source modes source target compiled facts goal r mode

section Fiber
variable {p : HornCertificate.Program} {modes : Modes}
    {out : List (Clause (Signature (Label p)))} (ok : compileProgram? modes p = some out)

private theorem safe (i : Label p) : RangeRestricted (lower (emitted ok) i) :=
  compileRule?_rangeRestricted (emitted_at ok i)

def providers (p : HornCertificate.Program) (facts : Finset RawAtom) :
    Finset (Mettapedia.Logic.LP.Atom (Signature (Label p))) :=
  facts.image wrapAtom

private theorem ground_providers {facts : Finset RawAtom} (g : ∀ a ∈ facts, a.isGround) :
    ∀ a ∈ providers p facts, a.isGround := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  exact (wrap_atom_ground_iff _).2 (g b hb)

abbrev Finished (timing : SetStore.AskTiming) (facts : Finset RawAtom) (input : Datum (Label p))
    (after : Finset (Datum (Label p))) : Prop :=
  Relation.ReflTransGen (QuantifiedStep .every timing (reading (lower (emitted ok))))
    (seed input (providers p facts)) after ∧
  QuantifiedTerminal .every timing (reading (lower (emitted ok))) after

/-- Both inclusion directions, on the computed module and the independent
Horn least model, for every declared goal mode and fixed provider facts. -/
theorem answers_iff (timing : SetStore.AskTiming) (facts : Finset RawAtom)
    (g : ∀ a ∈ facts, a.isGround) (goal : RawAtom) (r : CallRow (Signature (Label p)))
    (mode : lowerAtom? modes goal = some (.intensional r)) (inputGround : r.input.isGround)
    {after} (done : Finished ok timing facts r.input after) :
    valueRow r.input r.output ∈ after ↔
      SourceLeast (rolesOf modes) (fun i : Label p => p[i.val]) facts goal :=
  labelled_answers modes _ _ (emitted_at ok) timing facts g goal r mode inputGround done.1 done.2

/-- This is an iff: finite syntax and a well-moded rule do not by themselves
imply termination. Only calls actually demanded and their derived values count. -/
theorem terminal_iff (timing : SetStore.AskTiming) (facts : Finset RawAtom)
    (g : ∀ a ∈ facts, a.isGround) (input : Datum (Label p)) (gi : input.isGround) :
    (∃ after, Finished ok timing facts input after) ↔
    {c | Demanded (lower (emitted ok)) (providers p facts) input c}.Finite ∧
      ∀ c, Demanded (lower (emitted ok)) (providers p facts) input c →
        {v | Derives (lower (emitted ok)) (providers p facts) c v}.Finite := by
  have silent := fun r hr => (module_propagates (emitted ok) (safe ok) r hr).noTell
  constructor
  · rintro ⟨after, run, terminal⟩
    exact ModuleReading.finite_of_terminal_run (σ := signature) (Equiv.refl Nat) .every timing
      (safe ok) gi (ground_providers g) ((SetStoreSyntax.quantified_run_iff_of_no_tells silent).mp run)
      ((SetStoreSyntax.quantified_terminal_iff_of_no_tells silent).mp terminal) (by intro h; cases h)
  · rintro ⟨calls, answers⟩
    obtain ⟨after, run, terminal⟩ := ModuleReading.exists_terminal_run .every timing (safe ok)
      gi (ground_providers g) calls answers
    exact ⟨after, (SetStoreSyntax.quantified_run_iff_of_no_tells silent).mpr run,
      (SetStoreSyntax.quantified_terminal_iff_of_no_tells silent).mpr terminal⟩

/-- A bound on *changing module rounds*, not search probes, CPU instructions
or source evaluation fuel. Each such round adds at least one distinct row to
the reachable closure; the initially present rows cannot be charged again. -/
theorem round_bound (timing : SetStore.AskTiming) (facts : Finset RawAtom)
    (g : ∀ a ∈ facts, a.isGround) (input : Datum (Label p)) (gi : input.isGround)
    (calls : {c | Demanded (lower (emitted ok)) (providers p facts) input c}.Finite)
    (values : ∀ c, Demanded (lower (emitted ok)) (providers p facts) input c →
      {v | Derives (lower (emitted ok)) (providers p facts) c v}.Finite)
    (states : ℕ → Finset (Datum (Label p))) (starts : states 0 = seed input (providers p facts))
    (n : ℕ) (step : ∀ j < n, QuantifiedStep .every timing (reading (lower (emitted ok)))
      (states j) (states (j+1))) :
    n + (states 0).card ≤
      (ModuleReading.closure_finite (safe ok) gi (ground_providers g) calls values).toFinset.card := by
  have pure := module_propagates (emitted ok) (safe ok)
  let carrier := SetStoreClosure.closure
    (SetStoreSyntax.consequence (P := reading (lower (emitted ok)))) (seed input (providers p facts))
  have inv : ∀ j ≤ n, SetStoreSyntax.GroundRows (states j) ∧
      (states j : Set _) ⊆ carrier ∧ j + (states 0).card ≤ (states j).card := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨starts ▸ ModuleReading.seed_ground gi (ground_providers g),
        starts ▸ SetStoreClosure.seed_subset_closure _ _, by omega⟩
    | succ j ih =>
      intro hj
      obtain ⟨ground, inside, size⟩ := ih (by omega)
      have raw := SetStoreSyntax.disciplined_is_step
        ((SetStoreSyntax.quantified_iff_of_no_tells (fun r hr => (pure r hr).noTell)).1
          (step j (by omega)))
      have grows := SetStoreSyntax.actual_step_card_lt pure ground raw
      exact ⟨SetStoreSyntax.actual_step_preserves_ground pure ground raw,
        SetStoreSyntax.actual_step_le_closure pure _ ground inside raw, by omega⟩
  obtain ⟨_, inside, size⟩ := inv n le_rfl
  exact size.trans (Finset.card_le_card (fun x hx => (Set.Finite.mem_toFinset _).2 (inside hx)))

end Fiber

namespace Controls
open Mettapedia.Logic.LP (Term Subst)

private def sym : HornUnification.RelationSymbol := ⟨"grow", 1⟩
private def mode : Modes := fun h => if h = sym then some (.derived [true]) else none
private def atom (t : HornCertificate.Term) : HornCertificate.Atom := ⟨"grow", .cons t .nil⟩
private def program : HornCertificate.Program :=
  [⟨"grow-again", atom (.var 0), [atom (.app "s" (.cons (.var 0) .nil))]⟩]
private abbrev D := Datum (Label program)
private def call (x : D) : D := pack (.call sym 1) fun _ => x
private def s (x : D) : D := pack (.authored ⟨"s", 1⟩) fun _ => x
private def unitOut : D := pack (.outputs 0) Fin.elim0
private def clauses : List (Clause (Signature (Label program))) :=
  [⟨⟨call (.var 0), unitOut⟩, [.intensional ⟨call (s (.var 0)), unitOut⟩]⟩]
private theorem accepted : compileProgram? mode program = some clauses := by
  change some [Clause.mk ⟨_, _⟩ [.intensional ⟨_, _⟩]] =
    some [Clause.mk ⟨_, _⟩ [.intensional ⟨_, _⟩]]
  simp only [Option.some.injEq, List.cons.injEq, Clause.mk.injEq, CallRow.mk.injEq,
    BodyLiteral.intensional.injEq, and_true]
  decide +kernel
private def onlyLabel : Label program := ⟨0, by decide⟩
private def tower : Nat → D
  | 0 => .const (.atom "z")
  | n + 1 => s (tower n)

private theorem demanded (n : Nat) :
    Demanded (lower (emitted accepted)) (providers program ∅) (call (tower 0)) (call (tower n)) := by
  induction n with
  | zero => exact .seed
  | succ n ih =>
    exact .call (l := onlyLabel) (θ := fun _ => tower n) (pre := []) (post := [])
      (source := call (s (.var 0))) (target := unitOut) ih rfl (by simp)

private theorem tower_size (n : Nat) : (tower n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 1 + ∑ _ : Fin 1, (tower n).size = n + 1 + 1
    simp [ih, Nat.add_comm]

private theorem call_injective : Function.Injective (fun n => call (tower n)) := by
  intro i j h
  have size := congrArg Term.size h
  change 1 + ∑ _ : Fin 1, (tower i).size = 1 + ∑ _ : Fin 1, (tower j).size at size
  simpa [tower_size] using size

/-- A single accepted, range-restricted rule grow(x) ← grow(s(x)).
It produces infinitely many different *demands*, even without any provider
facts or any answers. Finite declaration syntax is not a fuel certificate. -/
theorem finite_text_no_terminal (timing : SetStore.AskTiming) :
    ¬ ∃ after, Finished accepted timing ∅ (call (tower 0)) after := by
  intro terminal
  have finite := ((terminal_iff accepted timing ∅ (by simp) (call (tower 0))
    (by intro i; trivial)).1 terminal).1
  exact (Set.infinite_range_of_injective call_injective)
    (finite.subset (by rintro _ ⟨n, rfl⟩; exact demanded n))

end Controls
end Mettapedia.GSLT.Compilation.DeclaredHornReading
