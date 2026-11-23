import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Languages.MeTTa.OSLFCore.Bridge
import Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# A PeTTa space snapshot as a call catalogue

Each executable equation occurrence contributes a GSLT rewrite from a head
lookup to that equation's row position. The positions and the head vocabulary
refer to the captured space. Its raw atoms remain available for matching and
inspection. The catalogue and ordinary PeTTa argument matching give exactly
the source body activations, with their order and multiplicity.

This is the symbol-headed loader from `SpaceSemantics`. Primitive priority,
argument demand, and evaluation of a selected body belong to the caller.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.SpaceLanguageDef

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.OSLF.MeTTaIL.Syntax (LanguageDef Pattern RewriteRule GrammarRule)
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction
open Mettapedia.OSLF.Framework.TypeSynthesis
  (langSemanticReduces langSemanticReducesUsing langSemanticReducesUsing_iff_langReducesUsing_of_equation_free)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises)
open SpaceSemantics

def readEquation : Atom → Option Equation
  | .expression [.symbol "=", .expression (.symbol head :: arguments), body] =>
    some ⟨head, arguments, body⟩
  | _ => none

@[simp] theorem readEquation_toAtom (row : Equation) :
    readEquation row.toAtom = some row := by
  cases row
  rfl

private theorem readEquation_eq_none {row : Atom}
    (notEquation : ∀ head arguments body,
      row ≠ .expression [.symbol "=", .expression (.symbol head :: arguments), body]) :
    readEquation row = none := by
  unfold readEquation
  split
  · rename_i _ head arguments body
    exact (notEquation head arguments body rfl).elim
  · rfl

def headNames (rows : List Atom) : List String :=
  rows.filterMap fun row => (readEquation row).map (·.head)

@[simp] theorem headNames_append (rows added : List Atom) :
    headNames (rows ++ added) = headNames rows ++ headNames added := by
  simp [headNames]

private theorem headNames_eq {rows : List Atom} {program : Program} (indexed : Indexes rows program) :
    headNames rows = program.equations.map (·.head) := by
  induction indexed with
  | nil => rfl
  | equation head args body tail ih => simp [headNames, readEquation, ← ih]
  | declaration subject type tail ih => simpa [headNames, readEquation] using ih
  | fact row notEquation notDeclaration tail ih =>
    simpa [headNames, readEquation_eq_none notEquation] using ih

def encodeSlot : Nat → Pattern
  | 0 => .apply "SpaceZero" []
  | slot + 1 => .apply "SpaceNext" [encodeSlot slot]

def decodeSlot : Pattern → Option Nat
  | .apply "SpaceZero" [] => some 0
  | .apply "SpaceNext" [slot] => (decodeSlot slot).map (· + 1)
  | _ => none

@[simp] theorem decodeSlot_encodeSlot (slot : Nat) :
    decodeSlot (encodeSlot slot) = some slot := by
  induction slot with
  | zero => rfl
  | succ slot ih => simp [encodeSlot, decodeSlot, ih]

private theorem encodeSlot_binderFree (slot : Nat) : binderFree (encodeSlot slot) = true := by
  induction slot with
  | zero => rfl
  | succ slot ih => simp [encodeSlot, binderFree, binderFreeList, ih]

private theorem applyBindings_encodeSlot (bindings : Bindings) (slot : Nat) :
    applyBindings bindings (encodeSlot slot) = encodeSlot slot := by
  induction slot with
  | zero => simp [encodeSlot, applyBindings]
  | succ slot ih => simp [encodeSlot, applyBindings, ih]

private theorem matchPattern_slots (first second : Nat) :
    matchPattern (encodeSlot first) (encodeSlot second) =
      if first = second then [[]] else [] := by
  induction first generalizing second with
  | zero => cases second <;> simp [encodeSlot, matchPattern, matchArgs]
  | succ first ih =>
    cases second with
    | zero => simp [encodeSlot, matchPattern]
    | succ second =>
      simp only [encodeSlot, matchPattern, beq_self_eq_true, List.length_cons,
        List.length_nil, Bool.and_self, ↓reduceIte, matchArgs, ih, Nat.succ.injEq]
      split <;> simp [mergeBindings]

def lookup (names : List String) (head : String) : Pattern :=
  .apply "SpaceLookup" [encodeSlot (names.idxOf head)]

def candidate (position : Nat) : Pattern := .apply "SpaceRule" [encodeSlot position]

def constructors : List GrammarRule :=
  [{ label := "SpaceZero", category := "SpaceSlot", params := [],
      syntaxPattern := [.terminal "zero"] },
    { label := "SpaceNext", category := "SpaceSlot", params := [.simple "slot" (.base "SpaceSlot")],
      syntaxPattern := [.terminal "next", .nonTerminal "slot"] },
    { label := "SpaceLookup", category := "SpaceControl", params := [.simple "key" (.base "SpaceSlot")],
      syntaxPattern := [.terminal "lookup", .nonTerminal "key"] },
    { label := "SpaceRule", category := "SpaceControl", params := [.simple "slot" (.base "SpaceSlot")],
      syntaxPattern := [.terminal "rule", .nonTerminal "slot"] }]

def candidateRule (names : List String) (position : Nat) (row : Equation) : RewriteRule :=
  { name := "space-row-" ++ toString position
    typeContext := []
    premises := []
    left := lookup names row.head
    right := candidate position }

def compileRules (names : List String) : Nat → List Atom → List RewriteRule
  | _, [] => []
  | position, row :: rest =>
    match readEquation row with
    | some equation => candidateRule names position equation :: compileRules names (position + 1) rest
    | none => compileRules names (position + 1) rest

def language (name : String) (rows : List Atom) : LanguageDef :=
  { name, types := GroundData.dataLanguage.types ++ [{ name := "SpaceSlot" }, { name := "SpaceControl" }],
    terms := GroundData.dataLanguage.terms ++ constructors,
    equations := [], rewrites := compileRules (headNames rows) 0 rows }

private theorem candidate_reducts (names : List String) (position : Nat) (row : Equation)
    (member : row.head ∈ names) (head : String) :
    (matchPattern (candidateRule names position row).left (lookup names head)).map
        (fun bindings => applyBindings bindings (candidateRule names position row).right) =
      if row.head = head then [candidate position] else [] := by
  simp only [candidateRule, lookup, matchPattern, beq_self_eq_true, List.length_cons,
    List.length_nil, Bool.and_self, ↓reduceIte, matchArgs, matchPattern_slots,
    List.idxOf_inj member]
  split <;> simp [mergeBindings, candidate, applyBindings, applyBindings_encodeSlot]

def resolve (rows : List Atom) : Pattern → Option Equation
  | .apply "SpaceRule" [slot] => do
    let position ← decodeSlot slot
    let row ← rows[position]?
    readEquation row
  | _ => none

private theorem located_tail (allRows : List Atom) (position : Nat) (row : Atom) (rest : List Atom)
    (located : ∀ offset : Nat, (row :: rest)[offset]? = allRows[position + offset]?) :
    ∀ offset : Nat, rest[offset]? = allRows[position + 1 + offset]? := by
  intro offset
  rw [show position + 1 + offset = position + (offset + 1) by omega]
  exact located (offset + 1)

private theorem resolve_catalogue {rows : List Atom} {program : Program}
    (indexed : Indexes rows program) (allRows : List Atom) (position : Nat)
    (located : ∀ offset : Nat, rows[offset]? = allRows[position + offset]?) (names : List String) :
    (compileRules names position rows).filterMap (fun rule => resolve allRows rule.right) =
      program.equations := by
  induction indexed generalizing position with
  | nil => rfl
  | equation head arguments body tail ih =>
    have first := (located 0).symm
    simp only [Nat.add_zero, List.getElem?_cons_zero] at first
    have resolved : resolve allRows (candidate position) = some ⟨head, arguments, body⟩ := by
      simp [resolve, candidate, first, readEquation]
    simp only [compileRules, readEquation, List.filterMap_cons, candidateRule, resolved]
    rw [ih (position + 1) (located_tail allRows position _ _ located)]
  | declaration subject type tail ih =>
    simpa [compileRules, readEquation] using
      ih (position + 1) (located_tail allRows position _ _ located)
  | fact row notEquation notDeclaration tail ih =>
    simpa only [compileRules, readEquation_eq_none notEquation] using
      ih (position + 1) (located_tail allRows position _ _ located)

/-- Read the program from generated rewrite rows. Type declarations are
read from the same store and keep their original argument-demand role. -/
def programView (presentation : LanguageDef) (rows : List Atom) : Program :=
  { index rows with equations := presentation.rewrites.filterMap (fun rule => resolve rows rule.right) }

theorem programView_exact (name : String) (rows : List Atom) :
    programView (language name rows) rows = index rows := by
  unfold programView language
  simp only [resolve_catalogue (index_exact rows) rows 0 (by simp) (headNames rows)]

/-- The raw Atom carrier is shared by every generated presentation, including
variables and expression atoms whose heads have no active rules. -/
def dataTerms (rows : List Atom) : List Pattern := GroundData.encodeList rows

theorem dataTerms_roundtrip (rows : List Atom) : GroundData.decodeList (dataTerms rows) = some rows :=
  GroundData.decodeList_encodeList rows

private theorem compileRules_resolve {rows : List Atom} {program : Program}
    (indexed : Indexes rows program) (allRows : List Atom) (position : Nat)
    (located : ∀ offset : Nat, rows[offset]? = allRows[position + offset]?)
    (names : List String) (contains : ∀ row ∈ program.equations, row.head ∈ names) (head : String) :
    ((compileRules names position rows).flatMap
        (fun rule => (matchPattern rule.left (lookup names head)).map
          (fun bindings => applyBindings bindings rule.right))).filterMap (resolve allRows) =
      program.equations.filter (fun row => row.head == head) := by
  induction indexed generalizing position with
  | nil => rfl
  | equation eqHead args body tail ih =>
    have firstLocated := (located 0).symm
    simp only [Nat.add_zero, List.getElem?_cons_zero] at firstLocated
    have member := contains ⟨eqHead, args, body⟩ List.mem_cons_self
    have remain := ih (position + 1) (located_tail allRows position _ _ located)
      (fun row member => contains row (List.mem_cons_of_mem _ member))
    simp only [compileRules, readEquation, List.flatMap_cons]
    rw [candidate_reducts _ _ _ member, List.filterMap_append, remain]
    by_cases equal : eqHead = head
    · simp [equal, resolve, candidate, firstLocated, readEquation]
    · simp [equal]
  | declaration subject type tail ih =>
    simpa [compileRules, readEquation] using
      ih (position + 1) (located_tail allRows position _ _ located) contains
  | fact row notEquation notDeclaration tail ih =>
    simpa only [compileRules, readEquation_eq_none notEquation] using
      ih (position + 1) (located_tail allRows position _ _ located) contains

def candidates (presentation : LanguageDef) (rows : List Atom) (head : String) : List Equation :=
  (rootReducts presentation (lookup (headNames rows) head)).filterMap (resolve rows)

theorem candidates_exact (name : String) (rows : List Atom) (head : String) :
    candidates (language name rows) rows head =
      (index rows).equations.filter (fun row => row.head == head) := by
  exact compileRules_resolve (index_exact rows) rows 0 (by simp) (headNames rows)
    (by rw [headNames_eq (index_exact rows)]; exact fun _ member => List.mem_map_of_mem member)
    head

private theorem unconditional (name : String) (rows : List Atom) :
    isUnconditionalAligned (language name rows) = true := by
  have suffix (names : List String) (rows : List Atom) :
      ∀ position, (compileRules names position rows).all
        (fun rule => rule.premises.isEmpty && ruleDepthAligned rule) = true := by
    induction rows with
    | nil => intro; rfl
    | cons row tail ih =>
      intro position
      simp only [compileRules]
      split
      · rename_i equation _
        have aligned := ruleDepthAligned_of_binderFree (candidateRule names position equation)
          (by simp [candidateRule, lookup, binderFree, binderFreeList, encodeSlot_binderFree])
          (by simp [candidateRule, candidate, binderFree, binderFreeList, encodeSlot_binderFree])
        change ((true && ruleDepthAligned (candidateRule names position equation)) && _) = true
        rw [aligned, ih]
        rfl
      · exact ih (position + 1)
  exact suffix (headNames rows) rows 0

/-- The declarative GSLT step agrees with membership in the root frontier. -/
theorem step_lookup_iff (name : String) (rows : List Atom) (head : String) (target : Pattern) :
    langSemanticReduces (language name rows) (lookup (headNames rows) head) target ↔
      target ∈ rootReducts (language name rows) (lookup (headNames rows) head) := by
  change langSemanticReducesUsing RelationEnv.empty (language name rows) _ _ ↔ _
  rw [langSemanticReducesUsing_iff_langReducesUsing_of_equation_free RelationEnv.empty
    (by rfl : (language name rows).isEquationFree = true)]
  change Step (engineBasePremises RelationEnv.empty) (language name rows) _ _ ↔ _
  exact step_iff_mem_rootReducts _ _ (unconditional name rows) _ _

def dispatch (presentation : LanguageDef) (rows : List Atom) (head : String)
    (values : List Atom) : Eval.Control :=
  let program : Program := { equations := candidates presentation rows head, declarations := [] }
  Eval.application program head values

/-- Once the ordinary call protocol has produced the arguments, the catalogue
supplies the same body activations, missing-pattern and arity behavior. -/
theorem dispatch_exact (name : String) (rows : List Atom) (head : String) (values : List Atom) :
    dispatch (language name rows) rows head values = Eval.application (index rows) head values := by
  let catalogue : Program :=
    { equations := candidates (language name rows) rows head, declarations := [] }
  have named : catalogue.equations.filter (fun row => row.head == head) =
      (index rows).equations.filter (fun row => row.head == head) := by
    simp [catalogue, candidates_exact, List.filter_filter, Bool.and_self]
  have arities : Eval.arities catalogue head = Eval.arities (index rows) head := by
    unfold Eval.arities
    rw [named]
  have clauses : Eval.clauses catalogue head values = Eval.clauses (index rows) head values := by
    rw [Eval.clauses_use_only_the_named_equations, Eval.clauses_use_only_the_named_equations, named]
  change Eval.application catalogue head values = _
  simp only [Eval.application, clauses, arities, Eval.knownArities]

/-- One ordinary instruction against this space. The generated rewrite
catalogue supplies callability and ready-call selection. The existing
machine supplies argument demand, continuations and effects. -/
def step (rows : List Atom) (source : Eval.Configuration) : Option Eval.Configuration :=
  let presentation := language "MeTTaSpace" rows
  let ordinary := fun _ : Unit => Eval.step (programView presentation rows) source
  match source.control with
  | .arguments _ (.function head) [] values _ =>
    if Eval.ioHead head || StdLib.known head then ordinary ()
    else some { source with control := dispatch presentation rows head values }
  | _ => ordinary ()

theorem step_exact (rows : List Atom) (source : Eval.Configuration) :
    step rows source = Eval.step (index rows) source := by
  cases control : source.control <;> simp only [step, control, programView_exact]
  case arguments bindings target pending values index =>
    cases target <;> cases pending <;> simp only
    rename_i head
    by_cases ordinary : Eval.ioHead head = true
    · simp [ordinary]
    · have noIO : Eval.ioHead head = false := Bool.eq_false_iff.mpr ordinary
      by_cases native : StdLib.known head = true
      · simp [noIO, native]
      · have authored : StdLib.known head = false := Bool.eq_false_iff.mpr native
        simp only [noIO, authored, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
          dispatch_exact, Eval.step, control]

/-- With the chosen head vocabulary, append-only loading compiles the new
suffix at the next source slot. -/
theorem compileRules_append (names : List String) (rows added : List Atom) (position : Nat) :
    compileRules names position (rows ++ added) =
      compileRules names position rows ++ compileRules names (position + rows.length) added := by
  induction rows generalizing position with
  | nil => simp [compileRules]
  | cons row rest ih =>
    have nextPosition : position + (row :: rest).length = position + 1 + rest.length := by
      simp only [List.length_cons]
      omega
    simp only [List.cons_append, compileRules, nextPosition]
    cases readEquation row <;> simp [ih]

private theorem compileRules_names_agree (first second : List String) (rows : List Atom) (position : Nat)
    (agrees : ∀ head ∈ headNames rows, first.idxOf head = second.idxOf head) :
    compileRules first position rows = compileRules second position rows := by
  induction rows generalizing position with
  | nil => rfl
  | cons row rest ih =>
    have tail : compileRules first (position + 1) rest = compileRules second (position + 1) rest :=
      ih (position + 1) (fun head member => by
        apply agrees head
        unfold headNames at member ⊢
        obtain ⟨source, fromTail, decoded⟩ := List.mem_filterMap.mp member
        exact List.mem_filterMap.mpr ⟨source, List.mem_cons_of_mem _ fromTail, decoded⟩)
    cases read : readEquation row with
    | none => simpa [compileRules, read] using tail
    | some equation =>
      have key := agrees equation.head (by simp [headNames, read])
      simp [compileRules, read, candidateRule, lookup, key, tail]

/-- Appending rows preserves the earlier code. Newly named heads get slots
after those assigned by the old vocabulary. -/
theorem language_append_rewrites (name : String) (rows added : List Atom) :
    (language name (rows ++ added)).rewrites =
      (language name rows).rewrites ++
        compileRules (headNames (rows ++ added)) rows.length added := by
  have earlier := compileRules_names_agree (headNames rows ++ headNames added) (headNames rows)
    rows 0 (fun _ member => List.idxOf_append_of_mem member)
  simp [language, compileRules_append, earlier]

/-- An append with no executable equation leaves the compiled language intact.
A type declaration can still affect the caller's argument protocol. -/
theorem language_after_fact (name : String) (rows : List Atom) (fact : Atom)
    (passive : readEquation fact = none) :
    language name (rows ++ [fact]) = language name rows := by
  have sameHeads : headNames (rows ++ [fact]) = headNames rows := by simp [headNames, passive]
  simp [language, sameHeads, compileRules_append, compileRules, passive]

/-- The ordered, mixed store remains visible to source queries. -/
theorem raw_rows_exact (rows : List Atom) :
    loadedAtoms (index rows) = rows :=
  loadedAtoms_collect (index_collected rows)

section Examples

private def coin : Atom := .expression [.symbol "coin"]
private def rule (result : String) : Atom :=
  .expression [.symbol "=", coin, .symbol result]
private def rows : List Atom := [.symbol "a-fact", rule "heads", rule "tails", rule "heads"]

#guard (language "Example" rows).validate.isEmpty

example : (candidates (language "Example" rows) rows "coin").map (·.body) =
    [.symbol "heads", .symbol "tails", .symbol "heads"] := by decide +kernel

example : (candidates (language "Example" rows) rows "other").isEmpty = true := by decide +kernel

end Examples

#print axioms candidates_exact
#print axioms programView_exact
#print axioms step_lookup_iff
#print axioms dispatch_exact
#print axioms step_exact
#print axioms language_append_rewrites
#print axioms language_after_fact

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.SpaceLanguageDef
