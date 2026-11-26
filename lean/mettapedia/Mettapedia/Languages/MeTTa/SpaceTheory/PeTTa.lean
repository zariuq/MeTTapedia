import Mettapedia.Languages.MeTTa.SpaceTheory.Atoms
import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Languages.MeTTa.OSLFCore.Bridge
import Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# A PeTTa space snapshot as a call catalogue

Each function definition contributes a GSLT rewrite from a head lookup to an
identified occurrence in the snapshot. The positions and the head vocabulary
refer to the captured space. Its raw atoms remain available for matching and
inspection. The catalogue and ordinary PeTTa argument matching give exactly
the source body activations, with their order and multiplicity.

This is the symbol-headed loader from `SpaceSemantics`. Primitive priority,
argument demand, and evaluation of a selected body belong to the caller.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaPresentation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.OSLF.MeTTaIL.Syntax (LanguageDef Pattern RewriteRule GrammarRule)
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction
open Mettapedia.OSLF.Framework.TypeSynthesis
  (langSemanticReduces langSemanticReducesUsing langSemanticReducesUsing_iff_langReducesUsing_of_equation_free)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

def readEquation (atom : Atom) : Option Equation := do
  let (lhs, rhs) ← Atoms.definition? atom
  match lhs with
  | .expression (.symbol head :: arguments) => some ⟨head, arguments, rhs⟩
  | _ => none

theorem readEquation_shape (a : Atom) :
    readEquation a =
      match a with
      | .expression [.symbol "=", .expression (.symbol head :: arguments), body] =>
        some ⟨head, arguments, body⟩
      | _ => none := by
  cases parsed : Atoms.definition? a with
  | none =>
    unfold readEquation
    rw [parsed]
    split
    · simp [Atoms.definition?, Atoms.content] at parsed
    · rfl
  | some sides =>
    obtain ⟨lhs, rhs⟩ := sides
    have same := Atoms.definition?_iff.mp parsed
    subst a
    unfold readEquation
    rw [parsed]
    cases lhs with
    | expression children =>
      cases children with
      | nil => rfl
      | cons head args => cases head <;> rfl
    | _ => rfl

@[simp] theorem readEquation_toAtom (atom : Equation) :
    readEquation atom.toAtom = some atom := by
  cases atom
  rfl

@[simp] theorem readEquation_definition (head : String) (arguments : List Atom) (body : Atom) :
    readEquation (.expression [.symbol "=", .expression (.symbol head :: arguments), body]) =
      some ⟨head, arguments, body⟩ :=
  rfl

@[simp] theorem readEquation_assignment (subject type : Atom) :
    readEquation (.expression [.symbol ":", subject, type]) = none :=
  rfl

theorem readEquation_eq_none {atom : Atom}
    (notEquation : ∀ head arguments body,
      atom ≠ .expression [.symbol "=", .expression (.symbol head :: arguments), body]) :
    readEquation atom = none := by
  rw [readEquation_shape]
  split
  · rename_i _ head arguments body
    exact (notEquation head arguments body rfl).elim
  · rfl

def headNames (atoms : List Atom) : List String :=
  atoms.filterMap fun atom => (readEquation atom).map (·.head)

@[simp] theorem headNames_append (atoms added : List Atom) :
    headNames (atoms ++ added) = headNames atoms ++ headNames added := by
  simp [headNames]

private theorem headNames_eq {atoms : List Atom} {program : Program} (indexed : Indexes atoms program) :
    headNames atoms = program.equations.map (·.head) := by
  induction indexed with
  | nil => rfl
  | equation head args body tail ih => simp [headNames, readEquation_shape, ← ih]
  | declaration subject type tail ih => simpa [headNames, readEquation_shape] using ih
  | fact atom notEquation notDeclaration tail ih =>
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

def candidateRule (names : List String) (position : Nat) (atom : Equation) : RewriteRule :=
  { name := "space-atom-" ++ toString position
    typeContext := []
    premises := []
    left := lookup names atom.head
    right := candidate position }

def compileRules (names : List String) : Nat → List Atom → List RewriteRule
  | _, [] => []
  | position, atom :: rest =>
    match readEquation atom with
    | some equation => candidateRule names position equation :: compileRules names (position + 1) rest
    | none => compileRules names (position + 1) rest

def language (name : String) (atoms : List Atom) : LanguageDef :=
  { name, types := GroundData.dataLanguage.types ++ [{ name := "SpaceSlot" }, { name := "SpaceControl" }],
    terms := GroundData.dataLanguage.terms ++ constructors,
    equations := [], rewrites := compileRules (headNames atoms) 0 atoms }

private theorem candidate_reducts (names : List String) (position : Nat) (atom : Equation)
    (member : atom.head ∈ names) (head : String) :
    (matchPattern (candidateRule names position atom).left (lookup names head)).map
        (fun bindings => applyBindings bindings (candidateRule names position atom).right) =
      if atom.head = head then [candidate position] else [] := by
  simp only [candidateRule, lookup, matchPattern, beq_self_eq_true, List.length_cons,
    List.length_nil, Bool.and_self, ↓reduceIte, matchArgs, matchPattern_slots,
    List.idxOf_inj member]
  split <;> simp [mergeBindings, candidate, applyBindings, applyBindings_encodeSlot]

def resolve (atoms : List Atom) : Pattern → Option Equation
  | .apply "SpaceRule" [slot] => do
    let position ← decodeSlot slot
    let atom ← atoms[position]?
    readEquation atom
  | _ => none

private theorem located_tail (allAtoms : List Atom) (position : Nat) (atom : Atom) (rest : List Atom)
    (located : ∀ offset : Nat, (atom :: rest)[offset]? = allAtoms[position + offset]?) :
    ∀ offset : Nat, rest[offset]? = allAtoms[position + 1 + offset]? := by
  intro offset
  rw [show position + 1 + offset = position + (offset + 1) by omega]
  exact located (offset + 1)

private theorem resolve_catalogue {atoms : List Atom} {program : Program}
    (indexed : Indexes atoms program) (allAtoms : List Atom) (position : Nat)
    (located : ∀ offset : Nat, atoms[offset]? = allAtoms[position + offset]?) (names : List String) :
    (compileRules names position atoms).filterMap (fun rule => resolve allAtoms rule.right) =
      program.equations := by
  induction indexed generalizing position with
  | nil => rfl
  | equation head arguments body tail ih =>
    have first := (located 0).symm
    simp only [Nat.add_zero, List.getElem?_cons_zero] at first
    have resolved : resolve allAtoms (candidate position) = some ⟨head, arguments, body⟩ := by
      simp [resolve, candidate, first, readEquation_shape]
    simp only [compileRules, readEquation_shape, List.filterMap_cons, candidateRule, resolved]
    rw [ih (position + 1) (located_tail allAtoms position _ _ located)]
  | declaration subject type tail ih =>
    simpa [compileRules, readEquation_shape] using
      ih (position + 1) (located_tail allAtoms position _ _ located)
  | fact atom notEquation notDeclaration tail ih =>
    simpa only [compileRules, readEquation_eq_none notEquation] using
      ih (position + 1) (located_tail allAtoms position _ _ located)

/-- Read the program from generated rewrite atoms. Type declarations are
read from the same store and keep their original argument-demand role. -/
def programView (presentation : LanguageDef) (atoms : List Atom) : Program :=
  { index atoms with equations := presentation.rewrites.filterMap (fun rule => resolve atoms rule.right) }

theorem programView_exact (name : String) (atoms : List Atom) :
    programView (language name atoms) atoms = index atoms := by
  unfold programView language
  simp only [resolve_catalogue (index_exact atoms) atoms 0 (by simp) (headNames atoms)]

/-- The raw Atom carrier is shared by every generated presentation, including
variables and expression atoms whose heads have no active rules. -/
def dataTerms (atoms : List Atom) : List Pattern := GroundData.encodeList atoms

theorem dataTerms_roundtrip (atoms : List Atom) : GroundData.decodeList (dataTerms atoms) = some atoms :=
  GroundData.decodeList_encodeList atoms

private theorem compileRules_resolve {atoms : List Atom} {program : Program}
    (indexed : Indexes atoms program) (allAtoms : List Atom) (position : Nat)
    (located : ∀ offset : Nat, atoms[offset]? = allAtoms[position + offset]?)
    (names : List String) (contains : ∀ atom ∈ program.equations, atom.head ∈ names) (head : String) :
    ((compileRules names position atoms).flatMap
        (fun rule => (matchPattern rule.left (lookup names head)).map
          (fun bindings => applyBindings bindings rule.right))).filterMap (resolve allAtoms) =
      program.equations.filter (fun atom => atom.head == head) := by
  induction indexed generalizing position with
  | nil => rfl
  | equation eqHead args body tail ih =>
    have firstLocated := (located 0).symm
    simp only [Nat.add_zero, List.getElem?_cons_zero] at firstLocated
    have member := contains ⟨eqHead, args, body⟩ List.mem_cons_self
    have remain := ih (position + 1) (located_tail allAtoms position _ _ located)
      (fun atom member => contains atom (List.mem_cons_of_mem _ member))
    simp only [compileRules, readEquation_shape, List.flatMap_cons]
    rw [candidate_reducts _ _ _ member, List.filterMap_append, remain]
    by_cases equal : eqHead = head
    · simp [equal, resolve, candidate, firstLocated, readEquation_shape]
    · simp [equal]
  | declaration subject type tail ih =>
    simpa [compileRules, readEquation_shape] using
      ih (position + 1) (located_tail allAtoms position _ _ located) contains
  | fact atom notEquation notDeclaration tail ih =>
    simpa only [compileRules, readEquation_eq_none notEquation] using
      ih (position + 1) (located_tail allAtoms position _ _ located) contains

def candidates (presentation : LanguageDef) (atoms : List Atom) (head : String) : List Equation :=
  (rootReducts presentation (lookup (headNames atoms) head)).filterMap (resolve atoms)

theorem candidates_exact (name : String) (atoms : List Atom) (head : String) :
    candidates (language name atoms) atoms head =
      (index atoms).equations.filter (fun atom => atom.head == head) := by
  exact compileRules_resolve (index_exact atoms) atoms 0 (by simp) (headNames atoms)
    (by rw [headNames_eq (index_exact atoms)]; exact fun _ member => List.mem_map_of_mem member)
    head

private theorem unconditional (name : String) (atoms : List Atom) :
    isUnconditionalAligned (language name atoms) = true := by
  have suffix (names : List String) (atoms : List Atom) :
      ∀ position, (compileRules names position atoms).all
        (fun rule => rule.premises.isEmpty && ruleDepthAligned rule) = true := by
    induction atoms with
    | nil => intro; rfl
    | cons atom tail ih =>
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
  exact suffix (headNames atoms) atoms 0

/-- The declarative GSLT step agrees with membership in the root frontier. -/
theorem step_lookup_iff (name : String) (atoms : List Atom) (head : String) (target : Pattern) :
    langSemanticReduces (language name atoms) (lookup (headNames atoms) head) target ↔
      target ∈ rootReducts (language name atoms) (lookup (headNames atoms) head) := by
  change langSemanticReducesUsing RelationEnv.empty (language name atoms) _ _ ↔ _
  rw [langSemanticReducesUsing_iff_langReducesUsing_of_equation_free RelationEnv.empty
    (by rfl : (language name atoms).isEquationFree = true)]
  change Step (engineBasePremises RelationEnv.empty) (language name atoms) _ _ ↔ _
  exact step_iff_mem_rootReducts _ _ (unconditional name atoms) _ _

def dispatch (presentation : LanguageDef) (atoms : List Atom) (head : String)
    (values : List Atom) : Eval.Control :=
  let program : Program := { equations := candidates presentation atoms head, declarations := [] }
  Eval.application program head values

/-- Once the ordinary call protocol has produced the arguments, the catalogue
supplies the same body activations, missing-pattern and arity behavior. -/
theorem dispatch_exact (name : String) (atoms : List Atom) (head : String) (values : List Atom) :
    dispatch (language name atoms) atoms head values = Eval.application (index atoms) head values := by
  let catalogue : Program :=
    { equations := candidates (language name atoms) atoms head, declarations := [] }
  have named : catalogue.equations.filter (fun atom => atom.head == head) =
      (index atoms).equations.filter (fun atom => atom.head == head) := by
    simp [catalogue, candidates_exact, List.filter_filter, Bool.and_self]
  have arities : Eval.arities catalogue head = Eval.arities (index atoms) head := by
    unfold Eval.arities
    rw [named]
  have clauses : Eval.clauses catalogue head values = Eval.clauses (index atoms) head values := by
    rw [Eval.clauses_use_only_the_named_equations, Eval.clauses_use_only_the_named_equations, named]
  change Eval.application catalogue head values = _
  simp only [Eval.application, clauses, arities, Eval.knownArities]

/-- One ordinary instruction against this space. The generated rewrite
catalogue supplies callability and ready-call selection. The existing
machine supplies argument demand, continuations and effects. -/
def step (atoms : List Atom) (source : Eval.Configuration) : Option Eval.Configuration :=
  let presentation := language "MeTTaSpace" atoms
  let ordinary := fun _ : Unit => Eval.step (programView presentation atoms) source
  match source.control with
  | .arguments _ (.function head) [] values _ =>
    if Eval.ioHead head || StdLib.known head then ordinary ()
    else some { source with control := dispatch presentation atoms head values }
  | _ => ordinary ()

theorem step_exact (atoms : List Atom) (source : Eval.Configuration) :
    step atoms source = Eval.step (index atoms) source := by
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
theorem compileRules_append (names : List String) (atoms added : List Atom) (position : Nat) :
    compileRules names position (atoms ++ added) =
      compileRules names position atoms ++ compileRules names (position + atoms.length) added := by
  induction atoms generalizing position with
  | nil => simp [compileRules]
  | cons atom rest ih =>
    have nextPosition : position + (atom :: rest).length = position + 1 + rest.length := by
      simp only [List.length_cons]
      omega
    simp only [List.cons_append, compileRules, nextPosition]
    cases readEquation atom <;> simp [ih]

private theorem compileRules_names_agree (first second : List String) (atoms : List Atom) (position : Nat)
    (agrees : ∀ head ∈ headNames atoms, first.idxOf head = second.idxOf head) :
    compileRules first position atoms = compileRules second position atoms := by
  induction atoms generalizing position with
  | nil => rfl
  | cons atom rest ih =>
    have tail : compileRules first (position + 1) rest = compileRules second (position + 1) rest :=
      ih (position + 1) (fun head member => by
        apply agrees head
        unfold headNames at member ⊢
        obtain ⟨source, fromTail, decoded⟩ := List.mem_filterMap.mp member
        exact List.mem_filterMap.mpr ⟨source, List.mem_cons_of_mem _ fromTail, decoded⟩)
    cases read : readEquation atom with
    | none => simpa [compileRules, read] using tail
    | some equation =>
      have key := agrees equation.head (by simp [headNames, read])
      simp [compileRules, read, candidateRule, lookup, key, tail]

/-- Appending atoms preserves the earlier code. Newly named heads get slots
after those assigned by the old vocabulary. -/
theorem language_append_rewrites (name : String) (atoms added : List Atom) :
    (language name (atoms ++ added)).rewrites =
      (language name atoms).rewrites ++
        compileRules (headNames (atoms ++ added)) atoms.length added := by
  have earlier := compileRules_names_agree (headNames atoms ++ headNames added) (headNames atoms)
    atoms 0 (fun _ member => List.idxOf_append_of_mem member)
  simp [language, compileRules_append, earlier]

/-- An append with no executable equation leaves the compiled language intact.
A type declaration can still affect the caller's argument protocol. -/
theorem language_after_fact (name : String) (atoms : List Atom) (fact : Atom)
    (passive : readEquation fact = none) :
    language name (atoms ++ [fact]) = language name atoms := by
  have sameHeads : headNames (atoms ++ [fact]) = headNames atoms := by simp [headNames, passive]
  simp [language, sameHeads, compileRules_append, compileRules, passive]

/-- The ordered, mixed store remains visible to source queries. -/
theorem raw_atoms_exact (atoms : List Atom) :
    loadedAtoms (index atoms) = atoms :=
  loadedAtoms_collect (index_collected atoms)

section Examples

private def coin : Atom := .expression [.symbol "coin"]
private def rule (result : String) : Atom :=
  .expression [.symbol "=", coin, .symbol result]
private def atoms : List Atom := [.symbol "a-fact", rule "heads", rule "tails", rule "heads"]

#guard (language "Example" atoms).validate.isEmpty

example : (candidates (language "Example" atoms) atoms "coin").map (·.body) =
    [.symbol "heads", .symbol "tails", .symbol "heads"] := by decide +kernel

example : (candidates (language "Example" atoms) atoms "other").isEmpty = true := by decide +kernel

end Examples

#print axioms candidates_exact
#print axioms programView_exact
#print axioms step_lookup_iff
#print axioms dispatch_exact
#print axioms step_exact
#print axioms language_append_rewrites
#print axioms language_after_fact

end Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaPresentation
