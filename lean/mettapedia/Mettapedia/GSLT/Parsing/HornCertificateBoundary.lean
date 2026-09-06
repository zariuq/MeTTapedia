import Mettapedia.GSLT.Parsing.HornCertificateGSLT
import Mettapedia.GSLT.Parsing.CanonicalSourceHornElaboration

/-!
# Detecting unseeded relations in clause-only execution

A declaration of an external capability is not an implementation of that
relation. This check exposes the distinction in the existing Horn execution
model. A collection of relations is unseeded when every rule with a head in
the collection requires another premise in the same collection. No finite
derivation can establish any of them, including through mutual recursion.

The check is only a sufficient test for nonderivability. Failure of the check
does not establish derivability. It neither adds primitive evaluation nor
changes the authored program or its rule-occurrence inventory.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.HornCertificateBoundary

open HornCertificate HornCertificateGSLT

/-- Every possible producer needs another member of this unseeded collection. -/
def Unseeded (program : Program) (relations : List String) : Prop :=
  ∀ rule ∈ program, rule.head.relation ∈ relations →
    ∃ premise ∈ rule.body, premise.relation ∈ relations

def checkUnseeded (program : Program) (relations : List String) : Bool :=
  program.all fun rule =>
    !relations.contains rule.head.relation ||
      rule.body.any (fun premise => relations.contains premise.relation)

theorem checkUnseeded_iff (program : Program) (relations : List String) :
    checkUnseeded program relations = true ↔ Unseeded program relations := by
  simp [checkUnseeded, Unseeded, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true, List.contains_eq_mem, or_iff_not_imp_left]

theorem instantiateAtom_relation {substitution : Substitution} {atom : Atom}
    {goal : GroundAtom} (instantiated : instantiateAtom substitution atom = some goal) :
    goal.relation = atom.relation := by
  cases arguments : instantiateTerms substitution atom.arguments with
  | none => simp [instantiateAtom, arguments] at instantiated
  | some values =>
    have same : GroundAtom.mk atom.relation values = goal := by
      simpa [instantiateAtom, arguments] using instantiated
    exact congrArg GroundAtom.relation same.symm

theorem instantiateAtoms_relations {substitution : Substitution} {atoms : List Atom}
    {goals : List GroundAtom}
    (instantiated : instantiateAtoms substitution atoms = some goals) :
    goals.map GroundAtom.relation = atoms.map Atom.relation := by
  induction atoms generalizing goals with
  | nil => simp [instantiateAtoms] at instantiated; simp_all
  | cons atom atoms ih =>
    cases head : instantiateAtom substitution atom with
    | none => simp [instantiateAtoms, head] at instantiated
    | some goal =>
      cases tail : instantiateAtoms substitution atoms with
      | none =>
        simp only [instantiateAtoms] at tail
        simp [instantiateAtoms, head, tail] at instantiated
      | some rest =>
        have same : goal :: rest = goals := by
          simp only [instantiateAtoms] at tail
          simpa [instantiateAtoms, head, tail] using instantiated
        subst goals
        simp [instantiateAtom_relation head, ih tail]

theorem derivationsWithin_member {program : Program} {fuel : Nat}
    {goals : List GroundAtom} (derivations : DerivationsWithin program fuel goals)
    {goal : GroundAtom} (member : goal ∈ goals) :
    DerivesWithin program fuel goal := by
  induction goals with
  | nil => simp at member
  | cons first rest ih =>
    cases derivations with
    | cons head tail =>
      rcases List.mem_cons.mp member with rfl | occurs
      · exact head
      · exact ih tail occurs

/-- This rules out every fuel bound, not just a failed bounded search. -/
theorem Unseeded.not_derivable {program : Program} {relations : List String}
    (unseeded : Unseeded program relations) (fuel : Nat) (goal : GroundAtom)
    (blocked : goal.relation ∈ relations) : ¬ DerivesWithin program fuel goal := by
  induction fuel generalizing goal with
  | zero => intro derivation; cases derivation
  | succ fuel ih =>
    intro derivation
    cases derivation with
    | apply _ _ rule member substitution valid goals head body premises =>
      obtain ⟨premise, occurs, blockedPremise⟩ :=
        unseeded rule member (by rwa [← instantiateAtom_relation head])
      have occursAfter : premise.relation ∈ goals.map GroundAtom.relation := by
        rw [instantiateAtoms_relations body]
        exact List.mem_map.mpr ⟨premise, occurs, rfl⟩
      obtain ⟨next, nextMember, sameRelation⟩ := List.mem_map.mp occursAfter
      exact ih next (by rwa [sameRelation]) (derivationsWithin_member premises nextMember)

theorem Unseeded.no_certificate {program : Program} {relations : List String}
    (unseeded : Unseeded program relations) (fuel : Nat) (goal : GroundAtom)
    (blocked : goal.relation ∈ relations) (certificate : Certificate) :
    replay program fuel goal certificate = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact unseeded.not_derivable fuel goal blocked
    (replay_sound program fuel goal certificate accepted)

theorem Unseeded.no_terminal_path {program : Program} {relations : List String}
    (unseeded : Unseeded program relations) (fuel : Nat) (goal : GroundAtom)
    (blocked : goal.relation ∈ relations) :
    ¬ (theory program).MultiStep [(fuel, goal)] [] := by
  intro path
  exact unseeded.not_derivable fuel goal blocked
    ((derivesWithin_iff_terminal_path program fuel goal).mpr path)

/-- An absent relation is the singleton case of the recursive criterion. -/
theorem unseeded_of_no_head {program : Program} {relation : String}
    (absent : ∀ rule ∈ program, rule.head.relation ≠ relation) :
    Unseeded program [relation] := by
  intro rule member blocked
  exact False.elim (absent rule member (by simpa using blocked))

/-! The same obstruction can be checked on exact authored source rows, without
reducing their term arguments or using a separately maintained rule table. -/

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
open CanonicalSourceHornElaboration

def sourceRelation? : SExpr → Option String
  | .list (.atom name :: _) => some name
  | _ => none

def sourcePatternBlocked (relations : List String) (pattern : SExpr) : Bool :=
  match sourceRelation? pattern with
  | some relation => relations.contains relation
  | none => false

def checkSourceUnseeded (sources : List Source) (relations : List String) : Bool :=
  (compositionRewrites sources).all fun row =>
    !sourcePatternBlocked relations row.head ||
      row.body.any (sourcePatternBlocked relations)

private theorem quoted_atom_blocked {names : List String} {atom : Atom}
    {pattern : SExpr} (quoted : quoteAtom? names atom = some pattern)
    (relations : List String) :
    sourcePatternBlocked relations pattern = relations.contains atom.relation := by
  cases arguments : quoteTerms? names atom.arguments with
  | none => simp [quoteAtom?, arguments] at quoted
  | some values =>
    have same : SExpr.list (.atom atom.relation :: values) = pattern := by
      simpa [quoteAtom?, arguments] using quoted
    subst pattern
    rfl

private theorem quoted_body_blocked {names : List String} {atoms : List Atom}
    {patterns : List SExpr} (quoted : quoteAtoms? names atoms = some patterns)
    (relations : List String) :
    patterns.any (sourcePatternBlocked relations) =
      atoms.any (fun atom => relations.contains atom.relation) := by
  induction atoms generalizing patterns with
  | nil => simp [quoteAtoms?] at quoted; simp_all
  | cons atom atoms ih =>
    cases head : quoteAtom? names atom with
    | none => simp [quoteAtoms?, head] at quoted
    | some pattern =>
      cases tail : List.mapM (quoteAtom? names) atoms with
      | none => simp [quoteAtoms?, head, tail] at quoted
      | some rest =>
        have same : pattern :: rest = patterns := by
          simpa [quoteAtoms?, head, tail] using quoted
        subst patterns
        simp [quoted_atom_blocked head, ih tail]

private theorem quoted_rule_blocked {names : List String} {rule : Rule}
    {row : Rewrite} (quoted : quoteRule? names rule = some row)
    (relations : List String) :
    (!sourcePatternBlocked relations row.head ||
      row.body.any (sourcePatternBlocked relations)) =
    (!relations.contains rule.head.relation ||
      rule.body.any (fun atom => relations.contains atom.relation)) := by
  cases head : quoteAtom? names rule.head with
  | none => simp [quoteRule?, head] at quoted
  | some pattern =>
    cases body : quoteAtoms? names rule.body with
    | none => simp [quoteRule?, head, body] at quoted
    | some patterns =>
      have same : Rewrite.mk rule.name pattern patterns = row := by
        simpa [quoteRule?, head, body] using quoted
      subst row
      simp [quoted_atom_blocked head, quoted_body_blocked body]

theorem unseeded_of_source_check {sources : List Source} {program : Program}
    (elaborated : elaborateProgram? sources = some program) (relations : List String)
    (checked : checkSourceUnseeded sources relations = true) :
    Unseeded program relations := by
  apply (checkUnseeded_iff program relations).mp
  apply List.all_eq_true.mpr
  intro rule member
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  have sourceRow := elaborateProgram?_getElem? elaborated index
  rw [selected] at sourceRow
  cases sourceSelected : (compositionRewrites sources)[index]? with
  | none => simp [sourceSelected] at sourceRow
  | some row =>
    cases rowElaborated : elaborateRewrite? row with
    | none => simp [sourceSelected, rowElaborated] at sourceRow
    | some namedRule =>
      have same : rule = namedRule.2 := by
        simpa [sourceSelected, rowElaborated] using sourceRow
      subst rule
      have rowChecked := List.all_eq_true.mp checked row (List.mem_of_getElem? sourceSelected)
      rw [quoted_rule_blocked (quoteRule?_of_elaborateRewrite? rowElaborated)] at rowChecked
      exact rowChecked

private def cycleProgram : Program :=
  [⟨"left-to-right", ⟨"left", .nil⟩, [⟨"right", .nil⟩]⟩,
   ⟨"right-to-left", ⟨"right", .nil⟩, [⟨"left", .nil⟩]⟩]

theorem mutual_recursion_without_seed_is_detected :
    checkUnseeded cycleProgram ["left", "right"] = true := by decide

theorem mutual_recursion_has_no_finite_proof (fuel : Nat) :
    ¬ DerivesWithin cycleProgram fuel ⟨"left", .nil⟩ :=
  ((checkUnseeded_iff _ _).mp mutual_recursion_without_seed_is_detected).not_derivable
    fuel _ (by simp)

private def seed : Rule := ⟨"right-fact", ⟨"right", .nil⟩, []⟩

theorem adding_a_real_seed_invalidates_the_obstruction :
    checkUnseeded (cycleProgram ++ [seed]) ["left", "right"] = false := by decide

theorem adding_a_real_seed_permits_a_proof :
    DerivesWithin (cycleProgram ++ [seed]) 2 ⟨"left", .nil⟩ := by
  apply replay_sound _ _ _
    (.node ⟨"left-to-right", ⟨"left", .nil⟩, [⟨"right", .nil⟩]⟩ []
      (.cons (.node seed [] .nil) .nil))
  decide

#print axioms Unseeded.not_derivable
#print axioms Unseeded.no_terminal_path

end Mettapedia.GSLT.Parsing.HornCertificateBoundary
