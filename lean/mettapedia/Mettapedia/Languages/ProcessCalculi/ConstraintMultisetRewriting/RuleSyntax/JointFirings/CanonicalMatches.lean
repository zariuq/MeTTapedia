import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricReselection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricIncidence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricFinite

/-!
# Ordered representatives of admitted symmetric CMR matches

Profile: one first-order occurrence-bag store, ambient finite rule presentations,
one-match judgments after tells. Normalization sorts only assignments within
identical-pattern groups. Rule-name quotienting is a separate part of class
identity; ordering alone does not canonicalize different local-name spellings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open PatternAssignmentOrder

variable {signature : LPSignature} {O : Type} [LinearOrder O]
  [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {P : Program (Terms (Term signature))}

omit [LinearOrder O] [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols] in
private theorem pair_supply (patterns : List (Term signature)) (selected : List O)
    (length : patterns.length = selected.length) :
    ((patterns.zip selected : List (Term signature × O)) : Multiset (Term signature × O)).map Prod.fst =
      (patterns : Multiset (Term signature)) := by
  rw [Multiset.map_coe, List.map_fst_zip length.le]

omit [LinearOrder O] [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols] in
private theorem rezip (pairs : List (Term signature × O)) (patterns : List (Term signature))
    (source : pairs.map Prod.fst = patterns) : patterns.zip (pairs.map Prod.snd) = pairs := by
  rw [← source, List.zip_map']
  exact List.map_id pairs

def normalizeFiring {a : PUnit} (f : Firing O (ext (FirstOrder.action signature)) P a) :
    Option (Firing O (ext (FirstOrder.action signature)) P a) := do
  let takes ← normalize f.rule.body.take (f.rule.body.take.zip f.selection.taken : List (Term signature × O))
  let reads ← normalize f.rule.body.read (f.rule.body.read.zip f.selection.read : List (Term signature × O))
  pure (reselect f (takes.map Prod.snd) (reads.map Prod.snd))

theorem normalizeFiring_correct (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (admitted : f.Admits (frames (FirstOrder.action signature)) s) :
    ∃ normalized, normalizeFiring f = some normalized ∧
      normalized.Admits (frames (FirstOrder.action signature)) s ∧
      identity.key normalized = identity.key f ∧ normalized.rule = f.rule ∧
      StrictlyOrdered (normalized.rule.body.take.zip normalized.selection.taken) ∧
      Ordered (normalized.rule.body.read.zip normalized.selection.read) := by
  obtain ⟨takes, takeRun, takeContent, takeSource, takeOrdered⟩ := normalize_complete
    f.rule.body.take _ (pair_supply _ _ admitted.1.2.2.2.1)
  obtain ⟨reads, readRun, readContent, readSource, readOrdered⟩ := normalize_complete
    f.rule.body.read _ (pair_supply _ _ admitted.1.2.2.2.2.1)
  have takesZip := rezip takes _ takeSource
  have readsZip := rezip reads _ readSource
  have takesPerm : (f.rule.body.take.zip f.selection.taken).Perm
      (f.rule.body.take.zip (takes.map Prod.snd)) := by
    rw [takesZip]
    exact Multiset.coe_eq_coe.mp takeContent.symm
  have readsPerm : (f.rule.body.read.zip f.selection.read).Perm
      (f.rule.body.read.zip (reads.map Prod.snd)) := by
    rw [readsZip]
    exact Multiset.coe_eq_coe.mp readContent.symm
  have takeSelection : f.selection.taken.Perm (takes.map Prod.snd) := by
    have mapped := takesPerm.map Prod.snd
    rwa [List.map_snd_zip admitted.1.2.2.2.1.ge, takesZip] at mapped
  have readSelection : f.selection.read.Perm (reads.map Prod.snd) := by
    have mapped := readsPerm.map Prod.snd
    rwa [List.map_snd_zip admitted.1.2.2.2.2.1.ge, readsZip] at mapped
  refine ⟨reselect f (takes.map Prod.snd) (reads.map Prod.snd), ?_,
    (reselect_admitted_iff s f _ _ takeSelection readSelection takesPerm readsPerm).mp admitted,
    (reselect_key f _ _ takesPerm readsPerm).symm, rfl, ?_, ?_⟩
  · simp only [normalizeFiring, takeRun, readRun, pure, Pure.pure]
    rfl
  · change StrictlyOrdered (f.rule.body.take.zip (takes.map Prod.snd))
    rw [takesZip]
    exact strict_of_distinct takes takeOrdered (takeSelection.nodup_iff.mp admitted.1.2.1)
  · change Ordered (f.rule.body.read.zip (reads.map Prod.snd))
    rwa [readsZip]

theorem same_rule_pair_bags (s : State (Terms (Term signature)) O)
    (first second : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (firstShapes : first.Shapes (frames (FirstOrder.action signature)) s)
    (secondShapes : second.Shapes (frames (FirstOrder.action signature)) s)
    (rule : first.rule = second.rule) (same : identity.key first = identity.key second) :
    (presentation first).takes = (presentation second).takes ∧
      (presentation first).reads = (presentation second).reads := by
  have related : Same (presentation first) (presentation second) := Quotient.exact same
  have takeRows := related.take_incidence
  have readRows := related.read_incidence
  change first.rule.body.take.map (rowsFor (presentation first).takes) =
    second.rule.body.take.map (rowsFor (presentation second).takes) at takeRows
  change first.rule.body.read.map (rowsFor (presentation first).reads) =
    second.rule.body.read.map (rowsFor (presentation second).reads) at readRows
  rw [← rule] at takeRows readRows
  constructor
  · change (↑(first.rule.body.take.zip first.selection.taken) : Multiset (Term signature × O)) =
      (↑(second.rule.body.take.zip second.selection.taken) : Multiset (Term signature × O))
    apply pairs_eq_of_fibres first.rule.body.take _ _
      (pair_supply _ _ firstShapes.2.2.2.1)
    · rw [rule]
      exact pair_supply _ _ secondShapes.2.2.2.1
    · exact List.map_inj_left.mp takeRows
  · change (↑(first.rule.body.read.zip first.selection.read) : Multiset (Term signature × O)) =
      (↑(second.rule.body.read.zip second.selection.read) : Multiset (Term signature × O))
    apply pairs_eq_of_fibres first.rule.body.read _ _
      (pair_supply _ _ firstShapes.2.2.2.2.1)
    · rw [rule]
      exact pair_supply _ _ secondShapes.2.2.2.2.1
    · exact List.map_inj_left.mp readRows

/-- At a fixed rule presentation, group ordering selects exactly one pair
of take/read assignment words per symmetric class. Fresh output names are
not part of that assignment identity. -/
theorem ordered_class_unique (s : State (Terms (Term signature)) O)
    (first second : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (firstShapes : first.Shapes (frames (FirstOrder.action signature)) s)
    (secondShapes : second.Shapes (frames (FirstOrder.action signature)) s)
    (rule : first.rule = second.rule) (same : identity.key first = identity.key second)
    (firstTake : Ordered (first.rule.body.take.zip first.selection.taken))
    (secondTake : Ordered (second.rule.body.take.zip second.selection.taken))
    (firstRead : Ordered (first.rule.body.read.zip first.selection.read))
    (secondRead : Ordered (second.rule.body.read.zip second.selection.read)) :
    first.selection.taken = second.selection.taken ∧ first.selection.read = second.selection.read := by
  obtain ⟨takes, reads⟩ := same_rule_pair_bags s first second firstShapes secondShapes rule same
  have takePatterns : (first.rule.body.take : List (Term signature)) = second.rule.body.take := by rw [rule]
  have readPatterns : (first.rule.body.read : List (Term signature)) = second.rule.body.read := by rw [rule]
  have takePairs := ordered_unique (first.rule.body.take.zip first.selection.taken)
    (second.rule.body.take.zip second.selection.taken)
    ((List.map_fst_zip firstShapes.2.2.2.1.le).trans
      (takePatterns.trans
        (List.map_fst_zip secondShapes.2.2.2.1.le).symm))
    (Multiset.coe_eq_coe.mp takes) firstTake secondTake
  have readPairs := ordered_unique (first.rule.body.read.zip first.selection.read)
    (second.rule.body.read.zip second.selection.read)
    ((List.map_fst_zip firstShapes.2.2.2.2.1.le).trans
      (readPatterns.trans
        (List.map_fst_zip secondShapes.2.2.2.2.1.le).symm))
    (Multiset.coe_eq_coe.mp reads) firstRead secondRead
  constructor
  · have mapped := congrArg (List.map Prod.snd) takePairs
    simpa only [List.map_snd_zip firstShapes.2.2.2.1.ge,
      List.map_snd_zip secondShapes.2.2.2.1.ge] using mapped
  · have mapped := congrArg (List.map Prod.snd) readPairs
    simpa only [List.map_snd_zip firstShapes.2.2.2.2.1.ge,
      List.map_snd_zip secondShapes.2.2.2.2.1.ge] using mapped

def orderedRepresentative {a : PUnit} (f : Firing O (ext (FirstOrder.action signature)) P a) :
    Firing O (ext (FirstOrder.action signature)) P a := (normalizeFiring f).getD f

theorem orderedRepresentative_correct (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (admitted : f.Admits (frames (FirstOrder.action signature)) s) :
    (orderedRepresentative f).Admits (frames (FirstOrder.action signature)) s ∧
      identity.key (orderedRepresentative f) = identity.key f ∧
      (orderedRepresentative f).rule = f.rule ∧
      StrictlyOrdered ((orderedRepresentative f).rule.body.take.zip (orderedRepresentative f).selection.taken) ∧
      Ordered ((orderedRepresentative f).rule.body.read.zip (orderedRepresentative f).selection.read) := by
  obtain ⟨normalized, run, admitted, key, rule, takeOrder, readOrder⟩ := normalizeFiring_correct s f admitted
  have representative : orderedRepresentative f = normalized := by
    change (normalizeFiring f).getD f = normalized
    rw [run]
    rfl
  rw [representative]
  exact ⟨admitted, key, rule, takeOrder, readOrder⟩

/-- Finite class coverage and executable group normalization together give
exactly one admitted ordered representative per offered class. Choosing the
initial admitted witnesses is still noncomputable. -/
theorem finite_ordered_symmetric_representatives (s : State (Terms (Term signature)) O)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules) :
    ∃ representatives : List (Firing O (ext (FirstOrder.action signature)) P s.frame),
      (representatives.map identity.key).Nodup ∧
      (∀ f ∈ representatives, f.Admits (frames (FirstOrder.action signature)) s ∧
        StrictlyOrdered (f.rule.body.take.zip f.selection.taken) ∧
        Ordered (f.rule.body.read.zip f.selection.read)) ∧
      ∀ f : Firing O (ext (FirstOrder.action signature)) P s.frame,
        f.Admits (frames (FirstOrder.action signature)) s →
          identity.key f ∈ representatives.map identity.key := by
  obtain ⟨originals, distinct, admitted, complete⟩ := finite_admitted_representatives s rules covers
  let representatives := originals.map orderedRepresentative
  have sameKeys : representatives.map identity.key = originals.map identity.key := by
    dsimp only [representatives]
    rw [List.map_map]
    exact List.map_congr_left fun f member => (orderedRepresentative_correct s f (admitted f member)).2.1
  refine ⟨representatives, sameKeys.symm ▸ distinct, ?_, ?_⟩
  · intro f member
    obtain ⟨g, inside, rfl⟩ := List.mem_map.mp member
    have correct := orderedRepresentative_correct s g (admitted g inside)
    exact ⟨correct.1, correct.2.2.2.1, correct.2.2.2.2⟩
  · intro f given
    rw [sameKeys]
    exact complete f given

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
