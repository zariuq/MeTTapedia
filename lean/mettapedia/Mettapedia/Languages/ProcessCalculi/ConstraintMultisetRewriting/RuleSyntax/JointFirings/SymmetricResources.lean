import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.FreshResultNames

/-!
# Resource identities retained by symmetric CMR match classes

Profile: one occurrence-bag store, ambient rules, actual one-match judgments
after tells. Equal classes consume the same source resources; their newly
made occurrence identities can be renamed while fixing the whole source.
Payload/model preservation is proved separately, not inferred from this map.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open MeTTaCalculus.OccurrenceCommits (fire)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {P P' : Program (Terms (Term signature))}

omit [DecidableEq O] in
private theorem zip_occurrences {A : Type*} : ∀ (patterns : List A) (selected : List O),
    patterns.length = selected.length → (patterns.zip selected).map Prod.snd = selected := by
  intro patterns
  induction patterns with
  | nil =>
    intro selected length
    have empty := List.length_eq_zero_iff.mp length.symm
    subst selected
    rfl
  | cons head rest ih =>
    intro selected length
    cases selected with
    | nil => cases length
    | cons o later => simpa only [List.zip_cons_cons, List.map_cons] using congrArg (o :: ·) (ih later (Nat.succ.inj length))

omit [DecidableEq O] in
theorem taken_key (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (shapes : f.Shapes (frames (FirstOrder.action signature)) s) :
    taken (identity.key f) = (f.selection.taken : Multiset O) := by
  change ((f.rule.body.take.zip f.selection.taken : List (Term signature × O)) :
    Multiset (Term signature × O)).map Prod.snd = _
  rw [Multiset.map_coe, zip_occurrences _ _ shapes.2.2.2.1]

theorem same_class_taken (s : State (Terms (Term signature)) O)
    (first : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (second : Firing O (ext (FirstOrder.action signature)) P' s.frame)
    (firstAdmitted : first.Admits (frames (FirstOrder.action signature)) s)
    (secondAdmitted : second.Admits (frames (FirstOrder.action signature)) s)
    (same : identity.key first = identity.key second) :
    (first.selection.taken : Multiset O) = (second.selection.taken : Multiset O) := by
  rw [← taken_key s first firstAdmitted.1, ← taken_key s second secondAdmitted.1, same]

theorem same_class_made_length (s : State (Terms (Term signature)) O)
    (first : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (second : Firing O (ext (FirstOrder.action signature)) P' s.frame)
    (firstAdmitted : first.Admits (frames (FirstOrder.action signature)) s)
    (secondAdmitted : second.Admits (frames (FirstOrder.action signature)) s)
    (same : identity.key first = identity.key second) :
    first.selection.made.length = second.selection.made.length := by
  have arities := congrArg productionArity same
  change first.rule.body.produce.length = second.rule.body.produce.length at arities
  exact firstAdmitted.1.2.2.2.2.2.1.symm.trans
    (arities.trans secondAdmitted.1.2.2.2.2.2.1)

omit [DecidableEq O] in
theorem source_map_fixed (source : Finset O) (rename : Equiv.Perm O)
    (fixes : ∀ o ∈ source, rename o = o) : source.map rename.toEmbedding = source := by
  ext o
  rw [Finset.mem_map]
  constructor
  · rintro ⟨old, member, image⟩
    have same : old = o := (fixes old member).symm.trans image
    exact same ▸ member
  · intro member
    exact ⟨o, member, fixes o member⟩

theorem made_toFinset_map {first second : List O} {rename : Equiv.Perm O}
    (maps : first.map rename = second) : first.toFinset.map rename.toEmbedding = second.toFinset := by
  ext o
  rw [Finset.mem_map, List.mem_toFinset]
  constructor
  · rintro ⟨old, member, image⟩
    have inMap : o ∈ first.map rename := List.mem_map.mpr ⟨old, List.mem_toFinset.mp member, image⟩
    rwa [maps] at inMap
  · intro member
    have inMap : o ∈ first.map rename := by rw [maps]; exact member
    obtain ⟨old, inFirst, image⟩ := List.mem_map.mp inMap
    exact ⟨old, List.mem_toFinset.mpr inFirst, image⟩

theorem same_class_occurrence_renaming (s : State (Terms (Term signature)) O)
    (first : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (second : Firing O (ext (FirstOrder.action signature)) P' s.frame)
    (firstAdmitted : first.Admits (frames (FirstOrder.action signature)) s)
    (secondAdmitted : second.Admits (frames (FirstOrder.action signature)) s)
    (same : identity.key first = identity.key second) :
    ∃ rename : Equiv.Perm O,
      (∀ o ∈ s.present, rename o = o) ∧ first.selection.made.map rename = second.selection.made ∧
      (first.result (frames (FirstOrder.action signature)) s).present.map rename.toEmbedding =
        (second.result (frames (FirstOrder.action signature)) s).present := by
  obtain ⟨rename, maps, fixes⟩ := FreshResultNames.align s.present first.selection.made second.selection.made
    firstAdmitted.1.2.2.1 secondAdmitted.1.2.2.1
    (same_class_made_length s first second firstAdmitted secondAdmitted same)
    (fun o member => fun present => Finset.disjoint_left.mp firstAdmitted.2.1.fresh
      (List.mem_toFinset.mpr member) present)
    (fun o member => fun present => Finset.disjoint_left.mp secondAdmitted.2.1.fresh
      (List.mem_toFinset.mpr member) present)
  refine ⟨rename, fixes, maps, ?_⟩
  have takes : first.selection.taken.toFinset = second.selection.taken.toFinset :=
    congrArg Multiset.toFinset (same_class_taken s first second firstAdmitted secondAdmitted same)
  have old : (s.present \ first.selection.taken.toFinset).map rename.toEmbedding =
      s.present \ first.selection.taken.toFinset :=
    source_map_fixed _ rename (fun o member => fixes o (Finset.mem_sdiff.mp member).1)
  change ((s.present \ first.selection.taken.toFinset) ∪ first.selection.made.toFinset).map rename.toEmbedding =
    (s.present \ second.selection.taken.toFinset) ∪ second.selection.made.toFinset
  rw [Finset.map_union, old, made_toFinset_map maps, takes]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
