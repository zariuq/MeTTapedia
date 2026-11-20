import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.OwnUnknowns

/-!
# Consistent local renaming transports actual CMR firings

Profile: one first-order occurrence-bag store, ambient programs, the existing
one-match judgment and after-tells guards. These transports do not erase rule
origins or choose a batch discipline. The same selected resources and result
are retained by the explicitly transported firing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {P P' : Program (Terms (Term signature))}

def renameFiring (names : Names signature.vars) {a : PUnit}
    (f : Firing O (ext (FirstOrder.action signature)) P a)
    (member : renameRule names.forward f.rule ∈ P') :
    Firing O (ext (FirstOrder.action signature)) P' a :=
  ⟨renameRule names.forward f.rule, member, f.ext,
    fun v => f.opening (names.backward v), f.selection, f.seen⟩

theorem renameFiring_admission_result (names : Names signature.vars)
    (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (member : renameRule names.forward f.rule ∈ P') :
    (f.Admits (frames (FirstOrder.action signature)) s ↔
      (renameFiring names f member).Admits (frames (FirstOrder.action signature)) s) ∧
    f.result (frames (FirstOrder.action signature)) s =
      (renameFiring names f member).result (frames (FirstOrder.action signature)) s := by
  let forward : Subst signature := fun v => .var (names.forward v)
  let backward : Subst signature := fun v => .var (names.backward v)
  have undo : ∀ t ∈ f.rule.terms,
      (FirstOrder.action signature).apply backward
        ((FirstOrder.action signature).apply forward t) = t := by
    intro t _
    exact UnificationRenaming.rename_leftInverse names.forward names.backward names.inverse t
  exact RuleOccurrences.renamed_firing_back (frames (FirstOrder.action signature))
    f.rule forward backward undo f.member member s f.ext f.opening f.selection f.seen

omit [DecidableEq O] in
theorem presentation_renameFiring (names : Names signature.vars) {a : PUnit}
    (f : Firing O (ext (FirstOrder.action signature)) P a)
    (member : renameRule names.forward f.rule ∈ P') :
    presentation (renameFiring names f member) = (presentation f).rename names.forward := by
  simp only [presentation, renameFiring, renameRule, Presentation.rename, RuleInstance.map,
    List.zip_map_left, Multiset.map_coe]
  rfl

omit [DecidableEq O] in
theorem renameFiring_key (names : Names signature.vars) {a : PUnit}
    (f : Firing O (ext (FirstOrder.action signature)) P a)
    (member : renameRule names.forward f.rule ∈ P') :
    identity.key (renameFiring names f member) = identity.key f := by
  change (presentation (renameFiring names f member)).key = (presentation f).key
  rw [presentation_renameFiring]
  exact rename_key names (presentation f)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
