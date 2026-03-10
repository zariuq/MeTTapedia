import Mettapedia.Languages.ProcessCalculi.MORK.CollectionBridge

/-!
# Extended MORK ↔ MeTTaIL Bridge

Extends the base `MeTTaILBridge` with theorems for rewrite rules whose RHS
contains `.subst` nodes or collection rest-variables. These patterns are
*eliminated* by `applyBindings` (which calls `openBVar` for `.subst` and
splices rest-variable lookups), so the post-application result is always in
the `morkTranslatable` fragment — as proven by `morkTranslatable_applyBindings`
in `MeTTaILBridge.lean`.

The exec-rule and source-rule fire witnesses use the ad-hoc
`collectionReplaceRule` / `collectionReplaceSourceRule` from
`CollectionBridge.lean`, which require only groundness of old/new atoms.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK.ExtendedBridge

open Mettapedia.Languages.MeTTa.Core (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

private abbrev ILP := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
private abbrev ILRRule := Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule
private abbrev ILBind := Mettapedia.OSLF.MeTTaIL.Match.Bindings

private abbrev ilApplyBindings : ILBind → ILP → ILP :=
  Mettapedia.OSLF.MeTTaIL.Match.applyBindings
private abbrev ilMatchPattern : ILP → ILP → List ILBind :=
  Mettapedia.OSLF.MeTTaIL.Match.matchPattern

/-- **Extended exec-rule bridge**: a MeTTaIL rewrite step fires via an ad-hoc
    `collectionReplaceRule`, even when the rule's RHS uses `.subst` or rest-vars.

    Unlike `declReduces_topRule_fvar_mork_fire` (which requires `morkTranslatable r.right`),
    this theorem has NO translatability requirement on `r.right` — it relies on
    `applyBindings` normalizing the RHS, combined with the ad-hoc replace rule. -/
theorem declReduces_extended_mork_fire (p q : ILP) (r : ILRRule)
    (bs : ILBind) (_hbs : bs ∈ ilMatchPattern r.left p)
    (_hrhs : ilApplyBindings bs r.right = q)
    (hground_p : isGroundAtom (morkPatternToAtom p) = true)
    (hground_q : isGroundAtom (morkPatternToAtom q) = true) :
    ∃ rule : ExecRule,
      patternToSpace q ∈ fireRule (patternToSpace p) rule := by
  refine ⟨collectionReplaceRule (morkPatternToAtom p) (morkPatternToAtom q), ?_⟩
  simp only [patternToSpace]
  have := fireRule_collectionReplace {morkPatternToAtom p} _ _
    (Finset.mem_singleton_self _) hground_p hground_q
  simp [Finset.erase_eq] at this
  exact this

/-- **Extended source-rule bridge**: same as above but at the `SourceExecRule` /
    `fireSourceRule` level. -/
theorem declReduces_extended_mork_sourceRuleFire (p q : ILP) (r : ILRRule)
    (bs : ILBind) (_hbs : bs ∈ ilMatchPattern r.left p)
    (_hrhs : ilApplyBindings bs r.right = q)
    (hground_p : isGroundAtom (morkPatternToAtom p) = true)
    (hground_q : isGroundAtom (morkPatternToAtom q) = true)
    {workspace : Space} (hp_in : morkPatternToAtom p ∈ workspace) :
    ∃ rule : SourceExecRule,
      ∃ S ∈ fireSourceRule workspace rule, True :=
  ⟨collectionReplaceSourceRule (morkPatternToAtom p) (morkPatternToAtom q),
    workspace.erase (morkPatternToAtom p) ∪ {morkPatternToAtom q},
    fireSourceRule_collectionReplaceSource workspace _ _ hp_in hground_p hground_q,
    trivial⟩

/-! ## Canaries -/

section Canaries
#check @declReduces_extended_mork_fire
#check @declReduces_extended_mork_sourceRuleFire
-- Re-check the base bridge theorem
#check @Mettapedia.Languages.ProcessCalculi.MORK.morkTranslatable_applyBindings
end Canaries

/-! ## Axiom audit -/

section AxiomAudit
#print axioms declReduces_extended_mork_fire
#print axioms declReduces_extended_mork_sourceRuleFire
end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK.ExtendedBridge
