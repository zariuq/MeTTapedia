import Mettapedia.Languages.ProcessCalculi.MORK.CollectionBridge

/-!
# Extended MORK ↔ MeTTaIL Bridge

The exec-rule and source-rule witnesses below use the ad-hoc
`collectionReplaceRule` / `collectionReplaceSourceRule` from
`CollectionBridge.lean`, which require only groundness of old/new atoms. The
proofs do not use the supplied match or RHS-binding evidence, and therefore do
not establish generic translation of `.subst`, collection rests, or arbitrary
MeTTaIL rewrite rules into MORK.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK.ExtendedBridge

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

private abbrev ILP := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
private abbrev ILRRule := Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule
private abbrev ILBind := Mettapedia.OSLF.MeTTaIL.Match.Bindings

private abbrev ilApplyBindings : ILBind → ILP → ILP :=
  Mettapedia.OSLF.MeTTaIL.Match.applyBindings
private abbrev ilMatchPattern : ILP → ILP → List ILBind :=
  Mettapedia.OSLF.MeTTaIL.Match.matchPattern

/-- **Ad-hoc exec-rule calibration**: any two ground encoded atoms can be
    related by a freshly constructed `collectionReplaceRule`. The match and
    RHS-equality arguments retain the intended call shape but are not used by
    this proof, so the result is not a rewrite-compilation theorem. -/
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
#check @fireRule_collectionReplace
#check @fireSourceRule_collectionReplaceSource
end Canaries

/-! ## Axiom audit -/

section AxiomAudit
#print axioms declReduces_extended_mork_fire
#print axioms declReduces_extended_mork_sourceRuleFire
end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK.ExtendedBridge
