import Mettapedia.GSLT.Parsing.ClassAwareParserPackReplay

/-! A finite certificate determines its CST, not only the replay proof at an
already fixed CST. This links executable replay output to independently
constructed source derivations without choosing another parse. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareParserPackOutput

open ParserProfileSemantics PresentationExprSemantics
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate

private theorem terminal_output {profile : ParserProfileLayer} {input : List Nat}
    {matcher : TerminalMatcher} {start stop : Nat} {first second : List CST}
    (left : CSTTerminalMatchesAt profile input matcher start stop first)
    (right : CSTTerminalMatchesAt profile input matcher start stop second) : first = second :=
  left.property.symm.trans ((ClassAwareParserPackLexicalReplay.terminalOutput_exact left.val).trans
    ((ClassAwareParserPackLexicalReplay.terminalOutput_exact right.val).symm.trans right.property))

mutual
  theorem output_unique {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {certificate : Certificate} {sort : String} {start stop : Nat}
      {first second : CST}
      (left : Replays profile plan input certificate sort start stop first)
      (right : Replays profile plan input certificate sort start stop second) : first = second := by
    cases left <;> cases right
    · exact congrArg₂ (CST.node · _ _ ·) (by simp_all only) (terminal_output ‹_› ‹_›)
    · exact congrArg₂ (CST.node · _ _ ·) (by simp_all only) (items_output_unique ‹_› ‹_›)


  theorem items_output_unique {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {certificate : ItemsCertificate} {items : List PackItem}
      {start stop : Nat} {first second : List CST}
      (left : ItemsReplays profile plan input certificate items start stop first)
      (right : ItemsReplays profile plan input certificate items start stop second) : first = second := by
    cases left <;> cases right
    · rfl
    · exact items_output_unique ‹_› ‹_›
    · exact congrArg₂ List.cons (output_unique ‹_› ‹_›) (items_output_unique ‹_› ‹_›)

end

/-- A valid certificate replays to its exact tree and evidence, including
physical production identity. Typed readers may enrich this single result. -/
theorem replay_exact {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {certificate : Certificate} {sort : String} {start stop : Nat} {tree : CST}
    (source : Replays profile plan input certificate sort start stop tree) :
    ClassAwareParserPackReplay.replay profile plan input sort start stop certificate = some ⟨tree, source⟩ := by
  obtain ⟨result, found⟩ := Option.isSome_iff_exists.mp (ClassAwareParserPackReplay.replay_complete source)
  obtain ⟨actual, replayed⟩ := result
  cases output_unique replayed source
  simpa only [Replays.unique replayed source] using found

theorem replay_output {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {certificate : Certificate} {sort : String} {start stop : Nat} {tree : CST}
    (source : Replays profile plan input certificate sort start stop tree) :
    (ClassAwareParserPackReplay.replay profile plan input sort start stop certificate).map Sigma.fst = some tree := by
  rw [replay_exact source]
  rfl

#print axioms output_unique
#print axioms items_output_unique
#print axioms replay_output

end Mettapedia.GSLT.Parsing.ClassAwareParserPackOutput
