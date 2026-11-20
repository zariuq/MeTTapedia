import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricSemantics

/-!
# Produced bags for a finite family of symmetric CMR matches

Profile: one occurrence-bag store and ambient rules. All members use one
source assignment, with independent local assignments. This value relation
does not choose an admission discipline or erase chronological observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP

variable {signature : LPSignature} {O : Type}

inductive Emissions (label : O → Term signature) (source : Subst signature) :
    List (Class signature O) → Multiset (Term signature) → Prop
  | nil : Emissions label source [] 0
  | cons {key : Class signature O} {rest : List (Class signature O)}
      {produced : List (Term signature)} {later : Multiset (Term signature)}
      (here : realizes key label source produced) (after : Emissions label source rest later) :
      Emissions label source (key :: rest) ((produced : Multiset (Term signature)) + later)

theorem Emissions.perm {label : O → Term signature} {source : Subst signature}
    {first second : List (Class signature O)} (perm : first.Perm second)
    {produced : Multiset (Term signature)} (emits : Emissions label source first produced) :
    Emissions label source second produced := by
  induction perm generalizing produced with
  | nil => exact emits
  | cons key _ ih =>
    cases emits with
    | cons here later => exact .cons here (ih later)
  | swap first second rest =>
    cases emits with
    | cons firstOutput afterFirst =>
      cases afterFirst with
      | cons secondOutput later =>
        simpa only [add_assoc, add_left_comm] using Emissions.cons secondOutput (.cons firstOutput later)
  | trans _ _ first second => exact second (first emits)

theorem emissions_perm_iff {label : O → Term signature} {source : Subst signature}
    {first second : List (Class signature O)} (perm : first.Perm second)
    (produced : Multiset (Term signature)) :
    Emissions label source first produced ↔ Emissions label source second produced :=
  ⟨fun emits => Emissions.perm perm emits, fun emits => Emissions.perm perm.symm emits⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
