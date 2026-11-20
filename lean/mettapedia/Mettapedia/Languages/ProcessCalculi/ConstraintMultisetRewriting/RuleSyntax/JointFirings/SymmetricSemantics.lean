import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

/-!
# The independent value relation of a CMR match class

Profile: one occurrence-bag store, ambient rules, first-order equations.
Source values and rule-local values are separate assignments. Tells constrain
the local assignment; the existing after-tells guard judgment is unchanged.
The relation is proved invariant before it is lifted to symmetric classes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms)

variable {signature : LPSignature} {O : Type}

def pullLocals (names : signature.vars → signature.vars) (locals : Subst signature) : Subst signature :=
  fun name => locals (names name)

def pushLocals (names : Names signature.vars) (locals : Subst signature) : Subst signature :=
  fun name => locals (names.backward name)

theorem pullLocals_apply (names : signature.vars → signature.vars) (locals : Subst signature)
    (term : Term signature) :
    (pullLocals names locals).applyTerm term = locals.applyTerm (UnificationRenaming.rename names term) := by
  induction term with
  | var _ => rfl
  | const _ => rfl
  | app head fields ih => simp only [Subst.applyTerm, UnificationRenaming.rename_app, ih]

theorem pushLocals_apply (names : Names signature.vars) (locals : Subst signature)
    (term : Term signature) :
    (pushLocals names locals).applyTerm (UnificationRenaming.rename names.forward term) =
      locals.applyTerm term := by
  rw [← pullLocals_apply]
  have same : pullLocals names.forward (pushLocals names locals) = locals := by
    funext name
    exact congrArg locals (names.inverse name)
  rw [same]

def Presentation.uses (match_ : Presentation signature O) : Multiset (Term signature × O) :=
  match_.takes + match_.reads

theorem uses_rename (names : signature.vars → signature.vars) (match_ : Presentation signature O) :
    (match_.rename names).uses =
      match_.uses.map (fun pair => (UnificationRenaming.rename names pair.1, pair.2)) := by
  simp [Presentation.uses, Presentation.rename]

/-- A source assignment and an independent local assignment realize exactly
the selected equations, tells and ordered produced values. -/
def Presentation.Realizes (match_ : Presentation signature O) (label : O → Term signature)
    (source : Subst signature) (produced : List (Term signature)) : Prop :=
  ∃ locals : Subst signature,
    (∀ pair ∈ match_.uses, locals.applyTerm pair.1 = source.applyTerm (label pair.2)) ∧
      Unifies locals match_.rule.body.tell ∧ produced = match_.rule.body.produce.map locals.applyTerm

theorem realizes_rename (names : Names signature.vars) (match_ : Presentation signature O)
    (label : O → Term signature) (source : Subst signature) (produced : List (Term signature)) :
    (match_.rename names.forward).Realizes label source produced ↔
      match_.Realizes label source produced := by
  constructor
  · rintro ⟨locals, pairs, tells, output⟩
    refine ⟨pullLocals names.forward locals, ?_, ?_, ?_⟩
    · intro pair member
      rw [pullLocals_apply]
      exact pairs (UnificationRenaming.rename names.forward pair.1, pair.2)
        (by rw [uses_rename]; exact Multiset.mem_map.mpr ⟨pair, member, rfl⟩)
    · intro equation member
      rw [pullLocals_apply, pullLocals_apply]
      exact tells _ (List.mem_map.mpr ⟨equation, member, rfl⟩)
    · rw [output]
      change (match_.rule.body.produce.map (UnificationRenaming.rename names.forward)).map
        locals.applyTerm = _
      rw [List.map_map]
      apply List.map_congr_left
      intro term _
      exact (pullLocals_apply names.forward locals term).symm
  · rintro ⟨locals, pairs, tells, output⟩
    refine ⟨pushLocals names locals, ?_, ?_, ?_⟩
    · intro pair member
      rw [uses_rename] at member
      obtain ⟨original, inOriginal, rfl⟩ := Multiset.mem_map.mp member
      rw [pushLocals_apply]
      exact pairs original inOriginal
    · intro equation member
      obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
      rw [pushLocals_apply, pushLocals_apply]
      exact tells original inOriginal
    · simpa only [Presentation.rename, renameRule, RuleInstance.map, List.map_map,
        Function.comp_def, pushLocals_apply] using output

theorem Same.realizes_iff {first second : Presentation signature O} (same : Same first second)
    (label : O → Term signature) (source : Subst signature) (produced : List (Term signature)) :
    first.Realizes label source produced ↔ second.Realizes label source produced := by
  induction same with
  | rel first second change =>
    obtain ⟨names, rfl⟩ := change
    exact (realizes_rename names first label source produced).symm
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

def realizes (key : Class signature O) (label : O → Term signature)
    (source : Subst signature) (produced : List (Term signature)) : Prop :=
  Quotient.liftOn key (fun match_ => match_.Realizes label source produced)
    (fun _ _ same => propext (Same.realizes_iff same label source produced))

theorem realizes_key (match_ : Presentation signature O) (label : O → Term signature)
    (source : Subst signature) (produced : List (Term signature)) :
    realizes match_.key label source produced ↔ match_.Realizes label source produced := Iff.rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
