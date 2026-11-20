import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationOpening

/-!
# A concrete candidate for the single application rule

The rule, major premise and minor premise use namespace indices zero, one and
two. The premise occurrences may coincide: their datum binders are opened per
position. The candidate reads both premises and allocates one fresh result;
its admission is still the original row-labelled firing judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSyntax

universe uOcc
variable {O : Type uOcc}

def candidate (judgmentTag arrowTag bound : Nat) (s : Store O) (major minor made : O) :
    Firing O E (program judgmentTag arrowTag) s where
  rule := Rule.ofShared (interpreter judgmentTag arrowTag)
  member := Set.mem_singleton _
  ext := PUnit.unit
  opening := privateOpening bound 0
  selection := ⟨[], [major, minor], [made]⟩
  taken i := Fin.elim0 i
  read i := privateUse bound (i.val + 1) (s.label ([major, minor].get i))
  seen := []

theorem candidate_uses (judgmentTag arrowTag bound : Nat) (s : Store O) (major minor made : O) :
    (candidate judgmentTag arrowTag bound s major minor made).uses =
      [⟨s.label major, privateUse bound 1 (s.label major)⟩,
        ⟨s.label minor, privateUse bound 2 (s.label minor)⟩] := by
  rfl

theorem candidate_information (judgmentTag arrowTag bound : Nat) (s : Store O) (major minor made : O) :
    (candidate judgmentTag arrowTag bound s major minor made).information X =
      s.knowledge ++
      (RowUse.information (Tm := RowTerms) X (Subst.id rowSig) (privateUse bound 1 (s.label major)) ++
        RowUse.information (Tm := RowTerms) X (Subst.id rowSig) (privateUse bound 2 (s.label minor))) ++
      [( (privateOpening bound 0).applyTerm (judgment judgmentTag (.var 0) (arrow arrowTag (.var 1) (.var 2))),
          RowUse.value (Tm := RowTerms) X (Subst.id rowSig) (privateUse bound 1 (s.label major))),
        ((privateOpening bound 0).applyTerm (judgment judgmentTag (.var 3) (.var 1)),
          RowUse.value (Tm := RowTerms) X (Subst.id rowSig) (privateUse bound 2 (s.label minor)))] := by
  simp only [Firing.information, candidate_uses]
  simp only [candidate, Firing.takenValues, Firing.takenUses, Firing.readValues, Firing.readUses,
    Rule.ofShared, interpreter, List.ofFn_zero, List.ofFn_succ, List.map_cons,
    List.map_nil, List.zip_nil_right, List.zip_cons_cons,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  dsimp only [E, OneFrame.ext, Extensions.identity]
  change X.applyStore (X.id s.frame) s.knowledge ++
      (RowUse.information (Tm := RowTerms) X (Subst.id rowSig) (privateUse bound 1 (s.label major)) ++
        RowUse.information (Tm := RowTerms) X (Subst.id rowSig) (privateUse bound 2 (s.label minor))) ++
      [((privateOpening bound 0).applyTerm (judgment judgmentTag (.var 0) (arrow arrowTag (.var 1) (.var 2))),
          RowUse.value (Tm := RowTerms) X (Subst.id rowSig) (privateUse bound 1 (s.label major))),
        ((privateOpening bound 0).applyTerm (judgment judgmentTag (.var 3) (.var 1)),
          RowUse.value (Tm := RowTerms) X (Subst.id rowSig) (privateUse bound 2 (s.label minor)))] ++ [] = _
  simp only [Interface.Frames.applyStore_id, List.append_nil]

open JointFirings

abbrev ScopeMember (a : PUnit) :=
  Member Tm E (Set.univ : RuleSyntax.Program RowTerms) (a := a) PUnit.unit

def privateScope {a : PUnit} (bound index : Nat) : Row RowTerms a → List (Nat × ScopeMember a)
  | .shared _ => []
  | .schematic closure =>
      [(index, ⟨RowUse.scopeRule closure, Set.mem_univ _, privateOpening bound index, ⟨[], [], []⟩, []⟩)]

def candidateScopes (judgmentTag arrowTag bound : Nat) (s : Store O) (major minor made : O) :
    List (Nat × ScopeMember s.frame) :=
  (0, (candidate judgmentTag arrowTag bound s major minor made).scopeMember) ::
    (privateScope bound 1 (s.label major) ++ privateScope bound 2 (s.label minor))

private theorem privateScope_opening {a : PUnit} (bound index : Nat) (row : Row RowTerms a)
    (entry : Nat × ScopeMember a) (inside : entry ∈ privateScope bound index row) :
    entry.2.opening = privateOpening bound entry.1 := by
  cases row with
  | shared value => cases inside
  | schematic closure =>
    obtain rfl := List.mem_singleton.mp inside
    rfl

theorem candidateScopes_members (judgmentTag arrowTag bound : Nat) (s : Store O) (major minor made : O) :
    (candidateScopes judgmentTag arrowTag bound s major minor made).map Prod.snd =
      (candidate judgmentTag arrowTag bound s major minor made).scopeBag.members := by
  simp only [candidateScopes, Firing.scopeBag, candidate_uses, List.filterMap_cons, List.filterMap_nil]
  cases first : s.label major <;> cases second : s.label minor <;>
    dsimp only [privateScope, privateUse, RowUse.scopeMember] <;> rfl

theorem candidateScopes_distinct (judgmentTag arrowTag bound : Nat) (s : Store O) (major minor made : O) :
    ((candidateScopes judgmentTag arrowTag bound s major minor made).map Prod.fst).Nodup := by
  cases first : s.label major <;> cases second : s.label minor <;>
    simp [candidateScopes, privateScope, first, second]

theorem candidateScopes_openings (judgmentTag arrowTag bound : Nat) (s : Store O) (major minor made : O)
    (entry : Nat × ScopeMember s.frame)
    (inside : entry ∈ candidateScopes judgmentTag arrowTag bound s major minor made) :
    entry.2.opening = privateOpening bound entry.1 := by
  rcases List.mem_cons.mp inside with rfl | later
  · rfl
  · rcases List.mem_append.mp later with first | second
    · exact privateScope_opening bound 1 (s.label major) entry first
    · exact privateScope_opening bound 2 (s.label minor) entry second

#print axioms candidate_information
#print axioms candidateScopes_members
#print axioms candidateScopes_distinct
#print axioms candidateScopes_openings

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
