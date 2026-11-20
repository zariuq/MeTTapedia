import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationCandidateFresh

/-!
# An independent direct schematic-read firing

The rule reads one occurrence and makes its value at a new occurrence. It is
an actual firing of `singleFiring`, with two independent namespace slots for
the rule and the selected datum. No held-rule execution occurs in its
definition. Its information and joint freshness use the existing row opening
and protected-source constructions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadDirect

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationMachine (RowTerms Store X E privateOpening privateUse privateScope ScopeMember sourceBound)

universe uOcc
variable {O : Type uOcc}

def readRule : RuleSyntax.Rule RowTerms :=
  ⟨PUnit.unit, ⟨[], [.var 0], [], [], [.var 0]⟩, []⟩

def program : Set (Rule RowTerms) := {Rule.ofShared readRule}

def candidate (bound : Nat) (s : Store O) (selected made : O) : Firing O E program s where
  rule := Rule.ofShared readRule
  member := Set.mem_singleton _
  ext := PUnit.unit
  opening := privateOpening bound 0
  selection := ⟨[], [selected], [made]⟩
  taken i := Fin.elim0 i
  read i := privateUse bound 1 (s.label ([selected].get i))
  seen := []

theorem candidate_uses (bound : Nat) (s : Store O) (selected made : O) :
    (candidate bound s selected made).uses =
      [⟨s.label selected, privateUse bound 1 (s.label selected)⟩] := rfl

theorem candidate_information (bound : Nat) (s : Store O) (selected made : O) :
    (candidate bound s selected made).information X = s.knowledge ++
      RowUse.information (Tm := RowTerms) X (Subst.id rowSig) (privateUse bound 1 (s.label selected)) ++
      [((privateOpening bound 0).applyTerm (.var 0),
        RowUse.value (Tm := RowTerms) X (Subst.id rowSig) (privateUse bound 1 (s.label selected)))] := by
  simp only [Firing.information, candidate_uses]
  simp only [candidate, Firing.takenValues, Firing.takenUses, Firing.readValues, Firing.readUses,
    Rule.ofShared, readRule, List.ofFn_zero, List.ofFn_succ, List.map_cons,
    List.map_nil, List.zip_nil_right, List.zip_cons_cons,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  dsimp only [E, OneFrame.ext, Extensions.identity]
  change X.applyStore (X.id s.frame) s.knowledge ++
      RowUse.information (Tm := RowTerms) X (Subst.id rowSig) (privateUse bound 1 (s.label selected)) ++
      [((privateOpening bound 0).applyTerm (.var 0),
        RowUse.value (Tm := RowTerms) X (Subst.id rowSig) (privateUse bound 1 (s.label selected)))] ++ [] = _
  simp only [Interface.Frames.applyStore_id, List.append_nil]

def scopeEntries (bound : Nat) (s : Store O) (selected made : O) :
    List (Nat × ScopeMember s.frame) :=
  (0, (candidate bound s selected made).scopeMember) :: privateScope bound 1 (s.label selected)

theorem scopeEntries_members (bound : Nat) (s : Store O) (selected made : O) :
    (scopeEntries bound s selected made).map Prod.snd =
      (candidate bound s selected made).scopeBag.members := by
  simp only [scopeEntries, Firing.scopeBag, candidate_uses, List.filterMap_cons, List.filterMap_nil]
  cases row : s.label selected <;>
    dsimp only [privateScope, privateUse, RowUse.scopeMember] <;> rfl

theorem scopeEntries_distinct (bound : Nat) (s : Store O) (selected made : O) :
    ((scopeEntries bound s selected made).map Prod.fst).Nodup := by
  cases row : s.label selected <;> simp [scopeEntries, privateScope, row]

theorem scopeEntries_openings (bound : Nat) (s : Store O) (selected made : O)
    (entry : Nat × ScopeMember s.frame) (inside : entry ∈ scopeEntries bound s selected made) :
    entry.2.opening = privateOpening bound entry.1 := by
  rcases List.mem_cons.mp inside with rfl | later
  · rfl
  · cases row : s.label selected with
    | shared value => simp [row, privateScope] at later
    | schematic datum =>
      simp only [row, privateScope] at later
      obtain rfl := List.mem_singleton.mp later
      rfl

open JointFirings

theorem candidate_fresh (s : Store O) (selected made : O) :
    (candidate (sourceBound s) s selected made).Fresh X := by
  rcases s with ⟨frame, knowledge, present, label⟩
  cases frame
  let source : Store O := ⟨PUnit.unit, knowledge, present, label⟩
  let family := scopeEntries (sourceBound source) source selected made
  have distinct : (family.map Prod.fst).Nodup :=
    scopeEntries_distinct (sourceBound source) source selected made
  have opened : ∀ entry ∈ family,
      entry.2.opening = FreshNamespaces.opening (Equiv.refl Nat) (sourceBound source) entry.1 :=
    scopeEntries_openings (sourceBound source) source selected made
  have below : ∀ term,
      (⟨PUnit.unit, source.scope.knowledge, source.scope.present, source.scope.label⟩ :
        RuleSyntax.State RowTerms Tm).Mentions term →
      ∀ name ∈ term.freeVars, (Equiv.refl Nat) name < sourceBound source :=
    fun term mentioned name occurs => ApplicationMachine.mentioned_below source term mentioned name occurs
  have fresh := FreshNamespaces.fresh (Equiv.refl Nat) (sourceBound source)
    source.scope.knowledge source.scope.present source.scope.label family distinct opened below
  change Bag.Fresh X source.scope
    (⟨PUnit.unit, (candidate (sourceBound source) source selected made).scopeBag.members⟩ :
      Bag Tm E (Set.univ : RuleSyntax.Program RowTerms) PUnit.unit)
  rw [← scopeEntries_members]
  exact fresh

variable [DecidableEq O]

theorem result_present (bound : Nat) (s : Store O) (selected made : O) :
    ((candidate bound s selected made).result X).present = s.present ∪ {made} := by
  simp [Firing.result, MeTTaCalculus.OccurrenceCommits.fire, Selection.commit, candidate]

theorem result_label_made (bound : Nat) (s : Store O) (selected made : O) :
    ((candidate bound s selected made).result X).label made =
      .shared ((privateOpening bound 0).applyTerm (.var 0)) := by
  change RuleSyntax.relabel (Tm := fun a => Row RowTerms a) (a := s.frame)
    ((candidate bound s selected made).row X) [made]
    [.shared ((privateOpening bound 0).applyTerm (.var 0))] made = _
  simp [RuleSyntax.relabel]

#print axioms candidate_information
#print axioms scopeEntries_members
#print axioms candidate_fresh
#print axioms result_present
#print axioms result_label_made

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadDirect
