import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Step
import Mathlib.Data.List.OfFn

/-!
# The shared-row fragment and the original single-firing construction

The program embedding chooses only shared outputs. Source occurrence identities,
rule syntax, selections, openings and collect claims remain unchanged. No row-local
activation is needed. The scope view has exactly the original ambient terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Shared

open Interface (Frames)

universe uO uT uH uE uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : RuleSyntax.Program Tm}

def program (P : RuleSyntax.Program Tm) : Set (Rule Tm) :=
  {rule | rule.basic ∈ P ∧ rule.schematic = []}

def lift (s : RuleSyntax.State Tm O) (f : RuleSyntax.Firing O E P s.frame) :
    Firing O E (program P) (State.ofShared s) where
  rule := Rule.ofShared f.rule
  member := ⟨f.member, rfl⟩
  ext := f.ext
  opening := f.opening
  selection := f.selection
  taken i := .shared (s.label (f.selection.taken.get i))
  read i := .shared (s.label (f.selection.read.get i))
  seen := f.seen

theorem taken_values (X : Frames Tm Hom) (s : RuleSyntax.State Tm O) (f : RuleSyntax.Firing O E P s.frame) :
    (lift s f).takenValues X = f.selection.taken.map (f.row X s) := by
  simp only [Firing.takenValues, Firing.takenUses, lift, List.map_ofFn, RowUse.value]
  change List.ofFn (fun i => f.row X s f.selection.taken[i.val]) = _
  exact List.ofFn_getElem_eq_map f.selection.taken (f.row X s)

theorem read_values (X : Frames Tm Hom) (s : RuleSyntax.State Tm O) (f : RuleSyntax.Firing O E P s.frame) :
    (lift s f).readValues X = f.selection.read.map (f.row X s) := by
  simp only [Firing.readValues, Firing.readUses, lift, List.map_ofFn, RowUse.value]
  change List.ofFn (fun i => f.row X s f.selection.read[i.val]) = _
  exact List.ofFn_getElem_eq_map f.selection.read (f.row X s)

theorem selected_scope_members_empty (s : RuleSyntax.State Tm O) (f : RuleSyntax.Firing O E P s.frame) :
    (lift s f).uses.filterMap (fun selected => RowUse.scopeMember E (lift s f).ext selected.2) = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro selected member
  rcases List.mem_append.mp member with taken | read
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp taken
    rfl
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp read
    rfl

theorem fresh_iff (X : Frames Tm Hom) (s : RuleSyntax.State Tm O) (f : RuleSyntax.Firing O E P s.frame) :
    (lift s f).Fresh X ↔ f.Fresh X s := by
  unfold Firing.Fresh Firing.scopeBag
  rw [selected_scope_members_empty]
  change (∀ b g h, ∃ u,
    (∀ term, (State.ofShared s).scope.Mentions term →
      X.E (X.act u (X.act (E.weaken f.ext) term)) (X.act g term)) ∧
    ∀ term ∈ (Rule.ofShared f.rule).scope.terms,
      X.E (X.act u (X.act f.opening term)) (X.act h term)) ↔ f.Fresh X s
  have terms : (Rule.ofShared f.rule).scope.terms = f.rule.terms := by
    have transport : ∀ (first second : RuleSyntax.Rule Tm), first = second →
        HEq first.terms second.terms := by
      intro first second same
      cases same
      rfl
    exact eq_of_heq (transport _ _ (Rule.scope_ofShared f.rule))
  constructor
  · intro fresh b g h
    obtain ⟨u, source, localTerms⟩ := fresh b g h
    refine ⟨u, fun term member => source term ((State.shared_scope_mentions_iff s term).mpr member), ?_⟩
    intro term member
    exact localTerms term (terms.symm ▸ member)
  · intro fresh b g h
    obtain ⟨u, source, localTerms⟩ := fresh b g h
    refine ⟨u, fun term member => source term ((State.shared_scope_mentions_iff s term).mp member), ?_⟩
    intro term member
    exact localTerms term (terms ▸ member)

#print axioms taken_values
#print axioms read_values
#print axioms selected_scope_members_empty
#print axioms fresh_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Shared
