import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Selection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Regions

/-!
# A direct single-firing instance with per-datum binders

Choices: an occurrence-bag store, one firing, guards after its matching and told
equations, a fixed set of row rules, and one knowledge store. Each source datum
independently chooses shared or schematic variables. This selects no language
default and does not change the original single-firing construction.

Selected schematic rows contribute independently opened local knowledge and
capture equations. Their stored code is not rewritten. Source-row observations
use the common region-query interface; every pattern remains in the rule's
freshness scope. Shared outputs and explicit schematic closure outputs are
distinguished by the rule syntax. Closing an arbitrary existing shared witness
is not inferred automatically.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows

open Interface (Frames)
open PredicateQueryAdmission (RegionQuery)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uE uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

namespace Firing

variable (X : Frames Tm Hom) {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom}
  {P : Set (Rule Tm)} {s : State Tm O} (f : Firing O E P s)

def row (o : O) : Row Tm (E.target f.ext) := (s.label o).act X (E.weaken f.ext)

def checkHolds {b : Obj} (σ : Hom (E.target f.ext) b) : Check (Tm f.rule.basic.locals) → Prop
  | .equal left right => X.E (X.act σ (X.act f.opening left)) (X.act σ (X.act f.opening right))
  | .predicate quantifier pattern =>
      (RegionQuery.predicate quantifier (Regions.membership X (X.act f.opening pattern))).Holds σ
        (f.row X) s.present
  | .count pattern number =>
      (RegionQuery.count (Regions.membership X (X.act f.opening pattern)) number).Holds σ (f.row X) s.present

def Holds {b : Obj} (σ : Hom (E.target f.ext) b) : Prop :=
  (∀ check ∈ f.rule.basic.body.checks, f.checkHolds X σ check) ∧
    ∀ query ∈ (f.rule.basic.collect.map (X.act f.opening)).zip f.seen,
      (RegionQuery.exact (Regions.membership X query.1) query.2).Holds σ (f.row X) s.present

def Shapes : Prop :=
  f.Fresh X ∧ f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧
    f.rule.basic.body.take.length = f.selection.taken.length ∧
    f.rule.basic.body.read.length = f.selection.read.length ∧
    f.rule.basic.body.produce.length + f.rule.schematic.length = f.selection.made.length ∧
    f.rule.basic.collect.length = f.seen.length ∧
    (∀ selected ∈ f.uses, selected.1.WellFormed) ∧
    ∀ output ∈ f.rule.schematic, output.WellFormed

variable [DecidableEq O]

def Admits : Prop :=
  f.Shapes X ∧ Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    X.Solvable (f.information X) ∧ X.Entails (f.information X) (fun _ σ => f.Holds X σ)

def result : State Tm O where
  frame := E.target f.ext
  knowledge := f.information X
  present := fire s.present (f.selection.commit (T := Unit))
  label := RuleSyntax.relabel (Tm := fun a => Row Tm a) (a := E.target f.ext)
    (f.row X) f.selection.made (f.rule.outputs X f.opening)

end Firing

variable (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O]
  (E : Extensions.{uO, uH, uE} Hom) (P : Set (Rule Tm))

def singleFiring : Interface.Step.Standard X O (State Tm O) (Firing O E P) where
  frame s := s.frame
  knowledge s := s.knowledge
  present s := s.present
  selection f := f.selection
  target f := E.target f.ext
  extension f := E.weaken f.ext
  information f := f.information X
  transported := by
    intro s f equation member
    have transported : (X.act (E.weaken f.ext) equation.1, X.act (E.weaken f.ext) equation.2) ∈
        X.applyStore (E.weaken f.ext) s.knowledge := List.mem_map_of_mem member
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ transported)))
  Shapes f := f.Shapes X
  Holds f _ σ := f.Holds X σ
  Admits f := f.Admits X
  admits_iff _ := Iff.rfl
  preparedResult f _ := f.result X
  present_preparedResult _ _ := rfl
  preparedSettle f _ := X.id (E.target f.ext)
  knowledge_preparedResult f _ := (Frames.applyStore_id (X := X) (f.information X)).symm

#print axioms singleFiring

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows
