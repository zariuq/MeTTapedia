import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Amalgamation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Atoms

/-!
# Actual held-row materialization and its private result

A premiseless held rule with no checks materializes its row whenever the
closure reading has a witness compatible with the caller. The existing
admission still checks shapes, physical enabling and solvability. The result
retains the persistent source and labels its fresh ordinary occurrence by the
opened term. Consuming that private occurrence removes it from the final store.

These are the ingredients of the two-firing read expansion, not a claim that
an arbitrary observer can ignore its intermediate state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Materialization

open Interface (Frames)
open RuleOccurrences Opening Amalgamation
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

universe uO uT uH uE uOcc uR uC uZ
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) {O : Type uOcc} [DecidableEq O] {R : Type uR} {C : Type uC} {Z : Type uZ}
  {E : Extensions.{uO, uH, uE} Hom} {codes : Codes Tm C Z} {s : RState Tm O R C Z}
  (f : RFiring O R E codes s)

theorem admits_of_reading (ambient : Set C) (shapes : f.Shapes X ambient)
    (enabled : Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)))
    (noTake : f.spec.body.take = []) (noRead : f.spec.body.read = [])
    (noChecks : f.spec.body.checks = []) (noCollect : f.spec.collect = [])
    (noUnmatched : f.spec.unmatched = []) (noInstalls : f.spec.installs = [])
    (noRemoves : f.spec.removes = []) (noPublishes : f.spec.publishes = [])
    (term : Tm f.spec.locals) (produced : term ∈ f.spec.body.produce)
    {b : Obj} (σ : Hom s.frame b) (known : X.Models σ s.knowledge) (value : Tm b)
    (reading : (rowClosure f term).ReadsAt X σ value) : f.Admits X ambient := by
  obtain ⟨u, solved, _, _⟩ := (readsAt_iff_opened X f ambient shapes.2.2.available shapes.1 noTake noRead
    shapes.2.2.arguments term produced σ known value).mp reading
  refine ⟨shapes, enabled, ⟨b, u, solved⟩, ?_⟩
  intro target assignment _
  exact holds_of_none X f noChecks noCollect noUnmatched noInstalls noRemoves noPublishes assignment

variable [DecidableEq R]

theorem result_label_single (out : O) (term : Tm f.spec.locals)
    (made : f.selection.made = [out]) (produced : f.spec.body.produce = [term]) :
    (f.result X).label out = X.act f.opening term := by
  change relabel (f.base.row X s.toState) f.selection.made (f.base.opened X).produce out = _
  have output : (f.base.opened X).produce = [X.act f.opening term] := by
    simp [Firing.opened, RuleInstance.map, produced]
  rw [made, output]
  simp [relabel]

theorem result_present_single (out : O) (noTaken : f.selection.taken = [])
    (made : f.selection.made = [out]) : (f.result X).present = s.present ∪ {out} := by
  simp [RFiring.result, fire, Selection.commit, noTaken, made]

theorem persistent_source_retained (occurrence : R) (used : f.use = .held occurrence)
    (persistent : (s.held occurrence).mode = .persistent)
    (noRemoved : f.removedRules = []) (noMade : f.madeRules = []) :
    (f.result X).rules = s.rules ∧
      (f.result X).held occurrence = (s.held occurrence).act X (E.weaken f.ext) := by
  constructor
  · change f.kept ∪ f.madeRules.toFinset = s.rules
    rw [f.kept_persistent used persistent noRemoved, noMade, List.toFinset_nil, Finset.union_empty]
  · exact f.result_held_other (by simp [noMade])

theorem consumed_private_instance_is_absent {t : RState Tm O R C Z}
    (consumer : RFiring O R E codes t) (out : O)
    (taken : out ∈ consumer.selection.taken) (notMade : out ∉ consumer.selection.made) :
    out ∉ (consumer.result X).present := by
  change out ∉ fire t.present (consumer.selection.commit (T := Unit))
  simp only [mem_fire, Selection.commit, List.mem_toFinset, not_or, not_and]
  exact ⟨fun _ absent => absent taken, notMade⟩

theorem materialized_reading (ambient : Set C) (available : s.Available ambient f.use)
    (fresh : f.Fresh X) (noTake : f.spec.body.take = []) (noRead : f.spec.body.read = [])
    (lengths : f.spec.params.length = (s.argsOf f.use).length)
    (term : Tm f.spec.locals) (out : O) (made : f.selection.made = [out])
    (produced : f.spec.body.produce = [term]) {b : Obj} (σ : Hom s.frame b)
    (known : X.Models σ s.knowledge) (value : Tm b) :
    (rowClosure f term).ReadsAt X σ value ↔
      ∃ u : Hom (E.target f.ext) b, X.Models u (f.result X).knowledge ∧
        (∀ t, s.Mentions t →
          X.E (X.act u (X.act (E.weaken f.ext) t)) (X.act σ t)) ∧
        X.E (X.act u ((f.result X).label out)) value := by
  have producedMember : term ∈ f.spec.body.produce := by rw [produced]; exact List.mem_singleton_self _
  rw [result_label_single X f out term made produced]
  exact readsAt_iff_opened X f ambient available fresh noTake noRead lengths term producedMember σ known value

#print axioms admits_of_reading
#print axioms result_label_single
#print axioms persistent_source_retained
#print axioms consumed_private_instance_is_absent
#print axioms materialized_reading

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Materialization
