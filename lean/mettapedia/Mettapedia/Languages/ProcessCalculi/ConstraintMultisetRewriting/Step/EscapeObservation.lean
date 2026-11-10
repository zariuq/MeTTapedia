import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EscapeFirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObservationModuloFrames

/-!
# Traces refine observation in the one-frame instance

The escape-relative isomorphisms (`Transport.EscapeIso`) and the row isomorphisms modulo the
knowledge (`RowIsoModulo`) share their clauses: a frame isomorphism and an occurrence renaming over
the interface's isomorphism of states, and what clients read carried to its counterpart at every
solution of the knowledge (`Frames.Carried`). Here the two meet, in the one-frame transport, whose
renamings are identities.

* **An escape-relative isomorphism is a row isomorphism modulo the knowledge**
  (`escapeIso_rowIsoModulo`): reading the configurations as row states (`ofConfiguration`), with the
  identities the environment's record mentions as `E` (`Observation.Record.support`).
* **Trace-equivalent runs are observationally equivalent at their ends**
  (`traceEquiv_rowEquivalentModulo`, `traceEquiv_observes`): every frame probe that names only
  identities the record mentions observes the same at the ends of two trace-equivalent runs.

When renamings move identities the record mentions, only the probes that its automorphisms keep
agree (`Interface.FrameProbe.observes_iff_of_aut`, for the transports that rename occurrences).

The converse fails in this instance: its isomorphisms keep every label and rename nothing, while
observation identifies rows that the knowledge alone equates, and renames private identities.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Interface (Frames Transport Escaped RowIsoModulo RowEquivalentModulo FrameProbe ofConfiguration)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T)

omit [DecidableEq O] in
theorem renameConfiguration_refl (C : Configuration T O) : renameConfiguration (Equiv.refl O) C = C := by
  obtain ⟨equations, present⟩ := C
  simp [renameConfiguration]

/-- The escape-relative transport of the one-frame instance. -/
abbrev firstOrderEscaping :=
  (firstOrderTransport A label).escaping (firstOrderNatural A label) (firstOrderEscape A label)

/-- **An escape-relative isomorphism is a row isomorphism modulo the knowledge**, relative to the
identities the environment's record mentions. -/
def escapeIso_rowIsoModulo {x y : Escaped (firstOrder A label).toStep} (i : (firstOrderEscaping A label).Iso x y) :
    RowIsoModulo (Observation.Record.support x.record) (ofConfiguration A label x.state) (ofConfiguration A label y.state) :=
  Interface.rowIsoModulo_of_renaming A label Observation.RenamingUpTo.refl
    (by rw [renameConfiguration_refl]; exact i.base.down)

/-- **Trace-equivalent runs end in states related modulo the knowledge**, relative to what the
record mentions at the end. -/
theorem traceEquiv_rowEquivalentModulo {x : Escaped (firstOrder A label).toStep}
    {r r' : (firstOrderEscape A label).step.Run x}
    (equivalent : (firstOrderEscaping A label).TraceEquiv x r r') :
    RowEquivalentModulo (Observation.Record.support r.last.record) (ofConfiguration A label r.last.state)
      (ofConfiguration A label r'.last.state) := by
  obtain ⟨i⟩ := Transport.TraceEquiv.same_last equivalent
  exact ⟨escapeIso_rowIsoModulo A label i⟩

/-- **Traces refine observation**: at the ends of two trace-equivalent runs, every frame probe that
names only identities the record mentions observes the same. -/
theorem traceEquiv_observes {x : Escaped (firstOrder A label).toStep}
    {r r' : (firstOrderEscape A label).step.Run x}
    (equivalent : (firstOrderEscaping A label).TraceEquiv x r r')
    {p : FrameProbe (Frames.ofSubstitution A) PUnit.unit O} (named : p.names ⊆ Observation.Record.support r.last.record) :
    p.Observes (ofConfiguration A label r.last.state) ↔ p.Observes (ofConfiguration A label r'.last.state) := by
  obtain ⟨i⟩ := traceEquiv_rowEquivalentModulo A label equivalent
  exact Interface.FrameProbe.observes_iff_modulo i named

#print axioms escapeIso_rowIsoModulo
#print axioms traceEquiv_rowEquivalentModulo
#print axioms traceEquiv_observes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
