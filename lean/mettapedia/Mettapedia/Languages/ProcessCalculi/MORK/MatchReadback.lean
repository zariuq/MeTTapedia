import Mettapedia.Languages.ProcessCalculi.MORK.ComputableMatchExactness

/-! # Exact readback of structural matches -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- The matcher materializes the original subject, with captures read once.
A capture can itself contain variables belonging to the subject. -/
theorem matchAtom_applySubst_exact {before after : Subst} {pattern subject : Atom}
    (matched : matchAtom before pattern subject = some after) :
    applySubst after pattern = subject :=
  Conformance.Computable.cmatchAtom_applySubst before pattern subject after
    (by simpa only [Conformance.cmatchAtom_eq_matchAtom] using matched)

/-- Readback additionally confirms that every outer template slot is bound. -/
theorem matchAtom_readback {before after : Subst} {pattern subject : Atom}
    (matched : matchAtom before pattern subject = some after) :
    instantiateTemplateAtom? after pattern = some subject := by
  have computableMatch : Conformance.Computable.cmatchAtom before pattern subject = some after :=
    by simpa only [Conformance.cmatchAtom_eq_matchAtom] using matched
  have covered := Conformance.Computable.cmatchAtom_templateCovered
    before pattern subject after computableMatch
  simp [instantiateTemplateAtom?, covered, matchAtom_applySubst_exact matched]

theorem instantiateTemplateAtom?_materializes {after : Subst} {field value : Atom}
    (instantiated : instantiateTemplateAtom? after field = some value) :
    applySubst after field = value := by
  unfold instantiateTemplateAtom? at instantiated
  split at instantiated
  · exact Option.some.inj instantiated
  · contradiction

private theorem mem_applySubstList {after : Subst} {field : Atom} {fields : List Atom}
    (authored : field ∈ fields) :
    applySubst after field ∈ applySubst.applySubstList after fields := by
  induction fields with
  | nil => simp at authored
  | cons first rest ih =>
      rcases List.mem_cons.mp authored with rfl | tail
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih tail)

/-- Each readback of an authored field comes from the reconstructed carrier's
ordered payload list. The caller supplies the field membership witness. -/
theorem materialized_field_instantiation_mem
    {after : Subst} {tag : String} {fields payloads : List Atom} {field value : Atom}
    (replay : applySubst after (.expression (.symbol tag :: fields)) =
      .expression (.symbol tag :: payloads))
    (authored : field ∈ fields)
    (instantiated : instantiateTemplateAtom? after field = some value) : value ∈ payloads := by
  simp only [applySubst, applySubst.applySubstList, Atom.expression.injEq,
    List.cons.injEq, true_and] at replay
  rw [← replay, ← instantiateTemplateAtom?_materializes instantiated]
  exact mem_applySubstList authored

/-- Instantiating a matched factor reads an actual carrier from the input. -/
theorem compat_factor_instantiated_mem (space : List Atom) (patterns : Pattern)
    {after : Subst} {factor value : Atom} (authored : factor ∈ patterns.atoms)
    (matched : after ∈
      (Conformance.Computable.cmatchInputSpec [] space (.compat patterns)).map Prod.fst)
    (instantiated : instantiateTemplateAtom? after factor = some value) : value ∈ space := by
  obtain ⟨carrier, present, materialized⟩ :=
    Conformance.Computable.cmatchInputSpec_compat_factor_replay_origin space patterns factor
      authored matched
  simpa only [← instantiateTemplateAtom?_materializes instantiated, materialized] using present

section Controls

example : instantiateTemplateAtom? [("first", .var "second"), ("second", .symbol "value")]
    (.expression [.var "first", .var "second"]) =
    some (.expression [.var "second", .symbol "value"]) :=
  matchAtom_readback (before := [("second", .symbol "value")]) (by decide)

example : matchAtom [] (.expression [.var "same", .var "same"])
    (.expression [.symbol "first", .symbol "second"]) = none := by decide

end Controls

#print axioms matchAtom_readback
#print axioms materialized_field_instantiation_mem
#print axioms compat_factor_instantiated_mem

end Mettapedia.Languages.ProcessCalculi.MORK
