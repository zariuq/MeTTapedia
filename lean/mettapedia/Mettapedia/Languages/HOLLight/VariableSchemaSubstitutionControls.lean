import Mettapedia.Languages.OpenTheory.VariableSchemaSubstitution
import Mettapedia.Languages.HOLLight.AdmittedMembershipSchemas

/-!
# Simultaneous variable-schema substitution controls

Crossing replacements are inserted once. A self-referencing replacement does
not recursively substitute itself. Binders retain their own variable while
the two outer parameters exchange positions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.VariableSchemaSubstitutionControls
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ReverseTranslation VariableSchema

abbrev context : HOL.Ctx AtomicTy := [.prop, .prop]
def names : Naming context := Naming.cons (.global "p") (Naming.cons (.global "q") Naming.empty)
def schema : ParameterTerm context (.arr .prop .prop) :=
  .lam (.imp (.var .vz) (.and (.var (.vs .vz)) (.var (.vs (.vs .vz)))))

def entries := [
  AdmittedMembershipSchemas.typedReplacement names "p" (.var (.vs .vz) : HOL.Term Symbol context .prop),
  AdmittedMembershipSchemas.typedReplacement names "q" (.var .vz : HOL.Term Symbol context .prop)]

def crossing : TypeCorrectTermSubstitution where
  raw := ⟨TypeSubst.empty, entries.map Subtype.val⟩
  typeCorrect := by
    intro entry member
    obtain ⟨typed, _, rfl⟩ := List.mem_map.mp member
    exact typed.property

def theta : HOL.Subst Symbol context context
  | _, .vz => .var (.vs .vz)
  | _, .vs .vz => .var .vz

theorem crossing_compatible {type : HOL.Ty AtomicTy} (index : HOL.Var context type) :
    reverseTerm names (theta (index.mapTypes crossing.raw.types.baseInstance)) =
      crossing.raw.applyDB (Naming.env names index) := by
  cases index with
  | vz =>
    change DBTerm.free ⟨.global "q", .bool⟩ =
      crossing.raw.applyDB (.free ⟨.global "p", .bool⟩)
    rw [TermSubst.applyDB_free_of_lookup_some crossing.raw _
      (PrimitiveTransport.checkedSource (reverseCanonical names
        (.var (.vs .vz) : HOL.Term Symbol context .prop))) (by
        simp [crossing, entries, TermSubst.lookup, AdmittedMembershipSchemas.typedReplacement,
          TypeSubst.applyVar, TermSubst.keySame, sourceVarSame, HOL.ImpredicativeConnectives.expand])]
    simpa only [reverseCanonical_term, reverseTerm, reverseTermWith, names, Naming.env,
      Naming.sourceVar, Naming.cons, reverseTy_prop] using
      (congrArg CanonicalTerm.term (PrimitiveTransport.checkedSource_exact
        (reverseCanonical names (.var (.vs .vz) : HOL.Term Symbol context .prop)))).symm
  | vs index =>
    cases index with
    | vz =>
      change DBTerm.free ⟨.global "p", .bool⟩ =
        crossing.raw.applyDB (.free ⟨.global "q", .bool⟩)
      rw [TermSubst.applyDB_free_of_lookup_some crossing.raw _
        (PrimitiveTransport.checkedSource (reverseCanonical names
          (.var .vz : HOL.Term Symbol context .prop))) (by
          simp [crossing, entries, TermSubst.lookup, AdmittedMembershipSchemas.typedReplacement,
            TypeSubst.applyVar, TermSubst.keySame, sourceVarSame, HOL.ImpredicativeConnectives.expand,
            Name.global])]
      simpa only [reverseCanonical_term, reverseTerm, reverseTermWith, names, Naming.env,
        Naming.sourceVar, Naming.cons, reverseTy_prop] using
        (congrArg CanonicalTerm.term (PrimitiveTransport.checkedSource_exact
          (reverseCanonical names (.var .vz : HOL.Term Symbol context .prop)))).symm
    | vs impossible => cases impossible

theorem crossing_under_binder : crossing.apply (reverseCanonical names (embed schema)) =
    reverseCanonical names
      (HOL.Term.lam (.imp (.var .vz) (.and (.var (.vs (.vs .vz))) (.var (.vs .vz))))) := by
  have action := canonical_action crossing schema names names theta (fun index => crossing_compatible index)
  apply action.trans
  rfl

def selfEntries := [AdmittedMembershipSchemas.typedReplacement names "p"
  (.not (.var .vz) : HOL.Term Symbol context .prop)]
def selfReference : TypeCorrectTermSubstitution where
  raw := ⟨TypeSubst.empty, selfEntries.map Subtype.val⟩
  typeCorrect := by
    intro entry member
    obtain ⟨typed, _, rfl⟩ := List.mem_map.mp member
    exact typed.property

theorem self_reference_inserted_once : selfReference.raw.applyDB (.free ⟨.global "p", Ty.bool⟩) =
    reverseTerm names (HOL.ImpredicativeConnectives.expand
      (.not (.var .vz) : HOL.Term Symbol context .prop)) := by
  simp [selfReference, selfEntries, AdmittedMembershipSchemas.typedReplacement,
    TermSubst.applyDB, TermSubst.lookup, TermSubst.keySame, TypeSubst.applyVar,
    TypeSubst.empty, PrimitiveTransport.checkedSource_exact,
    HOL.ImpredicativeConnectives.expand]

theorem crossing_is_not_sequential :
    crossing.raw.applyDB (.free ⟨.global "p", Ty.bool⟩) ≠
      crossing.raw.applyDB (crossing.raw.applyDB (.free ⟨.global "p", Ty.bool⟩)) := by
  have p := crossing_compatible (HOL.Var.vz : HOL.Var context .prop)
  have q := crossing_compatible (HOL.Var.vs .vz : HOL.Var context .prop)
  change DBTerm.free ⟨.global "q", .bool⟩ = crossing.raw.applyDB (.free ⟨.global "p", .bool⟩) at p
  change DBTerm.free ⟨.global "p", .bool⟩ = crossing.raw.applyDB (.free ⟨.global "q", .bool⟩) at q
  rw [← p, ← q]
  intro same
  exact (by decide : ("q" : String) ≠ "p")
    (congrArg (fun key : SourceVar => key.name.component) (DBTerm.free.inj same))

#print axioms crossing_under_binder
#print axioms self_reference_inserted_once
#print axioms crossing_is_not_sequential

end Mettapedia.Languages.HOLLight.VariableSchemaSubstitutionControls
