import Mettapedia.GSLT.Parsing.HornHeadEnumeration
import Mettapedia.GSLT.Parsing.HornSpecialization

/-!
# Specialization heads arise from compiler head enumeration

This module connects a checked symbolic specialization to apart-renamed Horn
head matching.  Residual variables in the specialized query live in the
query namespace; variables of the admitted source rule live in the rule
namespace.  Applying the symbolic substitution therefore gives an explicit
unifier without relying on numeric variable names being globally fresh.
-/

namespace Mettapedia.GSLT.Parsing.HornSpecializationHead

open HornCertificate HornSpecialization HornUnification HornHeadEnumeration

def symbolicLPSubstitution (substitution : SymbolicSubstitution) :
    Mettapedia.Logic.LP.Subst compilerSignature
  | { origin := .query, identifier := identifier } =>
      .var { origin := .query, identifier := identifier }
  | { origin := .rule, identifier := identifier } =>
      match lookupSymbolic identifier substitution with
      | none => .var { origin := .rule, identifier := identifier }
      | some value => encodeScopedTerm .query value

mutual
  theorem symbolicLPSubstitution_apply_encodeTerm
      (substitution : SymbolicSubstitution) (source target : Term)
      (instantiated : instantiateSymbolicTerm substitution source = some target) :
      (symbolicLPSubstitution substitution).applyTerm
          (encodeScopedTerm .rule source) =
        encodeScopedTerm .query target := by
    cases source with
    | var identifier =>
        cases found : lookupSymbolic identifier substitution with
        | none => simp [instantiateSymbolicTerm, found] at instantiated
        | some value =>
            simp [instantiateSymbolicTerm, found] at instantiated
            subst target
            simp [encodeScopedTerm, symbolicLPSubstitution, found]
    | atom name =>
        simp [instantiateSymbolicTerm] at instantiated
        subst target
        rfl
    | integer value =>
        simp [instantiateSymbolicTerm] at instantiated
        subst target
        rfl
    | app constructor arguments =>
        cases found : instantiateSymbolicTerms substitution arguments with
        | none => simp [instantiateSymbolicTerm, found] at instantiated
        | some targetArguments =>
            simp [instantiateSymbolicTerm, found] at instantiated
            subst target
            have argumentsEqual :=
              symbolicLPSubstitution_apply_encodeTerms substitution arguments
                targetArguments found
            have lengths :
                (encodeScopedTerms .rule arguments).length =
                  (encodeScopedTerms .query targetArguments).length := by
              simpa using congrArg List.length argumentsEqual
            simp only [encodeScopedTerm, Mettapedia.Logic.LP.Subst.applyTerm]
            congr 1
            · exact congrArg (fun arity =>
                ({ name := constructor, arity := arity } : FunctionSymbol))
                lengths
            apply (Fin.heq_fun_iff lengths).2
            intro index
            have pointwise := List.get_of_eq argumentsEqual
              (⟨index.val, by simp⟩ :
                Fin ((encodeScopedTerms .rule arguments).map
                  (symbolicLPSubstitution substitution).applyTerm).length)
            simpa using pointwise

  theorem symbolicLPSubstitution_apply_encodeTerms
      (substitution : SymbolicSubstitution) (sources targets : Terms)
      (instantiated : instantiateSymbolicTerms substitution sources = some targets) :
      (encodeScopedTerms .rule sources).map
          (symbolicLPSubstitution substitution).applyTerm =
        encodeScopedTerms .query targets := by
    cases sources with
    | nil =>
        simp [instantiateSymbolicTerms] at instantiated
        subst targets
        rfl
    | cons head tail =>
        cases headFound : instantiateSymbolicTerm substitution head with
        | none => simp [instantiateSymbolicTerms, headFound] at instantiated
        | some targetHead =>
            cases tailFound : instantiateSymbolicTerms substitution tail with
            | none =>
                simp [instantiateSymbolicTerms, headFound, tailFound] at instantiated
            | some targetTail =>
                simp [instantiateSymbolicTerms, headFound, tailFound] at instantiated
                subst targets
                simp only [encodeScopedTerms, List.map_cons, List.cons.injEq]
                exact ⟨
                  symbolicLPSubstitution_apply_encodeTerm substitution head
                    targetHead headFound,
                  symbolicLPSubstitution_apply_encodeTerms substitution tail
                    targetTail tailFound⟩
end

mutual
  theorem symbolicLPSubstitution_apply_queryTerm
      (substitution : SymbolicSubstitution) (term : Term) :
      (symbolicLPSubstitution substitution).applyTerm
          (encodeScopedTerm .query term) =
        encodeScopedTerm .query term := by
    cases term with
    | var identifier => rfl
    | atom name => rfl
    | integer value => rfl
    | app constructor arguments =>
        have argumentsEqual :=
          symbolicLPSubstitution_apply_queryTerms substitution arguments
        simp only [encodeScopedTerm, Mettapedia.Logic.LP.Subst.applyTerm]
        congr 1
        funext index
        have pointwise := List.get_of_eq argumentsEqual
          (⟨index.val, by simp⟩ :
            Fin ((encodeScopedTerms .query arguments).map
              (symbolicLPSubstitution substitution).applyTerm).length)
        simpa using pointwise

  theorem symbolicLPSubstitution_apply_queryTerms
      (substitution : SymbolicSubstitution) (terms : Terms) :
      (encodeScopedTerms .query terms).map
          (symbolicLPSubstitution substitution).applyTerm =
        encodeScopedTerms .query terms := by
    cases terms with
    | nil => rfl
    | cons head tail =>
        simp only [encodeScopedTerms, List.map_cons, List.cons.injEq]
        exact ⟨symbolicLPSubstitution_apply_queryTerm substitution head,
          symbolicLPSubstitution_apply_queryTerms substitution tail⟩
end

theorem symbolicLPSubstitution_apply_queryAtom
    (substitution : SymbolicSubstitution) (atom : Atom) :
    (symbolicLPSubstitution substitution).applyAtom
        (encodeScopedAtom .query atom) =
      encodeScopedAtom .query atom := by
  have argumentsEqual :=
    symbolicLPSubstitution_apply_queryTerms substitution atom.arguments
  simp only [Mettapedia.Logic.LP.Subst.applyAtom, encodeScopedAtom]
  congr 1
  funext index
  have pointwise := List.get_of_eq argumentsEqual
    (⟨index.val, by simp⟩ :
      Fin ((encodeScopedTerms .query atom.arguments).map
        (symbolicLPSubstitution substitution).applyTerm).length)
  simpa using pointwise

theorem symbolicLPSubstitution_apply_encodeAtom
    (substitution : SymbolicSubstitution) (source target : Atom)
    (instantiated : instantiateSymbolicAtom substitution source = some target) :
    (symbolicLPSubstitution substitution).applyAtom
        (encodeScopedAtom .rule source) =
      encodeScopedAtom .query target := by
  cases found : instantiateSymbolicTerms substitution source.arguments with
  | none => simp [instantiateSymbolicAtom, found] at instantiated
  | some targetArguments =>
      simp [instantiateSymbolicAtom, found] at instantiated
      subst target
      have argumentsEqual :=
        symbolicLPSubstitution_apply_encodeTerms substitution source.arguments
          targetArguments found
      have lengths :
          (encodeScopedTerms .rule source.arguments).length =
            (encodeScopedTerms .query targetArguments).length := by
        simpa using congrArg List.length argumentsEqual
      simp only [Mettapedia.Logic.LP.Subst.applyAtom, encodeScopedAtom]
      congr 1
      · exact congrArg (fun arity =>
          ({ name := source.relation, arity := arity } : RelationSymbol))
          lengths
      apply (Fin.heq_fun_iff lengths).2
      intro index
      have pointwise := List.get_of_eq argumentsEqual
        (⟨index.val, by simp⟩ :
          Fin ((encodeScopedTerms .rule source.arguments).map
            (symbolicLPSubstitution substitution).applyTerm).length)
      simpa using pointwise

theorem specializationHead_semanticallyUnifiable
    {program : Program} {parseRelation : String}
    {certificate : SpecializationCertificate} {production : StreamProduction}
    (specializes : Specializes program parseRelation certificate production) :
    ∃ instantiatedHead,
      instantiateSymbolicAtom certificate.substitution certificate.rule.head =
        some instantiatedHead ∧
      SemanticallyUnifiable instantiatedHead certificate.rule := by
  cases specializes with
  | intro head body parsedHead member substitutionValid categoriesValid
      instantiatedHead instantiatedBody decodedHead bodyEvidence sourceRule
      category start finish =>
      refine ⟨head, instantiatedHead, symbolicLPSubstitution certificate.substitution,
        ?_⟩
      rw [symbolicLPSubstitution_apply_queryAtom]
      exact (symbolicLPSubstitution_apply_encodeAtom certificate.substitution
        certificate.rule.head head instantiatedHead).symm

/-- Every specialization accepted by the independent checker is discoverable
by the finite, apart-renamed head enumerator at some common program bound. -/
theorem checkedSpecialization_head_is_enumerated
    {program : Program} {parseRelation : String}
    {certificate : SpecializationCertificate} {production : StreamProduction}
    (specializes : Specializes program parseRelation certificate production) :
    ∃ instantiatedHead maximumFuel result,
      instantiateSymbolicAtom certificate.substitution certificate.rule.head =
        some instantiatedHead ∧
      result ∈ matchHeads program instantiatedHead maximumFuel ∧
      HeadMatches instantiatedHead maximumFuel certificate.rule result := by
  obtain ⟨instantiatedHead, headInstantiated, unifiable⟩ :=
    specializationHead_semanticallyUnifiable specializes
  have ruleMember : certificate.rule ∈ program := by
    cases specializes with
    | intro head body parsedHead member substitutionValid categoriesValid
        instantiatedHead instantiatedBody decodedHead bodyEvidence sourceRule
        category start finish => exact member
  obtain ⟨maximumFuel, bounded⟩ :=
    finiteProgram_has_unification_bound program instantiatedHead
  obtain ⟨result, resultMember, matched⟩ :=
    matchHeads_semantically_exhaustive program instantiatedHead maximumFuel
      bounded certificate.rule ruleMember unifiable
  exact ⟨instantiatedHead, maximumFuel, result, headInstantiated,
    resultMember, matched⟩

end Mettapedia.GSLT.Parsing.HornSpecializationHead
