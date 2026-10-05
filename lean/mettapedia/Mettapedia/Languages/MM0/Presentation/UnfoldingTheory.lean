import Mettapedia.Languages.MM0.Presentation.UnfoldingCorrespondence
import Mettapedia.Languages.MM0.Presentation.TypingTheory

/-!
# Unfolding in the actual admitted MM0 theory

The authored operation uses the declaration and body tables of the current
theory. Checked admission supplies body typing, and genuine extensions
preserve successful unfolding requests. Neither claim treats arbitrary stored
bodies as admitted declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalDefinitions

open Kernel ComputationalContext ComputationalArguments ComputationalTyping
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => unfoldingProgram
local notation "H" => computationalHost

theorem theory_definitions (theory : Theory) :
    definitionsOf theory.definitions = theory.definitionSignature := rfl

theorem theory_unfolding_computes (theory : Theory) (target : Context)
    (symbol : Nat) (arguments : List Preterm) (images : List Nat) :
    Applies P H "mm0:unfold"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeContext target,
        natural symbol, encodeExpressions arguments, encodeNaturals images]
      (encodeResult (Definition.unfold? theory.termSignature theory.definitionSignature target symbol arguments images)) := by
  simpa only [theory_signature, theory_definitions] using
    unfolding_computes theory.terms theory.definitions target symbol arguments images

theorem theory_unfolding_accepts_iff (theory : Theory) (target : Context)
    (symbol : Nat) (arguments : List Preterm) (images : List Nat) (result : Preterm) :
    Applies P H "mm0:unfold"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeContext target,
        natural symbol, encodeExpressions arguments, encodeNaturals images] (encodeResult (some result)) ↔
      Definition.Unfolds theory.termSignature theory.definitionSignature target symbol arguments images result := by
  simpa only [theory_signature, theory_definitions] using
    unfolding_accepts_iff theory.terms theory.definitions target symbol arguments images result

theorem theory_extension_preserves_unfolding {before after : Theory} (extension : Theory.Extends before after)
    {target : Context} {symbol : Nat} {arguments : List Preterm} {images : List Nat} {result : Preterm}
    (accepted : Applies P H "mm0:unfold"
      [encodeTable before.terms, encodeDefinitions before.definitions, encodeContext target,
        natural symbol, encodeExpressions arguments, encodeNaturals images] (encodeResult (some result))) :
    Applies P H "mm0:unfold"
      [encodeTable after.terms, encodeDefinitions after.definitions, encodeContext target,
        natural symbol, encodeExpressions arguments, encodeNaturals images] (encodeResult (some result)) := by
  apply (theory_unfolding_accepts_iff after target symbol arguments images result).mpr
  exact ((theory_unfolding_accepts_iff before target symbol arguments images result).mp accepted).extendSignatures
    extension.terms extension.definitions

theorem admitted_theory_unfolding_is_typed (theory : Theory) (valid : Theory.WellFormed theory)
    {target : Context} {symbol : Nat} {declaration : TermDecl}
    (known : theory.termSignature symbol = some declaration)
    {arguments : List Preterm} {images : List Nat} {result : Preterm}
    (accepted : Applies P H "mm0:unfold"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeContext target,
        natural symbol, encodeExpressions arguments, encodeNaturals images] (encodeResult (some result))) :
    Preterm.HasType theory.termSignature target result [] declaration.resultSort := by
  have unfolded := (theory_unfolding_accepts_iff theory target symbol arguments images result).mp accepted
  cases unfolded with
  | intro actualLookup bodyLookup typed fresh substituted =>
      obtain ⟨storedDeclaration, storedLookup, admitted⟩ := valid.definitions _ _ bodyLookup
      have same := Option.some.inj (storedLookup.symm.trans actualLookup)
      subst storedDeclaration
      have output := admitted.typed.substitute (fresh.typed_substitution typed) substituted
      have sameResult := Option.some.inj (actualLookup.symm.trans known)
      simpa only [sameResult] using output

theorem checked_theory_unfolding_is_typed {theory : Theory} {admissions : List Admission}
    (formed : Theory.run? {} admissions = some theory)
    {target : Context} {symbol : Nat} {declaration : TermDecl}
    (known : theory.termSignature symbol = some declaration)
    {arguments : List Preterm} {images : List Nat} {result : Preterm}
    (accepted : Applies P H "mm0:unfold"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeContext target,
        natural symbol, encodeExpressions arguments, encodeNaturals images] (encodeResult (some result))) :
    Preterm.HasType theory.termSignature target result [] declaration.resultSort :=
  admitted_theory_unfolding_is_typed theory (Theory.run_from_empty_wellFormed formed) known accepted

theorem checked_extension_preserves_unfolding {before after : Theory} {admissions : List Admission}
    (extended : Theory.run? before admissions = some after)
    {target : Context} {symbol : Nat} {arguments : List Preterm} {images : List Nat} {result : Preterm}
    (accepted : Applies P H "mm0:unfold"
      [encodeTable before.terms, encodeDefinitions before.definitions, encodeContext target,
        natural symbol, encodeExpressions arguments, encodeNaturals images] (encodeResult (some result))) :
    Applies P H "mm0:unfold"
      [encodeTable after.terms, encodeDefinitions after.definitions, encodeContext target,
        natural symbol, encodeExpressions arguments, encodeNaturals images] (encodeResult (some result)) :=
  theory_extension_preserves_unfolding ((Theory.run_eq_some_iff _ _ _).mp extended).extends accepted

namespace Controls

private def sortAdmission : Admission := .sort 0 {}
private def constantAdmission : Admission := .term 0 ⟨[], 0, ∅⟩
private def identityAdmission : Admission := .definition 1 ⟨[.regular 0 ∅], 0, ∅⟩ ⟨[], .var 0⟩
private def withSort : Theory := sortAdmission.insert {}
private def withConstant : Theory := constantAdmission.insert withSort
private def withIdentity : Theory := identityAdmission.insert withConstant

theorem concrete_history_is_admitted :
    Theory.Runs {} [sortAdmission, constantAdmission, identityAdmission] withIdentity := by
  refine .cons (.intro ((Admission.check_iff _ _).mp ?_))
    (.cons (.intro ((Admission.check_iff _ _).mp ?_))
      (.cons (.intro ((Admission.check_iff _ _).mp ?_)) (.nil _))) <;> decide +kernel

theorem admitted_identity_computes :
    Applies P H "mm0:unfold"
      [encodeTable withIdentity.terms, encodeDefinitions withIdentity.definitions, encodeContext [],
        natural 1, encodeExpressions [.term 0], encodeNaturals []] (encodeResult (some (.term 0))) := by
  have calculation : Definition.unfold? withIdentity.termSignature withIdentity.definitionSignature
      [] 1 [.term 0] [] = some (.term 0) := by decide +kernel
  simpa only [calculation] using theory_unfolding_computes withIdentity [] 1 [.term 0] []

theorem admitted_computation_has_declared_type :
    Preterm.HasType withIdentity.termSignature [] (.term 0) [] 0 :=
  checked_theory_unfolding_is_typed
    ((Theory.run_eq_some_iff _ _ _).mpr concrete_history_is_admitted)
    (declaration := ⟨[.regular 0 ∅], 0, ∅⟩) (by rfl) admitted_identity_computes

theorem missing_symbol_cannot_be_admitted_as_a_body :
    Admission.check withConstant (.definition 1 ⟨[.regular 0 ∅], 0, ∅⟩ ⟨[], .term 99⟩) = false := by
  decide +kernel

theorem definition_cannot_refer_to_itself :
    Admission.check withConstant (.definition 1 ⟨[], 0, ∅⟩ ⟨[], .term 1⟩) = false := by
  decide +kernel

theorem extending_theory_keeps_the_same_computation :
    let later := Admission.insert withIdentity (.term 2 ⟨[], 0, ∅⟩)
    Applies P H "mm0:unfold"
      [encodeTable later.terms, encodeDefinitions later.definitions, encodeContext [],
        natural 1, encodeExpressions [.term 0], encodeNaturals []] (encodeResult (some (.term 0))) := by
  exact theory_extension_preserves_unfolding
    (Theory.Step.extends (.intro ((Admission.check_iff _ _).mp (by decide +kernel))))
    admitted_identity_computes

end Controls

end Mettapedia.Languages.MM0.Presentation.ComputationalDefinitions
