import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

/-!
# An explicit extension by context constructors

A closure view keeps the value of an eliminated binder under a context
constructor `κ`, which lies outside the authored signature. Compilation keeps the
authored signature (`GeneralExecutionAdmission.compile`). A caller that wants to
execute over terms holding `κ` asks for the extension by name
(`GeneralExecutionAdmission.compileWithContextRules`):

* each context rule has its origin in one presentation of the profile
  (`ReflectionProfile.mem_contextRules`);
* the profile is validated against the authored signature, which keeps `κ` fresh;
* the extended signature, over which the plan executes, is validated as a whole,
  so two presentations that propose one constructor are refused, and so is
  extending an extended signature again (`compileWithContextRules_complete_iff`).

An extended plan is not `compile` of its own snapshot. Theorems that assume a
compiled plan speak of the authored one.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Reflection

open Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- The typing rule of the context constructor a presentation proposes, if any:
`κ(v) : N` when `v : N`, at the presentation's name sort `N`. -/
def contextRule (presentation : ReflectivePresentationDecl) : Option GrammarRule :=
  presentation.quoteScope.contextConstructor?.map fun context =>
    { label := context
      category := presentation.nameSort
      params := [.simple "value" (.base presentation.nameSort)]
      syntaxPattern := [.terminal context, .terminal "(", .nonTerminal "value", .terminal ")"] }

namespace ReflectionProfile

/-- The context rules a whole profile proposes. -/
def contextRules (profile : ReflectionProfile) : List GrammarRule :=
  profile.presentations.filterMap contextRule

/-- Every proposed rule has a presentation as its origin. -/
theorem mem_contextRules {profile : ReflectionProfile} {rule : GrammarRule} :
    rule ∈ profile.contextRules ↔
      ∃ presentation ∈ profile.presentations, contextRule presentation = some rule :=
  List.mem_filterMap

/-- The signature extended by the context rules of a profile: a language of its
own, distinct from the authored one. -/
def extendLanguage (profile : ReflectionProfile) (language : LanguageDef) : LanguageDef :=
  { language with terms := profile.contextRules ++ language.terms }

/-- What the authored signature types, the extension types the same way. -/
theorem hasType_extendLanguage {profile : ReflectionProfile} {language : LanguageDef}
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free bound pattern type) :
    HasType (profile.extendLanguage language) free bound pattern type :=
  HasType.of_terms_subset (List.subset_append_right _ _) typed

/-- **The typing rule of a context constructor.** In the extension, `κ(v)` is a
name of the presentation's name sort when `v` is. -/
theorem context_hasType {profile : ReflectionProfile} {presentation : ReflectivePresentationDecl}
    (member : presentation ∈ profile.presentations) {context : String}
    (declared : presentation.quoteScope = .reaching (.closure context)) {language : LanguageDef}
    {free : FreeTypeContext} {bound : List TypeExpr} {value : Pattern}
    (typed : HasType (profile.extendLanguage language) free bound value (.base presentation.nameSort)) :
    HasType (profile.extendLanguage language) free bound (.apply context [value])
      (.base presentation.nameSort) := by
  let rule : GrammarRule :=
    { label := context
      category := presentation.nameSort
      params := [.simple "value" (.base presentation.nameSort)]
      syntaxPattern := [.terminal context, .terminal "(", .nonTerminal "value", .terminal ")"] }
  have proposed : contextRule presentation = some rule := by simp [contextRule, declared, rule]
  have declaredRule : rule ∈ (profile.extendLanguage language).terms :=
    List.mem_append_left _ (mem_contextRules.mpr ⟨presentation, member, proposed⟩)
  have ordinary : ¬ UsesBareCollection rule := by
    rintro ⟨_, _, _, shape⟩
    simp [rule, GrammarRule.bareParams] at shape
  exact HasType.constructor (rule := rule) declaredRule ordinary (.cons trivial rfl typed .nil)

end ReflectionProfile

end Mettapedia.OSLF.MeTTaIL.Reflection

namespace Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

open Syntax

/-- The target snapshot of the extension. The authored snapshot is unchanged. -/
def Snapshot.extendContexts (snapshot : Snapshot) (profile : Reflection.ReflectionProfile) : Snapshot :=
  { snapshot with language := profile.extendLanguage snapshot.language }

/-- **Compile with context rules, by explicit request.** Declarations are
compiled and checked on the authored snapshot. The plan executes over the
extended snapshot, whose language must itself be valid. -/
def compileWithContextRules (authored : Snapshot) (permissions : Permissions) : Plan :=
  let target := authored.extendContexts permissions.reflection
  let compiled := compile authored permissions
  { compiled with
    snapshot := target
    obligations := (if target.language.validate.isEmpty then [] else [.invalidLanguage]) ++
      compiled.obligations }

/-- An extended plan is complete exactly when the authored compilation is
complete and the signature it executes over is valid. -/
theorem compileWithContextRules_complete_iff {authored : Snapshot} {permissions : Permissions} :
    (compileWithContextRules authored permissions).complete = true ↔
      (authored.extendContexts permissions.reflection).language.validate = [] ∧
        (compile authored permissions).complete = true := by
  simp [compileWithContextRules, Plan.complete]

end Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
