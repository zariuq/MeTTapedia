import Mettapedia.Languages.VibeITP.Presentation.SoundDefinitions

/-!
# Vibe-ITP presentation: meanings of admitted facts

Built-in and allocated symbol declarations follow the signature. Axiom and
definition facts follow membership in the concrete theory. These lemmas use
the actual closed rule conclusions, so substituting any rule argument vector
cannot change an admitted fact.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec

theorem inst_closedRule (id : String) {J : Pattern} (hJ : IsData J) :
    (mkRule id [] [] J).instPremises [] = [] ∧
      (mkRule id [] [] J).instConclusion [] = J := by
  constructor
  · rfl
  · exact ab_data [] hJ

theorem ms_closedRule (T : Theory) (id : String) {J : Pattern}
    (hJ : IsData J) (hmeaning : Meaning T J) :
    ∀ args : List Pattern, args.length = (mkRule id [] [] J).vars.length →
      (∀ p ∈ (mkRule id [] [] J).instPremises args, Meaning T p) →
        Meaning T ((mkRule id [] [] J).instConclusion args) := by
  intro args hlen _
  have hargs : args = [] := List.length_eq_zero_iff.mp hlen
  subst hargs
  rw [(inst_closedRule id hJ).2]
  exact hmeaning

theorem ms_builtin (T : Theory) (hb : BuiltinsFixed T.sig) (b : Builtin) :
    Meaning T (jSymDecl (patBuiltinSym b)) := by
  change SymDeclM T.sig (patBuiltinSym b)
  exact ⟨.builtin b, by simp [hb b], (encSym_builtin hb b).symm⟩

theorem ms_builtinRules (T : Theory) (hb : BuiltinsFixed T.sig)
    {r : FORule} (hr : r ∈ builtinRules) :
    ∀ args : List Pattern, args.length = r.vars.length →
      (∀ p ∈ r.instPremises args, Meaning T p) →
        Meaning T (r.instConclusion args) := by
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hr
  exact ms_closedRule T _ (IsData.app1 _ (isData_patBuiltinSym b)) (ms_builtin T hb b)

theorem ms_symbolRule (T : Theory) (allocated : Nat) (h : Hosted T allocated)
    (n : Nat) (hn : n < allocated) :
    ∀ args : List Pattern, args.length = (symbolRule T.sig n).vars.length →
      (∀ p ∈ (symbolRule T.sig n).instPremises args, Meaning T p) →
        Meaning T ((symbolRule T.sig n).instConclusion args) := by
  apply ms_closedRule T _ (IsData.app1 _ (isData_encSym T.sig (.fresh n)))
  exact ⟨.fresh n, (h.fresh n).mpr hn, rfl⟩

theorem ms_axiomRule (T : Theory) (k : Nat) {φ : Term} (hφ : φ ∈ T.axioms) :
    ∀ args : List Pattern, args.length = (axiomRule T.sig k φ).vars.length →
      (∀ p ∈ (axiomRule T.sig k φ).instPremises args, Meaning T p) →
        Meaning T ((axiomRule T.sig k φ).instConclusion args) := by
  apply ms_closedRule T _ (IsData.app1 _ (isData_encTerm T.sig φ))
  exact ⟨φ, rfl, .axiom hφ⟩

theorem ms_definitionRule (T : Theory) (k : Nat) {d : Definition}
    (hd : d ∈ T.definitions) :
    ∀ args : List Pattern, args.length = (definitionRule T.sig k d).vars.length →
      (∀ p ∈ (definitionRule T.sig k d).instPremises args, Meaning T p) →
        Meaning T ((definitionRule T.sig k d).instConclusion args) := by
  apply ms_closedRule T _ (IsData.app1 _ (isData_encTerm T.sig _))
  exact ⟨_, rfl, .definition hd⟩

theorem ms_theoryRules (T : Theory) (allocated : Nat) (h : Hosted T allocated)
    {r : FORule} (hr : r ∈ theoryRules T allocated) :
    ∀ args : List Pattern, args.length = r.vars.length →
      (∀ p ∈ r.instPremises args, Meaning T p) →
        Meaning T (r.instConclusion args) := by
  simp only [theoryRules, List.mem_append] at hr
  rcases hr with (hr | hr) | hr
  · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hr
    exact ms_symbolRule T allocated h n (List.mem_range.mp hn)
  · obtain ⟨k, φ, hφ, rfl⟩ := mem_axiomRules hr
    exact ms_axiomRule T k hφ
  · obtain ⟨k, d, hd, rfl⟩ := mem_theoryDefinitionRules hr
    exact ms_definitionRule T k hd

theorem intro_closedRule {R : List FORule} (id : String) {J : Pattern}
    (hJ : IsData J) (hr : mkRule id [] [] J ∈ R) : FODerivable R J := by
  apply FODerivable.intro hr [] rfl
  · simp
  · exact (inst_closedRule id hJ).2
  · simp [FORule.instPremises, mkRule]

theorem intro_symbolRule {R : List FORule} (sig : Sig) (n : Nat)
    (hr : symbolRule sig n ∈ R) : FODerivable R (jSymDecl (encSym sig (.fresh n))) :=
  intro_closedRule _ (IsData.app1 _ (isData_encSym sig _)) hr

theorem intro_axiomRule {R : List FORule} (sig : Sig) (k : Nat) (φ : Term)
    (hr : axiomRule sig k φ ∈ R) : FODerivable R (jThm (encTerm sig φ)) :=
  intro_closedRule _ (IsData.app1 _ (isData_encTerm sig φ)) hr

theorem intro_definitionRule {R : List FORule} (sig : Sig) (k : Nat) (d : Definition)
    (hr : definitionRule sig k d ∈ R) :
    FODerivable R (jThm (encTerm sig (definitionStatement sig d.symbol d.fvars d.value))) :=
  intro_closedRule _ (IsData.app1 _ (isData_encTerm sig _)) hr

end Mettapedia.Languages.VibeITP.Presentation
