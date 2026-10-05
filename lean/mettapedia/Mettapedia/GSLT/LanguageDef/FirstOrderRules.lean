import Mettapedia.GSLT.LanguageDef.InferenceInstantiationBridge

/-!
# First-order rule packages for the generic inference checker

A first-order rule has depth-zero metavariables and schemas built from
applications and metavariables only.  For such a package, derivations of the
generic checker coincide with a plain inductive derivability predicate in which
a rule instance substitutes its argument vector for its metavariables.  The
bridge is proved once here, so that correspondence proofs for a concrete
package reason about substitution instances instead of schema instantiation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.FirstOrderRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceInstantiationBridge

/-- A first-order inference rule: identifier, metavariable names (all at
depth zero), ordered premise schemas, and conclusion schema. -/
structure FORule where
  id : String
  vars : List String
  premises : List Pattern
  conclusion : Pattern

namespace FORule

def formals (r : FORule) : List (String × Nat) := r.vars.map fun x => (x, 0)

def toSchema (r : FORule) : RuleSchema :=
  { id := ⟨r.id⟩, metavariables := r.formals, premises := r.premises,
    conclusion := r.conclusion }

/-- The substitution of an argument vector for the metavariables. -/
def bindings (r : FORule) (args : List Pattern) : Bindings := r.vars.zip args

def instPremises (r : FORule) (args : List Pattern) : List Pattern :=
  r.premises.map (applyBindings (r.bindings args))

def instConclusion (r : FORule) (args : List Pattern) : Pattern :=
  applyBindings (r.bindings args) r.conclusion

end FORule

/-- Derivability in a first-order package. -/
inductive FODerivable (rules : List FORule) : Pattern → Prop where
  | rule (r : FORule) (member : r ∈ rules) (args : List Pattern)
      (length : args.length = r.vars.length)
      (valid : ∀ a ∈ args, argumentValidAt 0 a = true)
      (premises : ∀ p ∈ r.instPremises args, FODerivable rules p) :
      FODerivable rules (r.instConclusion args)

/-- Structural admissibility of a first-order package: metavariable names are
distinct and every schema lies in the first-order fragment. -/
structure FOPackage (rules : List FORule) : Prop where
  nodup : ∀ r ∈ rules, r.vars.Nodup
  premisesFragment : ∀ r ∈ rules, BindingSchemasFragment r.formals r.premises
  conclusionFragment : ∀ r ∈ rules, BindingSchemaFragment r.formals r.conclusion

theorem FORule.formals_names (r : FORule) : r.formals.map Prod.fst = r.vars := by
  simp [FORule.formals, List.map_map, Function.comp_def]

theorem bindingsOfArguments?_formals :
    ∀ (vars : List String) (args : List Pattern), args.length = vars.length →
      bindingsOfArguments? (vars.map fun x => (x, 0)) args = some (vars.zip args)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, a :: as, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp [bindingsOfArguments?, bindingsOfArguments?_formals xs as h]

theorem argumentsOfBindings?_formals (r : FORule) (args : List Pattern)
    (nodup : r.vars.Nodup) (length : args.length = r.vars.length) :
    argumentsOfBindings? r.formals (r.bindings args) = some args := by
  apply argumentsOfBindings?_of_bindingsOfArguments
  · rw [FORule.formals_names]; exact nodup
  · intro formal member
    simp only [FORule.formals, List.mem_map] at member
    obtain ⟨_, _, rfl⟩ := member
    rfl
  · exact bindingsOfArguments?_formals r.vars args length

theorem argumentsValidAt_formals :
    ∀ (vars : List String) (args : List Pattern),
      argumentsValidAt (vars.map fun x => (x, 0)) args = true ↔
        args.length = vars.length ∧ ∀ a ∈ args, argumentValidAt 0 a = true
  | [], [] => by simp [argumentsValidAt]
  | [], _ :: _ => by simp [argumentsValidAt]
  | _ :: _, [] => by simp [argumentsValidAt]
  | x :: xs, a :: as => by
      simp only [List.map_cons, argumentsValidAt, Bool.and_eq_true,
        argumentsValidAt_formals xs as, List.length_cons, Nat.add_right_cancel_iff,
        List.mem_cons, forall_eq_or_imp]
      tauto

/-- A rule of a first-order package applies exactly to substitution
instances of its schemas. -/
theorem ruleApplication_iff (definition : ValidatedCalculusLanguageDef)
    (rules : List FORule) (package : FOPackage rules)
    (r : FORule) (member : r ∈ rules)
    (lookup : definition.1.lookupRule? ⟨r.id⟩ = some r.toSchema)
    (args premises : List Pattern) (conclusion : Pattern) :
    RuleApplication definition ⟨⟨r.id⟩, args⟩ premises conclusion ↔
      args.length = r.vars.length ∧ (∀ a ∈ args, argumentValidAt 0 a = true) ∧
        premises = r.instPremises args ∧ conclusion = r.instConclusion args := by
  constructor
  · rintro ⟨rule, hlookup, hargs, _hside, hprem, hconc⟩
    have hrule : rule = r.toSchema := by
      rw [lookup] at hlookup; exact (Option.some.inj hlookup).symm
    subst hrule
    have hvalid := (argumentsValidAt_formals r.vars args).mp hargs
    have hbind := argumentsOfBindings?_formals r args (package.nodup r member) hvalid.1
    have hp := instantiateSchemasAt?_eq_applyBindings
      (package.premisesFragment r member) hbind
    have hc := instantiateSchemaAt?_eq_applyBindings
      (package.conclusionFragment r member) hbind
    have hp' := instantiateSchemasAt?_complete hprem
    have hc' := instantiateSchemaAt?_complete hconc
    refine ⟨hvalid.1, hvalid.2, ?_, ?_⟩
    · have := hp'.symm.trans hp
      exact Option.some.inj this
    · have := hc'.symm.trans hc
      exact Option.some.inj this
  · rintro ⟨hlen, hvalid, rfl, rfl⟩
    have hbind := argumentsOfBindings?_formals r args (package.nodup r member) hlen
    refine ⟨r.toSchema, lookup, ?_, ?_, ?_, ?_⟩
    · exact (argumentsValidAt_formals r.vars args).mpr ⟨hlen, hvalid⟩
    · simp [RuleSchema.sideConditionsHold, FORule.toSchema]
    · exact instantiateSchemasAt?_sound
        (instantiateSchemasAt?_eq_applyBindings (package.premisesFragment r member) hbind)
    · exact instantiateSchemaAt?_sound
        (instantiateSchemaAt?_eq_applyBindings (package.conclusionFragment r member) hbind)

/-- The validated definition presents exactly the first-order rules. -/
structure Presents (definition : ValidatedCalculusLanguageDef)
    (rules : List FORule) : Prop where
  package : FOPackage rules
  rules_eq : definition.1.rules = rules.map FORule.toSchema

theorem Presents.lookup {definition : ValidatedCalculusLanguageDef}
    {rules : List FORule} (presents : Presents definition rules)
    {r : FORule} (member : r ∈ rules) :
    definition.1.lookupRule? ⟨r.id⟩ = some r.toSchema := by
  have hmem : r.toSchema ∈ definition.1.rules := by
    rw [presents.rules_eq]; exact List.mem_map_of_mem member
  exact lookupRule?_eq_some_of_mem definition hmem

theorem Presents.rule_of_lookup {definition : ValidatedCalculusLanguageDef}
    {rules : List FORule} (presents : Presents definition rules)
    {id : RuleId} {rule : RuleSchema}
    (lookup : definition.1.lookupRule? id = some rule) :
    ∃ r ∈ rules, rule = r.toSchema ∧ id = ⟨r.id⟩ := by
  have hfind : definition.1.rules.find? (fun candidate => decide (candidate.id = id)) =
      some rule := lookup
  have hmem := List.mem_of_find?_eq_some hfind
  have hid : rule.id = id := by simpa using List.find?_some hfind
  rw [presents.rules_eq] at hmem
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hmem
  exact ⟨r, hr, rfl, hid.symm⟩

/-- Every rule application of the presented definition is a first-order
rule instance, so first-order derivability is closed under it. -/
theorem foDerivable_ruleSound {definition : ValidatedCalculusLanguageDef}
    {rules : List FORule} (presents : Presents definition rules)
    (ruleInstance : RuleInstance) (premises : List Pattern) (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (children : ∀ p ∈ premises, FODerivable rules p) :
    FODerivable rules conclusion := by
  have application' := application
  obtain ⟨rule, lookup, _, _, _, _⟩ := application'
  obtain ⟨r, hr, rfl, hid⟩ := presents.rule_of_lookup lookup
  rcases ruleInstance with ⟨id, args⟩
  simp only at hid
  subst hid
  obtain ⟨hlen, hvalid, hprem, hconc⟩ :=
    (ruleApplication_iff definition rules presents.package r hr
      (presents.lookup hr) args _ _).mp application
  subst hprem
  subst hconc
  exact .rule r hr args hlen hvalid children

theorem foDerivable_of_derivation {definition : ValidatedCalculusLanguageDef}
    {rules : List FORule} (presents : Presents definition rules) {goal : Pattern}
    (derivation : Derivation definition goal) : FODerivable rules goal :=
  Derivation.sound_of_ruleApplications (FODerivable rules)
    (foDerivable_ruleSound presents) derivation

theorem derivationList_of_forall {definition : ValidatedCalculusLanguageDef} :
    ∀ (premises : List Pattern), (∀ p ∈ premises, Nonempty (Derivation definition p)) →
      Nonempty (DerivationList definition premises)
  | [], _ => ⟨.nil⟩
  | p :: ps, h => by
      obtain ⟨d⟩ := h p (by simp)
      obtain ⟨ds⟩ := derivationList_of_forall ps (fun q hq => h q (by simp [hq]))
      exact ⟨.cons d ds⟩

theorem derivation_of_foDerivable {definition : ValidatedCalculusLanguageDef}
    {rules : List FORule} (presents : Presents definition rules) {goal : Pattern}
    (derivable : FODerivable rules goal) : Nonempty (Derivation definition goal) := by
  induction derivable with
  | rule r hr args hlen hvalid _ ih =>
      obtain ⟨children⟩ := derivationList_of_forall _ ih
      have application :=
        (ruleApplication_iff definition rules presents.package r hr
          (presents.lookup hr) args (r.instPremises args) (r.instConclusion args)).mpr
          ⟨hlen, hvalid, rfl, rfl⟩
      exact ⟨.byRule ⟨⟨r.id⟩, args⟩ application children⟩

/-- Generic checker derivations of a first-order package are exactly its
first-order derivations. -/
theorem derivation_iff_foDerivable {definition : ValidatedCalculusLanguageDef}
    {rules : List FORule} (presents : Presents definition rules) (goal : Pattern) :
    Nonempty (Derivation definition goal) ↔ FODerivable rules goal :=
  ⟨fun ⟨d⟩ => foDerivable_of_derivation presents d, derivation_of_foDerivable presents⟩

/-- Raw proof checking of a first-order package accepts some article for a
goal exactly when the goal is first-order derivable. -/
theorem checkRaw_exists_iff_foDerivable {definition : ValidatedCalculusLanguageDef}
    {rules : List FORule} (presents : Presents definition rules) (goal : Pattern) :
    (∃ proof, checkRaw definition goal proof = true) ↔ FODerivable rules goal := by
  rw [← derivation_iff_foDerivable presents goal]
  constructor
  · rintro ⟨proof, hproof⟩
    obtain ⟨derivation, -⟩ :=
      (G2_checkRaw_iff_exists_derivation_erases_to (definition := definition)
        (goal := goal) (proof := proof)).mp hproof
    exact ⟨derivation⟩
  · rintro ⟨derivation⟩
    exact ⟨derivation.erase,
      (G2_checkRaw_iff_exists_derivation_erases_to (definition := definition)
        (goal := goal) (proof := derivation.erase)).mpr ⟨derivation, rfl⟩⟩

/-- Packages combine. -/
theorem FOPackage.append {first second : List FORule}
    (hf : FOPackage first) (hs : FOPackage second) : FOPackage (first ++ second) := by
  constructor
  · intro r hr
    exact (List.mem_append.mp hr).elim (hf.nodup r) (hs.nodup r)
  · intro r hr
    exact (List.mem_append.mp hr).elim (hf.premisesFragment r) (hs.premisesFragment r)
  · intro r hr
    exact (List.mem_append.mp hr).elim (hf.conclusionFragment r) (hs.conclusionFragment r)

/-- Derivations remain valid when their real rule list is extended. -/
theorem FODerivable.mono {R S : List FORule} (hRS : R ⊆ S) {goal : Pattern}
    (derivation : FODerivable R goal) : FODerivable S goal := by
  induction derivation with
  | rule r hr args hlen hvalid _ ih => exact .rule r (hRS hr) args hlen hvalid ih

end Mettapedia.GSLT.LanguageDef.FirstOrderRules
