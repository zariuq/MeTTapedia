import Mettapedia.Languages.Metamath.InferenceProjection

/-!
# Side-judgment conservativity for Metamath prefix projections

The projected presentation extends the standalone side-condition calculus with
source rules whose conclusions are headed by `provesHead`.  Consequently,
standalone side proofs lift unchanged, while a projected derivation whose goal
has one of the side-judgment heads can use only side rules at every node.

This is deliberately not a conservativity theorem for the extended data
language, nor does it restrict derivations of `Proves` goals.
-/

namespace Mettapedia.Languages.Metamath.InferenceProjection

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceSideConditions

/-- The exact outer-head boundary on which projection is conservative. -/
def IsSideJudgment : Pattern → Prop
  | .apply head _ => head ∈ reservedJudgmentHeads
  | _ => False

def AllSideJudgments (judgments : List Pattern) : Prop :=
  ∀ judgment ∈ judgments, IsSideJudgment judgment

/-- Side-judgment status depends only on the outer constructor, which schema
instantiation preserves. -/
theorem isSideJudgment_of_instantiatesAt
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schema result : Pattern}
    (hside : IsSideJudgment schema)
    (hinst : InstantiatesAt formals arguments depth schema result) :
    IsSideJudgment result := by
  cases hinst <;> simp_all [IsSideJudgment]

/-- Ordered schema instantiation preserves the side-head invariant
pointwise. -/
theorem all_isSideJudgment_of_instantiatesListAt
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schemas results : List Pattern}
    (hsides : AllSideJudgments schemas)
    (hinst : InstantiatesListAt formals arguments depth schemas results) :
    AllSideJudgments results := by
  cases hinst with
  | nil => simp [AllSideJudgments]
  | cons head tail =>
      intro result hresult
      simp only [List.mem_cons] at hresult
      rcases hresult with rfl | hresult
      · exact isSideJudgment_of_instantiatesAt
          (hsides _ (by simp)) head
      · exact all_isSideJudgment_of_instantiatesListAt
          (fun schema hschema => hsides schema (by simp [hschema])) tail
          result hresult
termination_by results.length

/-- Every judgment shape declared by the standalone presentation has one of
the reserved side heads. -/
theorem isSideJudgment_of_sidePresentation_hasJudgmentShape
    {judgment : Pattern}
    (hshape : sidePresentation.hasJudgmentShape judgment = true) :
    IsSideJudgment judgment := by
  cases judgment with
  | apply head arguments =>
      unfold Presentation.hasJudgmentShape Presentation.lookupJudgment? at hshape
      cases hfound : (sidePresentation.language.judgments.filter fun declaration =>
          declaration.head == head &&
            declaration.arity == arguments.length) with
      | nil => simp [hfound] at hshape
      | cons declaration rest =>
          cases rest with
          | nil =>
              have hmemFilter : declaration ∈
                  (sidePresentation.language.judgments.filter fun candidate =>
                    candidate.head == head &&
                      candidate.arity == arguments.length) := by
                rw [hfound]
                simp
              have hparts := List.mem_filter.mp hmemFilter
              have hhead : declaration.head = head := by
                simp only [Bool.and_eq_true, beq_iff_eq] at hparts
                exact hparts.2.1
              have hmemDecl : declaration ∈ judgmentDecls := by
                simpa [sidePresentation] using hparts.1
              have hheadReserved :
                  declaration.head ∈ reservedJudgmentHeads := by
                have hmap :
                    declaration.head ∈
                      judgmentDecls.map JudgmentDecl.head :=
                  List.mem_map_of_mem hmemDecl
                simpa [judgmentDecls, reservedJudgmentHeads] using hmap
              subst head
              exact hheadReserved
          | cons second tail => simp [hfound] at hshape
  | bvar | fvar | lambda | multiLambda | subst | collection =>
      simp [Presentation.hasJudgmentShape] at hshape

/-- Premises of every standalone side rule remain inside the side-judgment
fragment.  This derives from V2 validation rather than an enumeration of the
current rule table. -/
theorem sideRule_premises_all_isSideJudgment
    {rule : RuleSchema} (hmem : rule ∈ sideRules) :
    AllSideJudgments rule.premises := by
  intro premise hpremise
  have hvalid := rule_isValidIn_of_mem validatedSidePresentation (by
    simpa [validatedSidePresentation, sidePresentation] using hmem)
  simp only [RuleSchema.isValidIn, Bool.and_eq_true] at hvalid
  have hpremiseValid :
      sidePresentation.judgmentSchemaValid premise = true :=
    (List.all_eq_true.mp hvalid.2.1) premise (by
      simp [RuleSchema.patterns, hpremise])
  exact isSideJudgment_of_sidePresentation_hasJudgmentShape
    (Presentation.hasJudgmentShape_of_judgmentSchemaValid hpremiseValid)

/-- Every generated source rule has exactly the source-provability outer
head. -/
theorem generatedSourceRule_conclusion_eq_proves
    {projection : PrefixProjection} {rule : RuleSchema}
    (hmem : rule ∈ generatedSourceRules projection) :
    ∃ formula, rule.conclusion = proves formula := by
  simp only [generatedSourceRules, List.mem_append, List.mem_map] at hmem
  rcases hmem with ⟨hypothesis, _, rfl⟩ | ⟨assertion, _, rfl⟩
  · exact ⟨encodeFormula hypothesis.formula, rfl⟩
  · exact
      ⟨Builder.formula (encodeString assertion.formula.typecode)
          (.fvar conclusionBodyFormalName), rfl⟩

theorem proves_not_isSideJudgment (formula : Pattern) :
    ¬ IsSideJudgment (proves formula) := by
  simp [IsSideJudgment, proves, reservedJudgmentHeads, provesHead,
    appendHead, lookupHead, substBodyHead, applySubstHead, varsHead,
    memberHead, dvRelHead, allWithHead, allPairsHead, dvListsHead, dvOKHead]

/-- Instantiating a generated source conclusion cannot produce a side
judgment. -/
theorem generatedSourceRule_instantiation_not_isSideJudgment
    {projection : PrefixProjection} {rule : RuleSchema}
    {arguments : List Pattern} {conclusion : Pattern}
    (hmem : rule ∈ generatedSourceRules projection)
    (hinst : Instantiates rule.metavariables arguments
      rule.conclusion conclusion) :
    ¬ IsSideJudgment conclusion := by
  rcases generatedSourceRule_conclusion_eq_proves hmem with
    ⟨formula, hconclusion⟩
  rw [hconclusion] at hinst
  cases hinst with
  | apply items =>
      simp [IsSideJudgment, reservedJudgmentHeads, provesHead,
        appendHead, lookupHead, substBodyHead, applySubstHead, varsHead,
        memberHead, dvRelHead, allWithHead, allPairsHead, dvListsHead,
        dvOKHead]

/-- If a rule found in a projected presentation belongs to the leading side
table, the standalone presentation finds that exact same rule.  No global
conservativity or reverse lookup refinement is asserted. -/
theorem standalone_lookup_of_projected_lookup_of_sideRule
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hrules :
      target.1.rules = sideRules ++ generatedSourceRules projection)
    {ruleInstance : RuleInstance} {rule : RuleSchema}
    (hlookup :
      target.1.lookupRule? ruleInstance.ruleId = some rule)
    (hside : rule ∈ sideRules) :
    validatedSidePresentation.1.lookupRule? ruleInstance.ruleId = some rule := by
  have hid : decide (rule.id = ruleInstance.ruleId) = true := by
    have hlookupFind :
        List.find? (fun candidate : RuleSchema =>
          decide (candidate.id = ruleInstance.ruleId)) target.1.rules =
            some rule := by
      simpa [Presentation.lookupRule?] using hlookup
    exact List.find?_some
      (p := fun candidate : RuleSchema =>
        decide (candidate.id = ruleInstance.ruleId)) hlookupFind
  unfold Presentation.lookupRule? at hlookup ⊢
  rw [hrules] at hlookup
  cases hsideLookup :
      sideRules.find? (fun candidate => decide (candidate.id = ruleInstance.ruleId)) with
  | none =>
      exact False.elim
        ((List.find?_eq_none.mp hsideLookup) rule hside hid)
  | some selectedRule =>
      rw [List.find?_append, hsideLookup] at hlookup
      have hselected : selectedRule = rule := Option.some.inj hlookup
      subst selectedRule
      simpa [validatedSidePresentation, sidePresentation] using hsideLookup

/-! ## Application and tree restriction -/

/-- Local reflection together with the recursive closure invariant needed to
restrict an entire ordered derivation tree. -/
def SideApplicationReflects
    (source target : ValidatedPresentation) : Prop :=
  ∀ {ruleInstance : RuleInstance} {premises : List Pattern}
      {conclusion : Pattern},
    IsSideJudgment conclusion →
      RuleApplication target ruleInstance premises conclusion →
      RuleApplication source ruleInstance premises conclusion ∧
        AllSideJudgments premises

/-- The projected rule table reflects applications whose conclusions have a
side head.  The generated-rule case is impossible because its instantiated
conclusion retains `provesHead`. -/
theorem sideApplicationReflects_of_generated_rules
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hrules :
      target.1.rules = sideRules ++ generatedSourceRules projection) :
    SideApplicationReflects validatedSidePresentation target := by
  intro ruleInstance premises conclusion hside happlication
  cases happlication with
  | intro rule hlookup harguments hsideConditions hpremises hconclusion =>
      have hmem :
          rule ∈ sideRules ++ generatedSourceRules projection := by
        rw [← hrules]
        exact List.mem_of_find?_eq_some hlookup
      rcases List.mem_append.mp hmem with hsideRule | hsourceRule
      · have hstandalone :=
          standalone_lookup_of_projected_lookup_of_sideRule
            projection target hrules hlookup hsideRule
        exact
          ⟨RuleApplication.intro rule hstandalone harguments
              hsideConditions hpremises hconclusion,
            all_isSideJudgment_of_instantiatesListAt
              (sideRule_premises_all_isSideJudgment hsideRule)
              hpremises⟩
      · exact False.elim
          ((generatedSourceRule_instantiation_not_isSideJudgment
            hsourceRule hconclusion) hside)

/-- Successful projection gives the concrete local reflection interface. -/
theorem sideApplicationReflects_of_projection
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1) :
    SideApplicationReflects validatedSidePresentation target :=
  sideApplicationReflects_of_generated_rules projection target
    (rules_eq_of_presentationOfProjection?_eq_some
      projection target.1 hprojection)

mutual

/-- Restrict a derivation whose root and recursively generated premises stay
inside the side-judgment fragment. -/
def restrictSideDerivation
    {source target : ValidatedPresentation}
    (hreflects : SideApplicationReflects source target)
    {goal : Pattern} (hgoal : IsSideJudgment goal) :
    Derivation target goal → Derivation source goal
  | .byRule ruleInstance application children =>
      let reflected := hreflects hgoal application
      .byRule ruleInstance reflected.1
        (restrictSideDerivationList hreflects reflected.2 children)

/-- Ordered premise lists restrict pointwise without permutation or loss. -/
def restrictSideDerivationList
    {source target : ValidatedPresentation}
    (hreflects : SideApplicationReflects source target)
    {premises : List Pattern} (hsides : AllSideJudgments premises) :
    DerivationList target premises → DerivationList source premises
  | .nil => .nil
  | .cons head tail =>
      .cons
        (restrictSideDerivation hreflects
          (hsides _ (by simp)) head)
        (restrictSideDerivationList hreflects
          (fun premise hpremise => hsides premise (by simp [hpremise]))
          tail)

end

mutual

/-- Restriction preserves the exact raw tree, including every ordered child
position. -/
@[simp] theorem erase_restrictSideDerivation
    {source target : ValidatedPresentation}
    (hreflects : SideApplicationReflects source target)
    {goal : Pattern} (hgoal : IsSideJudgment goal)
    (derivation : Derivation target goal) :
    (restrictSideDerivation hreflects hgoal derivation).erase =
      derivation.erase := by
  cases derivation with
  | byRule ruleInstance application children =>
      simp [restrictSideDerivation, Derivation.erase,
        erase_restrictSideDerivationList hreflects]

/-- Exact erasure preservation for restricted ordered premise lists. -/
@[simp] theorem erase_restrictSideDerivationList
    {source target : ValidatedPresentation}
    (hreflects : SideApplicationReflects source target)
    {premises : List Pattern} (hsides : AllSideJudgments premises)
    (derivations : DerivationList target premises) :
    (restrictSideDerivationList hreflects hsides derivations).erase =
      derivations.erase := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp [restrictSideDerivationList, DerivationList.erase,
        erase_restrictSideDerivation hreflects,
        erase_restrictSideDerivationList hreflects]

end

/-! ## Successfully projected presentations -/

/-- A standalone side derivation lifts to a successfully projected and V2
validated presentation through exact rule-lookup refinement. -/
def liftSideDerivationToProjection
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {goal : Pattern}
    (derivation : Derivation validatedSidePresentation goal) :
    Derivation target goal :=
  derivation.transport
    (validatedSidePresentation_refines_of_projection
      projection target hprojection)

/-- Lifting changes only the presentation index, not the raw evidence. -/
@[simp] theorem erase_liftSideDerivationToProjection
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {goal : Pattern}
    (derivation : Derivation validatedSidePresentation goal) :
    (liftSideDerivationToProjection projection target hprojection
      derivation).erase = derivation.erase := by
  exact Derivation.erase_transport
    (validatedSidePresentation_refines_of_projection
      projection target hprojection) derivation

/-- A standalone checked proof lifts with the identical untrusted raw proof
payload. -/
def liftSideCheckedProofToProjection
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {goal : Pattern}
    (proof : CheckedProof validatedSidePresentation goal) :
    CheckedProof target goal :=
  proof.transport
    (validatedSidePresentation_refines_of_projection
      projection target hprojection)

@[simp] theorem liftSideCheckedProofToProjection_payload
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {goal : Pattern}
    (proof : CheckedProof validatedSidePresentation goal) :
    (liftSideCheckedProofToProjection projection target hprojection proof).1 =
      proof.1 := rfl

/-- A projected derivation of a side judgment restricts back to the standalone
calculus.  This theorem intentionally has no analogue here for `Proves`. -/
def restrictSideDerivationFromProjection
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {goal : Pattern} (hgoal : IsSideJudgment goal)
    (derivation : Derivation target goal) :
    Derivation validatedSidePresentation goal :=
  restrictSideDerivation
    (sideApplicationReflects_of_projection projection target hprojection)
    hgoal derivation

@[simp] theorem erase_restrictSideDerivationFromProjection
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {goal : Pattern} (hgoal : IsSideJudgment goal)
    (derivation : Derivation target goal) :
    (restrictSideDerivationFromProjection projection target hprojection
      hgoal derivation).erase = derivation.erase := by
  exact erase_restrictSideDerivation
    (sideApplicationReflects_of_projection projection target hprojection)
    hgoal derivation

/-- Acceptance of an exact raw tree for a projected side goal reflects to the
standalone side checker. -/
theorem checkRaw_true_standalone_of_projection
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {goal : Pattern} (hgoal : IsSideJudgment goal) {proof : RawProof}
    (hcheck : checkRaw target goal proof = true) :
    checkRaw validatedSidePresentation goal proof = true := by
  rcases checkRaw_exists_derivation_with_exact_erasure hcheck with
    ⟨derivation, herasure⟩
  let restricted :=
    restrictSideDerivationFromProjection projection target hprojection
      hgoal derivation
  have hrestricted := checkRaw_erase restricted
  rw [erase_restrictSideDerivationFromProjection, herasure] at hrestricted
  exact hrestricted

/-- On side-judgment goals the two checkers accept exactly the same raw proof
trees. -/
theorem checkRaw_standalone_iff_projection
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {goal : Pattern} (hgoal : IsSideJudgment goal) (proof : RawProof) :
    checkRaw validatedSidePresentation goal proof = true ↔
      checkRaw target goal proof = true := by
  constructor
  · exact checkRaw_true_of_ruleLookupRefines
      (validatedSidePresentation_refines_of_projection
        projection target hprojection)
  · exact checkRaw_true_standalone_of_projection
      projection target hprojection hgoal

/-- Restriction of a checked projected side proof preserves its exact raw
payload. -/
def restrictSideCheckedProofFromProjection
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {goal : Pattern} (hgoal : IsSideJudgment goal)
    (proof : CheckedProof target goal) :
    CheckedProof validatedSidePresentation goal :=
  ⟨proof.1, checkRaw_true_standalone_of_projection
    projection target hprojection hgoal proof.2⟩

@[simp] theorem restrictSideCheckedProofFromProjection_payload
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {goal : Pattern} (hgoal : IsSideJudgment goal)
    (proof : CheckedProof target goal) :
    (restrictSideCheckedProofFromProjection projection target hprojection
      hgoal proof).1 = proof.1 := rfl

/-- Side-judgment derivability is conservative under a successful projection.
Only inhabitation is compared; no proof-irrelevance claim is needed. -/
theorem sideDerivation_nonempty_iff_projection
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {goal : Pattern} (hgoal : IsSideJudgment goal) :
    Nonempty (Derivation validatedSidePresentation goal) ↔
      Nonempty (Derivation target goal) := by
  constructor
  · rintro ⟨derivation⟩
    exact ⟨liftSideDerivationToProjection projection target hprojection
      derivation⟩
  · rintro ⟨derivation⟩
    exact ⟨restrictSideDerivationFromProjection projection target hprojection
      hgoal derivation⟩

/-! ## Executable head boundaries -/

theorem append_isSideJudgment (left right result : Pattern) :
    IsSideJudgment (append left right result) := by
  simp [IsSideJudgment, append, reservedJudgmentHeads]

end Mettapedia.Languages.Metamath.InferenceProjection
