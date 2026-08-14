import Mettapedia.Languages.MeTTa.PureKernel.RegularSemanticCoherence

/-!
# The regular Pure fundamental lemma

The regular judgment has two semantic faces.  A formation judgment presents a
semantic type code and has a result convertible to the untyped top sort.  An
ordinary typing judgment presents a semantic term in the candidate selected by
its semantic type code.  Keeping those faces in one inductive interpretation
makes conversion across either boundary explicit and prevents `U1` from being
silently treated as an inhabitant of the semantic universe.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Typing

namespace SemanticTerm

/-- The top sort itself normalizes, although it is deliberately not interpreted
as a type code. -/
def u1 (context : CoherentCandidateContext n) :
    SemanticTerm (ContextualCandidateType.normalizing context) (.u1 : PureTm n) where
  realizes := by
    intro m environment realized
    exact reductionAccessible_u1
  constantFree := .u1

/-- Lambda introduction for the contextual dependent-function candidate. -/
def lam
    {context : CoherentCandidateContext n}
    {domain : ContextualCandidateType context}
    {codomain : ContextualCandidateType (context.extendContextual domain)}
    {body : PureTm (n + 1)}
    (bodySemantic : SemanticTerm codomain body) :
    SemanticTerm (domain.pi codomain) (.lam body) where
  constantFree := .lam bodySemantic.constantFree
  realizes := by
    intro m environment realized k rho argument argumentCovered
    have futureRealized : context.Realizes (renameEnvironment rho environment) :=
      context.rename_realizes environment rho realized
    have extendedRealized :
        (context.extendContextual domain).Realizes
          (consSub argument (renameEnvironment rho environment)) :=
      contextualPi_extended_realizes domain futureRealized argumentCovered
    have contractumCovered :=
      bodySemantic.realizes
        (consSub argument (renameEnvironment rho environment)) extendedRealized
    have liftedRealized := context.liftSub_realizes domain realized
    have bodyAccessible := reductionAccessible_rename (liftRen rho)
      (codomain.cr1 liftedRealized
        (bodySemantic.realizes (liftSub environment) liftedRealized))
    have argumentAccessible := domain.cr1 futureRealized argumentCovered
    change codomain.pred
      (consSub argument (renameEnvironment rho environment))
      (.app (.lam (rename (liftRen rho)
        (Substitution.subst (liftSub environment) body)))
        argument)
    apply codomain.beta_expansion _ extendedRealized bodyAccessible
      argumentAccessible
    have betaEnvironmentEq :
        (fun i => Substitution.subst (subst0 argument)
          (rename (liftRen rho) (liftSub environment i))) =
          consSub argument (renameEnvironment rho environment) := by
      funext index
      rw [rename_liftSub]
      refine Fin.cases ?_ ?_ index
      · rfl
      · intro preceding
        change inst0 argument
          (rename wk (rename rho (environment preceding))) =
            rename rho (environment preceding)
        exact inst0_rename_wk_cancel argument
          (rename rho (environment preceding))
    have contractumEq :
        inst0 argument
            (rename (liftRen rho)
              (Substitution.subst (liftSub environment) body)) =
          Substitution.subst
            (consSub argument (renameEnvironment rho environment)) body := by
      unfold inst0
      rw [rename_subst, subst_comp]
      exact subst_ext (fun i => congrFun betaEnvironmentEq i) body
    rw [contractumEq]
    exact contractumCovered

/-- Application eliminates a contextual dependent function.  The resulting
candidate is the codomain pulled back along singleton substitution. -/
def app
    {context : CoherentCandidateContext n}
    {domain : ContextualCandidateType context}
    {codomain : ContextualCandidateType (context.extendContextual domain)}
    {function argument : PureTm n}
    (functionSemantic : SemanticTerm (domain.pi codomain) function)
    (argumentSemantic : SemanticTerm domain argument) :
    SemanticTerm
      (codomain.reindex (SemanticSubstitution.instantiate domain argumentSemantic).maps)
      (.app function argument) where
  constantFree := .app functionSemantic.constantFree argumentSemantic.constantFree
  realizes := by
    intro m environment realized
    have functionCovered :
        (domain.pi codomain).pred environment
          (Substitution.subst environment function) :=
      functionSemantic.realizes environment realized
    have argumentCovered :
        domain.pred environment (Substitution.subst environment argument) :=
      argumentSemantic.realizes environment realized
    have renameId : renameEnvironment (idRen (n := m)) environment =
        environment := by
      funext index
      exact rename_id (environment index)
    have argumentAtId :
        domain.pred (renameEnvironment (idRen (n := m)) environment)
          (Substitution.subst environment argument) := by
      rw [renameId]
      exact argumentCovered
    have applicationCovered :=
      functionCovered (idRen (n := m))
        (Substitution.subst environment argument) argumentAtId
    change codomain.pred
      (compSub environment (subst0 argument))
      (.app (Substitution.subst environment function)
        (Substitution.subst environment argument))
    have environmentEq :
        compSub environment (subst0 argument) =
          consSub (Substitution.subst environment argument) environment := by
      funext index
      refine Fin.cases ?_ ?_ index
      · rfl
      · intro preceding
        rfl
    rw [environmentEq]
    rw [renameId] at applicationCovered
    simpa only [rename_id] using applicationCovered

/-- Pair introduction for the contextual dependent-pair candidate. -/
def pair
    {context : CoherentCandidateContext n}
    {domain : ContextualCandidateType context}
    {codomain : ContextualCandidateType (context.extendContextual domain)}
    {first second : PureTm n}
    (firstSemantic : SemanticTerm domain first)
    (secondSemantic : SemanticTerm
      (codomain.reindex (SemanticSubstitution.instantiate domain firstSemantic).maps)
      second) :
    SemanticTerm (domain.sigma codomain) (.pair first second) where
  constantFree := .pair firstSemantic.constantFree secondSemantic.constantFree
  realizes := by
    intro m environment realized
    have firstCovered := firstSemantic.realizes environment realized
    have secondCovered := secondSemantic.realizes environment realized
    apply contextualSigma_pair_intro domain codomain realized firstCovered
    change codomain.pred
      (compSub environment (subst0 first))
        (Substitution.subst environment second) at secondCovered
    have environmentEq :
        compSub environment (subst0 first) =
          consSub (Substitution.subst environment first) environment := by
      funext index
      refine Fin.cases ?_ ?_ index
      · rfl
      · intro preceding
        rfl
    rw [environmentEq] at secondCovered
    exact secondCovered

/-- First projection eliminates a contextual dependent pair. -/
def fst
    {context : CoherentCandidateContext n}
    {domain : ContextualCandidateType context}
    {codomain : ContextualCandidateType (context.extendContextual domain)}
    {pair : PureTm n}
    (pairSemantic : SemanticTerm (domain.sigma codomain) pair) :
    SemanticTerm domain (.fst pair) where
  constantFree := .fst pairSemantic.constantFree
  realizes := by
    intro m environment realized
    exact (pairSemantic.realizes environment realized).1

/-- Second projection eliminates a contextual dependent pair into the codomain
pulled back along the first projection. -/
def snd
    {context : CoherentCandidateContext n}
    {domain : ContextualCandidateType context}
    {codomain : ContextualCandidateType (context.extendContextual domain)}
    {pair : PureTm n}
    (pairSemantic : SemanticTerm (domain.sigma codomain) pair) :
    SemanticTerm
      (codomain.reindex
        (SemanticSubstitution.instantiate domain (fst pairSemantic)).maps)
      (.snd pair) where
  constantFree := .snd pairSemantic.constantFree
  realizes := by
    intro m environment realized
    have covered := pairSemantic.realizes environment realized
    change codomain.pred
      (compSub environment (subst0 (.fst pair)))
      (.snd (Substitution.subst environment pair))
    have environmentEq :
        compSub environment (subst0 (.fst pair)) =
          consSub (.fst (Substitution.subst environment pair)) environment := by
      funext index
      refine Fin.cases ?_ ?_ index
      · rfl
      · intro preceding
        rfl
    rw [environmentEq]
    exact covered.2

/-- Reflexivity introduction for the normalization interpretation of identity. -/
def refl
    {context : CoherentCandidateContext n}
    {type : ContextualCandidateType context} {term : PureTm n}
    (termSemantic : SemanticTerm type term) :
    SemanticTerm (ContextualCandidateType.normalizing context) (.refl term) where
  constantFree := .refl termSemantic.constantFree
  realizes := by
    intro m environment realized
    exact contextual_refl_intro_normalizing type realized
      (termSemantic.realizes environment realized)

end SemanticTerm

namespace SemanticConstantFreeConv

/-- Reflexive semantic conversion for the top sort. -/
def u1Refl (context : CoherentCandidateContext n) :
    SemanticConstantFreeConv context (.u1 : PureTm n) .u1 where
  converts := .refl (.u1 : PureTm n) ConstantFree.u1
  sourceNormalizes := SemanticTerm.u1 context
  targetNormalizes := SemanticTerm.u1 context

end SemanticConstantFreeConv

/-- The two semantic faces of the regular judgment. -/
inductive SemanticJudgment
    (context : CoherentCandidateContext n) : PureTm n → PureTm n → Prop where
  | formation {code sort : PureTm n}
      {meaning : ContextualCandidateType context} :
      SemanticType context code meaning →
      SemanticConstantFreeConv context sort .u1 →
      SemanticJudgment context code sort
  | typing {term typeCode : PureTm n}
      {meaning : ContextualCandidateType context} :
      SemanticType context typeCode meaning →
      SemanticTerm meaning term →
      SemanticJudgment context term typeCode

namespace SemanticJudgment

/-- A judgment whose target is literally `U1` must be a formation judgment. -/
theorem type_of_u1
    {n : Nat} {context : CoherentCandidateContext n} {code : PureTm n}
    (judgment : SemanticJudgment context code .u1) :
    ∃ meaning : ContextualCandidateType context,
      SemanticType context code meaning := by
  cases judgment with
  | formation semantic conversion => exact ⟨_, semantic⟩
  | typing semantic term =>
      exact False.elim (semantic.not_conv_u1
        (.refl (.u1 : PureTm n)))

/-- If the target already has a semantic meaning, the judgment is necessarily
the ordinary typing face and its term transports to that chosen meaning. -/
theorem term_at
    {n : Nat} {context : CoherentCandidateContext n}
    {term typeCode : PureTm n}
    {targetMeaning : ContextualCandidateType context}
    (judgment : SemanticJudgment context term typeCode)
    (targetSemantic : SemanticType context typeCode targetMeaning) :
    SemanticTerm targetMeaning term := by
  cases judgment with
  | formation codeSemantic sortConversion =>
      exact False.elim (targetSemantic.not_conv_u1
        sortConversion.converts.toConv)
  | typing sourceSemantic sourceTerm =>
      exact sourceTerm.of_equivalent
        (SemanticType.meaning_equivalent_of_conv sourceSemantic targetSemantic
          (.refl typeCode))

/-- Every semantically interpreted regular judgment has an accessible subject. -/
theorem subject_accessible
    {n : Nat} {context : CoherentCandidateContext n}
    {term typeCode : PureTm n}
    (judgment : SemanticJudgment context term typeCode) :
    ReductionAccessible term := by
  cases judgment with
  | formation semantic conversion => exact semantic.code_accessible
  | typing semantic term => exact term.accessible

end SemanticJudgment

/-! ## Simultaneous formation-and-membership fundamental lemma -/

/-- Every regular typing derivation is interpreted by the proof-relevant
semantic universe over every semantic realization of its raw context.  The
induction is genuinely simultaneous: formation premises extend the semantic
context used by dependent term premises, while ordinary term premises consume
the exact candidate selected by those formation derivations. -/
theorem RegularHasType.fundamental
    {syntaxContext : Ctx n} {term typeCode : PureTm n}
    (typing : RegularHasType syntaxContext term typeCode)
    (regularContext : RegularCtx syntaxContext)
    {context : CoherentCandidateContext n}
    (contextSemantic : SemanticContext syntaxContext context) :
    SemanticJudgment context term typeCode := by
  induction typing with
  | u0_type =>
      exact .formation (.u0 context) (SemanticConstantFreeConv.u1Refl context)
  | var index =>
      rcases contextSemantic.lookup_exists index with
        ⟨meaning, typeSemantic, variableSemantic⟩
      exact .typing typeSemantic variableSemantic
  | pi_form domainTyping codomainTyping domainIH codomainIH =>
      rcases (domainIH regularContext contextSemantic).type_of_u1 with
        ⟨domain, domainSemantic⟩
      have extendedRegular : RegularCtx _ := .snoc regularContext domainTyping
      have extendedSemantic : SemanticContext _
          (context.extendContextual domain) :=
        .snoc contextSemantic domainSemantic
      rcases (codomainIH extendedRegular extendedSemantic).type_of_u1 with
        ⟨codomain, codomainSemantic⟩
      exact .formation (.pi domainSemantic codomainSemantic)
        (SemanticConstantFreeConv.u1Refl context)
  | sigma_form domainTyping codomainTyping domainIH codomainIH =>
      rcases (domainIH regularContext contextSemantic).type_of_u1 with
        ⟨domain, domainSemantic⟩
      have extendedRegular : RegularCtx _ := .snoc regularContext domainTyping
      have extendedSemantic : SemanticContext _
          (context.extendContextual domain) :=
        .snoc contextSemantic domainSemantic
      rcases (codomainIH extendedRegular extendedSemantic).type_of_u1 with
        ⟨codomain, codomainSemantic⟩
      exact .formation (.sigma domainSemantic codomainSemantic)
        (SemanticConstantFreeConv.u1Refl context)
  | lam_intro domainTyping codomainTyping bodyTyping domainIH codomainIH bodyIH =>
      rcases (domainIH regularContext contextSemantic).type_of_u1 with
        ⟨domain, domainSemantic⟩
      have extendedRegular : RegularCtx _ := .snoc regularContext domainTyping
      have extendedSemantic : SemanticContext _
          (context.extendContextual domain) :=
        .snoc contextSemantic domainSemantic
      rcases (codomainIH extendedRegular extendedSemantic).type_of_u1 with
        ⟨codomain, codomainSemantic⟩
      have bodySemantic :=
        (bodyIH extendedRegular extendedSemantic).term_at codomainSemantic
      exact .typing (.pi domainSemantic codomainSemantic)
        (SemanticTerm.lam bodySemantic)
  | app_elim domainTyping functionTyping argumentTyping codomainTyping domainIH
      functionIH argumentIH codomainIH =>
      rcases (domainIH regularContext contextSemantic).type_of_u1 with
        ⟨domain, domainSemantic⟩
      have extendedRegular : RegularCtx _ := .snoc regularContext domainTyping
      have extendedSemantic : SemanticContext _
          (context.extendContextual domain) :=
        .snoc contextSemantic domainSemantic
      rcases (codomainIH extendedRegular extendedSemantic).type_of_u1 with
        ⟨codomain, codomainSemantic⟩
      have functionSemantic :=
        (functionIH regularContext contextSemantic).term_at
        (.pi domainSemantic codomainSemantic)
      have argumentSemantic :=
        (argumentIH regularContext contextSemantic).term_at domainSemantic
      let instantiate := SemanticSubstitution.instantiate domain argumentSemantic
      rcases codomainSemantic.subst_exists instantiate with
        ⟨resultMeaning, resultSemantic, resultEquivalent⟩
      have applicationSemantic := SemanticTerm.app functionSemantic argumentSemantic
      exact .typing resultSemantic
        (applicationSemantic.of_equivalent resultEquivalent.symm)
  | pair_intro domainTyping firstTyping secondTyping codomainTyping domainIH firstIH
      secondIH codomainIH =>
      rcases (domainIH regularContext contextSemantic).type_of_u1 with
        ⟨domain, domainSemantic⟩
      have extendedRegular : RegularCtx _ := .snoc regularContext domainTyping
      have extendedSemantic : SemanticContext _
          (context.extendContextual domain) :=
        .snoc contextSemantic domainSemantic
      rcases (codomainIH extendedRegular extendedSemantic).type_of_u1 with
        ⟨codomain, codomainSemantic⟩
      have firstSemantic :=
        (firstIH regularContext contextSemantic).term_at domainSemantic
      let instantiate := SemanticSubstitution.instantiate domain firstSemantic
      rcases codomainSemantic.subst_exists instantiate with
        ⟨secondMeaning, secondTypeSemantic, secondEquivalent⟩
      have secondSemantic :=
        (secondIH regularContext contextSemantic).term_at secondTypeSemantic
      have secondAtPullback := secondSemantic.of_equivalent secondEquivalent
      exact .typing (.sigma domainSemantic codomainSemantic)
        (SemanticTerm.pair firstSemantic secondAtPullback)
  | fst_elim domainTyping pairTyping codomainTyping domainIH pairIH codomainIH =>
      rcases (domainIH regularContext contextSemantic).type_of_u1 with
        ⟨domain, domainSemantic⟩
      have extendedRegular : RegularCtx _ := .snoc regularContext domainTyping
      have extendedSemantic : SemanticContext _
          (context.extendContextual domain) :=
        .snoc contextSemantic domainSemantic
      rcases (codomainIH extendedRegular extendedSemantic).type_of_u1 with
        ⟨codomain, codomainSemantic⟩
      have pairSemantic := (pairIH regularContext contextSemantic).term_at
        (.sigma domainSemantic codomainSemantic)
      exact .typing domainSemantic (SemanticTerm.fst pairSemantic)
  | snd_elim domainTyping pairTyping codomainTyping domainIH pairIH codomainIH =>
      rcases (domainIH regularContext contextSemantic).type_of_u1 with
        ⟨domain, domainSemantic⟩
      have extendedRegular : RegularCtx _ := .snoc regularContext domainTyping
      have extendedSemantic : SemanticContext _
          (context.extendContextual domain) :=
        .snoc contextSemantic domainSemantic
      rcases (codomainIH extendedRegular extendedSemantic).type_of_u1 with
        ⟨codomain, codomainSemantic⟩
      have pairSemantic := (pairIH regularContext contextSemantic).term_at
        (.sigma domainSemantic codomainSemantic)
      have firstSemantic := SemanticTerm.fst pairSemantic
      let instantiate := SemanticSubstitution.instantiate domain firstSemantic
      rcases codomainSemantic.subst_exists instantiate with
        ⟨resultMeaning, resultSemantic, resultEquivalent⟩
      have secondSemantic := SemanticTerm.snd pairSemantic
      exact .typing resultSemantic
        (secondSemantic.of_equivalent resultEquivalent.symm)
  | id_form typeTyping leftTyping rightTyping typeIH leftIH rightIH =>
      rcases (typeIH regularContext contextSemantic).type_of_u1 with
        ⟨type, typeSemantic⟩
      have leftSemantic :=
        (leftIH regularContext contextSemantic).term_at typeSemantic
      have rightSemantic :=
        (rightIH regularContext contextSemantic).term_at typeSemantic
      exact .formation (.identity typeSemantic leftSemantic rightSemantic)
        (SemanticConstantFreeConv.u1Refl context)
  | refl_intro typeTyping termTyping typeIH termIH =>
      rcases (typeIH regularContext contextSemantic).type_of_u1 with
        ⟨type, typeSemantic⟩
      have termSemantic :=
        (termIH regularContext contextSemantic).term_at typeSemantic
      exact .typing (.identity typeSemantic termSemantic termSemantic)
        (SemanticTerm.refl termSemantic)
  | conv_type sourceTyping targetTyping conversion sourceIH targetIH =>
      rcases (targetIH regularContext contextSemantic).type_of_u1 with
        ⟨targetMeaning, targetSemantic⟩
      cases sourceIH regularContext contextSemantic with
      | formation sourceSemantic sourceSort =>
          have targetToSort : Conv _ .u1 := Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.symm _ _ conversion.toConv)
            sourceSort.converts.toConv
          exact False.elim (targetSemantic.not_conv_u1 targetToSort)
      | typing sourceTypeSemantic sourceTerm =>
          have equivalent : ContextualCandidateType.Equivalent _ targetMeaning :=
            SemanticType.meaning_equivalent_of_conv
              sourceTypeSemantic targetSemantic conversion.toConv
          exact .typing targetSemantic (sourceTerm.of_equivalent equivalent)
  | conv_sort sourceTyping conversion sourceIH =>
      cases sourceIH regularContext contextSemantic with
      | formation sourceSemantic sourceSort =>
          exact .formation sourceSemantic
            (SemanticConstantFreeConv.u1Refl context)
      | typing sourceTypeSemantic sourceTerm =>
          exact False.elim (sourceTypeSemantic.not_conv_u1 conversion.toConv)

/-- Every regular context has a proof-relevant semantic realization. -/
theorem RegularCtx.semantic_exists {syntaxContext : Ctx n}
    (regular : RegularCtx syntaxContext) :
    ∃ context : CoherentCandidateContext n,
      SemanticContext syntaxContext context := by
  induction regular with
  | nil => exact ⟨CoherentCandidateContext.empty, .nil⟩
  | snoc base typeTyping ih =>
      rcases ih with ⟨context, contextSemantic⟩
      rcases (typeTyping.fundamental base contextSemantic).type_of_u1 with
        ⟨meaning, typeSemantic⟩
      exact ⟨context.extendContextual meaning,
        .snoc contextSemantic typeSemantic⟩

/-- Strong normalization is earned for every subject admitted by the regular
kernel, in every regular context. -/
theorem RegularJudgment.subject_accessible
    (judgment : RegularJudgment syntaxContext term typeCode) :
    ReductionAccessible term := by
  rcases judgment.context.semantic_exists with ⟨context, contextSemantic⟩
  exact (judgment.typing.fundamental judgment.context
    contextSemantic).subject_accessible

/-- The ordinary identity program is a positive normalization witness. -/
theorem regular_identity_accessible :
    ReductionAccessible (.lam (.var 0) : PureTm 0) :=
  (show RegularJudgment (.nil : Ctx 0) (.lam (.var 0)) (.pi .u0 .u0) from
    ⟨.nil, regular_identity⟩).subject_accessible

/-- The self-applicative omega term is the negative boundary witness: because
it is not accessible, no regular kernel judgment can admit it at any type. -/
theorem regular_omega_has_no_judgment :
    ¬ ∃ typeCode, RegularJudgment (.nil : Ctx 0) regularOmega typeCode := by
  rintro ⟨typeCode, judgment⟩
  exact omega_not_in_normalizing_candidate
    ((ReductionCandidate.normalizing_pred regularOmega).2
      judgment.subject_accessible)

/-! ## Axiom audit for the semantic constructor layer -/

#print axioms SemanticTerm.lam
#print axioms SemanticTerm.app
#print axioms SemanticTerm.pair
#print axioms SemanticTerm.fst
#print axioms SemanticTerm.snd
#print axioms SemanticTerm.refl
#print axioms SemanticJudgment.type_of_u1
#print axioms SemanticJudgment.term_at
#print axioms SemanticJudgment.subject_accessible
#print axioms RegularHasType.fundamental
#print axioms RegularCtx.semantic_exists
#print axioms RegularJudgment.subject_accessible
#print axioms regular_identity_accessible
#print axioms regular_omega_has_no_judgment

end Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary
