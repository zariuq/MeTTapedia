import Mettapedia.GSLT.LanguageDef.DecidableRelations.Disequality

/-!
# Membership and non-membership in a closed collection

Two judgments over an element and a collection, held as rules by a language:
- `Member(p, {p, ...rest}) ~> Yes`: the element is in the collection, by an ordinary bag match;
- `NonMember(p, {...rest}) ~> Yes` if `forAll(rest, x, Unequal(x, p) ~> Yes)`: every element differs from it.

The rest of the non-membership pattern is bound to the whole collection, closed, and `forAll` quantifies over exactly
its elements. So non-membership reads the collection as complete, and the language's own disequality decides each
element.

Take the signature's equality and disequality rules, and no other rule applying to these judgments
(`MembershipPrivate`). Then, on a term of the signature and a closed bag or set of such terms:
- membership holds exactly when the term is an element (`derives_member_iff`);
- non-membership holds exactly when it is not (`derives_nonMember_iff`);
- so the pair is complemented there (`membership_complemented`): an element missing from a collection is witnessed by
  a derivation, not only by the lack of one.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DecidableRelations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-! ## The rules -/

/-- The judgment that an element is in a collection. -/
def memberJudgment : String := "Member"

/-- The judgment that an element is not in a collection. -/
def nonMemberJudgment : String := "NonMember"

/-- `Member(p, {p, ...rest}) ~> Yes`. -/
def memberRule (kind : CollType) : RewriteRule :=
  ⟨"Member", [], [], .apply memberJudgment [.fvar "p", .collection kind [.fvar "p"] (some "rest")], yes, none⟩

/-- The premise of non-membership: every element of the rest differs from the element asked about. -/
def nonMemberPremise : Premise :=
  .forAll "rest" "x" (.congruence (.apply unequalJudgment [.fvar "x", .fvar "p"]) yes)

/-- `NonMember(p, {...rest}) ~> Yes` if every element of `rest` is unequal to `p`. -/
def nonMemberRule (kind : CollType) : RewriteRule :=
  ⟨"NonMember", [], [nonMemberPremise], .apply nonMemberJudgment [.fvar "p", .collection kind [] (some "rest")], yes, none⟩

/-- **The rules of membership and non-membership**, with the equality and disequality of the elements' signature. -/
def membershipRules (signature : List (String × Nat)) (kind : CollType) : List RewriteRule :=
  disequalityRules signature ++ [memberRule kind, nonMemberRule kind]

/-- **The language's other rules do not apply to the four judgments.** -/
def MembershipPrivate (language : LanguageDef) (signature : List (String × Nat)) (kind : CollType) : Prop :=
  ∀ rule ∈ language.rewrites, rule ∉ membershipRules signature kind →
    ∀ judgment ∈ [equalJudgment, unequalJudgment, memberJudgment, nonMemberJudgment], ∀ arguments,
      matchPattern rule.left (.apply judgment arguments) = []

/-- Privacy of the four judgments gives privacy of equality and disequality. -/
theorem MembershipPrivate.toPrivate {language : LanguageDef} {signature : List (String × Nat)} {kind : CollType}
    (privacy : MembershipPrivate language signature kind) : Private language signature := by
  intro rule member notGenerated arguments
  by_cases inRules : rule ∈ membershipRules signature kind
  · simp only [membershipRules, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at inRules
    rcases inRules with generated | rfl | rfl
    · exact absurd generated notGenerated
    · simp [memberRule, matchPattern, memberJudgment, equalJudgment, unequalJudgment]
    · simp [nonMemberRule, matchPattern, nonMemberJudgment, equalJudgment, unequalJudgment]
  · exact ⟨privacy rule member inRules _ (by simp) arguments, privacy rule member inRules _ (by simp) arguments⟩

/-! ## Matching membership and non-membership -/

/-- **The non-membership pattern binds the element and the whole collection.** -/
theorem matchPattern_nonMember (kind : CollType) (notVector : kind ≠ .vec) (element : Pattern)
    (elements : List Pattern) :
    matchPattern (nonMemberRule kind).left (.apply nonMemberJudgment [element, .collection kind elements none]) =
      [[("rest", .collection kind elements none), ("p", element)]] := by
  cases kind with
  | vec => exact absurd rfl notVector
  | hashBag => simp [nonMemberRule, nonMemberJudgment, matchPattern, matchArgs, matchBag, mergeBindings]
  | hashSet => simp [nonMemberRule, nonMemberJudgment, matchPattern, matchArgs, matchBag, mergeBindings]

/-- **The membership pattern matches only where the element is in the collection.** -/
theorem mem_of_matchPattern_member {kind : CollType} (notVector : kind ≠ .vec) {element : Pattern}
    {elements : List Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (memberRule kind).left
      (.apply memberJudgment [element, .collection kind elements none])) : element ∈ elements := by
  have related := matchPattern_sound matched
  simp only [memberRule] at related
  cases related with
  | apply arguments _ =>
    cases arguments with
    | cons headRelated tailRelated headMerged =>
      cases headRelated
      cases tailRelated with
      | cons collectionRelated nilRelated tailMerged =>
        cases nilRelated
        cases collectionRelated with
        | collection _ bagRelated =>
          cases bagRelated with
          | cons index inside elementRelated restRelated bagMerged =>
            cases elementRelated
            cases restRelated
            simp only [mergeBindings_nil_right, Option.some.injEq] at tailMerged
            subst tailMerged
            have restAdded := mergeBindings_fresh [("p", elements[index])]
              [("rest", .collection kind (elements.eraseIdx index) none)] (by simp) (by simp)
            rw [restAdded] at bagMerged
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, Option.some.injEq]
              at bagMerged
            subst bagMerged
            simp [mergeBindings, List.find?, BEq.beq] at headMerged
            obtain ⟨same, _⟩ := headMerged
            exact same ▸ List.getElem_mem inside
        | vectorRest _ _ => exact absurd rfl notVector

/-- **The membership pattern matches wherever the element is in the collection.** -/
theorem matchPattern_member_nonempty {kind : CollType} (notVector : kind ≠ .vec) {element : Pattern}
    {elements : List Pattern} (member : element ∈ elements) :
    ∃ bindings, bindings ∈ matchPattern (memberRule kind).left
      (.apply memberJudgment [element, .collection kind elements none]) := by
  obtain ⟨index, inside, found⟩ := List.getElem_of_mem member
  have bagAdded := mergeBindings_fresh [("p", elements[index])]
    [("rest", .collection kind (elements.eraseIdx index) none)] (by simp) (by simp)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at bagAdded
  refine ⟨[("rest", .collection kind (elements.eraseIdx index) none), ("p", element)], matchRel_complete ?_⟩
  refine .apply (.cons .fvar (.cons (.collection notVector (.cons index inside .fvar .nilRest bagAdded)) .nil
    (mergeBindings_nil_right _)) ?_) rfl
  rw [found]
  simp [mergeBindings, List.find?, BEq.beq]

/-! ## Membership and non-membership, derived -/

section Judgments

variable {relEnv : RelationEnv} {language : LanguageDef} {signature : List (String × Nat)} {kind : CollType}

/-- The equality and disequality rules do not apply to other judgments. -/
theorem matchPattern_disequality_other {rule : RewriteRule} (member : rule ∈ disequalityRules signature)
    {judgment : String} (notEqual : judgment ≠ equalJudgment) (notUnequal : judgment ≠ unequalJudgment)
    (arguments : List Pattern) : matchPattern rule.left (.apply judgment arguments) = [] := by
  rcases mem_disequalityRules member with rfl | ⟨first, _, second, _, _, rfl⟩ | ⟨constructor, _, position, _, rfl⟩
  · simp [equalRule, matchPattern, Ne.symm notEqual]
  · simp [clashRule, matchPattern, Ne.symm notUnequal]
  · simp [argumentRule, matchPattern, Ne.symm notUnequal]

/-- The only rule applying to a membership judgment is the membership rule. -/
theorem eq_memberRule {rule : RewriteRule} (privacy : MembershipPrivate language signature kind)
    (member : rule ∈ language.rewrites) {arguments : List Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern rule.left (.apply memberJudgment arguments)) : rule = memberRule kind := by
  by_cases generated : rule ∈ membershipRules signature kind
  · simp only [membershipRules, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at generated
    rcases generated with equality | same | rfl
    · rw [matchPattern_disequality_other equality (by decide) (by decide)] at matched
      simp at matched
    · exact same
    · simp [nonMemberRule, matchPattern, memberJudgment, nonMemberJudgment] at matched
  · rw [privacy rule member generated memberJudgment (by simp) arguments] at matched
    simp at matched

/-- The only rule applying to a non-membership judgment is the non-membership rule. -/
theorem eq_nonMemberRule {rule : RewriteRule} (privacy : MembershipPrivate language signature kind)
    (member : rule ∈ language.rewrites) {arguments : List Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern rule.left (.apply nonMemberJudgment arguments)) : rule = nonMemberRule kind := by
  by_cases generated : rule ∈ membershipRules signature kind
  · simp only [membershipRules, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at generated
    rcases generated with equality | rfl | same
    · rw [matchPattern_disequality_other equality (by decide) (by decide)] at matched
      simp at matched
    · simp [memberRule, matchPattern, memberJudgment, nonMemberJudgment] at matched
    · exact same
  · rw [privacy rule member generated nonMemberJudgment (by simp) arguments] at matched
    simp at matched

/-- **Membership holds exactly of the collection's elements.** -/
theorem derives_member_iff (rules : ∀ rule ∈ membershipRules signature kind, rule ∈ language.rewrites)
    (privacy : MembershipPrivate language signature kind) (notVector : kind ≠ .vec) {element : Pattern}
    {elements : List Pattern} :
    Derives relEnv language memberJudgment [element, .collection kind elements none] ↔ element ∈ elements := by
  constructor
  · rintro ⟨witness, step⟩
    obtain ⟨rule, member, initial, _, _, matched, _⟩ := stepValid_yes_cases step
    rw [eq_memberRule privacy member matched] at matched
    exact mem_of_matchPattern_member notVector matched
  · intro elementMember
    obtain ⟨bindings, matched⟩ := matchPattern_member_nonempty notVector elementMember
    exact stepValid_of_rule (rules _ (by simp [membershipRules])) matched (.nil _) rfl

/-- The bindings of a non-membership match: the whole collection and the element. -/
abbrev nonMemberBindings (element collection : Pattern) : Bindings := [("rest", collection), ("p", element)]

/-- The quantified variable reads the element it is bound to. -/
theorem applyBindings_parameter (element collection value : Pattern) :
    applyBindings (bindParameter (nonMemberBindings element collection) "x" value) (.fvar "x") = value := by
  simp [bindParameter, applyBindings, List.find?]

/-- The element asked about reads through a quantified binding. -/
theorem applyBindings_asked (element collection value : Pattern) :
    applyBindings (bindParameter (nonMemberBindings element collection) "x" value) (.fvar "p") = element := by
  simp [bindParameter, applyBindings, List.find?, List.filter]

/-- The body of non-membership at one element is a disequality judgment between it and the element asked about. -/
theorem nonMemberBody_source {sites : Pattern} {depth : Nat} {element value : Pattern} (collection : Pattern)
    (elementFirst : FirstOrder element) (valueFirst : FirstOrder value) :
    applyBindingsScoped sites (bindParameter (nonMemberBindings element collection) "x" value) depth
        (.apply unequalJudgment [.fvar "x", .fvar "p"]) = .apply unequalJudgment [value, element] := by
  rw [applyBindingsScoped_apply]
  simp only [List.map_cons, List.map_nil]
  rw [applyBindingsScoped_fvar valueFirst (applyBindings_parameter element collection value),
    applyBindingsScoped_fvar elementFirst (applyBindings_asked element collection value)]

/-- Disequality at every element gives the quantified premise of non-membership. -/
theorem forAllValid_of_unequal {sites element collection : Pattern} (elementFirst : FirstOrder element) :
    ∀ elements : List Pattern, (∀ value ∈ elements, FirstOrder value) →
      (∀ value ∈ elements, Derives relEnv language unequalJudgment [value, element]) →
      ∃ witnesses, ForAllValid relEnv language sites (nonMemberBindings element collection) "x"
        (.congruence (.apply unequalJudgment [.fvar "x", .fvar "p"]) yes) elements witnesses
  | [], _, _ => ⟨[], .nil⟩
  | value :: values, firstOrder, unequal => by
      obtain ⟨witnesses, rest⟩ := forAllValid_of_unequal elementFirst values
        (fun other member => firstOrder other (List.mem_cons_of_mem _ member))
        (fun other member => unequal other (List.mem_cons_of_mem _ member))
      obtain ⟨witness, step⟩ := unequal value (List.mem_cons_self ..)
      have stepped : StepValid relEnv language
          (applyBindingsScoped sites (bindParameter (nonMemberBindings element collection) "x" value)
            (stepDepth sites (.congruence (.apply unequalJudgment [.fvar "x", .fvar "p"]) yes))
            (.apply unequalJudgment [.fvar "x", .fvar "p"])) witness yes := by
        rw [nonMemberBody_source collection elementFirst (firstOrder value (List.mem_cons_self ..))]
        exact step
      have matchedYes : ([] : Bindings) ∈ matchPattern yes yes := by
        rw [matchPattern_firstOrder yes_firstOrder yes]
        simp
      exact ⟨_ :: witnesses, .cons (.step rfl stepped matchedYes (mergeBindings_nil_right _)) rest⟩

/-- The quantified premise of non-membership gives disequality at every element. -/
theorem unequal_of_forAllValid {sites element collection : Pattern} {witnesses : List Witness}
    (elementFirst : FirstOrder element) {elements : List Pattern}
    (valid : ForAllValid relEnv language sites (nonMemberBindings element collection) "x"
      (.congruence (.apply unequalJudgment [.fvar "x", .fvar "p"]) yes) elements witnesses)
    (firstOrder : ∀ value ∈ elements, FirstOrder value) :
    ∀ value ∈ elements, Derives relEnv language unequalJudgment [value, element] := by
  induction elements generalizing witnesses with
  | nil => simp
  | cons value values inner =>
      cases valid with
      | cons premise rest =>
          intro other member
          rcases List.mem_cons.mp member with rfl | later
          · cases premise with
            | base isBaseTrue _ => simp [isBase] at isBaseTrue
            | step endpoints stepped matchedYes _ =>
                simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
                obtain ⟨rfl, rfl⟩ := endpoints
                have candidateYes := eq_yes_of_mem_matchPattern matchedYes
                subst candidateYes
                rw [nonMemberBody_source collection elementFirst (firstOrder other (List.mem_cons_self ..))] at stepped
                exact ⟨_, stepped⟩
          · exact inner rest (fun item itemMember => firstOrder item (List.mem_cons_of_mem _ itemMember)) other
              later

/-- **Non-membership holds exactly of what the collection lacks.** -/
theorem derives_nonMember_iff (rules : ∀ rule ∈ membershipRules signature kind, rule ∈ language.rewrites)
    (privacy : MembershipPrivate language signature kind) (names : (signature.map Prod.fst).Nodup)
    (notVector : kind ≠ .vec) {element : Pattern} {elements : List Pattern}
    (elementOver : TermOf signature element) (elementsOver : ∀ value ∈ elements, TermOf signature value) :
    Derives relEnv language nonMemberJudgment [element, .collection kind elements none] ↔ element ∉ elements := by
  have firstOrder : ∀ value ∈ elements, FirstOrder value := fun value member => (elementsOver value member).firstOrder
  constructor
  · rintro ⟨witness, step⟩ elementMember
    obtain ⟨rule, member, initial, final, witnesses, matched, premises⟩ := stepValid_yes_cases step
    have same := eq_nonMemberRule privacy member matched
    subst same
    rw [matchPattern_nonMember kind notVector] at matched
    simp only [List.mem_singleton] at matched
    subst matched
    cases premises with
    | cons premise rest =>
        cases premise with
        | base isBaseTrue _ => simp [nonMemberPremise, isBase] at isBaseTrue
        | step endpoints _ _ _ => simp [nonMemberPremise, stepEndpoints] at endpoints
        | forAll found valid =>
            simp only [Bindings.lookup, List.find?, beq_self_eq_true, Option.map_some,
              Option.some.injEq, Pattern.collection.injEq] at found
            obtain ⟨rfl, rfl, -⟩ := found
            have unequal := unequal_of_forAllValid elementOver.firstOrder valid firstOrder element elementMember
            exact ne_of_derives_unequal privacy.toPrivate elementOver.firstOrder elementOver.firstOrder unequal rfl
  · intro missing
    have unequal : ∀ value ∈ elements, Derives relEnv language unequalJudgment [value, element] := by
      intro value member
      exact derives_unequal_of_ne (fun rule generated => rules rule (List.mem_append_left _ generated)) names
        (elementsOver value member) elementOver (fun same => missing (same ▸ member))
    obtain ⟨witnesses, valid⟩ := forAllValid_of_unequal (collection := .collection kind elements none)
      elementOver.firstOrder elements firstOrder unequal
    have premises : PremisesValid relEnv language (captureSites (nonMemberRule kind))
        (nonMemberBindings element (.collection kind elements none)) (nonMemberRule kind).premises
        [.forAll witnesses] (nonMemberBindings element (.collection kind elements none)) :=
      .cons (.forAll (kind := kind) (elements := elements) (by simp [Bindings.lookup, List.find?]) valid) (.nil _)
    refine stepValid_of_rule (rules _ (by simp [membershipRules])) ?_ premises rfl
    rw [matchPattern_nonMember kind notVector]
    simp

/-- **Membership and non-membership are complemented** on a term of the signature and a closed bag or set of such terms: what a
collection lacks is witnessed by a derivation of non-membership. -/
theorem membership_complemented (rules : ∀ rule ∈ membershipRules signature kind, rule ∈ language.rewrites)
    (privacy : MembershipPrivate language signature kind) (names : (signature.map Prod.fst).Nodup)
    (notVector : kind ≠ .vec) :
    Complemented
      (fun asked : Pattern × List Pattern =>
        Derives relEnv language memberJudgment [asked.1, .collection kind asked.2 none])
      (fun asked => Derives relEnv language nonMemberJudgment [asked.1, .collection kind asked.2 none])
      (fun asked => TermOf signature asked.1 ∧ ∀ value ∈ asked.2, TermOf signature value) where
  disjoint asked inside member nonMember :=
    (derives_nonMember_iff rules privacy names notVector inside.1 inside.2).mp nonMember
      ((derives_member_iff rules privacy notVector).mp member)
  exhaustive asked inside := by
    by_cases member : asked.1 ∈ asked.2
    · exact .inl ((derives_member_iff rules privacy notVector).mpr member)
    · exact .inr ((derives_nonMember_iff rules privacy names notVector inside.1 inside.2).mpr member)

end Judgments

end Mettapedia.GSLT.LanguageDef.DecidableRelations
