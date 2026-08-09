import Mettapedia.GSLT.LanguageDef.CostSemanticAtomAlignment
import Mettapedia.GSLT.LanguageDef.CostSemanticAtomReifyCongruence
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalRootDichotomy

/-!
# Depth-uniform restoration equality

Hereditary Cost normalization compares semantic leaves below binders and
reflective quotations.  Equality at one ambient depth is therefore not a
stable induction hypothesis.  `RestoresTogether` records equality after the
same supported assignment at every depth and supplies the structural closure
rules needed by recursive common-apex constructions.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace ReflectiveContextSupport

/-- Two compact patterns restore to the same pattern at every ambient binder
depth under one profile, support function, and assignment. -/
def RestoresTogether (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment)
    (left right : Pattern) : Prop :=
  ∀ depth,
    substituteAt profile support assignment depth left =
      substituteAt profile support assignment depth right

namespace RestoresTogether

theorem refl (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile) (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment) (pattern : Pattern) :
    RestoresTogether profile support assignment pattern pattern := by
  intro depth
  rfl

theorem symm {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile} {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment} {left right : Pattern}
    (restores : RestoresTogether profile support assignment left right) :
    RestoresTogether profile support assignment right left := by
  intro depth
  exact (restores depth).symm

theorem trans {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile} {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment} {first second third : Pattern}
    (firstSecond : RestoresTogether profile support assignment first second)
    (secondThird : RestoresTogether profile support assignment second third) :
    RestoresTogether profile support assignment first third := by
  intro depth
  exact (firstSecond depth).trans (secondThird depth)

private theorem map_substituteAt_eq_of_forall₂
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile} {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment}
    {left right : List Pattern}
    (related : List.Forall₂
      (RestoresTogether profile support assignment) left right)
    (depth : Nat) :
    left.map (substituteAt profile support assignment depth) =
      right.map (substituteAt profile support assignment depth) := by
  induction related with
  | nil => rfl
  | cons headRestores tailRestores inductionHypothesis =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨headRestores depth, inductionHypothesis⟩

theorem apply {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile} {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment} {constructor : String}
    {leftArguments rightArguments : List Pattern}
    (arguments : List.Forall₂
      (RestoresTogether profile support assignment)
      leftArguments rightArguments) :
    RestoresTogether profile support assignment
      (.apply constructor leftArguments) (.apply constructor rightArguments) := by
  intro depth
  simp only [substituteAt, Pattern.apply.injEq, true_and]
  exact map_substituteAt_eq_of_forall₂ arguments
    (if isQuoteConstructor profile constructor then 0 else depth)

theorem lambda {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile} {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment} {binder : Option String}
    {leftBody rightBody : Pattern}
    (body : RestoresTogether profile support assignment leftBody rightBody) :
    RestoresTogether profile support assignment
      (.lambda binder leftBody) (.lambda binder rightBody) := by
  intro depth
  simp only [substituteAt, Pattern.lambda.injEq, true_and]
  exact body (depth + 1)

theorem multiLambda {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment} {arity : Nat}
    {binders : List String} {leftBody rightBody : Pattern}
    (body : RestoresTogether profile support assignment leftBody rightBody) :
    RestoresTogether profile support assignment
      (.multiLambda arity binders leftBody)
      (.multiLambda arity binders rightBody) := by
  intro depth
  simp only [substituteAt, Pattern.multiLambda.injEq, true_and]
  exact body (depth + arity)

theorem subst {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile} {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment}
    {leftBody rightBody leftReplacement rightReplacement : Pattern}
    (body : RestoresTogether profile support assignment leftBody rightBody)
    (replacement : RestoresTogether profile support assignment
      leftReplacement rightReplacement) :
    RestoresTogether profile support assignment
      (.subst leftBody leftReplacement) (.subst rightBody rightReplacement) := by
  intro depth
  simp only [substituteAt, Pattern.subst.injEq]
  exact ⟨body (depth + 1), replacement depth⟩

theorem collection {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {support : ContextSupport.Support}
    {assignment : ContextSupport.Assignment} {collectionType : CollType}
    {leftElements rightElements : List Pattern} {rest : Option String}
    (elements : List.Forall₂
      (RestoresTogether profile support assignment)
      leftElements rightElements) :
    RestoresTogether profile support assignment
      (.collection collectionType leftElements rest)
      (.collection collectionType rightElements rest) := by
  intro depth
  simp only [substituteAt]
  rw [map_substituteAt_eq_of_forall₂ elements depth]

/-- A bound variable is a rigid restoration leaf: supported substitution
never consults the assignment at that node. -/
theorem bvar (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile) (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment) (index : Nat) :
    RestoresTogether profile support assignment (.bvar index) (.bvar index) :=
  refl profile support assignment (.bvar index)

/-- Two parameter names with one closed assigned value restore together even
when their declared support suffixes differ.  Closedness is exactly what
makes both support-indexed weakenings inert. -/
theorem fvar_of_assignment_eq_of_scoped
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile) (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment) (leftName rightName : String)
    (assignmentEq : assignment leftName = assignment rightName)
    (assignedScoped : (assignment leftName).isWellScopedAt 0 = true) :
    RestoresTogether profile support assignment
      (.fvar leftName) (.fvar rightName) := by
  intro depth
  simp only [substituteAt]
  rw [assignmentEq]
  have rightScoped : (assignment rightName).isWellScopedAt 0 = true := by
    simpa only [assignmentEq] using assignedScoped
  rw [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
        rightScoped,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
        rightScoped]

/-- The closed-value premise of `fvar_of_assignment_eq_of_scoped` cannot be
dropped.  With one retained binder on the left and none on the right, assigning
the same bound variable produces different de Bruijn indices at depth one. -/
theorem unequal_support_bvar_assignment_not_restoresTogether
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile) (binderType : TypeExpr) :
    let support : ContextSupport.Support := fun name =>
      if name = "left" then [binderType] else []
    let assignment : ContextSupport.Assignment := fun _ => .bvar 0
    ¬ RestoresTogether profile support assignment
      (.fvar "left") (.fvar "right") := by
  dsimp only
  intro restores
  have atDepthOne := restores 1
  simp [substituteAt, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars] at atDepthOne

mutual
  /-- A structural semantic-leaf alignment whose selected leaves restore
  together itself restores together at every depth. -/
  def PatternLeafAligned.toRestoresTogether
      {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile} {support : ContextSupport.Support}
      {assignment : ContextSupport.Assignment} :
      ∀ {left right : Pattern},
        PatternLeafAligned
          (RestoresTogether profile support assignment) left right →
        RestoresTogether profile support assignment left right
    | _, _, .leaf related => related
    | _, _, .bvar index =>
        RestoresTogether.bvar profile support assignment index
    | _, _, .apply constructor arguments =>
        RestoresTogether.apply
          (PatternLeafAlignedList.toRestoresTogether arguments)
    | _, _, .lambda binder body =>
        RestoresTogether.lambda
          (PatternLeafAligned.toRestoresTogether body)
    | _, _, .multiLambda arity binders body =>
        RestoresTogether.multiLambda
          (PatternLeafAligned.toRestoresTogether body)
    | _, _, .subst body replacement =>
        RestoresTogether.subst
          (PatternLeafAligned.toRestoresTogether body)
          (PatternLeafAligned.toRestoresTogether replacement)
    | _, _, .collection collectionType rest elements =>
        RestoresTogether.collection
          (PatternLeafAlignedList.toRestoresTogether elements)

  /-- Listwise companion of `PatternLeafAligned.toRestoresTogether`. -/
  def PatternLeafAlignedList.toRestoresTogether
      {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile} {support : ContextSupport.Support}
      {assignment : ContextSupport.Assignment} :
      ∀ {left right : List Pattern},
        PatternLeafAlignedList
          (RestoresTogether profile support assignment) left right →
        List.Forall₂ (RestoresTogether profile support assignment) left right
    | _, _, .nil => .nil
    | _, _, .cons head tail =>
        .cons (PatternLeafAligned.toRestoresTogether head)
          (PatternLeafAlignedList.toRestoresTogether tail)
end

end RestoresTogether

end ReflectiveContextSupport

/-! ## Recursive common restoration apex

Pointwise leaf alignment is insufficient for canonical parallel frames: two
stable sorts may retain different orders among semantically equal keys.  A
single top-level permutation is also insufficient because a parallel frame
may occur below an ordinary constructor or binder.  The following family is
the congruence generated by depth-uniform leaf restoration and restored
parallel permutation.

Its endpoints live in the common namespace of a semantic-key cospan.  This is
important: occurrence and boundary identities remain in the endpoint
environments, while the relation compares only the meanings transported to
their common apex.
-/

namespace CostStaticAtomKeyCospan

open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/- Recursive equality evidence at a common semantic restoration apex.

The depth index is proof-relevant.  Ordinary binders increase it, reflective
quotes reset it, and a parallel node uses it both for semantic keying and for
the final supported restoration. -/
mutual
inductive CommonRestorationApex
    (source : CIGSLT) {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) :
    Nat → Pattern → Pattern → Prop where
  /-- Structural alignment outside leaves which already restore together at
  every possible depth. -/
  | leafAligned {depth : Nat} {left right : Pattern}
      (aligned : PatternLeafAligned
        (ReflectiveContextSupport.RestoresTogether
          source.costWholeReflectionProfile
          cospan.commonSupport cospan.commonAssignment) left right) :
      CommonRestorationApex source cospan declaration depth left right
  /-- Rigid ordinary application congruence.  Quote applications use depth
  zero for every argument; other constructors preserve the current depth. -/
  | apply {depth : Nat} (constructor : String)
      {leftArguments rightArguments : List Pattern}
      (arguments : CommonRestorationApexList source cospan declaration
        (if ReflectiveContextSupport.isQuoteConstructor
            source.costWholeReflectionProfile constructor then 0 else depth)
        leftArguments rightArguments) :
      CommonRestorationApex source cospan declaration depth
        (.apply constructor leftArguments) (.apply constructor rightArguments)
  | lambda {depth : Nat} (binder : Option String)
      {leftBody rightBody : Pattern}
      (body : CommonRestorationApex source cospan declaration (depth + 1)
        leftBody rightBody) :
      CommonRestorationApex source cospan declaration depth
        (.lambda binder leftBody) (.lambda binder rightBody)
  | multiLambda {depth arity : Nat} (binders : List String)
      {leftBody rightBody : Pattern}
      (body : CommonRestorationApex source cospan declaration (depth + arity)
        leftBody rightBody) :
      CommonRestorationApex source cospan declaration depth
        (.multiLambda arity binders leftBody)
        (.multiLambda arity binders rightBody)
  | subst {depth : Nat}
      {leftBody rightBody leftReplacement rightReplacement : Pattern}
      (body : CommonRestorationApex source cospan declaration (depth + 1)
        leftBody rightBody)
      (replacement : CommonRestorationApex source cospan declaration depth
        leftReplacement rightReplacement) :
      CommonRestorationApex source cospan declaration depth
        (.subst leftBody leftReplacement)
        (.subst rightBody rightReplacement)
  | collection {depth : Nat} (collectionType : CollType)
      (rest : Option String) {leftElements rightElements : List Pattern}
      (elements : CommonRestorationApexList source cospan declaration depth
        leftElements rightElements) :
      CommonRestorationApex source cospan declaration depth
        (.collection collectionType leftElements rest)
        (.collection collectionType rightElements rest)
  /-- Bare parallel canonicalization is compared after recursive
  canonicalization, flattening, unit deletion, and common restoration.  The
  remaining datum is exactly a finite permutation; no stable-tie order is
  promoted to semantics. -/
  | parallel {depth : Nat} {leftElements rightElements : List Pattern}
      (permutation : List.Perm
        ((parallelContents declaration
          (canonicalizeListByAt
            (cospan.commonSemanticPatternKeyAt source) declaration depth
            leftElements)).map
              (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
                cospan.commonSupport cospan.commonAssignment depth))
        ((parallelContents declaration
          (canonicalizeListByAt
            (cospan.commonSemanticPatternKeyAt source) declaration depth
            rightElements)).map
              (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
                cospan.commonSupport cospan.commonAssignment depth))) :
      CommonRestorationApex source cospan declaration depth
        (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
          declaration depth
          (.collection declaration.parallelCollection leftElements none))
        (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
          declaration depth
          (.collection declaration.parallelCollection rightElements none))

/-- Pointwise companion used by rigid application and collection
congruence. -/
inductive CommonRestorationApexList
    (source : CIGSLT) {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) :
    Nat → List Pattern → List Pattern → Prop where
  | nil (depth : Nat) :
      CommonRestorationApexList source cospan declaration depth [] []
  | cons {depth : Nat} {leftHead rightHead : Pattern}
      {leftTail rightTail : List Pattern}
      (head : CommonRestorationApex source cospan declaration depth
        leftHead rightHead)
      (tail : CommonRestorationApexList source cospan declaration depth
        leftTail rightTail) :
      CommonRestorationApexList source cospan declaration depth
        (leftHead :: leftTail) (rightHead :: rightTail)
end

namespace CommonRestorationApex

/-- Reflexive apex evidence.  Free variables use the depth-uniform reflexive
restoration law; all rigid structure is retained by `PatternLeafAligned`. -/
theorem refl
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    (pattern : Pattern) :
    CommonRestorationApex source cospan declaration depth pattern pattern :=
  .leafAligned (PatternLeafAligned.refl
    (fun name => ReflectiveContextSupport.RestoresTogether.refl
      source.costWholeReflectionProfile cospan.commonSupport
      cospan.commonAssignment
      (.fvar name)) pattern)

/-- Exact equality embeds into the restoration relation without inventing a
semantic leaf or a permutation. -/
theorem of_eq
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    {left right : Pattern} (equal : left = right) :
    CommonRestorationApex source cospan declaration depth left right := by
  subst right
  exact refl cospan declaration depth left

/-- Depth-uniform equality of the collision-free semantic key is sufficient
for a semantic-leaf apex.  This is the intended way stable key ties enter the
relation: the tie certifies equal restored meanings, not equal provenance or
raw spelling. -/
theorem leaf_of_key_eq
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    {left right : Pattern}
    (keysEqual : ∀ currentDepth,
      cospan.commonSemanticPatternKeyAt source currentDepth left =
        cospan.commonSemanticPatternKeyAt source currentDepth right) :
    CommonRestorationApex source cospan declaration depth left right :=
  .leafAligned (.leaf (fun currentDepth =>
    (cospan.commonSemanticPatternKeyAt_eq_iff source currentDepth left right).mp
      (keysEqual currentDepth)))

mutual
  /-- Reverse a common restoration apex.  The parallel terminal reverses its
  finite permutation; every other constructor reverses recursively. -/
  def symm
      {source : CIGSLT} {leftCount rightCount : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      {cospan : CostStaticAtomKeyCospan leftKey rightKey}
      {declaration : ReflectivePresentationDecl}
      {depth : Nat} {left right : Pattern}
      (apex : CommonRestorationApex source cospan declaration depth left right) :
      CommonRestorationApex source cospan declaration depth right left :=
    match apex with
    | .leafAligned aligned =>
        .leafAligned (.leaf (fun currentDepth =>
          (ReflectiveContextSupport.RestoresTogether.PatternLeafAligned.toRestoresTogether
            aligned currentDepth).symm))
    | .apply constructor arguments =>
        .apply constructor (symmList arguments)
    | .lambda binder body => .lambda binder (symm body)
    | .multiLambda binders body => .multiLambda binders (symm body)
    | .subst body replacement => .subst (symm body) (symm replacement)
    | .collection collectionType rest elements =>
        .collection collectionType rest (symmList elements)
    | .parallel permutation => .parallel permutation.symm

  /-- Listwise companion of `CommonRestorationApex.symm`. -/
  def symmList
      {source : CIGSLT} {leftCount rightCount : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      {cospan : CostStaticAtomKeyCospan leftKey rightKey}
      {declaration : ReflectivePresentationDecl}
      {depth : Nat} {left right : List Pattern}
      (apex : CommonRestorationApexList source cospan declaration depth
        left right) :
      CommonRestorationApexList source cospan declaration depth right left :=
    match apex with
    | .nil depth => .nil depth
    | .cons head tail => .cons (symm head) (symmList tail)
end

/-- A permutation of restoration-related entries, with positional alignment
and finite reordering retained as separate proof-relevant data.  This is the
list currency for canonical parallel inversion, which yields a multiset
correspondence rather than a positional zip. -/
structure Permutation
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    (left right : List Pattern) : Type where
  middle : List Pattern
  aligned : CommonRestorationApexList source cospan declaration depth
    left middle
  permutation : List.Perm middle right

/- Eliminate a recursive apex into exact equality after common restoration.

The leaf case consumes `PatternLeafAligned`; the parallel case consumes the
permutation terminal; all remaining cases are genuine structural congruence.
-/
mutual
  def restored_eq
      {source : CIGSLT} {leftCount rightCount : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      {cospan : CostStaticAtomKeyCospan leftKey rightKey}
      {declaration : ReflectivePresentationDecl}
      {depth : Nat} {left right : Pattern}
      (apex : CommonRestorationApex source cospan declaration depth left right) :
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
          cospan.commonSupport cospan.commonAssignment depth left =
        ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
          cospan.commonSupport cospan.commonAssignment depth right :=
    match apex with
    | .leafAligned aligned =>
        ReflectiveContextSupport.RestoresTogether.PatternLeafAligned.toRestoresTogether
          aligned depth
    | .apply constructor arguments => by
        simp only [ReflectiveContextSupport.substituteAt]
        exact congrArg (Pattern.apply constructor) (restoredList_eq arguments)
    | .lambda binder body => by
        simp only [ReflectiveContextSupport.substituteAt]
        exact congrArg (Pattern.lambda binder) (restored_eq body)
    | .multiLambda binders body => by
        simp only [ReflectiveContextSupport.substituteAt]
        exact congrArg (Pattern.multiLambda _ binders) (restored_eq body)
    | .subst body replacement => by
        simp only [ReflectiveContextSupport.substituteAt,
          Pattern.subst.injEq]
        exact ⟨restored_eq body, restored_eq replacement⟩
    | .collection collectionType rest elements => by
        simp only [ReflectiveContextSupport.substituteAt]
        exact congrArg (fun patterns =>
          Pattern.collection collectionType patterns rest)
            (restoredList_eq elements)
    | .parallel permutation =>
        cospan.substituteAt_canonicalizeByAt_parallel_eq_of_perm source
          depth declaration permutation

  /-- Listwise elimination for rigid congruence constructors. -/
  def restoredList_eq
      {source : CIGSLT} {leftCount rightCount : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      {cospan : CostStaticAtomKeyCospan leftKey rightKey}
      {declaration : ReflectivePresentationDecl}
      {depth : Nat} {left right : List Pattern}
      (apex : CommonRestorationApexList source cospan declaration depth
        left right) :
      left.map (ReflectiveContextSupport.substituteAt
          source.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment depth) =
        right.map (ReflectiveContextSupport.substituteAt
          source.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment depth) :=
    match apex with
    | .nil depth => rfl
    | .cons head tail =>
        congrArg₂ List.cons (restored_eq head) (restoredList_eq tail)
end

/-- Forget a proof-relevant aligned permutation to the permutation of its
restored compact meanings. -/
theorem Permutation.restored_perm
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl} {depth : Nat}
    {left right : List Pattern}
    (alignment : Permutation (source := source) cospan declaration depth
      left right) :
    List.Perm
      (left.map (ReflectiveContextSupport.substituteAt
        source.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment
        depth))
      (right.map (ReflectiveContextSupport.substituteAt
        source.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment
        depth)) := by
  rw [restoredList_eq alignment.aligned]
  exact alignment.permutation.map _

/-- Build the parallel apex from an occurrence-preserving alignment of the
post-canonicalization, post-splice frontiers. -/
theorem parallel_of_permutation
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    {leftElements rightElements : List Pattern}
    (alignment : Permutation (source := source) cospan declaration depth
      (parallelContents declaration
        (canonicalizeListByAt (cospan.commonSemanticPatternKeyAt source)
          declaration depth leftElements))
      (parallelContents declaration
        (canonicalizeListByAt (cospan.commonSemanticPatternKeyAt source)
          declaration depth rightElements))) :
    CommonRestorationApex source cospan declaration depth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration depth
        (.collection declaration.parallelCollection leftElements none))
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration depth
        (.collection declaration.parallelCollection rightElements none)) :=
  .parallel alignment.restored_perm

/-- A permutation of ordinary canonical images can be pulled back to an
occurrence-preserving permutation of the original right list, aligned
pointwise by canonical equality.  No injectivity of canonicalization is used:
duplicate and collapsing classes retain separate list occurrences. -/
theorem exists_forall₂_canonical_eq_of_map_perm
    (declaration : ReflectivePresentationDecl)
    {left right : List Pattern}
    (permutation : List.Perm
      (left.map (canonicalize declaration))
      (right.map (canonicalize declaration))) :
    ∃ middle,
      List.Forall₂
          (fun leftPattern rightPattern =>
            canonicalize declaration leftPattern =
              canonicalize declaration rightPattern)
          left middle ∧
        List.Perm middle right := by
  have rightGraph : List.Forall₂
      (fun canonicalPattern pattern =>
        canonicalPattern = canonicalize declaration pattern)
      (right.map (canonicalize declaration)) right := by
    rw [List.forall₂_map_left_iff]
    exact List.forall₂_same.mpr (fun _ _ => rfl)
  obtain ⟨middle, aligned, reordered⟩ :=
    List.perm_comp_forall₂ permutation rightGraph
  refine ⟨middle, ?_, reordered⟩
  simpa only [List.forall₂_map_left_iff] using aligned

/-- Lift a permutation of ordinary canonical classes through a local
common-apex constructor.  The supplied constructor is the recursive-call
interface used by the well-founded canonical-pair proof; multiplicities and
discarded positional identities are retained by the intermediate list. -/
noncomputable def Permutation.of_canonical_map_perm
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    {left right : List Pattern}
    (permutation : List.Perm
      (left.map (canonicalize declaration))
      (right.map (canonicalize declaration)))
    (close : ∀ {leftPattern rightPattern},
      canonicalize declaration leftPattern =
          canonicalize declaration rightPattern →
        CommonRestorationApex source cospan declaration depth
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
            declaration depth leftPattern)
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
            declaration depth rightPattern)) :
    Permutation (source := source) cospan declaration depth
      (canonicalizeListByAt (cospan.commonSemanticPatternKeyAt source)
        declaration depth left)
      (canonicalizeListByAt (cospan.commonSemanticPatternKeyAt source)
        declaration depth right) := by
  let evidence :=
    exists_forall₂_canonical_eq_of_map_perm declaration permutation
  let middle := Classical.choose evidence
  have middleSpec := Classical.choose_spec evidence
  have aligned := middleSpec.1
  have reordered := middleSpec.2
  let normalize := canonicalizeByAt
    (cospan.commonSemanticPatternKeyAt source) declaration depth
  have liftAligned : ∀ {leftPatterns rightPatterns : List Pattern},
      List.Forall₂
          (fun leftPattern rightPattern =>
            canonicalize declaration leftPattern =
              canonicalize declaration rightPattern)
          leftPatterns rightPatterns →
        CommonRestorationApexList source cospan declaration depth
          (leftPatterns.map normalize) (rightPatterns.map normalize) := by
    intro leftPatterns rightPatterns relation
    induction relation with
    | nil => exact .nil depth
    | cons related _ inductionHypothesis =>
        exact .cons (close related) inductionHypothesis
  have normalizedAligned : CommonRestorationApexList source cospan declaration
      depth (left.map normalize) (middle.map normalize) :=
    liftAligned aligned
  refine
    { middle := middle.map normalize
      aligned := ?_
      permutation := ?_ }
  simpa [normalize, canonicalizeListByAt_eq_map] using normalizedAligned
  simpa [normalize, canonicalizeListByAt_eq_map] using reordered.map normalize

/-- Away from the two root-changing reflective forms, ordinary canonical
root inversion lifts directly to the common-restoration apex.  The recursive
callback is invoked only for proper children and at the depth selected by the
rigid constructor: binders advance it, whereas this aligned arm cannot have a
quote head. -/
theorem of_canonicalRootAligned
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (close : ∀ leftChildDepth rightChildDepth childRootDepth
      {leftChild rightChild : Pattern},
      canonicalize declaration leftChild = canonicalize declaration rightChild →
        CommonRestorationApex source cospan declaration childRootDepth
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
            declaration leftChildDepth leftChild)
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
            declaration rightChildDepth rightChild))
    {leftDepth rightDepth rootDepth : Nat} {left right : Pattern}
    (ordinaryHead : ∀ {constructor : String}
      {leftArguments rightArguments : List Pattern},
      left = .apply constructor leftArguments →
      right = .apply constructor rightArguments →
      constructor ≠ declaration.quoteConstructor →
      ReflectiveContextSupport.isQuoteConstructor source.costWholeReflectionProfile
        constructor = false)
    (aligned : CanonicalRootAligned declaration left right) :
    CommonRestorationApex source cospan declaration rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration leftDepth left)
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration rightDepth right) := by
  let key := cospan.commonSemanticPatternKeyAt source
  have closeList : ∀ leftChildDepth rightChildDepth childRootDepth
      {leftChildren rightChildren : List Pattern},
      List.Forall₂
          (fun leftChild rightChild =>
            canonicalize declaration leftChild =
              canonicalize declaration rightChild)
          leftChildren rightChildren →
        CommonRestorationApexList source cospan declaration childRootDepth
          (canonicalizeListByAt key declaration leftChildDepth leftChildren)
          (canonicalizeListByAt key declaration rightChildDepth rightChildren) := by
    intro leftChildDepth rightChildDepth childRootDepth leftChildren
      rightChildren children
    rw [canonicalizeListByAt_eq_map, canonicalizeListByAt_eq_map]
    induction children with
    | nil => exact .nil childRootDepth
    | cons related _ inductionHypothesis =>
        exact .cons
          (close leftChildDepth rightChildDepth childRootDepth related)
          inductionHypothesis
  cases aligned with
  | bvar index => exact of_eq cospan declaration rootDepth rfl
  | fvar name => exact of_eq cospan declaration rootDepth rfl
  | @apply constructor ne leftArguments rightArguments children =>
      have quoteStatus := ordinaryHead rfl rfl ne
      have arguments : CommonRestorationApexList source cospan declaration
          (if ReflectiveContextSupport.isQuoteConstructor
              source.costWholeReflectionProfile constructor then 0 else rootDepth)
          (canonicalizeListByAt key declaration leftDepth leftArguments)
          (canonicalizeListByAt key declaration rightDepth rightArguments) := by
        simpa [quoteStatus] using
          closeList leftDepth rightDepth rootDepth children
      simpa [canonicalizeByAt, ne] using
        (CommonRestorationApex.apply constructor arguments)
  | lambda binder body =>
      exact .lambda binder
        (close (leftDepth + 1) (rightDepth + 1) (rootDepth + 1) body)
  | multiLambda arity binders body =>
      exact .multiLambda binders
        (close (leftDepth + arity) (rightDepth + arity)
          (rootDepth + arity) body)
  | subst body replacement =>
      exact .subst
        (close (leftDepth + 1) (rightDepth + 1) (rootDepth + 1) body)
        (close leftDepth rightDepth rootDepth replacement)
  | @collection collectionType ne leftElements rightElements children =>
      have notParallel :
          (collectionType == declaration.parallelCollection) = false :=
        beq_eq_false_iff_ne.mpr ne
      simpa [canonicalizeByAt, notParallel] using
        (CommonRestorationApex.collection collectionType none
          (closeList leftDepth rightDepth rootDepth children))
  | collectionRest collectionType rest children =>
      exact .collection collectionType (some rest)
        (closeList leftDepth rightDepth rootDepth children)

/-- A left Quote/Drop shell contributes no additional restoration evidence:
keyed canonicalization removes it and resets only the payload's quote-visible
depth.  The recursive apex may therefore compare that depth-zero payload with
an endpoint canonicalized at a different visible depth. -/
theorem of_quoteDrop_left
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (quote_ne_drop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    {leftDepth rightDepth rootDepth : Nat} {inner right : Pattern}
    (innerApex : CommonRestorationApex source cospan declaration rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration 0 inner)
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration rightDepth right)) :
    CommonRestorationApex source cospan declaration rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration leftDepth
        (.apply declaration.quoteConstructor
          [.apply declaration.dropConstructor [inner]]))
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration rightDepth right) := by
  simpa only [canonicalizeByAt_quote_drop _ declaration quote_ne_drop] using
    innerApex

/-- Right-oriented companion of `of_quoteDrop_left`. -/
theorem of_quoteDrop_right
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (quote_ne_drop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    {leftDepth rightDepth rootDepth : Nat} {left inner : Pattern}
    (innerApex : CommonRestorationApex source cospan declaration rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration leftDepth left)
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration 0 inner)) :
    CommonRestorationApex source cospan declaration rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration leftDepth left)
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration rightDepth
        (.apply declaration.quoteConstructor
          [.apply declaration.dropConstructor [inner]])) := by
  simpa only [canonicalizeByAt_quote_drop _ declaration quote_ne_drop] using
    innerApex

/-- Equality transports only the indices of a common apex; it adds no
semantic evidence. -/
theorem reindex
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    {depth : Nat} {left right left' right' : Pattern}
    (leftEq : left = left') (rightEq : right = right')
    (apex : CommonRestorationApex source cospan declaration depth left right) :
    CommonRestorationApex source cospan declaration depth left' right' := by
  cases leftEq
  cases rightEq
  exact apex

/-- Positive rigid-leaf canary. -/
theorem bvar_refl
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) (depth index : Nat) :
    CommonRestorationApex source cospan declaration depth
      (.bvar index) (.bvar index) :=
  .leafAligned (.bvar index)

/-- Positive non-reflexive-permutation canary.  Two rigid bound leaves may
occur in opposite parallel orders; the apex records the swap rather than
pretending it is positional alignment. -/
theorem parallel_swap_bvars
    (source : CIGSLT) {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (depth first second : Nat) :
    CommonRestorationApex source cospan declaration depth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration depth
        (.collection declaration.parallelCollection
          [.bvar first, .bvar second] none))
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration depth
        (.collection declaration.parallelCollection
          [.bvar second, .bvar first] none)) := by
  apply CommonRestorationApex.parallel
  simpa [canonicalizeListByAt, canonicalizeByAt, parallelContents,
    parallelSplice,
    ReflectiveContextSupport.substituteAt] using
      (List.Perm.swap (Pattern.bvar second) (Pattern.bvar first) [])

/-- A nested parallel permutation reaches the same spliced frontier on both
sides.  This is the regression for the central construction theorem: the
parallel constructor is indexed by `parallelContents` after recursive keyed
canonicalization, rather than by the raw element lists. -/
theorem parallel_nested_reassociation_bvars
    (source : CIGSLT) {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (depth : Nat) :
    CommonRestorationApex source cospan declaration depth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration depth
        (.collection declaration.parallelCollection
          [.bvar 0,
            .collection declaration.parallelCollection
              [.bvar 1, .bvar 2] none] none))
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration depth
        (.collection declaration.parallelCollection
          [.bvar 2,
            .collection declaration.parallelCollection
              [.bvar 0, .bvar 1] none] none)) := by
  let key := cospan.commonSemanticPatternKeyAt source depth
  have lengthTwelve :
      (normalizeParallelElementsBy key declaration
        [.bvar 1, .bvar 2]).length = 2 := by
    have permutation :=
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key
      [.bvar 1, .bvar 2]
    simpa [normalizeParallelElementsBy, parallelSplice] using
      permutation.length_eq
  have lengthZeroOne :
      (normalizeParallelElementsBy key declaration
        [.bvar 0, .bvar 1]).length = 2 := by
    have permutation :=
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key
      [.bvar 0, .bvar 1]
    simpa [normalizeParallelElementsBy, parallelSplice] using
      permutation.length_eq
  apply CommonRestorationApex.parallel
  simp only [canonicalizeListByAt, canonicalizeByAt]
  rw [show collapseParallel declaration
      (normalizeParallelElementsBy key declaration [.bvar 1, .bvar 2]) =
        .collection declaration.parallelCollection
          (normalizeParallelElementsBy key declaration
            [.bvar 1, .bvar 2]) none by
        exact collapseParallel_eq_collection_of_length_ge_two declaration
          (by omega),
    show collapseParallel declaration
      (normalizeParallelElementsBy key declaration [.bvar 0, .bvar 1]) =
        .collection declaration.parallelCollection
          (normalizeParallelElementsBy key declaration
            [.bvar 0, .bvar 1]) none by
        exact collapseParallel_eq_collection_of_length_ge_two declaration
          (by omega)]
  simp [parallelContents, parallelSplice, key]
  have twelvePermutation : List.Perm
      (normalizeParallelElementsBy key declaration [.bvar 1, .bvar 2])
      [.bvar 1, .bvar 2] := by
    simpa [normalizeParallelElementsBy, parallelSplice] using
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key
        [.bvar 1, .bvar 2])
  have zeroOnePermutation : List.Perm
      (normalizeParallelElementsBy key declaration [.bvar 0, .bvar 1])
      [.bvar 0, .bvar 1] := by
    simpa [normalizeParallelElementsBy, parallelSplice] using
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key
        [.bvar 0, .bvar 1])
  have twelveNoUnit :
      (normalizeParallelElementsBy key declaration
        [.bvar 1, .bvar 2]).filter
          (fun pattern => !decide
            (pattern = .apply declaration.parallelUnitConstructor [])) =
        normalizeParallelElementsBy key declaration [.bvar 1, .bvar 2] := by
    apply List.filter_eq_self.mpr
    intro pattern membership
    have rawMembership := twelvePermutation.mem_iff.mp membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at rawMembership
    rcases rawMembership with rfl | rfl <;> simp
  have zeroOneNoUnit :
      (normalizeParallelElementsBy key declaration
        [.bvar 0, .bvar 1]).filter
          (fun pattern => !decide
            (pattern = .apply declaration.parallelUnitConstructor [])) =
        normalizeParallelElementsBy key declaration [.bvar 0, .bvar 1] := by
    apply List.filter_eq_self.mpr
    intro pattern membership
    have rawMembership := zeroOnePermutation.mem_iff.mp membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at rawMembership
    rcases rawMembership with rfl | rfl <;> simp
  rw [twelveNoUnit, zeroOneNoUnit]
  have restoredTwelve := twelvePermutation.map
    (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
      cospan.commonSupport cospan.commonAssignment depth)
  have restoredZeroOne := zeroOnePermutation.map
    (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
      cospan.commonSupport cospan.commonAssignment depth)
  simp only [ReflectiveContextSupport.substituteAt, List.map_cons,
    List.map_nil] at restoredTwelve restoredZeroOne
  have leftPermutation := List.Perm.cons (Pattern.bvar 0) restoredTwelve
  have rightToRotated := List.Perm.cons (Pattern.bvar 2) restoredZeroOne
  have rotatedToCommon : List.Perm
      [Pattern.bvar 2, Pattern.bvar 0, Pattern.bvar 1]
      [Pattern.bvar 0, Pattern.bvar 1, Pattern.bvar 2] :=
    (List.Perm.swap (Pattern.bvar 0) (Pattern.bvar 2)
      [Pattern.bvar 1]).trans
      (List.Perm.cons (Pattern.bvar 0)
        (List.Perm.swap (Pattern.bvar 1) (Pattern.bvar 2) []))
  simpa only [ReflectiveContextSupport.substituteAt] using
    leftPermutation.trans (rightToRotated.trans rotatedToCommon).symm

/-- Positional leaf alignment cannot express even the flat rigid swap that
the restoration apex admits.  The semantic leaf escape hatch does not help:
restoration leaves bound variables unchanged, so the two lists remain
different. -/
theorem parallel_swap_bvars_not_patternLeafAligned
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (first second : Nat) (different : first ≠ second) :
    ¬ PatternLeafAligned
      (ReflectiveContextSupport.RestoresTogether
        source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment)
      (.collection .hashBag [.bvar first, .bvar second] none)
      (.collection .hashBag [.bvar second, .bvar first] none) := by
  intro aligned
  have atZero :=
    ReflectiveContextSupport.RestoresTogether.PatternLeafAligned.toRestoresTogether
      aligned 0
  simp only [ReflectiveContextSupport.substituteAt,
    List.map_cons, List.map_nil, Pattern.collection.injEq,
    true_and] at atZero
  exact different (Pattern.bvar.inj (List.cons.inj atZero.1).1)

/-- Restoring a keyed canonical frame does not generically commute with the
ordinary canonicalizer unless the assigned opaque values are themselves
canonical for that declaration.  Here the keyed canonicalizer correctly
leaves one atom opaque, restoration reveals a noncanonical Quote/Drop value,
and ordinary canonicalization subsequently contracts it.

This counterexample rules out a tempting shortcut in the static common-apex
proof: recursive canonicality of boundary values must be established before
any fixed-point argument can replace occurrence-aware restoration. -/
theorem substituteAt_canonicalizeByAt_not_commute_without_canonical_assignment
    (source : CIGSLT) (declaration : ReflectivePresentationDecl)
    (different : declaration.dropConstructor ≠
      declaration.quoteConstructor) :
    let support : ContextSupport.Support := fun _ => []
    let assignment : ContextSupport.Assignment :=
      fun _ => Pattern.apply declaration.quoteConstructor
        [Pattern.apply declaration.dropConstructor [Pattern.fvar "payload"]]
    let key : Nat → Pattern → Nat := fun _ pattern =>
      Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
        (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
          support assignment 0 pattern)
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile support
        assignment 0
        (canonicalizeByAt key declaration 0 (.fvar "atom")) ≠
      canonicalize declaration
        (ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile support
          assignment 0 (.fvar "atom")) := by
  dsimp only
  simp only [canonicalizeByAt, ReflectiveContextSupport.substituteAt,
    List.length_nil, Nat.sub_zero,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]
  rw [canonicalize_quote_drop declaration different]
  exact Pattern.noConfusion

/-- Negative rigid-leaf canary: the apex cannot identify distinct bound
indices because neither restoration nor permutation changes a bound leaf. -/
theorem bvar_ne_not
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) (depth leftIndex rightIndex : Nat)
    (different : leftIndex ≠ rightIndex) :
    ¬ CommonRestorationApex source cospan declaration depth
      (.bvar leftIndex) (.bvar rightIndex) := by
  intro apex
  have restored := apex.restored_eq
  have restored' : Pattern.bvar leftIndex = Pattern.bvar rightIndex := by
    simpa only [ReflectiveContextSupport.substituteAt] using restored
  exact different (Pattern.bvar.inj restored')

end CommonRestorationApex

end CostStaticAtomKeyCospan

end Mettapedia.GSLT.LanguageDef
