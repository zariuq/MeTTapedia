import Mettapedia.GSLT.Dedukti.Separation

/-!
# Four kinds of translation, kept apart

Translations between theories of the λΠ-calculus modulo are of at least four
kinds.  They are stated here in one vocabulary, each with a small worked
instance and with the property that tells it from the others.

1. **Structural theory morphism**: an interpretation of constants by closed
   terms, extended by a fold (`Interpretation`).  It is total and
   compositional.  Its two obligations are the typing of the images of the
   constants and the conversion of the images of the rules.  Instance:
   unfolding a defined function into its definition (`unfoldDouble`).  The
   image of a rule is a conversion of the target that need not be a rule: here
   it is a beta step.  A wrong definition meets the typing obligation and
   fails the rule obligation (`wrongDouble_typed`, `wrongDouble_not_respects`):
   checking the images of the constants does not check the rules.

2. **Weakening of the foundation**: the inclusion of a weak system in a strong
   one is a morphism (`Derives.mono`); there is no morphism back, since some
   judgments of the strong system are not judgments of the weak one
   (`no_retraction`).  A proof moves to the weak system when it is itself a
   proof of the weak system, which is checked proof by proof
   (`identity_in_both`, `polymorphicIdentity_only_strong`).

3. **Library alignment**: a renaming of constants onto constants that the
   target library already has, with its own computation rules.  The typing
   obligation holds (`align_typed`); the rule obligation fails, because the
   target computes differently (`align_rule_not_joinable`,
   `align_not_respects`).  The aligned equations are theorems of the target,
   so the image of a conversion is a proved equation, to be applied by
   transport.

4. **Explicit transport of a conversion**: the source has a rule that the
   target lacks; where a source derivation uses it, the translation inserts a
   transport.  The translation depends on the derivation, not on the term:
   one source term has two types and two translations
   (`source_two_types`, `target_cast_typed`, `target_untyped_without_cast`).
   No structural morphism that keeps the types fixed exists
   (`no_structural_translation`).  In the other direction, erasing the
   transport is a structural morphism (`eraseCast_respects`, `eraseCast_typed`)
   and a left inverse up to beta (`eraseCast_cast`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.Phenomena

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig Decl sigT lookupType lookupBody lift subst subst0 Ctx)
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-- A constant with a declared type is declared in the signature. -/
theorem lookupType_mem {signature : Sig} {name : String} {type : Term}
    (found : lookupType signature name = some type) :
    Decl.const name type ∈ signature ∨ ∃ body, Decl.defn name type body ∈ signature := by
  induction signature with
  | nil => simp [lookupType] at found
  | cons head tail ih =>
      cases head with
      | const other otherType =>
          simp only [lookupType] at found
          split at found
          · rename_i same
            cases found
            exact Or.inl (same ▸ List.mem_cons_self)
          · rcases ih found with member | ⟨body, member⟩
            · exact Or.inl (List.mem_cons_of_mem _ member)
            · exact Or.inr ⟨body, List.mem_cons_of_mem _ member⟩
      | defn other otherType otherBody =>
          simp only [lookupType] at found
          split at found
          · rename_i same
            cases found
            exact Or.inr ⟨otherBody, same ▸ List.mem_cons_self⟩
          · rcases ih found with member | ⟨body, member⟩
            · exact Or.inl (List.mem_cons_of_mem _ member)
            · exact Or.inr ⟨body, List.mem_cons_of_mem _ member⟩

/-! ## 1. A structural theory morphism -/

/-- The type of unary numbers. -/
def nat : Term := .con "nat"

def zero : Term := .con "z"

def succ (term : Term) : Term := .app (.con "s") term

def plus (left right : Term) : Term := .app (.app (.con "plus") left) right

/-- Unary numbers with addition by recursion on the first argument. -/
def unarySig : Sig :=
  [.const "nat" (.srt .type), .const "z" nat, .const "s" (.pi nat nat),
    .const "plus" (.pi nat (.pi nat nat))]

/-- `plus z y ⟶ y`. -/
def plusZero : RewriteRule := ⟨plus zero (.var 0), .var 0⟩

/-- `plus (s x) y ⟶ s (plus x y)`. -/
def plusSucc : RewriteRule := ⟨plus (succ (.var 1)) (.var 0), succ (plus (.var 1) (.var 0))⟩

def unary : Theory := Theory.ofSig unarySig [plusZero, plusSucc]

/-- The same with a doubling function, declared with the rule
`double x ⟶ plus x x`. -/
def doubleSig : Sig := unarySig ++ [.const "double" (.pi nat nat)]

def doubleRule : RewriteRule := ⟨.app (.con "double") (.var 0), plus (.var 0) (.var 0)⟩

def withDouble : Theory := Theory.ofSig doubleSig [plusZero, plusSucc, doubleRule]

/-- The definition of doubling: `λ x : nat. plus x x`. -/
def doubleBody : Term := .lam nat (plus (.var 0) (.var 0))

/-- **Unfolding the doubling function**: every other constant is kept. -/
def unfoldDouble : Interpretation where
  meaning := fun name => if name = "double" then doubleBody else .con name
  closed := fun name => by
    split
    · exact .lam .con (.app (.app .con (.var (by omega))) (.var (by omega)))
    · exact .con

def unaryCover : (unary).Cover :=
  Theory.coverOfRules unarySig [plusZero, plusSucc] fun name => by
    simp [unarySig, lookupBody]

theorem type_nat (context : Ctx) : LambdaPiModulo unary context nat (.srt .type) := .con rfl

/-- The definition has the declared type of the function it defines, in every
context. -/
theorem doubleBody_typed (context : Ctx) : LambdaPiModulo unary context doubleBody (.pi nat nat) := by
  have plusTyped : LambdaPiModulo unary (nat :: context) (.con "plus") (.pi nat (.pi nat nat)) :=
    .con rfl
  have argument : LambdaPiModulo unary (nat :: context) (.var 0) nat := .var rfl
  exact .lam (type_nat _) (type_nat _) arrow_rule (.app (.app plusTyped argument) argument)

/-- The obligation on rules holds: the image of the rule for doubling is a
beta step of the target, and the two rules of addition are kept. -/
theorem unfoldDouble_respects : unfoldDouble.Respects withDouble unary where
  body := fun name term defined => by
    have undefined : lookupBody doubleSig name = none := by simp [doubleSig, unarySig, lookupBody]
    exact absurd (undefined.symm.trans defined) (by simp)
  rule := fun rule member assignment => by
    have cases : rule = plusZero ∨ rule = plusSucc ∨ rule = doubleRule := by
      simpa [withDouble, Theory.ofSig] using member
    rw [unfoldDouble.apply_instantiate, unfoldDouble.apply_instantiate]
    rcases cases with rfl | rfl | rfl
    · have kept : unfoldDouble.apply plusZero.lhs = plusZero.lhs := by decide
      have keptRight : unfoldDouble.apply plusZero.rhs = plusZero.rhs := by decide
      rw [kept, keptRight]
      exact Conv.rule (theory := unary) (rule := plusZero) (by simp [unary, Theory.ofSig]) _
    · have kept : unfoldDouble.apply plusSucc.lhs = plusSucc.lhs := by decide
      have keptRight : unfoldDouble.apply plusSucc.rhs = plusSucc.rhs := by decide
      rw [kept, keptRight]
      exact Conv.rule (theory := unary) (rule := plusSucc) (by simp [unary, Theory.ofSig]) _
    · have left : unfoldDouble.apply doubleRule.lhs = .app doubleBody (.var 0) := by decide
      have right : unfoldDouble.apply doubleRule.rhs = plus (.var 0) (.var 0) := by decide
      rw [left, right]
      have beta := Conv.beta (theory := unary) nat (plus (.var 0) (.var 0))
        (unfoldDouble.apply (assignment 0))
      simpa [doubleBody, plus, nat, inst, instantiate, lift_zero, subst0, subst] using beta

/-- The obligation on constants holds. -/
theorem unfoldDouble_typed : unfoldDouble.Typed LFProfile.basic withDouble unary where
  constType := fun name type declared context => by
    rcases lookupType_mem declared with member | ⟨_, member⟩
    · simp only [doubleSig, unarySig, List.cons_append, List.nil_append, List.mem_cons,
        Decl.const.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .con rfl
      · exact .con rfl
      · exact .con rfl
      · exact .con rfl
      · exact doubleBody_typed _
    · simp [doubleSig, unarySig] at member

/-- **Positive**: the unfolding preserves typing and conversion. -/
theorem unfoldDouble_hasType {context : Ctx} {term type : Term}
    (typed : LambdaPiModulo withDouble context term type) :
    LambdaPiModulo unary (context.map unfoldDouble.apply) (unfoldDouble.apply term)
      (unfoldDouble.apply type) :=
  unfoldDouble_respects.hasType unfoldDouble_typed typed

/-- A wrong definition of doubling: the identity. -/
def wrongDouble : Interpretation where
  meaning := fun name => if name = "double" then .lam nat (.var 0) else .con name
  closed := fun name => by
    split
    · exact .lam .con (.var (by omega))
    · exact .con

/-- The wrong definition has the declared type: the obligation on constants
does not see the mistake. -/
theorem wrongDouble_typed : wrongDouble.Typed LFProfile.basic withDouble unary where
  constType := fun name type declared context => by
    rcases lookupType_mem declared with member | ⟨_, member⟩
    · simp only [doubleSig, unarySig, List.cons_append, List.nil_append, List.mem_cons,
        Decl.const.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .con rfl
      · exact .con rfl
      · exact .con rfl
      · exact .con rfl
      · exact .lam (type_nat _) (type_nat _) arrow_rule (.var rfl)
    · simp [doubleSig, unarySig] at member

/-- **Negative, where confluence is used**: the wrong definition fails the
obligation on rules.  At the argument `s z` the two sides of the rule have the
normal forms `s z` and `s (s z)`. -/
theorem wrongDouble_not_respects (confluent : Confluent (Step unary)) :
    ¬ wrongDouble.Respects withDouble unary := by
  intro respects
  have image := respects.rule doubleRule (by simp [withDouble, Theory.ofSig])
    (fun _ => succ zero)
  have left : wrongDouble.apply (inst (fun _ => succ zero) doubleRule.lhs) =
      .app (.lam nat (.var 0)) (succ zero) := by decide
  have right : wrongDouble.apply (inst (fun _ => succ zero) doubleRule.rhs) =
      plus (succ zero) (succ zero) := by decide
  rw [left, right] at image
  have leftReduces : Conv unary (.app (.lam nat (.var 0)) (succ zero)) (succ zero) :=
    Conv.beta nat (.var 0) (succ zero)
  have firstStep : Conv unary (plus (succ zero) (succ zero)) (succ (plus zero (succ zero))) := by
    have instance_ := Conv.rule (theory := unary) (rule := plusSucc) (by simp [unary, Theory.ofSig])
      fun index => if index = 0 then succ zero else zero
    simpa [plusSucc, plus, succ, inst, instantiate, lift_zero] using instance_
  have secondStep : Conv unary (succ (plus zero (succ zero))) (succ (succ zero)) := by
    have instance_ := Conv.rule (theory := unary) (rule := plusZero) (by simp [unary, Theory.ofSig])
      fun _ => succ zero
    have inner : Conv unary (plus zero (succ zero)) (succ zero) := by
      simpa [plusZero, plus, zero, inst, instantiate, lift_zero] using instance_
    exact Conv.app (.refl _) inner
  have collapsed : Conv unary (succ zero) (succ (succ zero)) :=
    .trans _ _ _ (.symm _ _ leftReduces) (.trans _ _ _ image (.trans _ _ _ firstStep secondStep))
  exact not_conv_of_normal confluent
    (normal_of_normalTest unaryCover (succ zero) (by decide))
    (normal_of_normalTest unaryCover (succ (succ zero)) (by decide)) (by decide) collapsed

/-! ## 2. Weakening of the foundation -/

/-- **The inclusion of a weak system in a strong one**: every derivation of
the weak system is a derivation of the strong one. -/
theorem Derives.mono {weak strong : Profile} (included : LFProfile.Subsumed weak strong)
    {context : SortedCtx} {judgment : Judgment} (derivation : Derives weak context judgment) :
    Derives strong context judgment := by
  induction derivation with
  | sort axiomHolds => exact .sort (included.1 _ _ axiomHolds)
  | pi _ _ member ihDomain ihBody => exact .pi ihDomain ihBody (included.2 _ member)
  | ofTerm _ axiomHolds ih => exact .ofTerm ih (included.1 _ _ axiomHolds)
  | toTerm _ axiomHolds ih => exact .toTerm ih (included.1 _ _ axiomHolds)
  | var found => exact .var found
  | lam _ _ member _ ihDomain ihBodyType ihBody =>
      exact .lam ihDomain ihBodyType (included.2 _ member) ihBody
  | app _ _ member _ _ ihDomain ihBodyType ihFunction ihArgument =>
      exact .app ihDomain ihBodyType (included.2 _ member) ihFunction ihArgument
  | conv _ convertible _ ihTerm ihTarget => exact .conv ihTerm convertible ihTarget

theorem simplyTyped_subsumed : LFProfile.Subsumed simplyTyped constructions :=
  ⟨fun _ _ same => same, fun rule member => by
    have same : rule = LFProfile.typeTypeType := List.mem_singleton.mp member
    rw [same]
    decide⟩

/-- The identity on a type variable: `λ x : X. x` of type `X → X`, for a
variable `X : Type` of the context. -/
def identityOnVariable : PTerm := .lam .type (.var 0) (.var 0)

def identityOnVariableType : PTerm := .pi LFProfile.typeTypeType (.var 0) (.var 1)

/-- **A proof of the strong system that is a proof of the weak one**: it uses
the one rule that both have. -/
theorem identity_in_both :
    Derives simplyTyped [(.sort .type, .kind)]
        (.term identityOnVariable identityOnVariableType .type) ∧
      Derives constructions [(.sort .type, .kind)]
        (.term identityOnVariable identityOnVariableType .type) := by
  have weak : Derives simplyTyped [(.sort .type, .kind)]
      (.term identityOnVariable identityOnVariableType .type) :=
    .lam (.ofTerm (.var rfl) rfl) (.ofTerm (.var rfl) rfl) (by decide) (.var rfl)
  exact ⟨weak, Derives.mono simplyTyped_subsumed weak⟩

/-- **A proof of the strong system that is not one of the weak**: the
polymorphic identity. -/
theorem polymorphicIdentity_only_strong :
    Derives constructions [] (.term Example.polymorphicIdentity Example.polymorphicIdentityType .type) ∧
      ∀ (context : SortedCtx) (sort : Srt),
        ¬ Derives simplyTyped context (.type Example.polymorphicIdentityType sort) :=
  ⟨Example.polymorphicIdentity_typed, Example.polymorphicIdentityType_not_simplyTyped⟩

/-- **There is no way back that keeps the judgment**: the strong system
derives a judgment that the weak one does not. -/
theorem no_retraction :
    ¬ ∀ (context : SortedCtx) (judgment : Judgment),
      Derives constructions context judgment → Derives simplyTyped context judgment := by
  intro retract
  have formed : Derives constructions [] (.type Example.polymorphicIdentityType .type) :=
    .pi (.sort rfl)
      (.pi Example.variable_is_type Example.outer_variable_is_type (by decide)) (by decide)
  exact Example.polymorphicIdentityType_not_simplyTyped [] .type (retract _ _ formed)

/-! ## 3. Library alignment -/

/-- A library whose addition recurses on its second argument. -/
def rightSig : Sig :=
  [.const "nat" (.srt .type), .const "z" nat, .const "s" (.pi nat nat),
    .const "add" (.pi nat (.pi nat nat))]

def add (left right : Term) : Term := .app (.app (.con "add") left) right

/-- `add x z ⟶ x`. -/
def addZero : RewriteRule := ⟨add (.var 0) zero, .var 0⟩

/-- `add x (s y) ⟶ s (add x y)`. -/
def addSucc : RewriteRule := ⟨add (.var 1) (succ (.var 0)), succ (add (.var 1) (.var 0))⟩

def rightLibrary : Theory := Theory.ofSig rightSig [addZero, addSucc]

/-- **The alignment**: the addition of the source is the addition of the
target library. -/
def align : Interpretation where
  meaning := fun name => if name = "plus" then .con "add" else .con name
  closed := fun name => by split <;> exact .con

/-- The signatures align: the obligation on constants holds. -/
theorem align_typed : align.Typed LFProfile.basic unary rightLibrary where
  constType := fun name type declared context => by
    rcases lookupType_mem declared with member | ⟨_, member⟩
    · simp only [unarySig, List.mem_cons, Decl.const.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .con rfl
      · exact .con rfl
      · exact .con rfl
      · exact .con rfl
    · simp [unarySig] at member

def rightLibraryCover : (rightLibrary).Cover :=
  Theory.coverOfRules rightSig [addZero, addSucc] fun name => by
    simp [rightSig, lookupBody]

/-- **The computation rules do not align**: the image of `plus z y ⟶ y` at a
variable relates two distinct normal terms of the target. -/
theorem align_rule_not_joinable :
    ¬ Joinable rightLibrary (align.apply (inst (fun index => .var index) plusZero.lhs))
      (align.apply (inst (fun index => .var index) plusZero.rhs)) := by
  have left : align.apply (inst (fun index => .var index) plusZero.lhs) = add zero (.var 0) := by
    decide
  have right : align.apply (inst (fun index => .var index) plusZero.rhs) = .var 0 := by decide
  rw [left, right]
  exact not_joinable_of_normal
    (normal_of_normalTest rightLibraryCover (add zero (.var 0)) (by decide))
    (normal_of_normalTest rightLibraryCover (.var 0) (by decide)) (by decide)

/-- **Where confluence is used**: the alignment is not a structural
morphism. -/
theorem align_not_respects (confluent : Confluent (Step rightLibrary)) :
    ¬ align.Respects unary rightLibrary := by
  intro respects
  have image := respects.rule plusZero (by simp [unary, Theory.ofSig]) fun index => .var index
  exact align_rule_not_joinable ((conv_iff_joinable confluent).mp image)

/-! ## 4. Explicit transport of a conversion -/

def typeA : Term := .con "A"

def typeB : Term := .con "B"

/-- The source: two types, an element of the first, and the rule `A ⟶ B`. -/
def silentSig : Sig := [.const "A" (.srt .type), .const "B" (.srt .type), .const "a" typeA]

def unfoldA : RewriteRule := ⟨typeA, typeB⟩

def silent : Theory := Theory.ofSig silentSig [unfoldA]

/-- The target: the same constants, no rule, and a transport from `A` to `B`. -/
def explicitSig : Sig := silentSig ++ [.const "cast" (.pi typeA typeB)]

def explicit : Theory := Theory.ofSig explicitSig []

theorem conv_A_B : Conv silent typeA typeB :=
  Conv.rule (theory := silent) (rule := unfoldA) (List.mem_singleton.mpr rfl) fun _ => .srt .type

/-- **In the source one term has two types**: the conversion leaves no
trace. -/
theorem source_two_types :
    LambdaPiModulo silent [] (.con "a") typeA ∧ LambdaPiModulo silent [] (.con "a") typeB :=
  ⟨.con rfl, .conv (.con rfl) conv_A_B (.con rfl)⟩

/-- In the target the element has its declared type, and the transported
element has the other. -/
theorem target_cast_typed :
    LambdaPiModulo explicit [] (.con "a") typeA ∧
      LambdaPiModulo explicit [] (.app (.con "cast") (.con "a")) typeB := by
  have transport : LambdaPiModulo explicit [] (.con "cast") (.pi typeA typeB) := .con rfl
  have element : LambdaPiModulo explicit [] (.con "a") typeA := .con rfl
  exact ⟨element, .app transport element⟩

def explicitCover : (explicit).Cover :=
  Theory.coverOfRules explicitSig [] fun name => by simp [explicitSig, silentSig, lookupBody]

theorem explicit_A_ne_B (confluent : Confluent (Step explicit)) : ¬ Conv explicit typeA typeB :=
  not_conv_of_normal confluent (normal_of_normalTest explicitCover typeA (by decide))
    (normal_of_normalTest explicitCover typeB (by decide)) (by decide)

/-- **Negative, where confluence is used**: without the transport the element
does not have the second type in the target. -/
theorem target_untyped_without_cast (confluent : Confluent (Step explicit)) {profile : Profile} :
    ¬ HasType profile explicit [] (.con "a") typeB := by
  intro typed
  obtain ⟨declared, found, convertible⟩ := typed.con_inv
  have same : declared = typeA := by
    have computed : explicit.constType "a" = some typeA := rfl
    exact Option.some.inj (found.symm.trans computed)
  rw [same] at convertible
  exact explicit_A_ne_B confluent convertible

/-- **No structural morphism keeps the two types fixed**, under confluence of
the target: the rule `A ⟶ B` would have to be a conversion there. -/
theorem no_structural_translation (confluent : Confluent (Step explicit))
    (interpretation : Interpretation) (keepsA : interpretation.meaning "A" = typeA)
    (keepsB : interpretation.meaning "B" = typeB) : ¬ interpretation.Respects silent explicit := by
  intro respects
  have image := respects.rule unfoldA (List.mem_singleton.mpr rfl) fun _ => .srt .type
  have left : interpretation.apply (inst (fun _ => .srt .type) unfoldA.lhs) = typeA := keepsA
  have right : interpretation.apply (inst (fun _ => .srt .type) unfoldA.rhs) = typeB := keepsB
  rw [left, right] at image
  exact explicit_A_ne_B confluent image

/-- **Erasing the transport**: the transport is the identity function. -/
def eraseCast : Interpretation where
  meaning := fun name => if name = "cast" then .lam typeA (.var 0) else .con name
  closed := fun name => by
    split
    · exact .lam .con (.var (by omega))
    · exact .con

/-- Erasing the transport meets the obligation on rules: the target of the
erasure has every conversion that the explicit theory has. -/
theorem eraseCast_respects : eraseCast.Respects explicit silent where
  body := fun name term defined => by
    have undefined : lookupBody explicitSig name = none := by
      simp [explicitSig, silentSig, lookupBody]
    exact absurd (undefined.symm.trans defined) (by simp)
  rule := fun _ member _ => absurd member List.not_mem_nil

/-- It meets the obligation on constants: the identity has type `A → B` in
the source, by the rule. -/
theorem eraseCast_typed : eraseCast.Typed LFProfile.basic explicit silent where
  constType := fun name type declared context => by
    rcases lookupType_mem declared with member | ⟨_, member⟩
    · simp only [explicitSig, silentSig, List.cons_append, List.nil_append, List.mem_cons,
        Decl.const.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .con rfl
      · exact .con rfl
      · exact .con rfl
      · have typeOfA : ∀ extra : Ctx, LambdaPiModulo silent extra typeA (.srt .type) :=
          fun _ => .con rfl
        have typeOfB : ∀ extra : Ctx, LambdaPiModulo silent extra typeB (.srt .type) :=
          fun _ => .con rfl
        have identity : LambdaPiModulo silent (context.map eraseCast.apply) (.lam typeA (.var 0))
            (.pi typeA typeA) :=
          .lam (typeOfA _) (typeOfA _) arrow_rule (.var rfl)
        exact .conv identity (Conv.pi (.refl _) conv_A_B) (.pi (typeOfA _) (typeOfB _) arrow_rule)
    · simp [explicitSig, silentSig] at member

/-- **Erasing the transport of the transported element gives the element**, up
to beta. -/
theorem eraseCast_cast :
    Conv silent (eraseCast.apply (.app (.con "cast") (.con "a"))) (.con "a") :=
  Conv.beta typeA (.var 0) (.con "a")

#print axioms unfoldDouble_respects
#print axioms unfoldDouble_typed
#print axioms unfoldDouble_hasType
#print axioms wrongDouble_typed
#print axioms wrongDouble_not_respects
#print axioms Derives.mono
#print axioms no_retraction
#print axioms align_typed
#print axioms align_rule_not_joinable
#print axioms align_not_respects
#print axioms source_two_types
#print axioms target_untyped_without_cast
#print axioms no_structural_translation
#print axioms eraseCast_respects
#print axioms eraseCast_typed

end Mettapedia.GSLT.Dedukti.Phenomena
