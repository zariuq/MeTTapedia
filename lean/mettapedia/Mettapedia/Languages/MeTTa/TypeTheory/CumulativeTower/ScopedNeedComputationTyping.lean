import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedComputation
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedComputationTyping
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.TowerConversionSkeleton

/-!
# Formation-sensitive typing with separately scoped need references

Native variables and need references have independent binding disciplines.
A native sequence weakens every available need-result type; a nonrecursive
need binding adds a result-type coordinate without adding a native variable.
The suspended source cannot refer to the handle being allocated.

The independent judgment types raw source code. Its structural laws retain
native formation and exact handle-type coordinates. Emitting an effect does
not change the logical result type, but no effect permission is asserted.
These laws do not establish allocation, caching, forcing, or heap preservation
for a need machine, nor classify native payloads as normalized CBPV values.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedNeedComputation

open ScopedComputation (OperationSignature OperationFormation)

variable {Head Operation Effect : Type} {n m k l : Nat}

/-- A new handle is coordinate zero; previous handle coordinates move up. -/
def extendNeedTypes (type : Tm Head n) (needTypes : Fin k → Tm Head n) :
    Fin (k + 1) → Tm Head n := Fin.cases type needTypes

/-- Native binding shifts native variables inside every available handle type. -/
def weakenNeedTypes (needTypes : Fin k → Tm Head n) :
    Fin k → Tm Head (n + 1) := fun index => rename wk (needTypes index)

theorem substitute_extendNeedTypes (σ : Sub Head n m)
    (type : Tm Head n) (needTypes : Fin k → Tm Head n) :
    (fun index => subst σ (extendNeedTypes type needTypes index)) =
      extendNeedTypes (subst σ type) (fun index => subst σ (needTypes index)) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

theorem substitute_weakenNeedTypes (σ : Sub Head n m)
    (needTypes : Fin k → Tm Head n) :
    (fun index => subst (liftSub σ) (weakenNeedTypes needTypes index)) =
      weakenNeedTypes (fun index => subst σ (needTypes index)) := by
  funext index
  exact subst_liftSub_wk σ (needTypes index)

/-- Every available need reference declares an independently formed native
result type. This does not assert that a heap entry realizes that type. -/
def NeedFormation (R : Rules Head) (Γ : Ctx Head n)
    (needTypes : Fin k → Tm Head n) : Prop :=
  ∀ index, ∃ u, R.isUniverse u ∧ FormationSensitive.Typing R Γ (needTypes index) (.head u)

theorem NeedFormation.substitute {R : Rules Head} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {needTypes : Fin k → Tm Head n} {σ : Sub Head n m}
    (formed : NeedFormation R Γ needTypes)
    (typed : FormationSensitive.CtxMor R Γ Δ σ) :
    NeedFormation R Δ (fun index => subst σ (needTypes index)) := by
  intro index
  obtain ⟨u, universeWitness, formation⟩ := formed index
  exact ⟨u, universeWitness, formation.substitute typed⟩

theorem NeedFormation.extend {R : Rules Head} {Γ : Ctx Head n}
    {needTypes : Fin k → Tm Head n} {A : Tm Head n} {u : Head}
    (formed : NeedFormation R Γ needTypes)
    (formation : FormationSensitive.Typing R Γ A (.head u))
    (universeWitness : R.isUniverse u) :
    NeedFormation R Γ (extendNeedTypes A needTypes) := by
  intro index
  refine Fin.cases ?_ (fun previous => formed previous) index
  exact ⟨u, universeWitness, formation⟩

theorem NeedFormation.weaken {R : Rules Head} {Γ : Ctx Head n}
    {needTypes : Fin k → Tm Head n} (formed : NeedFormation R Γ needTypes)
    (A : Tm Head n) :
    NeedFormation R (.snoc Γ A) (weakenNeedTypes needTypes) := by
  intro index
  obtain ⟨u, universeWitness, formation⟩ := formed index
  exact ⟨u, universeWitness, formation.weaken⟩

/-- Independent typing of the two-sorted scoped computation syntax. -/
inductive Typing (R : Rules Head) (signature : OperationSignature Head Operation) :
    {n k : Nat} → Ctx Head n → (Fin k → Tm Head n) →
      Code Head Operation Effect n k → Tm Head n → Prop where
  | returnValue {n k : Nat} {Γ : Ctx Head n} {needTypes : Fin k → Tm Head n}
      {value A : Tm Head n} :
      FormationSensitive.Typing R Γ value A →
      Typing R signature Γ needTypes (.returnValue value) A
  | sequence {n k : Nat} {Γ : Ctx Head n} {needTypes : Fin k → Tm Head n}
      {A B : Tm Head n} {u v : Head}
      {first : Code Head Operation Effect n k} {body : Code Head Operation Effect (n + 1) k} :
      FormationSensitive.Typing R Γ A (.head u) → R.isUniverse u →
      FormationSensitive.Typing R Γ B (.head v) → R.isUniverse v →
      Typing R signature Γ needTypes first A →
      Typing R signature (.snoc Γ A) (weakenNeedTypes needTypes) body (rename wk B) →
      Typing R signature Γ needTypes (.sequence first body) B
  | sequenceSigma {n k : Nat} {Γ : Ctx Head n} {needTypes : Fin k → Tm Head n}
      {A : Tm Head n} {B : Tm Head (n + 1)} {u : Head}
      {first : Code Head Operation Effect n k} {body : Code Head Operation Effect (n + 1) k} :
      FormationSensitive.Typing R Γ (.sigma A B) (.head u) → R.isUniverse u →
      Typing R signature Γ needTypes first A →
      Typing R signature (.snoc Γ A) (weakenNeedTypes needTypes) body B →
      Typing R signature Γ needTypes (.sequenceSigma first body) (.sigma A B)
  | choose {n k : Nat} {Γ : Ctx Head n} {needTypes : Fin k → Tm Head n}
      {A : Tm Head n} {left right : Code Head Operation Effect n k} :
      Typing R signature Γ needTypes left A → Typing R signature Γ needTypes right A →
      Typing R signature Γ needTypes (.choose left right) A
  | call {n k : Nat} {Γ : Ctx Head n} {needTypes : Fin k → Tm Head n}
      {operation : Operation} {argument : Tm Head n} :
      OperationFormation R signature operation →
      FormationSensitive.Typing R Γ argument (liftClosed (signature.input operation)) →
      Typing R signature Γ needTypes (.call operation argument) (signature.result operation argument)
  | emit {n k : Nat} {Γ : Ctx Head n} {needTypes : Fin k → Tm Head n}
      {effect : Effect} {next : Code Head Operation Effect n k} {A : Tm Head n} :
      Typing R signature Γ needTypes next A →
      Typing R signature Γ needTypes (.emit effect next) A
  | letNeed {n k : Nat} {Γ : Ctx Head n} {needTypes : Fin k → Tm Head n}
      {A B : Tm Head n} {u v : Head}
      {suspended : Code Head Operation Effect n k} {body : Code Head Operation Effect n (k + 1)} :
      FormationSensitive.Typing R Γ A (.head u) → R.isUniverse u →
      FormationSensitive.Typing R Γ B (.head v) → R.isUniverse v →
      Typing R signature Γ needTypes suspended A →
      Typing R signature Γ (extendNeedTypes A needTypes) body B →
      Typing R signature Γ needTypes (.letNeed suspended body) B
  | force {n k : Nat} {Γ : Ctx Head n} {needTypes : Fin k → Tm Head n} (index : Fin k) :
      Typing R signature Γ needTypes (.force index) (needTypes index)
  | conv {n k : Nat} {Γ : Ctx Head n} {needTypes : Fin k → Tm Head n}
      {code : Code Head Operation Effect n k} {A B : Tm Head n} {u : Head} :
      Typing R signature Γ needTypes code A →
      FormationSensitive.Typing R Γ B (.head u) → R.isUniverse u →
      Conv R.headEq A B R.computation → Typing R signature Γ needTypes code B

variable {R : Rules Head} {signature : OperationSignature Head Operation}
  {Γ : Ctx Head n} {Δ : Ctx Head m} {needTypes : Fin k → Tm Head n}

/-- Native substitution changes every declared handle-result type together
with the source payloads, using a lifted substitution only at native binders. -/
theorem Typing.substitute {code : Code Head Operation Effect n k} {A : Tm Head n}
    (typing : Typing R signature Γ needTypes code A) :
    ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head n m},
      FormationSensitive.CtxMor R Γ Δ σ →
      Typing R signature Δ (fun index => subst σ (needTypes index))
        (code.substitute σ) (subst σ A) := by
  induction typing with
  | returnValue admitted =>
      intro m Δ σ typed
      exact .returnValue (admitted.substitute typed)
  | sequence formedA universeA formedB universeB _ _ ihFirst ihBody =>
      intro m Δ σ typed
      apply Typing.sequence (formedA.substitute typed) universeA
        (formedB.substitute typed) universeB (ihFirst typed)
      simpa only [substitute_weakenNeedTypes, subst_liftSub_wk] using ihBody (typed.lift _)
  | sequenceSigma formed universeWitness _ _ ihFirst ihBody =>
      intro m Δ σ typed
      apply Typing.sequenceSigma (formed.substitute typed) universeWitness (ihFirst typed)
      simpa only [substitute_weakenNeedTypes] using ihBody (typed.lift _)
  | choose _ _ ihLeft ihRight =>
      intro m Δ σ typed
      exact .choose (ihLeft typed) (ihRight typed)
  | call declared admitted =>
      intro m Δ σ typed
      have argument := admitted.substitute typed
      rw [subst_liftClosed] at argument
      simpa only [Code.substitute, ScopedComputation.OperationSignature.substitute_result] using
        (Typing.call declared argument)
  | emit _ ih =>
      intro m Δ σ typed
      exact .emit (ih typed)
  | letNeed formedA universeA formedB universeB _ _ ihSuspended ihBody =>
      intro m Δ σ typed
      apply Typing.letNeed (formedA.substitute typed) universeA
        (formedB.substitute typed) universeB (ihSuspended typed)
      simpa only [substitute_extendNeedTypes] using ihBody typed
  | force index =>
      intro m Δ σ typed
      exact .force index
  | conv _ formed universeWitness conversion ih =>
      intro m Δ σ typed
      exact .conv (ih typed) (formed.substitute typed) universeWitness (conversion.substitute σ)

theorem Typing.rename {code : Code Head Operation Effect n k} {A : Tm Head n}
    (typing : Typing R signature Γ needTypes code A) {ρ : Ren n m}
    (compatible : CtxRen Γ Δ ρ) :
    Typing R signature Δ (fun index => rename ρ (needTypes index))
      (code.rename ρ) (rename ρ A) := by
  have typed : FormationSensitive.CtxMor R Γ Δ (renSub ρ) := by
    intro index
    simpa only [renSub, subst_renSub, compatible index] using
      (FormationSensitive.Typing.var (R := R) (Γ := Δ) (ρ index))
  simpa only [Code.substitute_renSub, subst_renSub] using typing.substitute typed

/-- Handle renaming requires exact type-coordinate compatibility. Native
sequence bodies weaken that compatibility; need bodies extend it at zero. -/
theorem Typing.renameHandles {code : Code Head Operation Effect n k} {A : Tm Head n}
    (typing : Typing R signature Γ needTypes code A) :
    ∀ {l : Nat} {targetTypes : Fin l → Tm Head n} {ρ : Fin k → Fin l},
      (∀ index, targetTypes (ρ index) = needTypes index) →
      Typing R signature Γ targetTypes (code.renameHandles ρ) A := by
  induction typing with
  | returnValue admitted =>
      intro l targetTypes ρ compatible
      exact .returnValue admitted
  | sequence formedA universeA formedB universeB _ _ ihFirst ihBody =>
      intro l targetTypes ρ compatible
      apply Typing.sequence formedA universeA formedB universeB (ihFirst compatible)
      apply ihBody
      intro index
      exact congrArg (Presentation.rename wk) (compatible index)
  | sequenceSigma formed universeWitness _ _ ihFirst ihBody =>
      intro l targetTypes ρ compatible
      apply Typing.sequenceSigma formed universeWitness (ihFirst compatible)
      apply ihBody
      intro index
      exact congrArg (Presentation.rename wk) (compatible index)
  | choose _ _ ihLeft ihRight =>
      intro l targetTypes ρ compatible
      exact .choose (ihLeft compatible) (ihRight compatible)
  | call declared admitted =>
      intro l targetTypes ρ compatible
      exact .call declared admitted
  | emit _ ih =>
      intro l targetTypes ρ compatible
      exact .emit (ih compatible)
  | letNeed formedA universeA formedB universeB _ _ ihSuspended ihBody =>
      intro l targetTypes ρ compatible
      apply Typing.letNeed formedA universeA formedB universeB (ihSuspended compatible)
      apply ihBody
      intro index
      exact Fin.cases rfl (fun previous => compatible previous) index
  | force index =>
      intro l targetTypes ρ compatible
      rw [← compatible index]
      exact .force _
  | conv _ formed universeWitness conversion ih =>
      intro l targetTypes ρ compatible
      exact .conv (ih compatible) formed universeWitness conversion

/-- A forced reference can acquire a displayed result type only through
the source judgment's actual conversion rules. -/
theorem Typing.force_conversion {code : Code Head Operation Effect n k} {A : Tm Head n}
    (typing : Typing R signature Γ needTypes code A) :
    ∀ {index : Fin k}, code = .force index →
      Conv R.headEq (needTypes index) A R.computation := by
  induction typing with
  | returnValue => intro index equal; cases equal
  | sequence => intro index equal; cases equal
  | sequenceSigma => intro index equal; cases equal
  | choose => intro index equal; cases equal
  | call => intro index equal; cases equal
  | emit => intro index equal; cases equal
  | letNeed => intro index equal; cases equal
  | force index =>
      intro other equal
      cases equal
      exact .refl _
  | conv _ _ _ conversion ih =>
      intro index equal
      exact .trans _ _ _ (ih equal) conversion

/-- An independently admitted cached result can replay the exact displayed
type adjustments of a typed force, retaining their formation obligations.
The cache admission itself remains an independent premise. -/
theorem Typing.force_replay {code : Code Head Operation Effect n k} {A : Tm Head n}
    (typing : Typing R signature Γ needTypes code A) :
    ∀ {index : Fin k}, code = .force index →
      ∀ {term : Tm Head n}, FormationSensitive.Typing R Γ term (needTypes index) →
        FormationSensitive.Typing R Γ term A := by
  induction typing with
  | returnValue => intro index equal; cases equal
  | sequence => intro index equal; cases equal
  | sequenceSigma => intro index equal; cases equal
  | choose => intro index equal; cases equal
  | call => intro index equal; cases equal
  | emit => intro index equal; cases equal
  | letNeed => intro index equal; cases equal
  | force index =>
      intro other equal term admitted
      cases equal
      exact admitted
  | conv _ formed universeWitness conversion ih =>
      intro index equal term admitted
      exact .conv (ih equal admitted) formed universeWitness conversion

/-- Logical admission keeps both the native telescope and every available
need-result type formed, separately from the source computation typing. -/
structure Judgment (R : Rules Head) (signature : OperationSignature Head Operation)
    (Γ : Ctx Head n) (needTypes : Fin k → Tm Head n)
    (code : Code Head Operation Effect n k) (A : Tm Head n) : Prop where
  context : FormationSensitive.ContextFormation R Γ
  needs : NeedFormation R Γ needTypes
  typing : Typing R signature Γ needTypes code A

theorem Judgment.substitute {code : Code Head Operation Effect n k} {A : Tm Head n}
    (judgment : Judgment R signature Γ needTypes code A) {σ : Sub Head n m}
    (target : FormationSensitive.ContextFormation R Δ)
    (typed : FormationSensitive.CtxMor R Γ Δ σ) :
    Judgment R signature Δ (fun index => subst σ (needTypes index))
      (code.substitute σ) (subst σ A) :=
  ⟨target, judgment.needs.substitute typed, judgment.typing.substitute typed⟩

/-- Newly available handles require their own formation evidence; a
non-surjective renaming cannot provide it for additional target coordinates. -/
theorem Judgment.renameHandles {code : Code Head Operation Effect n k} {A : Tm Head n}
    (judgment : Judgment R signature Γ needTypes code A)
    {targetTypes : Fin l → Tm Head n} {ρ : Fin k → Fin l}
    (target : NeedFormation R Γ targetTypes)
    (compatible : ∀ index, targetTypes (ρ index) = needTypes index) :
    Judgment R signature Γ targetTypes (code.renameHandles ρ) A :=
  ⟨judgment.context, target, judgment.typing.renameHandles compatible⟩

namespace Examples

def ground {n : Nat} : Tower.Tm n := .head .legacyGround

def operationSignature : OperationSignature Tower.Head Empty where
  input operation := nomatch operation
  output operation := nomatch operation

def context : Tower.Ctx 1 := .snoc .nil ground

def noNeeds : Fin 0 → Tower.Tm 1 := Fin.elim0

def identityFamily : Tower.Tm 2 := .id ground (.var 0) (.var 0)

theorem sigma_formed :
    FormationSensitive.Typing Tower.rules context (.sigma ground identityFamily)
      (sortTm (.max Tower.zero Tower.zero)) :=
  .sigmaForm (.headType .legacyGround) (.sort Tower.zero)
    (.idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0))
    (.sort Tower.zero) (.sorts Tower.zero Tower.zero)

/-- The second force is below a native binder. It still refers to the same
need coordinate, while the returned reflexivity uses the first selected
native value at de Bruijn index one. -/
def boundBody : Code Tower.Head Empty Bool 1 1 :=
  .sequenceSigma (.force 0)
    (.sequence (.force 0) (.returnValue (.refl (.var 1))))

def source : Code Tower.Head Empty Bool 1 0 :=
  .letNeed (.emit true (.returnValue (.var 0))) boundBody

theorem boundBody_typing :
    Typing Tower.rules operationSignature context (extendNeedTypes ground noNeeds)
      boundBody (.sigma ground identityFamily) := by
  apply Typing.sequenceSigma sigma_formed (.sort _) (.force 0)
  apply Typing.sequence (A := ground) (B := identityFamily)
  · exact .headType .legacyGround
  · exact .sort Tower.zero
  · exact .idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0)
  · exact .sort Tower.zero
  · exact .force 0
  · exact .returnValue (.reflIntro (.var 1))

theorem source_typing :
    Typing Tower.rules operationSignature context noNeeds source (.sigma ground identityFamily) :=
  .letNeed (.headType .legacyGround) (.sort Tower.zero) sigma_formed (.sort _)
    (.emit (.returnValue (.var 0))) boundBody_typing

theorem source_judgment :
    Judgment Tower.rules operationSignature context noNeeds source (.sigma ground identityFamily) :=
  ⟨.snoc .nil (.headType .legacyGround) (.sort Tower.zero),
    (fun index => Fin.elim0 index), source_typing⟩

def firstTypes : Fin 1 → Tower.Tm 1 := fun _ => ground

/-- Both target handle types are genuine native types, but their coordinates
are intentionally different from the source coordinate. -/
def secondTypes : Fin 2 → Tower.Tm 1 :=
  Fin.cases (.pi ground ground) (fun _ => ground)

theorem secondTypes_formed : NeedFormation Tower.rules context secondTypes := by
  intro index
  refine Fin.cases ?_ ?_ index
  · exact ⟨.sort (.max Tower.zero Tower.zero), .sort _,
      .piForm (.headType .legacyGround) (.sort Tower.zero)
        (.headType .legacyGround) (.sort Tower.zero) (.sorts Tower.zero Tower.zero)⟩
  · intro prior
    exact ⟨.sort Tower.zero, .sort _, .headType .legacyGround⟩

theorem correctly_renamed_force :
    Typing Tower.rules operationSignature context secondTypes
      (.force 1 : Code Tower.Head Empty Bool 1 2) ground := by
  have original : Typing Tower.rules operationSignature context firstTypes
      (.force 0 : Code Tower.Head Empty Bool 1 1) ground := .force 0
  exact original.renameHandles (ρ := fun _ => 1) (fun _ => rfl)

/-- Merely reusing coordinate zero fails the actual computation typing,
including its conversion tails, despite formation of both target types. -/
theorem incorrect_handle_not_admitted :
    ¬ Typing Tower.rules operationSignature context secondTypes
      (.force 0 : Code Tower.Head Empty Bool 1 2) ground := by
  intro typing
  exact TowerConversionSkeleton.not_conv_pi_head ground ground .legacyGround
    (typing.force_conversion rfl)

#print axioms source_judgment
#print axioms secondTypes_formed
#print axioms correctly_renamed_force
#print axioms incorrect_handle_not_admitted

end Examples


#print axioms NeedFormation.substitute
#print axioms NeedFormation.extend
#print axioms NeedFormation.weaken
#print axioms Typing.substitute
#print axioms Typing.rename
#print axioms Typing.renameHandles
#print axioms Typing.force_conversion
#print axioms Typing.force_replay
#print axioms Judgment.substitute
#print axioms Judgment.renameHandles

end ScopedNeedComputation
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
