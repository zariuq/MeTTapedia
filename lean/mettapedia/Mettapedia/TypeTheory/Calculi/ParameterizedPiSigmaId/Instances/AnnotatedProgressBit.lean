import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.CoreHeadReduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationForms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Progress
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Soundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.ChurchInterp
import Mettapedia.TypeTheory.UniverseLevel.Order

/-!
# Progress for a two-point type with negation

An inductive type `bit`, constructors `tt` and `ff`, and a computing constant
`not` of one argument. The root steps are `not tt ↦ ff` and `not ff ↦ tt`.
Every progress obligation holds, including a root step at each canonical
scrutinee, so a type of a universe progresses. The application `not tt` takes
that root step, and its erasure is not a weak-head normal form.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated
namespace ProgressBit

open Impredicative.Domain
open Normalization
open Progress (ScrutineeCanonical ScrutineeDecl)
open UniverseLevel (LevelOrder)

def bitName : DeclName := `bit
def ttName : DeclName := `tt
def ffName : DeclName := `ff
def notName : DeclName := `not
def propName : DeclName := `prop
def holdsName : DeclName := `holds
def numName : DeclName := `numB
def zeroName : DeclName := `zeroB
def sucName : DeclName := `sucB

def bitHeadTyping (n m : Nat) : Prop := m = n + 1

def bitConstType : DeclName → Option (Tm Nat 0)
  | name =>
    if name = bitName then some (.head 0)
    else if name = ttName then some (.const bitName)
    else if name = ffName then some (.const bitName)
    else if name = notName then some (.pi (.const bitName) (.const bitName))
    else if name = propName then some (.head 1)
    else if name = holdsName then some (.pi (.const propName) (.head 0))
    else none

inductive NotStepE {n : Nat} : Tm Nat n → Tm Nat n → Prop where
  | tt : NotStepE (.app (.const notName) (.const ttName)) (.const ffName)
  | ff : NotStepE (.app (.const notName) (.const ffName)) (.const ttName)

def bitComputationE : RootComputation Nat where
  step := NotStepE
  rename := fun {_ _} _ {_ _} h => by
    cases h with
    | tt => exact .tt
    | ff => exact .ff
  substitute := fun {_ _} _ {_ _} h => by
    cases h with
    | tt => exact .tt
    | ff => exact .ff

def bitRules : Rules Nat where
  headTyping := bitHeadTyping
  isUniverse := fun _ => True
  join := fun n m k => k = max n m
  cumulative := fun n m => n ≤ m
  headEq := fun n m => n = m
  constantType := bitConstType
  computation := bitComputationE

def bitConstTypeA : DeclName → Option (CTm Nat 0)
  | name =>
    if name = bitName then some (.head 0)
    else if name = ttName then some (.const bitName)
    else if name = ffName then some (.const bitName)
    else if name = notName then some (.pi (.const bitName) (.const bitName))
    else if name = propName then some (.head 1)
    else if name = holdsName then some (.pi (.const propName) (.head 0))
    else none

inductive NotStep {n : Nat} : CTm Nat n → CTm Nat n → Prop where
  | tt : NotStep (.app (.const notName) (.const ttName)) (.const ffName)
  | ff : NotStep (.app (.const notName) (.const ffName)) (.const ttName)

def bitComputation : CRootComputation Nat where
  step := NotStep
  rename := fun {_ _} _ {_ _} h => by
    cases h with
    | tt => exact .tt
    | ff => exact .ff
  substitute := fun {_ _} _ {_ _} h => by
    cases h with
    | tt => exact .tt
    | ff => exact .ff

def bitChurch : ChurchRules bitRules where
  constantType := bitConstTypeA
  computation := bitComputation
  erase_constantType := fun name => by
    by_cases hb : name = bitName
    · subst hb; rfl
    by_cases ht : name = ttName
    · subst ht; rfl
    by_cases hf : name = ffName
    · subst hf; rfl
    by_cases hn : name = notName
    · subst hn; rfl
    by_cases hp : name = propName
    · subst hp; rfl
    by_cases hh : name = holdsName
    · subst hh; rfl
    simp only [bitRules, bitConstType, bitConstTypeA, hb, ht, hf, hn, hp, hh, if_false,
      Option.map_none]
  erase_step := fun {_ _ _} h => by
    cases h with
    | tt => exact .tt
    | ff => exact .ff

def bitRoles : Roles Nat := fun name =>
  if name = bitName then .inductive [(ttName, ([] : List (Field Nat))), (ffName, [])]
  else if name = ttName then .constructor 0
  else if name = ffName then .constructor 0
  else if name = notName then .computes 1 (.split 0 .constructor fun _ => .leaf)
  else .rigid

theorem bitRoles_bit : bitRoles bitName = .inductive [(ttName, []), (ffName, [])] := by
  rw [bitRoles, if_pos rfl]

theorem bitRoles_tt : bitRoles ttName = .constructor 0 := by
  have hb : ttName ≠ bitName := by decide
  rw [bitRoles, if_neg hb, if_pos rfl]

theorem bitRoles_ff : bitRoles ffName = .constructor 0 := by
  have hb : ffName ≠ bitName := by decide
  have ht : ffName ≠ ttName := by decide
  rw [bitRoles, if_neg hb, if_neg ht, if_pos rfl]

theorem bitRoles_not :
    bitRoles notName = .computes 1 (.split 0 .constructor fun _ => .leaf) := by
  have hb : notName ≠ bitName := by decide
  have ht : notName ≠ ttName := by decide
  have hf : notName ≠ ffName := by decide
  rw [bitRoles, if_neg hb, if_neg ht, if_neg hf, if_pos rfl]

theorem bitRoles_rigid {c : DeclName} (hb : c ≠ bitName) (ht : c ≠ ttName) (hf : c ≠ ffName)
    (hn : c ≠ notName) : bitRoles c = .rigid := by
  rw [bitRoles, if_neg hb, if_neg ht, if_neg hf, if_neg hn]

theorem declared_bit : bitChurch.constantType bitName = some (.head 0) := by
  change bitConstTypeA bitName = some (.head 0)
  rw [bitConstTypeA, if_pos rfl]

theorem declared_tt : bitChurch.constantType ttName = some (.const bitName) := by
  have hb : ttName ≠ bitName := by decide
  change bitConstTypeA ttName = some (.const bitName)
  rw [bitConstTypeA, if_neg hb, if_pos rfl]

theorem declared_ff : bitChurch.constantType ffName = some (.const bitName) := by
  have hb : ffName ≠ bitName := by decide
  have ht : ffName ≠ ttName := by decide
  change bitConstTypeA ffName = some (.const bitName)
  rw [bitConstTypeA, if_neg hb, if_neg ht, if_pos rfl]

theorem declared_not :
    bitChurch.constantType notName = some (.pi (.const bitName) (.const bitName)) := by
  have hb : notName ≠ bitName := by decide
  have ht : notName ≠ ttName := by decide
  have hf : notName ≠ ffName := by decide
  change bitConstTypeA notName = some (.pi (.const bitName) (.const bitName))
  rw [bitConstTypeA, if_neg hb, if_neg ht, if_neg hf, if_pos rfl]

theorem declared_prop : bitChurch.constantType propName = some (.head 1) := by
  have hb : propName ≠ bitName := by decide
  have ht : propName ≠ ttName := by decide
  have hf : propName ≠ ffName := by decide
  have hn : propName ≠ notName := by decide
  change bitConstTypeA propName = some (.head 1)
  rw [bitConstTypeA, if_neg hb, if_neg ht, if_neg hf, if_neg hn, if_pos rfl]

theorem declared_holds :
    bitChurch.constantType holdsName = some (.pi (.const propName) (.head 0)) := by
  have hb : holdsName ≠ bitName := by decide
  have ht : holdsName ≠ ttName := by decide
  have hf : holdsName ≠ ffName := by decide
  have hn : holdsName ≠ notName := by decide
  have hp : holdsName ≠ propName := by decide
  change bitConstTypeA holdsName = some (.pi (.const propName) (.head 0))
  rw [bitConstTypeA, if_neg hb, if_neg ht, if_neg hf, if_neg hn, if_neg hp, if_pos rfl]

theorem bit_head_typed : CTyped bitChurch .nil (.head 0) (.head 1) :=
  .headType rfl

theorem bit_typed {n : Nat} (Γ : CCtx Nat n) :
    CTyped bitChurch Γ (.const bitName) (.head 0) := by
  simpa [CTm.liftClosed, CTm.rename] using
    (CDerivable.const (Γ := Γ) declared_bit bit_head_typed trivial)

theorem tt_typed {n : Nat} (Γ : CCtx Nat n) :
    CTyped bitChurch Γ (.const ttName) (.const bitName) := by
  simpa [CTm.liftClosed, CTm.rename] using
    (CDerivable.const (Γ := Γ) declared_tt (bit_typed .nil) trivial)

theorem ff_typed {n : Nat} (Γ : CCtx Nat n) :
    CTyped bitChurch Γ (.const ffName) (.const bitName) := by
  simpa [CTm.liftClosed, CTm.rename] using
    (CDerivable.const (Γ := Γ) declared_ff (bit_typed .nil) trivial)

theorem not_type_typed :
    CTyped bitChurch .nil (.pi (.const bitName) (.const bitName)) (.head 0) :=
  .piForm (u := 0) (v := 0) (w := 0) (bit_typed .nil) trivial
    (bit_typed (.snoc .nil (.const bitName))) trivial rfl

theorem not_typed {n : Nat} (Γ : CCtx Nat n) :
    CTyped bitChurch Γ (.const notName) (.pi (.const bitName) (.const bitName)) := by
  simpa [CTm.liftClosed, CTm.rename] using
    (CDerivable.const (Γ := Γ) declared_not not_type_typed trivial)

theorem prop_head_typed : CTyped bitChurch .nil (.head 1) (.head 2) :=
  .headType rfl

theorem prop_typed {n : Nat} (Γ : CCtx Nat n) :
    CTyped bitChurch Γ (.const propName) (.head 1) := by
  simpa [CTm.liftClosed, CTm.rename] using
    (CDerivable.const (Γ := Γ) declared_prop prop_head_typed trivial)

theorem holds_type_typed :
    CTyped bitChurch .nil (.pi (.const propName) (.head 0)) (.head 1) :=
  .piForm (u := 1) (v := 1) (w := 1) (prop_typed .nil) trivial
    (.headType (Γ := .snoc .nil (.const propName)) (h := 0) (u := 1) rfl) trivial rfl

def bitLevels : LevelModel bitRules Nat where
  level := id
  successor := fun {u} _ => ⟨u + 1, trivial, rfl, rfl⟩
  universe_typing := fun _ h => ⟨trivial, h⟩
  ground_typing := fun _ => trivial
  cumulative_universe := fun h => ⟨trivial, trivial, h⟩
  headEq_level := fun h => ⟨Iff.rfl, h⟩
  join_level := fun h => ⟨trivial, h⟩
  join_exists := fun _ _ => ⟨_, rfl⟩
  join_upper := fun h => by
    subst h
    exact ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  cumulative_refl := fun _ => Nat.le_refl _
  headEq_symm := Eq.symm
  headEq_trans := Eq.trans
  universe_decided := fun _ => Or.inl trivial

theorem bitAlgebra : CumulativeAlgebra bitRules where
  trans := fun h₁ h₂ => Nat.le_trans h₁ h₂
  same_left := fun same h => by
    rcases same with rfl | rfl
    · exact h
    · exact h
  same_right := fun h same => by
    rcases same with rfl | rfl
    · exact h
    · exact h
  join_least := fun hj hu hv => by
    subst hj
    exact Nat.max_le.2 ⟨hu, hv⟩

def bitRigid : RigidTypes bitChurch where
  prop := propName
  holds := holdsName
  num := numName
  zero := zeroName
  suc := sucName
  holds_typed := fun Γ => ⟨0, trivial, by
    simpa [CTm.liftClosed, CTm.rename] using
      (CDerivable.const (Γ := Γ) declared_holds holds_type_typed trivial)⟩
  ground := fun _ => False

theorem suc_ne_holds : bitRigid.suc ≠ bitRigid.holds := by decide
theorem suc_ne_not : bitRigid.suc ≠ notName := by decide
theorem holds_ne_not : bitRigid.holds ≠ notName := by decide
theorem tt_ne_ff : ttName ≠ ffName := by decide

theorem core_shape {K : RigidTypes bitChurch} {n : Nat} {t u : CTm Nat n}
    (s : CoreStep bitChurch K t u) :
    (∃ f a, t = .app f a) ∨ (∃ p, t = .fst p) ∨ (∃ p, t = .snd p) := by
  cases s with
  | beta _ _ _ => exact .inl ⟨_, _, rfl⟩
  | appFun _ _ => exact .inl ⟨_, _, rfl⟩
  | root h =>
      cases h with
      | tt => exact .inl ⟨_, _, rfl⟩
      | ff => exact .inl ⟨_, _, rfl⟩
  | holdsArg _ => exact .inl ⟨_, _, rfl⟩
  | fstPair _ _ => exact .inr (.inl ⟨_, rfl⟩)
  | sndPair _ _ => exact .inr (.inr ⟨_, rfl⟩)
  | fst _ => exact .inr (.inl ⟨_, rfl⟩)
  | snd _ => exact .inr (.inr ⟨_, rfl⟩)

theorem not_core_of_shape {K : RigidTypes bitChurch} {n : Nat} {t u : CTm Nat n}
    (happ : ∀ f a, t ≠ .app f a) (hfst : ∀ p, t ≠ .fst p) (hsnd : ∀ p, t ≠ .snd p) :
    ¬ CoreStep bitChurch K t u := by
  intro s
  rcases core_shape s with ⟨f, a, e⟩ | ⟨p, e⟩ | ⟨p, e⟩
  · exact happ f a e
  · exact hfst p e
  · exact hsnd p e

theorem not_core_const {K : RigidTypes bitChurch} {n : Nat} {c : DeclName} {u : CTm Nat n} :
    ¬ CoreStep bitChurch K (.const c) u :=
  not_core_of_shape (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)

theorem not_core_head {K : RigidTypes bitChurch} {n : Nat} {h : Nat} {u : CTm Nat n} :
    ¬ CoreStep bitChurch K (.head h) u :=
  not_core_of_shape (fun _ _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)

theorem not_core_lam {K : RigidTypes bitChurch} {n : Nat} {A : CTm Nat n} {b : CTm Nat (n + 1)}
    {u : CTm Nat n} : ¬ CoreStep bitChurch K (.lam A b) u :=
  not_core_of_shape (fun _ _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)

theorem not_core_pair {K : RigidTypes bitChurch} {n : Nat} {a b u : CTm Nat n} :
    ¬ CoreStep bitChurch K (.pair a b) u :=
  not_core_of_shape (fun _ _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)

theorem not_core_pi {K : RigidTypes bitChurch} {n : Nat} {A : CTm Nat n} {B : CTm Nat (n + 1)}
    {u : CTm Nat n} : ¬ CoreStep bitChurch K (.pi A B) u :=
  not_core_of_shape (fun _ _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)

theorem not_core_sigma {K : RigidTypes bitChurch} {n : Nat} {A : CTm Nat n} {B : CTm Nat (n + 1)}
    {u : CTm Nat n} : ¬ CoreStep bitChurch K (.sigma A B) u :=
  not_core_of_shape (fun _ _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)

theorem not_core_id {K : RigidTypes bitChurch} {n : Nat} {A a b u : CTm Nat n} :
    ¬ CoreStep bitChurch K (.id A a b) u :=
  not_core_of_shape (fun _ _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)

theorem not_core_refl {K : RigidTypes bitChurch} {n : Nat} {a u : CTm Nat n} :
    ¬ CoreStep bitChurch K (.refl a) u :=
  not_core_of_shape (fun _ _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)

theorem not_core_suc {n : Nat} {m u : CTm Nat n} :
    ¬ CoreStep bitChurch bitRigid (.app (.const bitRigid.suc) m) u := by
  intro s
  generalize e : (.app (.const bitRigid.suc) m : CTm Nat n) = t at s
  cases s with
  | beta _ _ _ =>
      injection e with _ hf _
      injection hf
  | appFun _ s' =>
      injection e with _ hf _
      subst hf
      exact False.elim (not_core_const s')
  | root h =>
      cases h with
      | tt =>
          injection e with _ hf _
          injection hf with _ hc
          exact suc_ne_not hc
      | ff =>
          injection e with _ hf _
          injection hf with _ hc
          exact suc_ne_not hc
  | holdsArg _ =>
      injection e with _ hf _
      injection hf with _ hc
      exact suc_ne_holds hc
  | fstPair _ _ => cases e
  | sndPair _ _ => cases e
  | fst _ => cases e
  | snd _ => cases e

theorem not_core_holds_head {n : Nat} {h : Nat} {u : CTm Nat n} :
    ¬ CoreStep bitChurch bitRigid (.app (.const bitRigid.holds) (.head h)) u := by
  intro s
  generalize e : (.app (.const bitRigid.holds) (.head h) : CTm Nat n) = t at s
  cases s with
  | beta _ _ _ =>
      injection e with _ hf _
      injection hf
  | appFun _ s' =>
      injection e with _ hf _
      subst hf
      exact False.elim (not_core_const s')
  | root hs =>
      cases hs with
      | tt =>
          injection e with _ hf _
          injection hf with _ hc
          exact holds_ne_not hc
      | ff =>
          injection e with _ hf _
          injection hf with _ hc
          exact holds_ne_not hc
  | holdsArg s' =>
      injection e with _ _ ha
      subst ha
      exact not_core_head s'
  | fstPair _ _ => cases e
  | sndPair _ _ => cases e
  | fst _ => cases e
  | snd _ => cases e

private theorem const_not_spine {n : Nat} {c d : DeclName} {args : List (Tm Nat n)}
    (h : (.const c : Tm Nat n) = appSpine (.const d) args) : c = d := by
  rcases appSpine_const_cases d args with hsp | ⟨_, _, hsp⟩
  · rw [hsp] at h
    injection h
  · rw [hsp] at h
    cases h

theorem core_deterministic {n : Nat} {t u u' : CTm Nat n}
    (s₁ : CoreStep bitChurch bitRigid t u) (s₂ : CoreStep bitChurch bitRigid t u') : u = u' := by
  induction s₁ generalizing u' with
  | beta _ _ _ =>
      cases s₂ with
      | beta => rfl
      | appFun _ s => exact absurd s not_core_lam
      | root h => cases h
  | appFun _ s ih =>
      cases s₂ with
      | beta => exact absurd s not_core_lam
      | appFun _ s' => rw [ih s']
      | root h =>
          cases h with
          | tt => exact absurd s not_core_const
          | ff => exact absurd s not_core_const
      | holdsArg _ => exact absurd s not_core_const
  | root h =>
      cases h with
      | tt =>
          generalize e : (.app (.const notName) (.const ttName) : CTm Nat n) = t at s₂
          cases s₂ with
          | beta _ _ _ =>
              injection e with _ hf _
              injection hf
          | appFun _ s =>
              injection e with _ hf _
              subst hf
              exact False.elim (not_core_const s)
          | root h' =>
              cases h' with
              | tt => rfl
              | ff =>
                  injection e with _ _ ha
                  injection ha with _ hc
                  exact False.elim (tt_ne_ff hc)
          | holdsArg _ =>
              injection e with _ hf _
              injection hf with _ hc
              exact False.elim (holds_ne_not hc.symm)
          | fstPair _ _ => cases e
          | sndPair _ _ => cases e
          | fst _ => cases e
          | snd _ => cases e
      | ff =>
          generalize e : (.app (.const notName) (.const ffName) : CTm Nat n) = t at s₂
          cases s₂ with
          | beta _ _ _ =>
              injection e with _ hf _
              injection hf
          | appFun _ s =>
              injection e with _ hf _
              subst hf
              exact False.elim (not_core_const s)
          | root h' =>
              cases h' with
              | tt =>
                  injection e with _ _ ha
                  injection ha with _ hc
                  exact False.elim (tt_ne_ff hc.symm)
              | ff => rfl
          | holdsArg _ =>
              injection e with _ hf _
              injection hf with _ hc
              exact False.elim (holds_ne_not hc.symm)
          | fstPair _ _ => cases e
          | sndPair _ _ => cases e
          | fst _ => cases e
          | snd _ => cases e
  | holdsArg s ih =>
      rename_i c c'
      generalize e : (.app (.const bitRigid.holds) c : CTm Nat n) = t at s₂
      cases s₂ with
      | beta _ _ _ =>
          injection e with _ hf _
          injection hf
      | appFun _ s' =>
          injection e with _ hf _
          subst hf
          exact False.elim (not_core_const s')
      | root h =>
          cases h with
          | tt =>
              injection e with _ hf _
              injection hf with _ hc
              exact False.elim (holds_ne_not hc)
          | ff =>
              injection e with _ hf _
              injection hf with _ hc
              exact False.elim (holds_ne_not hc)
      | holdsArg s' =>
          injection e with _ _ ha
          subst ha
          rw [ih s']
      | fstPair _ _ => cases e
      | sndPair _ _ => cases e
      | fst _ => cases e
      | snd _ => cases e
  | fstPair _ _ =>
      cases s₂ with
      | fstPair => rfl
      | fst s => exact absurd s not_core_pair
      | root h => cases h
  | sndPair _ _ =>
      cases s₂ with
      | sndPair => rfl
      | snd s => exact absurd s not_core_pair
      | root h => cases h
  | fst s ih =>
      cases s₂ with
      | fstPair => exact absurd s not_core_pair
      | fst s' => rw [ih s']
      | root h => cases h
  | snd s ih =>
      cases s₂ with
      | sndPair => exact absurd s not_core_pair
      | snd s' => rw [ih s']
      | root h => cases h

def bitReduction : HeadReduction bitChurch bitRigid where
  step := CoreStep bitChurch bitRigid
  beta := .beta
  appFun := fun a s => .appFun a s
  root := .root
  holdsArg := .holdsArg
  deterministic := core_deterministic
  head_normal := fun _ _ => not_core_head
  pi_normal := fun _ _ _ => not_core_pi
  id_normal := fun _ _ _ _ => not_core_id
  refl_normal := fun _ _ => not_core_refl
  prop_normal := fun _ => not_core_const
  num_normal := fun _ => not_core_const
  zero_normal := fun _ => not_core_const
  suc_normal := fun _ _ => not_core_suc
  fstPair := .fstPair
  sndPair := .sndPair
  fst := .fst
  snd := .snd
  sigma_normal := fun _ _ _ => not_core_sigma
  ground_normal := fun _ hg _ => hg.elim

theorem former_normal {n : Nat} {B : CTm Nat n} (former : CFormer B) :
    bitReduction.Normal B := by
  cases former with
  | head h => exact bitReduction.normal_head h
  | pi A B => exact bitReduction.normal_pi A B
  | sigma A B => exact bitReduction.normal_sigma A B
  | id A a b => exact bitReduction.normal_id A a b

theorem bitStuck : bitReduction.DecoderStuckAtUniverses := fun _ _ => not_core_holds_head

/-- Application of the least ideal to itself is the least ideal.  A function
token entailed by the empty witness has outputs that are entailed by it. -/
theorem app_bot_bot : Ideal.app Ideal.bot Ideal.bot = Ideal.bot := by
  refine Ideal.le_antisymm ?_ (Ideal.bot_le _)
  refine Ideal.closure_le ?_
  intro t ⟨_, X, Y, hfn, _, ht⟩
  rw [Ideal.bot, Ideal.mem_principal, ent_fn, Bool.and_eq_true] at hfn
  have hnil : fnApp .lam ([] : List Tok) X = [] := by
    unfold fnApp fns
    rfl
  rw [hnil] at hfn
  rw [Ideal.bot, Ideal.mem_principal]
  exact (List.all_eq_true.mp hfn.2) t ht

def bitReading : Reading Nat := ⟨fun _ => Elem.univ, fun _ => Ideal.bot⟩

theorem bitValid : ReadingValid bitReading bitChurch :=
  ReadingValid.ofLevels bitLevels (fun _ => rfl) (fun _ => Elem.ty_univ_univ) (fun _ => rfl)
    (fun _ _ => Ideal.le_antisymm (Ideal.projT_le _ _) (Ideal.bot_le _))
    (fun step _ _ _ _ _ => by
      cases step with
      | tt => simpa [cinterp, bitReading] using app_bot_bot
      | ff => simpa [cinterp, bitReading] using app_bot_bot)

theorem bitGroundHeads : bitRigid.GroundHeads bitReading := fun _ => Or.inl trivial

theorem bitGroundEq : GroundHeadEq bitRules := fun _ => Or.inl trivial

theorem bitSub : ChurchRulesSub bitChurch bitChurch := ChurchRulesSub.refl bitChurch

theorem bitConstAdequate : ConstAdequate bitReading bitReduction := by
  intro _ _ _ _ _ _ _ _ _ _ _ member _
  exact RT.of_vacuous member

/-- Roles used only to read a neutral type constant.  `bit` is rigid, and the
decoder is neither rigid nor computing, so a step at its argument is not the
step of a neutral term. -/
def neutralRoles : Roles Nat := fun name =>
  if name = bitName then .rigid
  else .constructor 0

theorem neutral_const_bit {n : Nat} {c : DeclName}
    (h : Neutral neutralRoles (.const c : Tm Nat n)) : c = bitName := by
  rcases Neutral.constSpine h (appSpine_nil (.const c)).symm with
      role | ⟨_, _, _, _, _, _, roleC, _, _, _, _, _⟩
  · by_cases hc : c = bitName
    · exact hc
    · rw [neutralRoles, if_neg hc] at role
      cases role
  · by_cases hc : c = bitName
    · rw [neutralRoles, if_pos hc] at roleC
      cases roleC
    · rw [neutralRoles, if_neg hc] at roleC
      cases roleC

theorem neutralRoles_rigid (c : DeclName) (role : neutralRoles c = .rigid) : c = bitName := by
  by_cases hc : c = bitName
  · exact hc
  · rw [neutralRoles, if_neg hc] at role
    cases role

theorem neutralRoles_not_computes {c : DeclName} {arity : Nat} {inspect : InspectTree} :
    neutralRoles c ≠ .computes arity inspect := by
  intro role
  by_cases hc : c = bitName
  · rw [neutralRoles, if_pos hc] at role
    cases role
  · rw [neutralRoles, if_neg hc] at role
    cases role

theorem not_core_neutral {n : Nat} (t : CTm Nat n) :
    Neutral neutralRoles t.erase → ∀ u, ¬ CoreStep bitChurch bitRigid t u := by
  induction t with
  | var _ =>
      intro _ _ s
      cases s with
      | root h => cases h
  | const _ =>
      intro _ _ s
      exact False.elim (not_core_const s)
  | head _ =>
      intro _ _ s
      exact not_core_head s
  | pi _ _ =>
      intro _ _ s
      exact not_core_pi s
  | sigma _ _ =>
      intro _ _ s
      exact not_core_sigma s
  | id _ _ _ =>
      intro _ _ s
      exact not_core_id s
  | lam _ _ =>
      intro _ _ s
      exact not_core_lam s
  | pair _ _ =>
      intro _ _ s
      exact not_core_pair s
  | refl _ =>
      intro _ _ s
      exact not_core_refl s
  | app f a ihf _ =>
      intro h _ s
      generalize he : (CTm.app f a).erase = te at h
      cases h with
      | var _ => cases he
      | fst _ => cases he
      | snd _ => cases he
      | app hf =>
          injection he with _ hfe hae
          subst hfe hae
          cases s with
          | beta _ _ _ => exact Neutral.ne_lam hf rfl
          | appFun _ sf => exact ihf hf _ sf
          | root hs =>
              cases hs with
              | tt => exact absurd (neutral_const_bit hf) (by decide : notName ≠ bitName)
              | ff => exact absurd (neutral_const_bit hf) (by decide : notName ≠ bitName)
          | holdsArg _ =>
              exact absurd (neutral_const_bit hf) (by decide : holdsName ≠ bitName)
      | rigid _ role =>
          have hc := neutralRoles_rigid _ role
          subst hc
          cases s with
          | beta _ _ _ => exact appSpine_const_ne_lam he.symm
          | appFun _ sf =>
              obtain ⟨init, _, hfsp⟩ := appSpine_const_eq_app he.symm
              have hn : Neutral neutralRoles f.erase := by
                rw [hfsp]
                exact Neutral.rigid init role
              exact ihf hn _ sf
          | root hs =>
              cases hs with
              | tt =>
                  obtain ⟨_, _, hfsp⟩ := appSpine_const_eq_app he.symm
                  exact absurd (const_not_spine hfsp) (by decide : notName ≠ bitName)
              | ff =>
                  obtain ⟨_, _, hfsp⟩ := appSpine_const_eq_app he.symm
                  exact absurd (const_not_spine hfsp) (by decide : notName ≠ bitName)
          | holdsArg _ =>
              obtain ⟨_, _, hfsp⟩ := appSpine_const_eq_app he.symm
              exact absurd (const_not_spine hfsp) (by decide : holdsName ≠ bitName)
      | stuck roleC _ _ _ _ => exact neutralRoles_not_computes roleC
  | fst p ih =>
      intro h _ s
      generalize he : (CTm.fst p).erase = te at h
      cases h with
      | var _ => cases he
      | app _ => cases he
      | snd _ => cases he
      | fst hp =>
          injection he with _ hpe
          subst hpe
          cases s with
          | fstPair _ _ => exact Neutral.ne_pair hp rfl
          | fst sp => exact ih hp _ sp
          | root hs => cases hs
      | rigid _ _ => exact appSpine_const_ne_fst he.symm
      | stuck roleC _ _ _ _ => exact neutralRoles_not_computes roleC
  | snd p ih =>
      intro h _ s
      generalize he : (CTm.snd p).erase = te at h
      cases h with
      | var _ => cases he
      | app _ => cases he
      | fst _ => cases he
      | snd hp =>
          injection he with _ hpe
          subst hpe
          cases s with
          | sndPair _ _ => exact Neutral.ne_pair hp rfl
          | snd sp => exact ih hp _ sp
          | root hs => cases hs
      | rigid _ _ => exact appSpine_const_ne_snd he.symm
      | stuck roleC _ _ _ _ => exact neutralRoles_not_computes roleC

theorem bitNeutralNormal : bitReduction.NeutralNormal neutralRoles :=
  fun h u step => not_core_neutral _ h u step

theorem bitFormers : CFormerFacts bitChurch where
  forms := fun equal formed former former' =>
    equal.formersMatch_of_normal bitLevels bitValid bitGroundHeads bitGroundEq bitStuck bitSub
      (fun _ => bitConstAdequate) formed former (former_normal former')

theorem only_inductive {T : DeclName} {ctors : List (DeclName × List (Field Nat))}
    (role : bitRoles T = .inductive ctors) : T = bitName := by
  by_cases hb : T = bitName
  · exact hb
  by_cases ht : T = ttName
  · subst ht
    rw [bitRoles_tt] at role
    cases role
  by_cases hf : T = ffName
  · subst hf
    rw [bitRoles_ff] at role
    cases role
  by_cases hn : T = notName
  · subst hn
    rw [bitRoles_not] at role
    cases role
  · rw [bitRoles_rigid hb ht hf hn] at role
    cases role

theorem only_constructor {k : DeclName} {arity : Nat}
    (role : bitRoles k = .constructor arity) : k = ttName ∨ k = ffName := by
  by_cases hb : k = bitName
  · subst hb
    rw [bitRoles_bit] at role
    cases role
  by_cases ht : k = ttName
  · exact Or.inl ht
  by_cases hf : k = ffName
  · exact Or.inr hf
  by_cases hn : k = notName
  · subst hn
    rw [bitRoles_not] at role
    cases role
  · rw [bitRoles_rigid hb ht hf hn] at role
    cases role

theorem constructor_result_bit {k : DeclName} {arity : Nat} {D : CTm Nat 0} {C : DeclName}
    (role : bitRoles k = .constructor arity) (declared : bitChurch.constantType k = some D)
    (result : Progress.afterBinders (Progress.isConstTest C) arity D = true) : C = bitName := by
  rcases only_constructor role with rfl | rfl
  · rw [bitRoles_tt] at role
    cases role
    rw [declared_tt] at declared
    obtain rfl := Option.some.inj declared
    dsimp only [Progress.afterBinders] at result
    have hX := Progress.isConstTest_inv result
    injection hX with _ h
    exact h.symm
  · rw [bitRoles_ff] at role
    cases role
    rw [declared_ff] at declared
    obtain rfl := Option.some.inj declared
    dsimp only [Progress.afterBinders] at result
    have hX := Progress.isConstTest_inv result
    injection hX with _ h
    exact h.symm

theorem domain_bit {c : DeclName} {arity pos : Nat} {D : CTm Nat 0} {C : DeclName}
    (role : bitRoles c = .computes arity (.split pos .constructor fun _ => .leaf))
    (declared : bitChurch.constantType c = some D)
    (domain : Progress.afterBinders (Progress.domainTest (Progress.isConstTest C)) pos D = true) :
    C = bitName := by
  have hc : c = notName := by
    by_cases hb : c = bitName
    · subst hb
      rw [bitRoles_bit] at role
      cases role
    by_cases ht : c = ttName
    · subst ht
      rw [bitRoles_tt] at role
      cases role
    by_cases hf : c = ffName
    · subst hf
      rw [bitRoles_ff] at role
      cases role
    by_cases hn : c = notName
    · exact hn
    · rw [bitRoles_rigid hb ht hf hn] at role
      cases role
  subst hc
  rw [bitRoles_not] at role
  cases role
  rw [declared_not] at declared
  obtain rfl := Option.some.inj declared
  dsimp only [Progress.afterBinders] at domain
  obtain ⟨_, _, hD, htest⟩ := Progress.domainTest_inv domain
  injection hD with _ hA _
  subst hA
  have hX := Progress.isConstTest_inv htest
  injection hX with _ h
  exact h.symm

theorem relevant_only {C : DeclName} (h : Progress.RelevantConst bitChurch bitRoles C) :
    C = bitName := by
  rcases h with ⟨_, role⟩ | ⟨_, _, _, role, declared, result⟩ | ⟨_, _, _, _, role, declared, domain⟩
  · exact only_inductive role
  · exact constructor_result_bit role declared result
  · exact domain_bit role declared domain

theorem bitFacts : Progress.ProgressFacts bitChurch bitRoles where
  formers := bitFormers
  constructorShape := by
    intro k arity role
    rcases only_constructor role with rfl | rfl
    · rw [bitRoles_tt] at role
      cases role
      exact ⟨.const bitName, bitName, declared_tt, by decide,
        fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    · rw [bitRoles_ff] at role
      cases role
      exact ⟨.const bitName, bitName, declared_ff, by decide,
        fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  declaredComputing := by
    intro c arity inspect role
    have hc : c = notName := by
      by_cases hb : c = bitName
      · subst hb
        rw [bitRoles_bit] at role
        cases role
      by_cases ht : c = ttName
      · subst ht
        rw [bitRoles_tt] at role
        cases role
      by_cases hf : c = ffName
      · subst hf
        rw [bitRoles_ff] at role
        cases role
      by_cases hn : c = notName
      · exact hn
      · rw [bitRoles_rigid hb ht hf hn] at role
        cases role
    subst hc
    rw [bitRoles_not] at role
    injection role with hArity hInspect
    subst hArity hInspect
    refine ⟨.pi (.const bitName) (.const bitName), declared_not, ?_, ?_⟩
    · intro j hj
      have : j = 0 := by omega
      subst this
      decide
    · exact .const 0 bitName rfl (by decide) (by decide)
  rootCoverage := by
    intro c arity inspect D role declared n args hlen canon
    have hc : c = notName := by
      by_cases hb : c = bitName
      · subst hb
        rw [bitRoles_bit] at role
        cases role
      by_cases ht : c = ttName
      · subst ht
        rw [bitRoles_tt] at role
        cases role
      by_cases hf : c = ffName
      · subst hf
        rw [bitRoles_ff] at role
        cases role
      by_cases hn : c = notName
      · exact hn
      · rw [bitRoles_rigid hb ht hf hn] at role
        cases role
    subst hc
    rw [bitRoles_not] at role
    injection role with hArity hInspect
    subst hArity hInspect
    have hD : D = .pi (.const bitName) (.const bitName) :=
      Option.some.inj (declared.symm.trans declared_not)
    subst hD
    obtain ⟨before, x, after, hargs, hpos, hform⟩ := canon
    have hbefore : before = [] := List.eq_nil_of_length_eq_zero hpos
    subst hbefore
    have hafter : after = [] := by
      rw [hargs, List.nil_append] at hlen
      have : after.length = 0 := by
        simp only [List.length_cons] at hlen
        omega
      exact List.eq_nil_of_length_eq_zero this
    subst hafter
    rcases hform with ⟨C, _, fits⟩ | ⟨hid, _⟩
    · obtain ⟨k, karity, kargs, kD, krole, klen, hx, kdecl, _⟩ := fits
      have : karity = 0 := by
        rcases only_constructor krole with rfl | rfl
        · rw [bitRoles_tt] at krole
          cases krole
          rfl
        · rw [bitRoles_ff] at krole
          cases krole
          rfl
      subst this
      have hkargs : kargs = [] := List.eq_nil_of_length_eq_zero klen
      subst hkargs
      have hx' : x = .const k := by simpa [CTm.appSpine] using hx
      subst hx'
      rcases only_constructor krole with rfl | rfl
      · refine ⟨.const ffName, ?_⟩
        unfold bitChurch bitComputation
        simp only [hargs, CTm.appSpine, List.foldl_cons, List.foldl_nil, List.nil_append]
        exact NotStep.tt
      · refine ⟨.const ttName, ?_⟩
        unfold bitChurch bitComputation
        simp only [hargs, CTm.appSpine, List.foldl_cons, List.foldl_nil, List.nil_append]
        exact NotStep.ff
    · dsimp only [Progress.afterBinders, Progress.domainTest, Progress.isIdTest] at hid
      exact False.elim (Bool.false_ne_true hid)
  inductiveDeclared := by
    intro T ctors role
    have hT := only_inductive role
    subst hT
    exact ⟨0, trivial, declared_bit⟩
  formerNeConst := by
    intro C rel n Γ X formed former equal
    have hC := relevant_only rel
    subst hC
    exact CTypeEq.neutral_not_former_sub bitLevels bitValid bitGroundHeads bitGroundEq bitStuck
      bitSub (fun _ => bitConstAdequate) bitNeutralNormal equal.symm formed
      (Neutral.rigid [] (by rw [neutralRoles, if_pos rfl])) former
  constDistinct := by
    intro C C' hC hC' hne n Γ formed equal
    exact hne ((relevant_only hC).trans (relevant_only hC').symm)

/-- A type of a universe progresses. -/
theorem bit_typeProgress {n : Nat} {Γ : CCtx Nat n} {A : CTm Nat n} {u : Nat}
    (formed : CCtxFormed bitChurch Γ) (hu : bitRules.isUniverse u)
    (typing : CTyped bitChurch Γ A (.head u)) :
    (∃ A', CWhStepR bitChurch bitRoles A A') ∨ IsTypeForm bitRoles A.erase :=
  Progress.typeProgress bitFacts bitLevels bitAlgebra formed hu typing

def notTerm : CTm Nat 0 := .app (.const notName) (.const ttName)

/-- `not tt` steps to `ff`, so the erased application is not a weak-head normal form. -/
theorem not_tt_steps_and_not_whnf :
    CWhStepR bitChurch bitRoles notTerm (.const ffName) ∧
      ¬ Whnf bitRules bitRoles notTerm.erase := by
  refine ⟨.root (by
    unfold bitChurch bitComputation notTerm
    exact NotStep.tt), ?_⟩
  intro normal
  exact normal (.const ffName) (.root (bitChurch.erase_step NotStep.tt))

end ProgressBit
end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
