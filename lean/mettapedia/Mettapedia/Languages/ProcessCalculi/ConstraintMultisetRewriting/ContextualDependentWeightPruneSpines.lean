import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentShortClosurePrune
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentHereditaryLong

/-!
# Instantiating a typed Π spine at arguments

The syntax that the η-long weight bound under pruning reads off a dependent Π spine, for any list of arguments.

* **Instantiation** (`spineInst`): the substitution of a spine's telescope that sends the outer variables through `θ`
  and each binder to its argument. It is read through the binder map of a pattern (`spineInst_argRen`), so a
  restriction's two telescopes are instantiated compatibly.
* **Types along the spine** (`piAfter_spineList`, `argsAt_spine`): the type of a spine after its arguments, read along
  the literal Π binders of the declared type (`piAfter`), is the result type instantiated at all of them, and the domain
  at each position is the declared type of that binder, instantiated.
* **Contraction** (`whRed_abstractBody`, `subst_openFunction`): an abstraction over a spine applied to arguments
  reduces in weak-head steps to its body instantiated; an opened function instantiated is the function applied to the
  arguments.
* **Counting** (`sum_kept_le`): along an injective binder map, the arguments kept weigh at most all of them.

Arguments are listed first first (`spineList`); a spine judgment lists them last first (`appsRev`), hence `reverse`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentWeightPrune

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentHereditary
open ContextualDependentDynamicFragment ContextualDependentRank

/-! ## Lists of arguments -/

section Lists

variable {Head : Type}

theorem appsRev_append_single {n : Nat} (head argument : Tm Head n) :
    ∀ (rest : List (Tm Head n)), appsRev head (rest ++ [argument]) = appsRev (.app head argument) rest
  | [] => rfl
  | other :: rest => by
      change Tm.app (appsRev head (rest ++ [argument])) other = Tm.app (appsRev (.app head argument) rest) other
      rw [appsRev_append_single head argument rest]

theorem piAfter_append_single {n : Nat} (type argument : Tm Head n) :
    ∀ (rest : List (Tm Head n)), piAfter type (rest ++ [argument]) = piAfter (piAfter type [argument]) rest
  | [] => rfl
  | other :: rest => by
      simp only [List.cons_append, piAfter, piAfter_append_single type argument rest]

theorem subst_appsRev {n m : Nat} (σ : Sub Head n m) (head : Tm Head n) :
    ∀ (arguments : List (Tm Head n)),
      subst σ (appsRev head arguments) = appsRev (subst σ head) (arguments.map (subst σ))
  | [] => rfl
  | argument :: rest => by
      change Tm.app (subst σ (appsRev head rest)) (subst σ argument) = _
      rw [subst_appsRev σ head rest]
      rfl

theorem weight_appsRev {n : Nat} (head : Tm Head n) :
    ∀ (arguments : List (Tm Head n)),
      weight (appsRev head arguments) = weight head + (arguments.map fun argument => weight argument + 1).sum
  | [] => by simp [appsRev]
  | argument :: rest => by
      change weight (appsRev head rest) + weight argument + 1 = _
      rw [weight_appsRev head rest, List.map_cons, List.sum_cons]
      omega

/-- **Substitution commutes with reading a type along its literal Π binders.** -/
theorem subst_piAfter {n m : Nat} (σ : Sub Head n m) (type : Tm Head n) :
    ∀ (arguments : List (Tm Head n)), arguments.length ≤ piCount type →
      subst σ (piAfter type arguments) = piAfter (subst σ type) (arguments.map (subst σ))
  | [], _ => rfl
  | argument :: rest, short => by
      obtain ⟨A, B, isPi⟩ := piAfter_pi type rest (by simp at short; omega)
      have earlier := subst_piAfter σ type rest (by simp at short; omega)
      rw [isPi] at earlier
      simp only [List.map_cons, piAfter, isPi, ← earlier]
      exact subst_inst0 σ argument B

theorem subst_piDomain_piAfter {n m : Nat} (σ : Sub Head n m) (type : Tm Head n) (arguments : List (Tm Head n))
    (short : arguments.length < piCount type) :
    subst σ (piDomain (piAfter type arguments)) = piDomain (piAfter (subst σ type) (arguments.map (subst σ))) := by
  obtain ⟨A, B, isPi⟩ := piAfter_pi type arguments short
  rw [← subst_piAfter σ type arguments (by omega), isPi]
  rfl

/-- Pointwise relations between two argument lists along a type's literal Π binders, each pair at the domain of its
position read after the first list's earlier arguments. -/
def ArgsAt2 {n : Nat} (Q : Tm Head n → Tm Head n → Tm Head n → Prop) (type : Tm Head n) :
    List (Tm Head n) → List (Tm Head n) → Prop
  | [], [] => True
  | argument :: rest, other :: others => ArgsAt2 Q type rest others ∧ Q argument other (piDomain (piAfter type rest))
  | _, _ => False

theorem ArgsAt2.length_eq {n : Nat} {Q : Tm Head n → Tm Head n → Tm Head n → Prop} {type : Tm Head n} :
    ∀ {first second : List (Tm Head n)}, ArgsAt2 Q type first second → first.length = second.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨rest, _⟩ => by simp [rest.length_eq]
  | [], _ :: _, impossible | _ :: _, [], impossible => impossible.elim

theorem argsAt2_append_single {n : Nat} (Q : Tm Head n → Tm Head n → Tm Head n → Prop) (argument other : Tm Head n) :
    ∀ (type : Tm Head n) (rest others : List (Tm Head n)), rest.length = others.length →
      (ArgsAt2 Q type (rest ++ [argument]) (others ++ [other]) ↔
        Q argument other (piDomain type) ∧ ArgsAt2 Q (piAfter type [argument]) rest others)
  | _, [], [], _ => by simp [ArgsAt2, piAfter]
  | type, first :: rest, second :: others, same => by
      have ih := argsAt2_append_single Q argument other type rest others (by simpa using same)
      simp only [List.cons_append, ArgsAt2, ih, piAfter_append_single]
      tauto
  | _, [], _ :: _, same | _, _ :: _, [], same => by simp at same

/-- `ArgsLong` is the pointwise relation of a list with itself. -/
theorem argsLong_iff {L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L} {n : Nat} (Γ : Ctx Head n)
    (type : Tm Head n) :
    ∀ (arguments : List (Tm Head n)), ArgsLong S.R S.roles Γ type arguments ↔
      ArgsAt2 (fun a _ T => ContextualDependentEtaLong.Long S.R S.roles (.term Γ a T)) type arguments arguments
  | [] => by simp [ArgsLong, ArgsAt2]
  | argument :: rest => by
      simp only [ArgsLong, ArgsAt2, argsLong_iff Γ type rest]

/-- Weak-head reduction of a head is weak-head reduction of the spine it heads. -/
theorem whRed_appsRev {R : Rules Head} {roles : Roles Head} {n : Nat} {head head' : Tm Head n}
    (red : WhRed R roles head head') :
    ∀ (arguments : List (Tm Head n)), WhRed R roles (appsRev head arguments) (appsRev head' arguments)
  | [] => red
  | argument :: rest =>
      Relation.ReflTransGen.lift (fun term => Tm.app term argument) (fun _ _ step => WhStep.appFun step) _ _
        (whRed_appsRev red rest)

theorem neutral_appsRev {roles : Roles Head} {n : Nat} {head : Tm Head n} (neutral : Neutral roles head) :
    ∀ (arguments : List (Tm Head n)), Neutral roles (appsRev head arguments)
  | [] => neutral
  | _ :: rest => .app (neutral_appsRev neutral rest)

end Lists

/-! ## Instantiating a spine -/

section Spines

variable {Head : Type} {rules : Rules Head}

/-- **The instantiation of a spine's telescope**: outer variables through `θ`, each binder to its argument. -/
def spineInst : {Γ : Context rules} → {type : TypeOver Γ} → (spine : Spine type) → {M : Nat} →
    Sub Head Γ.arity M → (spine.Local → Tm Head M) → Sub Head spine.target.arity M
  | _, _, .stop _, _, θ, _ => θ
  | _, _, .bind _ rest, _, θ, values => spineInst rest (consSub (values (.inl ())) θ) fun position => values (.inr position)

/-- The arguments of a spine, first first. -/
def spineList : {Γ : Context rules} → {type : TypeOver Γ} → (spine : Spine type) → {M : Nat} →
    (spine.Local → Tm Head M) → List (Tm Head M)
  | _, _, .stop _, _, _ => []
  | _, _, .bind _ rest, _, values => values (.inl ()) :: spineList rest fun position => values (.inr position)

theorem spineInst_outer : ∀ {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) {M : Nat}
    (θ : Sub Head Γ.arity M) (values : spine.Local → Tm Head M) (prior : Fin Γ.arity),
    spineInst spine θ values (spine.outerRen prior) = θ prior
  | _, _, .stop _, _, _, _, _ => rfl
  | _, _, .bind _ rest, _, _, _, prior => spineInst_outer rest _ _ prior.succ

theorem spineInst_local : ∀ {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) {M : Nat}
    (θ : Sub Head Γ.arity M) (values : spine.Local → Tm Head M) (position : spine.Local),
    spineInst spine θ values (spine.localIndex position) = values position
  | _, _, .stop _, _, _, _, position => position.elim
  | _, _, .bind shape rest, _, θ, values, position => by
      rcases position with ⟨⟨⟩⟩ | position
      · exact (congrArg (spineInst (Spine.bind shape rest) θ values) (Spine.localIndex_head shape rest)).trans
          (spineInst_outer rest _ _ 0)
      · exact spineInst_local rest _ _ position

/-- The newest outer variable of a spine's tail, instantiated, has the head binder's declared type. -/
theorem outer_zero_lookup {Γ : Context rules} (shape : ContextualDependentPiShape.Shape Γ) (rest : Spine shape.codomain)
    {M : Nat} (θ : Sub Head Γ.arity M) (argument : Tm Head M) (values : rest.Local → Tm Head M) :
    subst (spineInst rest (consSub argument θ) values) (Ctx.lookup rest.target.raw (rest.outerRen 0)) =
      subst θ shape.domain.code := by
  rw [rest.outerRen_compatible, subst_rename]
  have outer : (fun index => spineInst rest (consSub argument θ) values (rest.outerRen index)) = consSub argument θ :=
    funext fun index => spineInst_outer rest _ _ index
  rw [outer]
  exact subst_consSub_rename_wk argument θ shape.domain.code

theorem head_lookup {Γ : Context rules} (shape : ContextualDependentPiShape.Shape Γ) (rest : Spine shape.codomain)
    {M : Nat} (θ : Sub Head Γ.arity M) (values : (Spine.bind shape rest).Local → Tm Head M) :
    subst (spineInst (Spine.bind shape rest) θ values)
        (Ctx.lookup (Spine.bind shape rest).target.raw ((Spine.bind shape rest).localIndex (Sum.inl ()))) =
      subst θ shape.domain.code :=
  (congrArg (fun index => subst (spineInst rest (consSub (values (Sum.inl ())) θ) fun position => values (Sum.inr position))
    (Ctx.lookup rest.target.raw index)) (Spine.localIndex_head shape rest)).trans (outer_zero_lookup shape rest θ _ _)

/-- **Instantiation through a pattern's binder map**: reading the restricted telescope's variables through the binder
map, then instantiating the whole telescope, instantiates the restricted telescope at the kept arguments. -/
theorem spineInst_argRen {Γ : Context rules} {type keptType : TypeOver Γ} (spine : Spine type) (kept : Spine keptType)
    (keep : kept.Local → spine.Local) {M : Nat} (θ : Sub Head Γ.arity M) (values : spine.Local → Tm Head M)
    (index : Fin kept.target.arity) :
    spineInst spine θ values (argRen kept spine idRen keep index) = spineInst kept θ (fun position => values (keep position)) index := by
  rcases kept.variable_cases index with ⟨prior, rfl⟩ | ⟨position, rfl⟩
  · rw [argRen_outer, spineInst_outer, spineInst_outer]
    rfl
  · rw [argRen_local, spineInst_local, spineInst_local]

theorem length_spineList : ∀ {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) {M : Nat}
    (values : spine.Local → Tm Head M), (spineList spine values).length = spine.length
  | _, _, .stop _, _, _ => rfl
  | _, _, .bind _ rest, _, values => by
      simp only [spineList, List.length_cons, Spine.length, length_spineList rest]

/-- Every list of the spine's length is the list of some arguments. -/
theorem spineList_surjective : ∀ {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) {M : Nat}
    (arguments : List (Tm Head M)), arguments.length = spine.length → ∃ values, spineList spine values = arguments
  | _, _, .stop _, _, [], _ => ⟨fun position => position.elim, rfl⟩
  | _, _, .stop _, _, _ :: _, long => by simp [Spine.length] at long
  | _, _, .bind _ rest, _, [], short => by simp [Spine.length] at short
  | _, _, .bind _ rest, _, argument :: others, same => by
      obtain ⟨values, listed⟩ := spineList_surjective rest others (by simpa [Spine.length] using same)
      exact ⟨Sum.elim (fun _ => argument) values, by
        change argument :: spineList rest values = argument :: others
        rw [listed]⟩

theorem spineList_map : ∀ {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) {M M' : Nat}
    (values : spine.Local → Tm Head M) (f : Tm Head M → Tm Head M'),
    (spineList spine values).map f = spineList spine fun position => f (values position)
  | _, _, .stop _, _, _, _, _ => rfl
  | _, _, .bind _ rest, _, _, values, f => by
      simp only [spineList, List.map_cons, spineList_map rest]

/-- A spine has at least as many literal Π binders as positions. -/
theorem length_le_piCount : ∀ {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) {M : Nat}
    (θ : Sub Head Γ.arity M), spine.length ≤ piCount (subst θ type.code)
  | _, _, .stop _, _, _ => Nat.zero_le _
  | _, _, .bind shape rest, _, θ => by
      have ih := length_le_piCount rest (liftSub θ)
      change rest.length + 1 ≤ piCount (subst θ shape.whole.code)
      rw [shape.code]
      change rest.length + 1 ≤ piCount (subst (liftSub θ) shape.codomain.code) + 1
      omega

/-- **The type after all arguments is the instantiated result type.** -/
theorem piAfter_spineList : ∀ {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) {M : Nat}
    (θ : Sub Head Γ.arity M) (values : spine.Local → Tm Head M),
    piAfter (subst θ type.code) (spineList spine values).reverse = subst (spineInst spine θ values) spine.result.code
  | _, _, .stop _, _, _, _ => rfl
  | _, _, .bind shape rest, _, θ, values => by
      rw [show spineList (Spine.bind shape rest) values =
        values (Sum.inl ()) :: spineList rest (fun position => values (Sum.inr position)) from rfl, List.reverse_cons]
      rw [piAfter_append_single, shape.code]
      change piAfter (inst0 (values (.inl ())) (subst (liftSub θ) shape.codomain.code)) _ = _
      rw [← subst_consSub]
      exact piAfter_spineList rest _ _

/-- **The domains along the spine are its binders' declared types, instantiated.** -/
theorem argsAt_spine {n : Nat} (Q : Tm Head n → Tm Head n → Tm Head n → Prop) :
    ∀ {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) (θ : Sub Head Γ.arity n)
      (values others : spine.Local → Tm Head n),
      ArgsAt2 Q (subst θ type.code) (spineList spine values).reverse (spineList spine others).reverse ↔
        ∀ position, Q (values position) (others position)
          (subst (spineInst spine θ values) (Ctx.lookup spine.target.raw (spine.localIndex position)))
  | _, _, .stop _, _, _, _ => by simp [spineList, ArgsAt2]; intro position; exact position.elim
  | Γ, _, .bind shape rest, θ, values, others => by
      rw [show spineList (Spine.bind shape rest) values =
          values (Sum.inl ()) :: spineList rest (fun position => values (Sum.inr position)) from rfl,
        show spineList (Spine.bind shape rest) others =
          others (Sum.inl ()) :: spineList rest (fun position => others (Sum.inr position)) from rfl,
        List.reverse_cons, List.reverse_cons]
      rw [argsAt2_append_single Q _ _ _ _ _ (by simp [length_spineList])]
      rw [shape.code]
      change Q _ _ (subst θ shape.domain.code) ∧
          ArgsAt2 Q (inst0 (values (.inl ())) (subst (liftSub θ) shape.codomain.code)) _ _ ↔ _
      rw [← subst_consSub, argsAt_spine Q rest]
      have key := head_lookup shape rest θ values
      constructor
      · rintro ⟨first, later⟩ position
        rcases position with ⟨⟨⟩⟩ | position
        · exact (congrArg (Q (values (Sum.inl ())) (others (Sum.inl ()))) key).mpr first
        · exact later position
      · intro all
        exact ⟨(congrArg (Q (values (Sum.inl ())) (others (Sum.inl ()))) key).mp (all (Sum.inl ())),
          fun position => all (Sum.inr position)⟩

/-- **An abstraction over a spine, applied to arguments, contracts to its instantiated body.** -/
theorem whRed_abstractBody {R : Rules Head} {roles : Roles Head} :
    ∀ {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) {M : Nat} (θ : Sub Head Γ.arity M)
      (values : spine.Local → Tm Head M) (body : Term spine.target spine.result),
      WhRed R roles (appsRev (subst θ (spine.abstractBody body).code) (spineList spine values).reverse)
        (subst (spineInst spine θ values) body.code)
  | _, _, .stop _, _, _, _, _ => .refl
  | _, _, .bind shape rest, _, θ, values, body => by
      rw [show spineList (Spine.bind shape rest) values =
        values (Sum.inl ()) :: spineList rest (fun position => values (Sum.inr position)) from rfl, List.reverse_cons]
      change WhRed R roles (appsRev (.lam (subst (liftSub θ) (rest.abstractBody body).code)) _) _
      rw [appsRev_append_single]
      have step : WhStep R roles (.app (.lam (subst (liftSub θ) (rest.abstractBody body).code)) (values (.inl ())))
          (subst (consSub (values (.inl ())) θ) (rest.abstractBody body).code) := by
        rw [subst_consSub]
        exact .beta _ _
      exact (whRed_appsRev (Relation.ReflTransGen.single step) _).trans (whRed_abstractBody rest _ _ body)

/-- **An opened function, instantiated, is the function applied to the arguments.** -/
theorem subst_openFunction : ∀ {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) {M : Nat}
    (θ : Sub Head Γ.arity M) (values : spine.Local → Tm Head M) (function : Term Γ type),
    subst (spineInst spine θ values) (spine.openFunction function).code =
      appsRev (subst θ function.code) (spineList spine values).reverse
  | _, _, .stop _, _, _, _, _ => rfl
  | _, _, .bind shape rest, _, θ, values, function => by
      change subst (spineInst rest _ _) (rest.openFunction (shape.fresh function)).code = _
      rw [subst_openFunction rest]
      rw [show spineList (Spine.bind shape rest) values =
        values (Sum.inl ()) :: spineList rest (fun position => values (Sum.inr position)) from rfl, List.reverse_cons,
        appsRev_append_single]
      change appsRev (.app (subst (consSub (values (Sum.inl ())) θ) (Presentation.rename wk function.code))
        (values (Sum.inl ()))) _ = _
      rw [subst_consSub_rename_wk]

/-! ## Counting kept arguments -/

/-- The binders of a spine are finitely many. -/
@[instance_reducible] def localFintype : {Γ : Context rules} → {type : TypeOver Γ} → (spine : Spine type) → Fintype spine.Local
  | _, _, .stop _ => (inferInstance : Fintype Empty)
  | _, _, .bind _ rest => @instFintypeSum Unit rest.Local _ (localFintype rest)

theorem sum_spineList : ∀ {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) {M : Nat}
    (values : spine.Local → Tm Head M) (count : Tm Head M → Nat),
    ((spineList spine values).map count).sum =
      @Finset.sum spine.Local Nat _ (@Finset.univ spine.Local (localFintype spine)) fun position => count (values position)
  | _, _, .stop _, _, _, _ => rfl
  | _, _, .bind _ rest, _, values, count => by
      let _ : Fintype rest.Local := localFintype rest
      have split := Fintype.sum_sum_type (fun position : Unit ⊕ rest.Local => count (values position))
      have unit := Fintype.sum_unique (fun first : Unit => count (values (Sum.inl first)))
      have tail := sum_spineList rest (fun position => values (Sum.inr position)) count
      exact (congrArg (count (values (Sum.inl ())) + ·) tail).trans ((congrArg (· + _) unit.symm).trans split.symm)

theorem sum_comp_le {α β : Type} [Fintype α] [Fintype β] (keep : α → β) (injective : Function.Injective keep)
    (count : β → Nat) : ∑ a, count (keep a) ≤ ∑ b, count b := by
  classical
  calc ∑ a, count (keep a) = ∑ b ∈ Finset.univ.map ⟨keep, injective⟩, count b := by rw [Finset.sum_map]; rfl
    _ ≤ ∑ b, count b := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- **Kept arguments weigh at most all arguments**, along an injective binder map. -/
theorem sum_kept_le {Γ : Context rules} {type keptType : TypeOver Γ} (spine : Spine type) (kept : Spine keptType)
    (keep : kept.Local → spine.Local) (injective : Function.Injective keep) {M : Nat}
    (values : spine.Local → Tm Head M) (count : Tm Head M → Nat) :
    ((spineList kept fun position => values (keep position)).map count).sum ≤ ((spineList spine values).map count).sum := by
  let _ : Fintype spine.Local := localFintype spine
  let _ : Fintype kept.Local := localFintype kept
  rw [sum_spineList, sum_spineList]
  exact sum_comp_le keep injective fun position => count (values position)

end Spines

end ContextualDependentWeightPrune
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
