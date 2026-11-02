import Mettapedia.Logic.DerivationClosure
import Mathlib.Data.Set.Finite.Basic

/-! Finitary derivability characterizes closure responses with finite support.
The finite-carrier theorem is a specialization of that general result.
The reverse construction supplies actual rules and uses the existing
derivation closure; it does not define derivability as the desired response. -/

set_option autoImplicit false

namespace Mettapedia.Logic.FiniteHornClosureCharacterization

variable {A : Type*}

def ClosureLaws (response : Set A → Set A) : Prop :=
  (∀ seed, seed ⊆ response seed) ∧ Monotone response ∧
    ∀ seed, response (response seed) = response seed

def FinitelySupported (response : Set A → Set A) : Prop :=
  ∀ seed atom, atom ∈ response seed →
    ∃ premises : List A, (∀ premise ∈ premises, premise ∈ seed) ∧
      atom ∈ response {premise | premise ∈ premises}

def rulesOf (response : Set A → Set A) (premises : List A) (atom : A) : Prop :=
  atom ∈ response {premise | premise ∈ premises}

theorem derivation_has_finite_support (rules : List A → A → Prop) (seed : Set A) (atom : A)
    (derived : FinitaryClosure.close rules (· ∈ seed) atom) :
    ∃ support : List A, (∀ premise ∈ support, premise ∈ seed) ∧
      FinitaryClosure.close rules (fun premise => premise ∈ support) atom := by
  classical
  induction derived with
  | node premises conclusion rule children ih =>
    rcases rule with ⟨empty, initial⟩ | rule
    · exact ⟨[conclusion], by simpa using initial,
        FinitaryClosure.seeds_le_close rules _ conclusion (List.mem_singleton_self _)⟩
    · let support (premise : A) : List A :=
        if present : premise ∈ premises then Classical.choose (ih premise present) else []
      have supported (premise : A) (present : premise ∈ premises) :
          (∀ value ∈ support premise, value ∈ seed) ∧
            FinitaryClosure.close rules (fun value => value ∈ support premise) premise := by
        simpa only [support, dif_pos present] using Classical.choose_spec (ih premise present)
      refine ⟨premises.flatMap support, ?_, ?_⟩
      · intro value member
        obtain ⟨premise, present, inside⟩ := List.mem_flatMap.mp member
        exact (supported premise present).1 value inside
      · apply FinitaryClosure.close_closed rules _ premises conclusion rule
        intro premise present
        apply FinitaryClosure.close_mono rules ?_ premise (supported premise present).2
        intro value inside
        exact List.mem_flatMap.mpr ⟨premise, present, inside⟩

theorem close_le_response (response : Set A → Set A) (laws : ClosureLaws response) (seed : Set A) :
    {atom | FinitaryClosure.close (rulesOf response) (· ∈ seed) atom} ⊆ response seed := by
  apply FinitaryClosure.close_le (rulesOf response) (laws.1 seed)
  intro premises atom rule children
  exact laws.2.2 seed ▸ laws.2.1 children rule

theorem close_rulesOf_eq (response : Set A → Set A) (laws : ClosureLaws response)
    (support : FinitelySupported response) (seed : Set A) :
    {atom | FinitaryClosure.close (rulesOf response) (· ∈ seed) atom} = response seed := by
  apply Set.Subset.antisymm (close_le_response response laws seed)
  intro atom member
  obtain ⟨premises, contained, rule⟩ := support seed atom member
  exact FinitaryClosure.close_closed (rulesOf response) (· ∈ seed) premises atom rule
    (fun premise present => FinitaryClosure.seeds_le_close _ _ premise (contained premise present))

theorem finite_support [Finite A] (response : Set A → Set A) : FinitelySupported response := by
  classical
  intro seed atom member
  let premises := seed.toFinite.toFinset.toList
  have same : {premise | premise ∈ premises} = seed := by
    ext premise
    simp [premises]
  exact ⟨premises, fun premise present => same ▸ present, same.symm ▸ member⟩

theorem finitary_horn_characterization (response : Set A → Set A) :
    ClosureLaws response ∧ FinitelySupported response ↔
      ∃ rules : List A → A → Prop, ∀ seed atom,
        atom ∈ response seed ↔ FinitaryClosure.close rules (· ∈ seed) atom := by
  constructor
  · rintro ⟨laws, support⟩
    exact ⟨rulesOf response, fun seed atom => by rw [← close_rulesOf_eq response laws support seed]; rfl⟩
  · rintro ⟨rules, realizes⟩
    have responseEq : response = fun seed => {atom | FinitaryClosure.close rules (· ∈ seed) atom} := by
      funext seed
      exact Set.ext (realizes seed)
    refine ⟨?_, ?_⟩
    · rw [responseEq]
      exact ⟨FinitaryClosure.seeds_le_close rules, FinitaryClosure.close_mono rules,
        FinitaryClosure.close_idempotent rules⟩
    · intro seed atom member
      obtain ⟨support, included, derived⟩ := derivation_has_finite_support rules seed atom ((realizes seed atom).mp member)
      exact ⟨support, included, (realizes _ atom).mpr derived⟩

theorem finite_horn_characterization [Finite A] (response : Set A → Set A) :
    ClosureLaws response ↔ ∃ rules : List A → A → Prop, ∀ seed atom,
      atom ∈ response seed ↔ FinitaryClosure.close rules (· ∈ seed) atom := by
  simpa only [finite_support response, and_true] using finitary_horn_characterization response

/-- An actual two-stage derivation, needed because one pass is not closure. -/
inductive ChainAtom where | first | middle | last
  deriving DecidableEq

def chainRules : List ChainAtom → ChainAtom → Prop
  | [.first], .middle => True
  | [.middle], .last => True
  | _, _ => False

theorem chain_derives_last : FinitaryClosure.close chainRules (· = .first) .last := by
  apply FinitaryClosure.close_closed chainRules _ [.middle] .last trivial
  intro premise present
  have same := List.mem_singleton.mp present
  subst premise
  apply FinitaryClosure.close_closed chainRules _ [.first] .middle trivial
  intro premise present
  exact FinitaryClosure.seeds_le_close chainRules _ premise (List.mem_singleton.mp present)

def onePass (seed : Set ChainAtom) : Set ChainAtom := seed ∪
  {atom | ∃ premises, chainRules premises atom ∧ ∀ premise ∈ premises, premise ∈ seed}

theorem one_pass_is_not_idempotent :
    onePass (onePass {.first}) ≠ onePass {.first} := by
  intro same
  have middle : ChainAtom.middle ∈ onePass {.first} := Or.inr ⟨[.first], trivial, by simp⟩
  have last : ChainAtom.last ∈ onePass (onePass {.first}) :=
    Or.inr ⟨[.middle], trivial, by simpa using middle⟩
  rw [same] at last
  rcases last with initial | ⟨premises, rule, available⟩
  · cases initial
  · cases premises with
    | nil => cases rule
    | cons head tail =>
      cases head <;> cases tail <;> simp_all [chainRules]

end Mettapedia.Logic.FiniteHornClosureCharacterization
