import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiMoleculeCongruence

/-!
# Liftings of α-equivalent processes

Processes with the same locally nameless translation and the same skeleton of parallel compositions and restrictions
(`parShape`) lift to molecules with the same scope and related bodies (`lifts_of_piToPattern_eq`): the parallel
components correspond, a restriction is lifted with the same new name, and guarded processes with equal translations
are related.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners

open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open PiCalcInstance (piToPattern piComponents piPar piPar_components piToPattern_open_close_substitute
  freeVars_piToPattern piToPattern_alpha_nu piToPattern_alpha_input piToPattern_alpha_replicate piToPattern_substitute
  piToPattern_noExplicitSubst)

/-! ## Skeletons -/

/-- The skeleton of parallel compositions and restrictions. -/
inductive ParShape where
  | leaf
  | par (left right : ParShape)
  | nu (inner : ParShape)
  deriving DecidableEq

/-- **The skeleton of a process.** -/
def parShape : Process → ParShape
  | .par left right => .par (parShape left) (parShape right)
  | .nu _ body => .nu (parShape body)
  | _ => .leaf

theorem parShape_renameFree : ∀ (process : Process) (old new : Name),
    parShape (process.renameFree old new) = parShape process
  | .nil, _, _ => rfl
  | .output _ _, _, _ => rfl
  | .input _ _ _, _, _ => rfl
  | .replicate _ _ _, _, _ => rfl
  | .par left right, old, new => by
    simp only [Process.renameFree, parShape, parShape_renameFree left, parShape_renameFree right]
  | .nu x body, old, new => by
    simp only [Process.renameFree, parShape]
    split_ifs
    · rfl
    · rw [parShape_renameFree body]

theorem parShape_substitute : (process : Process) → (old new : Name) →
    parShape (process.substitute old new) = parShape process
  | .nil, _, _ => by rw [Process.substitute]
  | .output _ _, _, _ => by rw [Process.substitute]; rfl
  | .input _ _ _, old, new => by rw [Process.substitute]; split_ifs <;> rfl
  | .replicate _ _ _, old, new => by rw [Process.substitute]; split_ifs <;> rfl
  | .par left right, old, new => by
    rw [Process.substitute]
    simp only [parShape, parShape_substitute left, parShape_substitute right]
  | .nu x body, old, new => by
    rw [Process.substitute]
    split_ifs
    · rfl
    · simp only [parShape, parShape_substitute (body.renameFree x (body.freshFor old new)) old new,
        parShape_renameFree]
    · simp only [parShape, parShape_substitute body old new]
termination_by process => process.nodeCount
decreasing_by all_goals simp only [Process.nodeCount, Process.nodeCount_renameFree]; all_goals omega

theorem length_parts_of_parShape : ∀ {first second : Process}, parShape first = parShape second →
    (parts first).length = (parts second).length
  | .par left right, .par left' right', same => by
    simp only [parShape, ParShape.par.injEq] at same
    simp only [parts, List.length_append, length_parts_of_parShape same.1, length_parts_of_parShape same.2]
  | .par _ _, .nil, same | .par _ _, .input _ _ _, same | .par _ _, .output _ _, same
  | .par _ _, .nu _ _, same | .par _ _, .replicate _ _ _, same => by simp [parShape] at same
  | .nil, .par _ _, same | .input _ _ _, .par _ _, same | .output _ _, .par _ _, same
  | .nu _ _, .par _ _, same | .replicate _ _ _, .par _ _, same => by simp [parShape] at same
  | .nil, .nil, _ | .nil, .input _ _ _, _ | .nil, .output _ _, _ | .nil, .nu _ _, _ | .nil, .replicate _ _ _, _
  | .input _ _ _, .nil, _ | .input _ _ _, .input _ _ _, _ | .input _ _ _, .output _ _, _
  | .input _ _ _, .nu _ _, _ | .input _ _ _, .replicate _ _ _, _
  | .output _ _, .nil, _ | .output _ _, .input _ _ _, _ | .output _ _, .output _ _, _
  | .output _ _, .nu _ _, _ | .output _ _, .replicate _ _ _, _
  | .nu _ _, .nil, _ | .nu _ _, .input _ _ _, _ | .nu _ _, .output _ _, _ | .nu _ _, .nu _ _, _
  | .nu _ _, .replicate _ _ _, _
  | .replicate _ _ _, .nil, _ | .replicate _ _ _, .input _ _ _, _ | .replicate _ _ _, .output _ _, _
  | .replicate _ _ _, .nu _ _, _ | .replicate _ _ _, .replicate _ _ _, _ => rfl

theorem freeNames_of_piToPattern_eq {first second : Process} (same : piToPattern first = piToPattern second) :
    first.freeNames = second.freeNames := by
  ext name
  rw [← freeVars_piToPattern, ← freeVars_piToPattern, same]

/-- The translations of the two sides of a parallel composition, from the whole and the skeleton. -/
theorem piToPattern_par_split {left right left' right' : Process}
    (shape : parShape (.par left right) = parShape (.par left' right'))
    (same : piToPattern (.par left right) = piToPattern (.par left' right')) :
    piToPattern left = piToPattern left' ∧ piToPattern right = piToPattern right' := by
  simp only [parShape, ParShape.par.injEq] at shape
  have components := congrArg piComponents same
  rw [piComponents_piToPattern, piComponents_piToPattern] at components
  simp only [parts, List.map_append] at components
  obtain ⟨leftParts, rightParts⟩ := List.append_inj components (by simp [length_parts_of_parShape shape.1])
  have recover : ∀ {process process' : Process}, parShape process = parShape process' →
      (parts process).map piToPattern = (parts process').map piToPattern → piToPattern process = piToPattern process' := by
    intro process process' shapeEq partsEq
    cases process <;> cases process' <;> simp only [parShape, reduceCtorEq] at shapeEq
    case par.par a b c d =>
      rw [piToPattern, piToPattern, piPar_components, piPar_components, piComponents_piToPattern,
        piComponents_piToPattern, piComponents_piToPattern, piComponents_piToPattern]
      simp only [parts, List.map_append] at partsEq
      rw [partsEq]
    all_goals (simp only [parts, List.map_cons, List.map_nil, List.cons.injEq, and_true] at partsEq; first | exact partsEq | rfl)
  exact ⟨recover shape.1 leftParts, recover shape.2 rightParts⟩

/-! ## Inverting a lifting -/

theorem lifts_par_inv {left right : Process} {scope : Finset Name} {body : Multiset Prime}
    (lifts : Lifts (.par left right) scope body) :
    ∃ leftScope rightScope leftBody rightBody, Lifts left leftScope leftBody ∧ Lifts right rightScope rightBody ∧
      Disjoint leftScope rightScope ∧ Disjoint leftScope right.freeNames ∧ Disjoint rightScope left.freeNames ∧
      scope = leftScope ∪ rightScope ∧ body = leftBody + rightBody := by
  cases lifts with
  | guarded guarded => cases guarded
  | par leftLifts rightLifts apart leftFresh rightFresh =>
    exact ⟨_, _, _, _, leftLifts, rightLifts, apart, leftFresh, rightFresh, rfl, rfl⟩

theorem lifts_nu_inv {name : Name} {inner : Process} {scope : Finset Name} {body : Multiset Prime}
    (lifts : Lifts (.nu name inner) scope body) :
    ∃ new rest, Lifts (inner.substitute name new) rest body ∧ new ∉ rest ∧ new ∉ (Process.nu name inner).freeNames ∧
      scope = insert new rest := by
  cases lifts with
  | guarded guarded => cases guarded
  | nu inner' outside fresh => exact ⟨_, _, inner', outside, fresh, rfl⟩

theorem lifts_guarded_inv {process : Process} (guarded : Guarded process) {scope : Finset Name}
    {body : Multiset Prime} (lifts : Lifts process scope body) : scope = ∅ ∧ body = {⟨process, guarded⟩} := by
  cases lifts with
  | nil => cases guarded
  | guarded => exact ⟨rfl, rfl⟩
  | par => cases guarded
  | nu => cases guarded

theorem lifts_nil_inv {scope : Finset Name} {body : Multiset Prime} (lifts : Lifts .nil scope body) :
    scope = ∅ ∧ body = 0 := by
  cases lifts with
  | nil => exact ⟨rfl, rfl⟩
  | guarded guarded => cases guarded

/-! ## Related bodies -/

/-- **Bodies related guarded process by guarded process.** -/
def BodyRel (first second : Multiset Prime) : Prop :=
  ∃ (firstList secondList : List Prime), (firstList : Multiset Prime) = first ∧ (secondList : Multiset Prime) = second ∧
    List.Forall₂ PrimeRel firstList secondList

theorem BodyRel.add {first second first' second' : Multiset Prime} (related : BodyRel first second)
    (related' : BodyRel first' second') : BodyRel (first + first') (second + second') := by
  obtain ⟨list, list', rfl, rfl, pointwise⟩ := related
  obtain ⟨other, other', rfl, rfl, pointwise'⟩ := related'
  exact ⟨list ++ other, list' ++ other', by simp, by simp, List.rel_append pointwise pointwise'⟩

/-- **Guarded processes with equal translations are related.** -/
theorem primeRel_of_piToPattern_eq {process process' : Process} (guarded : Guarded process)
    (guarded' : Guarded process') (same : piToPattern process = piToPattern process') :
    PrimeRel ⟨process, guarded⟩ ⟨process', guarded'⟩ := by
  cases guarded with
  | output x z =>
    cases guarded' <;> simp [piToPattern] at same
    obtain ⟨rfl, rfl⟩ := same
    exact .refl _
  | input x binder inner =>
    cases guarded'
    case input x' binder' inner' =>
      simp only [piToPattern, Pattern.apply.injEq, List.cons.injEq, Pattern.fvar.injEq, Pattern.lambda.injEq,
        true_and, and_true] at same
      obtain ⟨rfl, closed⟩ := same
      exact .input fun payload => congruent_of_piToPattern_eq _ _ _ le_rfl
        (by rw [← piToPattern_open_close_substitute, ← piToPattern_open_close_substitute, closed])
    all_goals simp [piToPattern] at same
  | replicate x binder inner =>
    cases guarded'
    case replicate x' binder' inner' =>
      simp only [piToPattern, Pattern.apply.injEq, List.cons.injEq, Pattern.fvar.injEq, Pattern.lambda.injEq,
        true_and, and_true] at same
      obtain ⟨rfl, closed⟩ := same
      exact .replicate fun payload => congruent_of_piToPattern_eq _ _ _ le_rfl
        (by rw [← piToPattern_open_close_substitute, ← piToPattern_open_close_substitute, closed])
    all_goals simp [piToPattern] at same

/-! ## Liftings of α-equivalent processes -/

/-- **Processes with equal translations and skeletons lift alike**: to the same scope, with related bodies. -/
theorem lifts_of_piToPattern_eq : ∀ (size : ℕ) (first second : Process), first.nodeCount ≤ size →
    parShape first = parShape second → piToPattern first = piToPattern second →
    ∀ {scope : Finset Name} {body : Multiset Prime}, Lifts first scope body →
      ∃ body', Lifts second scope body' ∧ BodyRel body body'
  | 0, first, _, small, _, _, _, _, _ => by cases first <;> simp [Process.nodeCount] at small
  | size + 1, first, second, small, shape, same, scope, body, lifts => by
    cases first with
    | par left right =>
      cases second
      case par left' right' =>
        obtain ⟨leftSame, rightSame⟩ := piToPattern_par_split shape same
        simp only [parShape, ParShape.par.injEq] at shape
        obtain ⟨leftScope, rightScope, leftBody, rightBody, leftLifts, rightLifts, apart, leftFresh, rightFresh,
          rfl, rfl⟩ := lifts_par_inv lifts
        simp only [Process.nodeCount] at small
        obtain ⟨leftBody', leftLifts', leftRelated⟩ :=
          lifts_of_piToPattern_eq size left left' (by omega) shape.1 leftSame leftLifts
        obtain ⟨rightBody', rightLifts', rightRelated⟩ :=
          lifts_of_piToPattern_eq size right right' (by omega) shape.2 rightSame rightLifts
        refine ⟨leftBody' + rightBody', .par leftLifts' rightLifts' apart ?_ ?_, leftRelated.add rightRelated⟩
        · rw [← freeNames_of_piToPattern_eq rightSame]; exact leftFresh
        · rw [← freeNames_of_piToPattern_eq leftSame]; exact rightFresh
      all_goals simp [parShape] at shape
    | nil =>
      cases second <;> simp [piToPattern, piPar_components] at same
      obtain ⟨rfl, rfl⟩ := lifts_nil_inv lifts
      exact ⟨0, .nil, [], [], rfl, rfl, .nil⟩
    | output x z =>
      cases second <;> simp [piToPattern, piPar_components] at same
      obtain ⟨rfl, rfl⟩ := same
      obtain ⟨rfl, rfl⟩ := lifts_guarded_inv (.output x z) lifts
      exact ⟨_, .guarded (.output x z), [_], [_], rfl, rfl, .cons (.refl _) .nil⟩
    | input x binder inner =>
      cases second
      case input x' binder' inner' =>
        obtain ⟨rfl, rfl⟩ := lifts_guarded_inv (.input x binder inner) lifts
        exact ⟨_, .guarded (.input x' binder' inner'), [_], [_], rfl, rfl,
          .cons (primeRel_of_piToPattern_eq (.input _ _ _) (.input _ _ _) same) .nil⟩
      all_goals simp [piToPattern, piPar_components] at same
    | replicate x binder inner =>
      cases second
      case replicate x' binder' inner' =>
        obtain ⟨rfl, rfl⟩ := lifts_guarded_inv (.replicate x binder inner) lifts
        exact ⟨_, .guarded (.replicate x' binder' inner'), [_], [_], rfl, rfl,
          .cons (primeRel_of_piToPattern_eq (.replicate _ _ _) (.replicate _ _ _) same) .nil⟩
      all_goals simp [piToPattern, piPar_components] at same
    | nu name inner =>
      cases second
      case nu name' inner' =>
        simp only [parShape, ParShape.nu.injEq] at shape
        simp only [piToPattern, Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, true_and,
          and_true] at same
        obtain ⟨new, rest, innerLifts, outside, fresh, rfl⟩ := lifts_nu_inv lifts
        have renamed : piToPattern (inner.substitute name new) = piToPattern (inner'.substitute name' new) := by
          rw [← piToPattern_open_close_substitute, ← piToPattern_open_close_substitute, same]
        simp only [Process.nodeCount] at small
        obtain ⟨body', innerLifts', related⟩ := lifts_of_piToPattern_eq size _ _
          (by rw [nodeCount_substitute]; omega) (by rw [parShape_substitute, parShape_substitute, shape]) renamed
          innerLifts
        refine ⟨body', .nu innerLifts' outside ?_, related⟩
        have sameFree : (Process.nu name inner).freeNames = (Process.nu name' inner').freeNames :=
          freeNames_of_piToPattern_eq (by simp only [piToPattern, same])
        rw [← sameFree]
        exact fresh
      all_goals simp [parShape] at shape

/-! ## Bodies up to congruence -/

/-- **One step of body congruence**: a guarded process replaced with a related one, or a replicated input unfolded. -/
inductive BodyStep : Multiset Prime → Multiset Prime → Prop
  | prime {body : Multiset Prime} {first second : Prime} :
      PrimeRel first second → BodyStep (body + {first}) (body + {second})
  | unfold {body : Multiset Prime} {x binder : Name} {inner : Process} :
      BodyStep (body + {server x binder inner}) (body + {copy x binder inner, server x binder inner})

/-- **Body congruence.** -/
abbrev BodyEquiv : Multiset Prime → Multiset Prime → Prop := Relation.EqvGen BodyStep

theorem BodyStep.add {first second : Multiset Prime} (step : BodyStep first second) (extra : Multiset Prime) :
    BodyStep (first + extra) (second + extra) := by
  cases step with
  | @prime body _ _ related =>
    have := BodyStep.prime (body := body + extra) related
    rwa [add_right_comm, add_right_comm body extra] at this
  | @unfold body x binder inner =>
    have := BodyStep.unfold (body := body + extra) (x := x) (binder := binder) (inner := inner)
    rwa [add_right_comm, add_right_comm body extra] at this

theorem BodyEquiv.add {first second : Multiset Prime} (equivalent : BodyEquiv first second) (extra : Multiset Prime) :
    BodyEquiv (first + extra) (second + extra) := by
  induction equivalent with
  | rel _ _ step => exact .rel _ _ (step.add extra)
  | refl => exact .refl _
  | symm _ _ _ holds => exact .symm _ _ holds
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem BodyEquiv.add_both {first second first' second' : Multiset Prime} (equivalent : BodyEquiv first second)
    (equivalent' : BodyEquiv first' second') : BodyEquiv (first + first') (second + second') :=
  .trans _ _ _ (equivalent.add first') (by
    rw [add_comm second first', add_comm second second']
    exact equivalent'.add second)

theorem BodyRel.bodyEquiv {first second : Multiset Prime} (related : BodyRel first second) :
    BodyEquiv first second := by
  obtain ⟨list, list', rfl, rfl, pointwise⟩ := related
  induction pointwise with
  | nil => exact .refl _
  | @cons head head' tail tail' headRel _ holds =>
    have step : BodyStep (↑tail + {head}) (↑tail + {head'}) := .prime headRel
    have first : BodyEquiv (↑(head :: tail) : Multiset Prime) (↑tail + {head'}) := by
      rw [← Multiset.cons_coe, ← Multiset.singleton_add, add_comm]
      exact .rel _ _ step
    refine .trans _ _ _ first ?_
    rw [← Multiset.cons_coe, ← Multiset.singleton_add, add_comm ({head'} : Multiset Prime)]
    exact holds.add {head'}

theorem BodyStep.bodyNames {first second : Multiset Prime} (step : BodyStep first second) (scope scope' : Finset Name) :
    (Molecule.mk scope first).bodyNames = (Molecule.mk scope' second).bodyNames := by
  cases step with
  | prime related =>
    rw [bodyNames_scope scope scope']
    exact bodyNames_replace (PrimeRel.congruent related).freeNames_eq
  | unfold =>
    rw [bodyNames_scope scope scope']
    exact (bodyNames_unfold _ _ _ _ _).symm

theorem BodyEquiv.bodyNames {first second : Multiset Prime} (equivalent : BodyEquiv first second)
    (scope scope' : Finset Name) : (Molecule.mk scope first).bodyNames = (Molecule.mk scope' second).bodyNames := by
  induction equivalent generalizing scope scope' with
  | rel _ _ step => exact step.bodyNames scope scope'
  | refl => rfl
  | symm _ _ _ holds => exact (holds scope' scope).symm
  | trans _ _ _ _ _ first second => exact (first scope scope).trans (second scope scope')

theorem BodyEquiv.molEquiv {first second : Multiset Prime} (equivalent : BodyEquiv first second)
    (scope : Finset Name) : MolEquiv ⟨scope, first⟩ ⟨scope, second⟩ := by
  induction equivalent with
  | rel _ _ step =>
    cases step with
    | prime related => exact .rel _ _ (.prime related)
    | unfold => exact .rel _ _ .unfold
  | refl => exact .refl _
  | symm _ _ _ holds => exact .symm _ _ holds
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

/-! ## Trimmed molecules -/

/-- **A molecule trimmed** of the restricted names its body does not use. -/
def Molecule.trim (molecule : Molecule) : Molecule := ⟨molecule.scope ∩ molecule.bodyNames, molecule.body⟩

/-- **A molecule is congruent to its trimming.** -/
theorem molEquiv_trim : ∀ (count : ℕ) (molecule : Molecule), (molecule.scope \ molecule.bodyNames).card ≤ count →
    MolEquiv molecule molecule.trim
  | 0, molecule, small => by
    have empty : molecule.scope \ molecule.bodyNames = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp small)
    have same : molecule.scope ∩ molecule.bodyNames = molecule.scope := by
      ext name
      constructor
      · exact fun inside => (Finset.mem_inter.mp inside).1
      · intro inside
        by_contra outside
        have : name ∈ molecule.scope \ molecule.bodyNames := Finset.mem_sdiff.mpr ⟨inside, fun used =>
          outside (Finset.mem_inter.mpr ⟨inside, used⟩)⟩
        rw [empty] at this
        exact absurd this (Finset.notMem_empty _)
    simp only [Molecule.trim, same]
    exact .refl _
  | count + 1, molecule, small => by
    by_cases empty : molecule.scope \ molecule.bodyNames = ∅
    · exact molEquiv_trim 0 molecule (by rw [empty]; simp)
    obtain ⟨name, unusedMem⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    obtain ⟨restricted, unused⟩ := Finset.mem_sdiff.mp unusedMem
    have step : MolStep molecule ⟨molecule.scope.erase name, molecule.body⟩ := by
      have := MolStep.garbage (scope := molecule.scope.erase name) (body := molecule.body) (name := name)
        (Finset.notMem_erase _ _) unused
      rwa [Finset.insert_erase restricted] at this
    have smaller : ((molecule.scope.erase name) \ (Molecule.mk (molecule.scope.erase name) molecule.body).bodyNames).card
        ≤ count := by
      rw [← bodyNames_scope molecule.scope (molecule.scope.erase name)]
      have : (molecule.scope.erase name) \ molecule.bodyNames = (molecule.scope \ molecule.bodyNames).erase name := by
        ext other
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        tauto
      rw [this, Finset.card_erase_of_mem unusedMem]
      omega
    have rest := molEquiv_trim count _ smaller
    have trimEq : (Molecule.mk (molecule.scope.erase name) molecule.body).trim = molecule.trim := by
      simp only [Molecule.trim]
      congr 1
      ext other
      simp only [Finset.mem_inter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, inside⟩, used⟩
        exact ⟨inside, by rwa [bodyNames_scope _ molecule.scope] at used⟩
      · rintro ⟨inside, used⟩
        refine ⟨⟨fun same => unused (same ▸ used), inside⟩, ?_⟩
        rwa [bodyNames_scope _ molecule.scope]
    rw [trimEq] at rest
    exact .trans _ _ _ (.rel _ _ step) rest

/-! ## Liftings related -/

/-- **Liftings related**: every lifting of the first process has one of the second with the same trimmed scope and a
congruent body, whose restricted names are the first's or avoid any given finite set. -/
def LiftsRel (first second : Process) : Prop :=
  ∀ (avoid : Finset Name) {scope : Finset Name} {body : Multiset Prime}, Lifts first scope body →
    ∃ scope' body', Lifts second scope' body' ∧
      (Molecule.mk scope body).trim.scope = (Molecule.mk scope' body').trim.scope ∧ BodyEquiv body body' ∧
      ∀ name ∈ scope', name ∈ scope ∨ name ∉ avoid

theorem LiftsRel.refl (process : Process) : LiftsRel process process := fun _ _ _ lifts =>
  ⟨_, _, lifts, rfl, .refl _, fun _ inside => Or.inl inside⟩

theorem LiftsRel.trans {first second third : Process} (firstSecond : LiftsRel first second)
    (secondThird : LiftsRel second third) : LiftsRel first third := fun avoid scope body lifts => by
  obtain ⟨scope', body', lifts', trimmed, bodies, names⟩ := firstSecond avoid lifts
  obtain ⟨scope'', body'', lifts'', trimmed', bodies', names'⟩ := secondThird avoid lifts'
  refine ⟨scope'', body'', lifts'', trimmed.trans trimmed', .trans _ _ _ bodies bodies', fun name inside => ?_⟩
  rcases names' name inside with old | outside
  · exact names name old
  · exact Or.inr outside

/-- **Equal translations and skeletons relate the liftings**, with the same scope. -/
theorem liftsRel_of_piToPattern_eq {first second : Process} (shape : parShape first = parShape second)
    (same : piToPattern first = piToPattern second) : LiftsRel first second := fun _ scope body lifts => by
  obtain ⟨body', lifts', related⟩ := lifts_of_piToPattern_eq _ first second le_rfl shape same lifts
  refine ⟨scope, body', lifts', ?_, related.bodyEquiv, fun _ inside => Or.inl inside⟩
  simp only [Molecule.trim]
  rw [related.bodyEquiv.bodyNames scope scope]

theorem parShape_substList : ∀ (substitutions : List (Name × Name)) (process : Process),
    parShape (substList substitutions process) = parShape process
  | [], _ => rfl
  | (old, new) :: rest, process => by
    simp only [substList]
    rw [parShape_substList rest, parShape_substitute]

theorem substitute_nu_shape (binder : Name) (inner : Process) (old new : Name) :
    ∃ binder' inner', (Process.nu binder inner).substitute old new = .nu binder' inner' := by
  rw [Process.substitute]
  split_ifs <;> exact ⟨_, _, rfl⟩

theorem substList_nu_shape : ∀ (substitutions : List (Name × Name)) (binder : Name) (inner : Process),
    ∃ binder' inner', substList substitutions (.nu binder inner) = .nu binder' inner'
  | [], binder, inner => ⟨binder, inner, rfl⟩
  | (old, new) :: rest, binder, inner => by
    obtain ⟨binder', inner', shape⟩ := substitute_nu_shape binder inner old new
    simp only [substList, shape]
    exact substList_nu_shape rest binder' inner'

/-- **Under a substituted restriction, opened at a fresh name**, the body is the body substituted with the binder
renamed to that name: same translation, same skeleton. -/
theorem substList_nu_open {substitutions : List (Name × Name)} {binder fresh : Name} {inner : Process}
    (notFree : fresh ∉ inner.freeNames) (away : fresh ∉ substNames substitutions) {binder' : Name} {inner' : Process}
    (shape : substList substitutions (.nu binder inner) = .nu binder' inner') :
    piToPattern (inner'.substitute binder' fresh) = piToPattern (substList ((binder, fresh) :: substitutions) inner) ∧
      parShape (inner'.substitute binder' fresh) = parShape (substList ((binder, fresh) :: substitutions) inner) := by
  have images : piToPattern (Process.nu binder' inner') =
      piToPattern (Process.nu fresh (substList ((binder, fresh) :: substitutions) inner)) := by
    rw [← shape, show substList ((binder, fresh) :: substitutions) inner =
      substList substitutions (inner.substitute binder fresh) from rfl, ← substList_nu_fresh _ _ _ away,
      piToPattern_substList, piToPattern_substList, piToPattern_alpha_nu binder fresh inner notFree]
  simp only [piToPattern, Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, true_and, and_true] at images
  constructor
  · rw [← piToPattern_open_close_substitute, images, piToPattern_open_close_substitute, substitute_self]
  · have shapes := congrArg parShape shape
    rw [parShape_substList] at shapes
    simp only [parShape, ParShape.nu.injEq] at shapes
    rw [parShape_substitute, parShape_substList, ← shapes]

/-! ## Structural laws relate liftings: parallel composition -/

theorem trim_scope_add (leftScope rightScope : Finset Name) (leftBody rightBody : Multiset Prime)
    (leftApart : Disjoint leftScope (Molecule.mk ∅ rightBody).bodyNames)
    (rightApart : Disjoint rightScope (Molecule.mk ∅ leftBody).bodyNames) :
    (Molecule.mk (leftScope ∪ rightScope) (leftBody + rightBody)).trim.scope =
      (Molecule.mk leftScope leftBody).trim.scope ∪ (Molecule.mk rightScope rightBody).trim.scope := by
  ext name
  simp only [Molecule.trim, Finset.mem_inter, Finset.mem_union, mem_bodyNames_add]
  rw [bodyNames_scope leftScope ∅, bodyNames_scope rightScope ∅]
  constructor
  · rintro ⟨inLeft | inRight, usedLeft | usedRight⟩
    · exact Or.inl ⟨inLeft, usedLeft⟩
    · exact absurd usedRight (Finset.disjoint_left.mp leftApart inLeft)
    · exact absurd usedLeft (Finset.disjoint_left.mp rightApart inRight)
    · exact Or.inr ⟨inRight, usedRight⟩
  · rintro (⟨inLeft, used⟩ | ⟨inRight, used⟩)
    · exact ⟨Or.inl inLeft, Or.inl used⟩
    · exact ⟨Or.inr inRight, Or.inr used⟩

/-- Restricted names of one side are apart from the other's body. -/
theorem apart_of_lifts {scope otherScope : Finset Name} {other : Process} {otherBody : Multiset Prime}
    (otherLifts : Lifts other otherScope otherBody) (scopeApart : Disjoint scope otherScope)
    (scopeFresh : Disjoint scope other.freeNames) : Disjoint scope (Molecule.mk ∅ otherBody).bodyNames := by
  refine Finset.disjoint_left.mpr fun name restricted inside => ?_
  rw [bodyNames_scope ∅ otherScope] at inside
  rcases Finset.mem_union.mp (lifts_bodyNames otherLifts inside) with free | theirs
  · exact Finset.disjoint_left.mp scopeFresh restricted free
  · exact Finset.disjoint_left.mp scopeApart restricted theirs

theorem liftsRel_par_comm (left right : Process) : LiftsRel (.par left right) (.par right left) := by
  intro avoid scope body lifts
  obtain ⟨leftScope, rightScope, leftBody, rightBody, leftLifts, rightLifts, apart, leftFresh, rightFresh, rfl, rfl⟩ :=
    lifts_par_inv lifts
  refine ⟨rightScope ∪ leftScope, rightBody + leftBody, .par rightLifts leftLifts apart.symm rightFresh leftFresh, ?_,
    by rw [add_comm]; exact .refl _, fun name inside => Or.inl (by rwa [Finset.union_comm])⟩
  rw [Finset.union_comm rightScope, add_comm rightBody]

theorem liftsRel_par_assoc (first second third : Process) :
    LiftsRel (.par (.par first second) third) (.par first (.par second third)) := by
  intro avoid scope body lifts
  obtain ⟨outerScope, thirdScope, outerBody, thirdBody, outerLifts, thirdLifts, outerApart, outerFresh, thirdFresh,
    rfl, rfl⟩ := lifts_par_inv lifts
  obtain ⟨firstScope, secondScope, firstBody, secondBody, firstLifts, secondLifts, innerApart, firstFresh, secondFresh,
    rfl, rfl⟩ := lifts_par_inv outerLifts
  simp only [Process.freeNames] at thirdFresh firstFresh secondFresh outerFresh ⊢
  have inner : Lifts (.par second third) (secondScope ∪ thirdScope) (secondBody + thirdBody) :=
    .par secondLifts thirdLifts (outerApart.mono_left Finset.subset_union_right)
      (outerFresh.mono_left Finset.subset_union_right) (thirdFresh.mono_right Finset.subset_union_right)
  refine ⟨firstScope ∪ (secondScope ∪ thirdScope), firstBody + (secondBody + thirdBody),
    .par firstLifts inner ?_ ?_ ?_, by rw [Finset.union_assoc, add_assoc], by rw [add_assoc]; exact .refl _,
    fun name inside => Or.inl (by rwa [← Finset.union_assoc] at inside)⟩
  · exact Finset.disjoint_union_right.mpr ⟨innerApart, outerApart.mono_left Finset.subset_union_left⟩
  · simp only [Process.freeNames]
    exact Finset.disjoint_union_right.mpr ⟨firstFresh, outerFresh.mono_left Finset.subset_union_left⟩
  · exact Finset.disjoint_union_left.mpr ⟨secondFresh, thirdFresh.mono_right Finset.subset_union_left⟩

theorem liftsRel_par_assoc' (first second third : Process) :
    LiftsRel (.par first (.par second third)) (.par (.par first second) third) := by
  intro avoid scope body lifts
  obtain ⟨firstScope, innerScope, firstBody, innerBody, firstLifts, innerLifts, outerApart, firstFresh, innerFresh,
    rfl, rfl⟩ := lifts_par_inv lifts
  obtain ⟨secondScope, thirdScope, secondBody, thirdBody, secondLifts, thirdLifts, innerApart, secondFresh, thirdFresh,
    rfl, rfl⟩ := lifts_par_inv innerLifts
  simp only [Process.freeNames] at thirdFresh firstFresh secondFresh innerFresh ⊢
  have outer : Lifts (.par first second) (firstScope ∪ secondScope) (firstBody + secondBody) :=
    .par firstLifts secondLifts (outerApart.mono_right Finset.subset_union_left)
      (firstFresh.mono_right Finset.subset_union_left) (innerFresh.mono_left Finset.subset_union_left)
  refine ⟨(firstScope ∪ secondScope) ∪ thirdScope, (firstBody + secondBody) + thirdBody,
    .par outer thirdLifts ?_ ?_ ?_, by rw [Finset.union_assoc, add_assoc], by rw [add_assoc]; exact .refl _,
    fun name inside => Or.inl (by rwa [Finset.union_assoc] at inside)⟩
  · exact Finset.disjoint_union_left.mpr ⟨outerApart.mono_right Finset.subset_union_right, innerApart⟩
  · exact Finset.disjoint_union_left.mpr ⟨firstFresh.mono_right Finset.subset_union_right, secondFresh⟩
  · simp only [Process.freeNames]
    exact Finset.disjoint_union_right.mpr ⟨innerFresh.mono_left Finset.subset_union_right, thirdFresh⟩

theorem liftsRel_par_nil_left (process : Process) : LiftsRel (.par .nil process) process := by
  intro avoid scope body lifts
  obtain ⟨nilScope, scope', nilBody, body', nilLifts, lifts', _, _, _, rfl, rfl⟩ := lifts_par_inv lifts
  obtain ⟨rfl, rfl⟩ := lifts_nil_inv nilLifts
  exact ⟨scope', body', lifts', by rw [Finset.empty_union, zero_add], by rw [zero_add]; exact .refl _,
    fun name inside => Or.inl (by rwa [Finset.empty_union])⟩

theorem liftsRel_par_nil_left' (process : Process) : LiftsRel process (.par .nil process) :=
  fun avoid scope body lifts =>
    ⟨∅ ∪ scope, 0 + body, .par .nil lifts (Finset.disjoint_empty_left _) (Finset.disjoint_empty_left _)
      (by simp [Process.freeNames]), by rw [Finset.empty_union, zero_add], by rw [zero_add]; exact .refl _,
      fun name inside => Or.inl (by rwa [Finset.empty_union] at inside)⟩

theorem liftsRel_par_nil_right (process : Process) : LiftsRel (.par process .nil) process := by
  intro avoid scope body lifts
  obtain ⟨scope', nilScope, body', nilBody, lifts', nilLifts, _, _, _, rfl, rfl⟩ := lifts_par_inv lifts
  obtain ⟨rfl, rfl⟩ := lifts_nil_inv nilLifts
  exact ⟨scope', body', lifts', by rw [Finset.union_empty, add_zero], by rw [add_zero]; exact .refl _,
    fun name inside => Or.inl (by rwa [Finset.union_empty])⟩

theorem liftsRel_par_nil_right' (process : Process) : LiftsRel process (.par process .nil) :=
  fun avoid scope body lifts =>
    ⟨scope ∪ ∅, body + 0, .par lifts .nil (Finset.disjoint_empty_right _) (by simp [Process.freeNames])
      (Finset.disjoint_empty_left _), by rw [Finset.union_empty, add_zero], by rw [add_zero]; exact .refl _,
      fun name inside => Or.inl (by rwa [Finset.union_empty] at inside)⟩

/-- **Parallel composition keeps related liftings.** -/
theorem liftsRel_par {left left' right right' : Process} (leftRel : LiftsRel left left') (rightRel : LiftsRel right right')
    (leftNames : left.freeNames = left'.freeNames) (rightNames : right.freeNames = right'.freeNames) :
    LiftsRel (.par left right) (.par left' right') := by
  intro avoid scope body lifts
  obtain ⟨leftScope, rightScope, leftBody, rightBody, leftLifts, rightLifts, apart, leftFresh, rightFresh, rfl, rfl⟩ :=
    lifts_par_inv lifts
  obtain ⟨leftScope', leftBody', leftLifts', leftTrim, leftBodies, leftNew⟩ :=
    leftRel (avoid ∪ rightScope ∪ right.freeNames) leftLifts
  obtain ⟨rightScope', rightBody', rightLifts', rightTrim, rightBodies, rightNew⟩ :=
    rightRel (avoid ∪ leftScope' ∪ left.freeNames) rightLifts
  have leftOld : ∀ name ∈ leftScope', name ∉ rightScope ∧ name ∉ right.freeNames := by
    intro name inside
    rcases leftNew name inside with old | outside
    · exact ⟨Finset.disjoint_left.mp apart old, Finset.disjoint_left.mp leftFresh old⟩
    · simp only [Finset.mem_union, not_or] at outside
      exact ⟨outside.1.2, outside.2⟩
  have rightOld : ∀ name ∈ rightScope', name ∉ leftScope' ∧ name ∉ left.freeNames := by
    intro name inside
    rcases rightNew name inside with old | outside
    · exact ⟨fun mine => (leftOld name mine).1 old, Finset.disjoint_left.mp rightFresh old⟩
    · simp only [Finset.mem_union, not_or] at outside
      exact ⟨outside.1.2, outside.2⟩
  have apart' : Disjoint leftScope' rightScope' :=
    Finset.disjoint_left.mpr fun name mine theirs => (rightOld name theirs).1 mine
  have leftFresh' : Disjoint leftScope' right'.freeNames := by
    rw [← rightNames]; exact Finset.disjoint_left.mpr fun name mine => (leftOld name mine).2
  have rightFresh' : Disjoint rightScope' left'.freeNames := by
    rw [← leftNames]; exact Finset.disjoint_left.mpr fun name mine => (rightOld name mine).2
  refine ⟨leftScope' ∪ rightScope', leftBody' + rightBody', .par leftLifts' rightLifts' apart' leftFresh' rightFresh',
    ?_, leftBodies.add_both rightBodies, fun name inside => ?_⟩
  · rw [trim_scope_add _ _ _ _ (apart_of_lifts rightLifts apart leftFresh)
      (apart_of_lifts leftLifts apart.symm rightFresh),
      trim_scope_add _ _ _ _ (apart_of_lifts rightLifts' apart' leftFresh')
        (apart_of_lifts leftLifts' apart'.symm rightFresh'), leftTrim, rightTrim]
  · rcases Finset.mem_union.mp inside with mine | theirs
    · rcases leftNew name mine with old | outside
      · exact Or.inl (Finset.mem_union_left _ old)
      · exact Or.inr fun inAvoid => outside (Finset.mem_union_left _ (Finset.mem_union_left _ inAvoid))
    · rcases rightNew name theirs with old | outside
      · exact Or.inl (Finset.mem_union_right _ old)
      · exact Or.inr fun inAvoid => outside (Finset.mem_union_left _ (Finset.mem_union_left _ inAvoid))

/-- **Related guarded processes relate their liftings.** -/
theorem liftsRel_guarded {first second : Prime} (related : PrimeRel first second) : LiftsRel first.1 second.1 := by
  intro avoid scope body lifts
  obtain ⟨rfl, rfl⟩ := lifts_guarded_inv first.2 lifts
  refine ⟨∅, {second}, .guarded second.2, by simp [Molecule.trim], ?_, fun name inside => by simp at inside⟩
  have step : BodyStep (0 + {first}) (0 + {second}) := .prime related
  simpa using (Relation.EqvGen.rel _ _ step : BodyEquiv (0 + {first}) (0 + {second}))

/-! ## Structural laws relate liftings: restriction -/

theorem substList_append : ∀ (first second : List (Name × Name)) (process : Process),
    substList (first ++ second) process = substList second (substList first process)
  | [], _, _ => rfl
  | (old, new) :: rest, second, process => by
    simp only [List.cons_append, substList]
    exact substList_append rest second _

/-- **A substituted restriction opened at any name** is the body substituted with the binder renamed to it, through a
fresh intermediate name. -/
theorem substList_nu_open_any {substitutions : List (Name × Name)} {binder : Name} {inner : Process}
    {binder' : Name} {inner' : Process} (shape : substList substitutions (.nu binder inner) = .nu binder' inner')
    {new fresh : Name} (notFree : fresh ∉ inner.freeNames) (away : fresh ∉ substNames substitutions) :
    piToPattern (inner'.substitute binder' new) =
        piToPattern (substList (((binder, fresh) :: substitutions) ++ [(fresh, new)]) inner) ∧
      parShape (inner'.substitute binder' new) =
        parShape (substList (((binder, fresh) :: substitutions) ++ [(fresh, new)]) inner) := by
  obtain ⟨images, shapes⟩ := substList_nu_open notFree away shape
  have freshOut : isFresh fresh (closeFVar 0 binder' (piToPattern inner')) = true := by
    rw [isFresh_iff_not_mem]
    intro inside
    obtain ⟨different, present⟩ := (freeVars_closeFVar_iff _ _ _ _).mp inside
    have inNu : fresh ∈ (Process.nu binder' inner').freeNames := by
      simp only [Process.freeNames, Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨(freeVars_piToPattern inner' fresh).mp present, different⟩
    rw [← shape] at inNu
    rcases Finset.mem_union.mp (freeNames_substList substitutions _ inNu) with free | named
    · simp only [Process.freeNames, Finset.mem_sdiff] at free
      exact notFree free.1
    · exact away named
  have opened : piToPattern (inner'.substitute binder' new) =
      applySubst [(fresh, .fvar new)] (piToPattern (inner'.substitute binder' fresh)) := by
    rw [← piToPattern_open_close_substitute inner' binder' fresh, ← piToPattern_open_close_substitute inner' binder' new]
    exact (subst_intro freshOut (noExplicitSubst_closeFVar (piToPattern_noExplicitSubst inner'))).symm
  constructor
  · rw [opened, images, substList_append,
      show ∀ process : Process, substList [(fresh, new)] process = process.substitute fresh new from fun _ => rfl,
      piToPattern_substitute]
  · rw [parShape_substitute, parShape_substList] at shapes
    rw [parShape_substitute, substList_append, parShape_substList, parShape_substList]
    exact shapes

theorem freeNames_substList_congruent {first second : Process} (congruence : first ≡ second)
    (substitutions : List (Name × Name)) :
    (substList substitutions first).freeNames = (substList substitutions second).freeNames :=
  (congruent_substList congruence substitutions).freeNames_eq

/-- **A restriction keeps related liftings**, under every substitution. -/
theorem liftsRel_nu {binder : Name} {inner inner' : Process} (congruence : inner ≡ inner')
    (innerRel : ∀ substitutions, LiftsRel (substList substitutions inner) (substList substitutions inner'))
    (substitutions : List (Name × Name)) :
    LiftsRel (substList substitutions (.nu binder inner)) (substList substitutions (.nu binder inner')) := by
  obtain ⟨b, body, shape⟩ := substList_nu_shape substitutions binder inner
  obtain ⟨b', body', shape'⟩ := substList_nu_shape substitutions binder inner'
  intro avoid scope lifted lifts
  rw [shape] at lifts
  obtain ⟨new, rest, innerLifts, newOut, newFree, rfl⟩ := lifts_nu_inv lifts
  obtain ⟨fresh, freshNot⟩ := exists_fresh (inner.freeNames ∪ inner'.freeNames ∪ substNames substitutions)
  simp only [Finset.mem_union, not_or] at freshNot
  obtain ⟨⟨notInner, notInner'⟩, away⟩ := freshNot
  obtain ⟨images, shapes⟩ := substList_nu_open_any (new := new) shape notInner away
  obtain ⟨images', shapes'⟩ := substList_nu_open_any (new := new) shape' notInner' away
  obtain ⟨body₀, lifts₀, related₀⟩ := lifts_of_piToPattern_eq _ _ _ le_rfl shapes images innerLifts
  obtain ⟨rest', body₁, lifts₁, trim₁, bodies₁, names₁⟩ := innerRel _ (insert new avoid) lifts₀
  obtain ⟨body₂, lifts₂, related₂⟩ := lifts_of_piToPattern_eq _ _ _ le_rfl shapes'.symm images'.symm lifts₁
  have newOut' : new ∉ rest' := fun inside =>
    (names₁ new inside).elim newOut fun outside => outside (Finset.mem_insert_self _ _)
  have newFree' : new ∉ (Process.nu b' body').freeNames := by
    rw [← shape', ← freeNames_substList_congruent (.nu_cong binder inner inner' congruence), shape]
    exact newFree
  have names₀ := related₀.bodyEquiv.bodyNames rest rest
  have names₂ := related₂.bodyEquiv.bodyNames rest' rest'
  have namesMid := bodies₁.bodyNames rest rest'
  refine ⟨insert new rest', body₂, by rw [shape']; exact .nu lifts₂ newOut' newFree', ?_,
    .trans _ _ _ related₀.bodyEquiv (.trans _ _ _ bodies₁ related₂.bodyEquiv), fun name inside => ?_⟩
  · simp only [Molecule.trim] at trim₁ ⊢
    ext name
    simp only [Finset.mem_inter, Finset.mem_insert]
    rw [bodyNames_scope (insert new rest) rest, bodyNames_scope (insert new rest') rest', names₀, ← names₂,
      ← namesMid]
    by_cases isNew : name = new
    · simp [isNew]
    · have := congrArg (name ∈ ·) trim₁
      simp only [Finset.mem_inter, eq_iff_iff] at this
      simp only [isNew, false_or]
      rw [← namesMid] at this
      exact this
  · rcases Finset.mem_insert.mp inside with rfl | old
    · exact Or.inl (Finset.mem_insert_self _ _)
    · rcases names₁ name old with mine | outside
      · exact Or.inl (Finset.mem_insert_of_mem mine)
      · exact Or.inr fun inAvoid => outside (Finset.mem_insert_of_mem inAvoid)

/-! ## Structural laws relate liftings: α-conversion, guards, replication, inert restriction -/

theorem liftsRel_substList_of_piToPattern_eq (substitutions : List (Name × Name)) {first second : Process}
    (shape : parShape first = parShape second) (same : piToPattern first = piToPattern second) :
    LiftsRel (substList substitutions first) (substList substitutions second) :=
  liftsRel_of_piToPattern_eq (by rw [parShape_substList, parShape_substList, shape])
    (by rw [piToPattern_substList, piToPattern_substList, same])

/-- Single guarded processes with congruent bodies relate their liftings. -/
theorem liftsRel_guarded' {first second : Prime} (equivalent : BodyEquiv {first} {second}) :
    LiftsRel first.1 second.1 := by
  intro avoid scope body lifts
  obtain ⟨rfl, rfl⟩ := lifts_guarded_inv first.2 lifts
  refine ⟨∅, {second}, .guarded second.2, by simp [Molecule.trim], equivalent, fun name inside => by simp at inside⟩

theorem bodyEquiv_single {first second : Prime} (related : PrimeRel first second) : BodyEquiv {first} {second} := by
  have step : BodyStep (0 + {first}) (0 + {second}) := .prime related
  simpa using (Relation.EqvGen.rel _ _ step : BodyEquiv (0 + {first}) (0 + {second}))

theorem substList_guarded {process : Process} (guarded : Guarded process) :
    ∀ substitutions : List (Name × Name), Guarded (substList substitutions process)
  | [] => guarded
  | (old, new) :: rest => substList_guarded (guarded_substitute guarded old new) rest

/-- A substituted input is related to the input with its binder renamed fresh first. -/
theorem primeRel_substList_input (substitutions : List (Name × Name)) (x binder fresh : Name) (inner : Process)
    (notFree : fresh ∉ inner.freeNames) (away : fresh ∉ substNames substitutions) :
    PrimeRel ⟨substList substitutions (.input x binder inner), substList_guarded (.input _ _ _) substitutions⟩
      ⟨.input (substName substitutions x) fresh (substList ((binder, fresh) :: substitutions) inner), .input _ _ _⟩ := by
  refine primeRel_of_piToPattern_eq _ _ ?_
  rw [show substList ((binder, fresh) :: substitutions) inner = substList substitutions (inner.substitute binder fresh)
    from rfl, ← substList_input_fresh _ _ _ _ away, piToPattern_substList, piToPattern_substList,
    piToPattern_alpha_input x binder fresh inner notFree]

theorem primeRel_substList_replicate (substitutions : List (Name × Name)) (x binder fresh : Name) (inner : Process)
    (notFree : fresh ∉ inner.freeNames) (away : fresh ∉ substNames substitutions) :
    PrimeRel ⟨substList substitutions (.replicate x binder inner), substList_guarded (.replicate _ _ _) substitutions⟩
      ⟨.replicate (substName substitutions x) fresh (substList ((binder, fresh) :: substitutions) inner),
        .replicate _ _ _⟩ := by
  refine primeRel_of_piToPattern_eq _ _ ?_
  rw [show substList ((binder, fresh) :: substitutions) inner = substList substitutions (inner.substitute binder fresh)
    from rfl, ← substList_replicate_fresh _ _ _ _ away, piToPattern_substList, piToPattern_substList,
    piToPattern_alpha_replicate x binder fresh inner notFree]

/-- **Congruence under an input guard relates the liftings.** -/
theorem liftsRel_input_cong {x binder : Name} {inner inner' : Process} (congruence : inner ≡ inner')
    (substitutions : List (Name × Name)) :
    LiftsRel (substList substitutions (.input x binder inner)) (substList substitutions (.input x binder inner')) := by
  obtain ⟨fresh, freshNot⟩ := exists_fresh (inner.freeNames ∪ inner'.freeNames ∪ substNames substitutions)
  simp only [Finset.mem_union, not_or] at freshNot
  obtain ⟨⟨notInner, notInner'⟩, away⟩ := freshNot
  have middle : PrimeRel
      ⟨.input (substName substitutions x) fresh (substList ((binder, fresh) :: substitutions) inner), .input _ _ _⟩
      ⟨.input (substName substitutions x) fresh (substList ((binder, fresh) :: substitutions) inner'), .input _ _ _⟩ :=
    .input fun payload => congruent_substitute (congruent_substList congruence _) fresh payload
  exact liftsRel_guarded' (first := ⟨_, substList_guarded (.input _ _ _) substitutions⟩)
    (second := ⟨_, substList_guarded (.input _ _ _) substitutions⟩)
    (.trans _ _ _ (bodyEquiv_single (primeRel_substList_input substitutions x binder fresh inner notInner away))
      (.trans _ _ _ (bodyEquiv_single middle)
        (.symm _ _ (bodyEquiv_single (primeRel_substList_input substitutions x binder fresh inner' notInner' away)))))

/-- **Congruence under a replicated input guard relates the liftings.** -/
theorem liftsRel_replicate_cong {x binder : Name} {inner inner' : Process} (congruence : inner ≡ inner')
    (substitutions : List (Name × Name)) :
    LiftsRel (substList substitutions (.replicate x binder inner))
      (substList substitutions (.replicate x binder inner')) := by
  obtain ⟨fresh, freshNot⟩ := exists_fresh (inner.freeNames ∪ inner'.freeNames ∪ substNames substitutions)
  simp only [Finset.mem_union, not_or] at freshNot
  obtain ⟨⟨notInner, notInner'⟩, away⟩ := freshNot
  have middle : PrimeRel
      ⟨.replicate (substName substitutions x) fresh (substList ((binder, fresh) :: substitutions) inner),
        .replicate _ _ _⟩
      ⟨.replicate (substName substitutions x) fresh (substList ((binder, fresh) :: substitutions) inner'),
        .replicate _ _ _⟩ :=
    .replicate fun payload => congruent_substitute (congruent_substList congruence _) fresh payload
  exact liftsRel_guarded' (first := ⟨_, substList_guarded (.replicate _ _ _) substitutions⟩)
    (second := ⟨_, substList_guarded (.replicate _ _ _) substitutions⟩)
    (.trans _ _ _ (bodyEquiv_single (primeRel_substList_replicate substitutions x binder fresh inner notInner away))
      (.trans _ _ _ (bodyEquiv_single middle)
        (.symm _ _ (bodyEquiv_single
          (primeRel_substList_replicate substitutions x binder fresh inner' notInner' away)))))

theorem substitute_input_replicate (x binder : Name) (inner : Process) (old new : Name) :
    ∃ x' binder' inner', (Process.input x binder inner).substitute old new = .input x' binder' inner' ∧
      (Process.replicate x binder inner).substitute old new = .replicate x' binder' inner' := by
  rw [Process.substitute, Process.substitute]
  split_ifs <;> exact ⟨_, _, _, rfl, rfl⟩

theorem substList_input_replicate : ∀ (substitutions : List (Name × Name)) (x binder : Name) (inner : Process),
    ∃ x' binder' inner', substList substitutions (.input x binder inner) = .input x' binder' inner' ∧
      substList substitutions (.replicate x binder inner) = .replicate x' binder' inner'
  | [], x, binder, inner => ⟨x, binder, inner, rfl, rfl⟩
  | (old, new) :: rest, x, binder, inner => by
    obtain ⟨x', binder', inner', inputEq, replicateEq⟩ := substitute_input_replicate x binder inner old new
    simp only [substList, inputEq, replicateEq]
    exact substList_input_replicate rest x' binder' inner'

/-- **Unfolding a replicated input relates the liftings**, both ways. -/
theorem liftsRel_unfold (x binder : Name) (inner : Process) (substitutions : List (Name × Name)) :
    LiftsRel (substList substitutions (.replicate x binder inner))
        (substList substitutions (.par (.input x binder inner) (.replicate x binder inner))) ∧
      LiftsRel (substList substitutions (.par (.input x binder inner) (.replicate x binder inner)))
        (substList substitutions (.replicate x binder inner)) := by
  obtain ⟨x', binder', inner', inputEq, replicateEq⟩ := substList_input_replicate substitutions x binder inner
  rw [substList_par, inputEq, replicateEq]
  have unfold : BodyEquiv {server x' binder' inner'} ({copy x' binder' inner'} + {server x' binder' inner'}) := by
    have step : BodyStep (0 + {server x' binder' inner'}) (0 + {copy x' binder' inner', server x' binder' inner'}) :=
      .unfold
    simp only [zero_add] at step
    have same : ({copy x' binder' inner', server x' binder' inner'} : Multiset Prime) =
        {copy x' binder' inner'} + {server x' binder' inner'} := by
      simp only [Multiset.insert_eq_cons, Multiset.singleton_add]
    rw [← same]
    exact .rel _ _ step
  constructor
  · intro avoid scope body lifts
    obtain ⟨rfl, rfl⟩ := lifts_guarded_inv (.replicate x' binder' inner') lifts
    refine ⟨∅ ∪ ∅, {copy x' binder' inner'} + {server x' binder' inner'},
      .par (.guarded (.input _ _ _)) (.guarded (.replicate _ _ _)) (Finset.disjoint_empty_left _)
        (Finset.disjoint_empty_left _) (Finset.disjoint_empty_left _), by simp [Molecule.trim], unfold,
      fun name inside => by simp at inside⟩
  · intro avoid scope body lifts
    obtain ⟨inputScope, serverScope, inputBody, serverBody, inputLifts, serverLifts, _, _, _, rfl, rfl⟩ :=
      lifts_par_inv lifts
    obtain ⟨rfl, rfl⟩ := lifts_guarded_inv (.input x' binder' inner') inputLifts
    obtain ⟨rfl, rfl⟩ := lifts_guarded_inv (.replicate x' binder' inner') serverLifts
    exact ⟨∅, {server x' binder' inner'}, .guarded (.replicate _ _ _), by simp [Molecule.trim], .symm _ _ unfold,
      fun name inside => by simp at inside⟩

theorem BodyRel.eq_zero {body : Multiset Prime} (related : BodyRel body 0) : body = 0 := by
  obtain ⟨list, list', rfl, empty, pointwise⟩ := related
  have : list' = [] := (Multiset.coe_eq_zero list').mp empty
  subst this
  cases pointwise
  rfl

theorem BodyRel.zero_eq {body : Multiset Prime} (related : BodyRel 0 body) : body = 0 := by
  obtain ⟨list, list', empty, rfl, pointwise⟩ := related
  have : list = [] := (Multiset.coe_eq_zero list).mp empty
  subst this
  cases pointwise
  rfl

/-- **Restricting the inert process relates the liftings**, both ways. -/
theorem liftsRel_nu_nil (binder : Name) (substitutions : List (Name × Name)) :
    LiftsRel (substList substitutions (.nu binder .nil)) (substList substitutions .nil) ∧
      LiftsRel (substList substitutions .nil) (substList substitutions (.nu binder .nil)) := by
  obtain ⟨b, body, shape⟩ := substList_nu_shape substitutions binder .nil
  obtain ⟨fresh, away⟩ := exists_fresh (substNames substitutions)
  have notFree : fresh ∉ Process.nil.freeNames := by simp [Process.freeNames]
  constructor
  · intro avoid scope lifted lifts
    rw [shape] at lifts
    obtain ⟨new, rest, innerLifts, _, _, rfl⟩ := lifts_nu_inv lifts
    obtain ⟨images, shapes⟩ := substList_nu_open_any (new := new) shape notFree away
    obtain ⟨body₀, lifts₀, related₀⟩ := lifts_of_piToPattern_eq _ _ _ le_rfl shapes images innerLifts
    rw [substList_nil] at lifts₀
    obtain ⟨rfl, rfl⟩ := lifts_nil_inv lifts₀
    obtain rfl := related₀.eq_zero
    refine ⟨∅, 0, by rw [substList_nil]; exact .nil, ?_, .refl _, fun name inside => by simp at inside⟩
    simp [Molecule.trim, Molecule.bodyNames]
  · intro avoid scope lifted lifts
    rw [substList_nil] at lifts
    obtain ⟨rfl, rfl⟩ := lifts_nil_inv lifts
    obtain ⟨new, newNot⟩ := exists_fresh (avoid ∪ (Process.nu b body).freeNames)
    simp only [Finset.mem_union, not_or] at newNot
    obtain ⟨images, shapes⟩ := substList_nu_open_any (new := new) shape notFree away
    have nilLifts : Lifts (substList (((binder, fresh) :: substitutions) ++ [(fresh, new)]) .nil) ∅ 0 := by
      rw [substList_nil]; exact .nil
    obtain ⟨body', lifts', related'⟩ := lifts_of_piToPattern_eq _ _ _ le_rfl shapes.symm images.symm nilLifts
    obtain rfl := related'.zero_eq
    refine ⟨insert new ∅, 0, by rw [shape]; exact .nu lifts' (Finset.notMem_empty _) newNot.2, ?_, .refl _, ?_⟩
    · simp [Molecule.trim, Molecule.bodyNames]
    · intro name inside
      rw [Finset.mem_insert] at inside
      rcases inside with rfl | impossible
      · exact Or.inr newNot.1
      · exact absurd impossible (Finset.notMem_empty _)

/-! ## Structural laws relate liftings: scope extrusion -/

theorem freeNames_nu_subset (binder new : Name) (inner : Process) :
    (Process.nu binder inner).freeNames ⊆ (inner.substitute binder new).freeNames := by
  intro name inside
  simp only [Process.freeNames, Finset.mem_sdiff, Finset.mem_singleton] at inside
  rw [Process.substitute_freeNames_eq]
  exact Finset.mem_image.mpr ⟨name, inside.1, by simp [Process.replaceName, inside.2]⟩

/-- A component without the restricted name is unchanged by renaming the binder through a fresh name. -/
theorem piToPattern_substList_absent {substitutions : List (Name × Name)} {binder fresh new : Name}
    {process : Process} (absent : binder ∉ process.freeNames) (notFree : fresh ∉ process.freeNames)
    (away : fresh ∉ substNames substitutions) :
    piToPattern (substList (((binder, fresh) :: substitutions) ++ [(fresh, new)]) process) =
      piToPattern (substList substitutions process) := by
  have binderFresh : isFresh binder (piToPattern process) = true := by
    rw [isFresh_iff_not_mem]
    exact fun inside => absent ((freeVars_piToPattern _ _).mp inside)
  rw [substList_append]
  simp only [substList]
  have unchanged : applySubst [(binder, Pattern.fvar fresh)] (piToPattern process) = piToPattern process :=
    applySubst_fresh_single binderFresh (piToPattern_noExplicitSubst _)
  rw [piToPattern_substitute, piToPattern_substList, piToPattern_substitute, unchanged, ← piToPattern_substList]
  refine applySubst_fresh_single (x := fresh) (q := Pattern.fvar new) ?_ (piToPattern_noExplicitSubst _)
  rw [isFresh_iff_not_mem]
  intro inside
  rcases Finset.mem_union.mp (freeNames_substList substitutions process ((freeVars_piToPattern _ _).mp inside)) with
    free | named
  · exact notFree free
  · exact away named

theorem parShape_substList_open (substitutions : List (Name × Name)) (binder fresh new : Name) (process : Process) :
    parShape (substList (((binder, fresh) :: substitutions) ++ [(fresh, new)]) process) =
      parShape (substList substitutions process) := by
  rw [parShape_substList, parShape_substList]

/-- **Scope extrusion relates the liftings**: from the restriction over both components to the restriction beside the
component without its name. -/
theorem liftsRel_nu_par {binder : Name} {left right : Process} (absent : binder ∉ right.freeNames)
    (substitutions : List (Name × Name)) :
    LiftsRel (substList substitutions (.nu binder (.par left right)))
      (substList substitutions (.par (.nu binder left) right)) := by
  obtain ⟨b, body, shape⟩ := substList_nu_shape substitutions binder (.par left right)
  obtain ⟨bLeft, bodyLeft, shapeLeft⟩ := substList_nu_shape substitutions binder left
  have namesEq := freeNames_substList_congruent (.nu_par binder left right absent) substitutions
  intro avoid scope lifted lifts
  rw [shape] at lifts
  obtain ⟨new, rest, innerLifts, newOut, newFree, rfl⟩ := lifts_nu_inv lifts
  obtain ⟨fresh, freshNot⟩ := exists_fresh (left.freeNames ∪ right.freeNames ∪ substNames substitutions)
  simp only [Finset.mem_union, not_or] at freshNot
  obtain ⟨⟨notLeft, notRight⟩, away⟩ := freshNot
  have notBoth : fresh ∉ (Process.par left right).freeNames := by
    simp only [Process.freeNames, Finset.mem_union, not_or]; exact ⟨notLeft, notRight⟩
  obtain ⟨images, shapes⟩ := substList_nu_open_any (new := new) shape notBoth away
  obtain ⟨imagesLeft, shapesLeft⟩ := substList_nu_open_any (new := new) shapeLeft notLeft away
  obtain ⟨body₀, lifts₀, related₀⟩ := lifts_of_piToPattern_eq _ _ _ le_rfl shapes images innerLifts
  rw [substList_par] at lifts₀
  obtain ⟨leftRest, rightRest, leftBody, rightBody, leftLifts, rightLifts, apart, leftFresh, rightFresh, rfl, rfl⟩ :=
    lifts_par_inv lifts₀
  obtain ⟨leftBody', leftLifts', leftRelated⟩ :=
    lifts_of_piToPattern_eq _ _ _ le_rfl shapesLeft.symm imagesLeft.symm leftLifts
  have rightImages := piToPattern_substList_absent (new := new) absent notRight away
  obtain ⟨rightBody', rightLifts', rightRelated⟩ := lifts_of_piToPattern_eq _ _ _ le_rfl
    (parShape_substList_open _ _ _ _ _) rightImages rightLifts
  have rightNames : (substList (((binder, fresh) :: substitutions) ++ [(fresh, new)]) right).freeNames =
      (substList substitutions right).freeNames := freeNames_of_piToPattern_eq rightImages
  have newSource : new ∉ (substList substitutions (Process.par (.nu binder left) right)).freeNames := by
    rw [← namesEq, shape]; exact newFree
  rw [substList_par, shapeLeft] at newSource
  simp only [Process.freeNames, Finset.mem_union, not_or] at newSource
  have leftNu : Lifts (.nu bLeft bodyLeft) (insert new leftRest) leftBody' :=
    .nu leftLifts' (fun inside => newOut (Finset.mem_union_left _ inside)) newSource.1
  have leftNames : (Process.nu bLeft bodyLeft).freeNames ⊆
      (substList (((binder, fresh) :: substitutions) ++ [(fresh, new)]) left).freeNames := by
    rw [← freeNames_of_piToPattern_eq imagesLeft]
    exact freeNames_nu_subset _ _ _
  refine ⟨insert new leftRest ∪ rightRest, leftBody' + rightBody', ?_, ?_,
    .trans _ _ _ related₀.bodyEquiv (leftRelated.bodyEquiv.add_both rightRelated.bodyEquiv), fun name inside => ?_⟩
  · rw [substList_par, shapeLeft]
    refine .par leftNu rightLifts' ?_ ?_ ?_
    · refine Finset.disjoint_insert_left.mpr ⟨fun inside => newOut (Finset.mem_union_right _ inside), apart⟩
    · refine Finset.disjoint_insert_left.mpr ⟨newSource.2, ?_⟩
      rw [← rightNames]; exact leftFresh
    · exact rightFresh.mono_right leftNames
  · have chain : BodyEquiv lifted (leftBody' + rightBody') :=
      .trans _ _ _ related₀.bodyEquiv (leftRelated.bodyEquiv.add_both rightRelated.bodyEquiv)
    simp only [Molecule.trim]
    rw [Finset.insert_union, chain.bodyNames (insert new (leftRest ∪ rightRest)) (insert new (leftRest ∪ rightRest))]
  · rw [Finset.insert_union] at inside
    exact Or.inl inside

theorem freeNames_open_subset (binder new : Name) (inner : Process) :
    (inner.substitute binder new).freeNames ⊆ insert new (Process.nu binder inner).freeNames := by
  intro name inside
  have := Process.substitute_freeNames inner binder new inside
  simpa [Process.freeNames] using this

/-- **Scope extrusion relates the liftings**, back from the restriction beside the other component. -/
theorem liftsRel_nu_par' {binder : Name} {left right : Process} (absent : binder ∉ right.freeNames)
    (substitutions : List (Name × Name)) :
    LiftsRel (substList substitutions (.par (.nu binder left) right))
      (substList substitutions (.nu binder (.par left right))) := by
  obtain ⟨b, body, shape⟩ := substList_nu_shape substitutions binder (.par left right)
  obtain ⟨bLeft, bodyLeft, shapeLeft⟩ := substList_nu_shape substitutions binder left
  have namesEq := freeNames_substList_congruent (.nu_par binder left right absent) substitutions
  intro avoid scope lifted lifts
  rw [substList_par, shapeLeft] at lifts
  obtain ⟨nuScope, rightScope, nuBody, rightBody, nuLifts, rightLifts, apart, nuFresh, rightFresh, rfl, rfl⟩ :=
    lifts_par_inv lifts
  obtain ⟨new, leftRest, leftLifts, newOut, newFree, rfl⟩ := lifts_nu_inv nuLifts
  obtain ⟨fresh, freshNot⟩ := exists_fresh (left.freeNames ∪ right.freeNames ∪ substNames substitutions)
  simp only [Finset.mem_union, not_or] at freshNot
  obtain ⟨⟨notLeft, notRight⟩, away⟩ := freshNot
  have notBoth : fresh ∉ (Process.par left right).freeNames := by
    simp only [Process.freeNames, Finset.mem_union, not_or]; exact ⟨notLeft, notRight⟩
  obtain ⟨images, shapes⟩ := substList_nu_open_any (new := new) shape notBoth away
  obtain ⟨imagesLeft, shapesLeft⟩ := substList_nu_open_any (new := new) shapeLeft notLeft away
  have rightImages := piToPattern_substList_absent (new := new) absent notRight away
  have rightNames : (substList (((binder, fresh) :: substitutions) ++ [(fresh, new)]) right).freeNames =
      (substList substitutions right).freeNames := freeNames_of_piToPattern_eq rightImages
  obtain ⟨leftBody₀, leftLifts₀, leftRelated⟩ :=
    lifts_of_piToPattern_eq _ _ _ le_rfl shapesLeft imagesLeft leftLifts
  obtain ⟨rightBody₀, rightLifts₀, rightRelated⟩ := lifts_of_piToPattern_eq _ _ _ le_rfl
    (parShape_substList_open _ _ _ _ _).symm rightImages.symm rightLifts
  have newRight : new ∉ rightScope := fun inside => Finset.disjoint_left.mp apart (Finset.mem_insert_self _ _) inside
  have newRightFree : new ∉ (substList substitutions right).freeNames := fun inside =>
    Finset.disjoint_left.mp nuFresh (Finset.mem_insert_self _ _) inside
  have inner : Lifts (substList (((binder, fresh) :: substitutions) ++ [(fresh, new)]) (.par left right))
      (leftRest ∪ rightScope) (leftBody₀ + rightBody₀) := by
    rw [substList_par]
    refine .par leftLifts₀ rightLifts₀ ?_ ?_ ?_
    · exact (Finset.disjoint_insert_left.mp apart).2
    · rw [rightNames]; exact (Finset.disjoint_insert_left.mp nuFresh).2
    · rw [← freeNames_of_piToPattern_eq imagesLeft]
      refine Finset.disjoint_left.mpr fun name theirs inside => ?_
      rcases Finset.mem_insert.mp (freeNames_open_subset _ _ _ inside) with rfl | free
      · exact newRight theirs
      · exact Finset.disjoint_left.mp rightFresh theirs free
  obtain ⟨body', lifts', related'⟩ := lifts_of_piToPattern_eq _ _ _ le_rfl shapes.symm images.symm inner
  have newTarget : new ∉ (Process.nu b body).freeNames := by
    rw [← shape, namesEq, substList_par, shapeLeft]
    simp only [Process.freeNames, Finset.mem_union, not_or]
    exact ⟨newFree, newRightFree⟩
  have chain : BodyEquiv (nuBody + rightBody) body' :=
    .trans _ _ _ (leftRelated.bodyEquiv.add_both rightRelated.bodyEquiv) related'.bodyEquiv
  refine ⟨insert new (leftRest ∪ rightScope), body', ?_, ?_, chain, fun name inside => ?_⟩
  · rw [shape]
    exact .nu lifts' (fun inside => (Finset.mem_union.mp inside).elim newOut newRight) newTarget
  · simp only [Molecule.trim]
    rw [Finset.insert_union, chain.bodyNames (insert new (leftRest ∪ rightScope)) (insert new (leftRest ∪ rightScope))]
  · rw [Finset.insert_union]
    exact Or.inl inside

/-! ## Structural laws relate liftings: exchanging restrictions -/

theorem substName_append : ∀ (first second : List (Name × Name)) (name : Name),
    substName (first ++ second) name = substName second (substName first name)
  | [], _, _ => rfl
  | (old, new) :: rest, second, name => by
    simp only [List.cons_append, substName]
    exact substName_append rest second _

theorem substNames_append (first second : List (Name × Name)) :
    substNames (first ++ second) = substNames first ∪ substNames second := by
  induction first with
  | nil => simp [substNames]
  | cons pair rest holds =>
    obtain ⟨old, new⟩ := pair
    simp only [List.cons_append, substNames, holds, Finset.insert_union]

/-- Two restrictions opened in either order give the same body. -/
theorem piToPattern_open_twice {substitutions : List (Name × Name)} {first second : Name} {inner : Process}
    (different : first ≠ second) {firstNew secondNew firstFresh secondFresh firstFresh' secondFresh' : Name}
    (news : firstNew ≠ secondNew)
    (firstFreshFree : firstFresh ∉ inner.freeNames) (firstFreshAway : firstFresh ∉ substNames substitutions)
    (secondFreshFree : secondFresh ∉ inner.freeNames)
    (secondFreshAway : secondFresh ∉ substNames (((first, firstFresh) :: substitutions) ++ [(firstFresh, firstNew)]))
    (secondFreshFree' : secondFresh' ∉ inner.freeNames) (secondFreshAway' : secondFresh' ∉ substNames substitutions)
    (firstFreshFree' : firstFresh' ∉ inner.freeNames)
    (firstFreshAway' : firstFresh' ∉
      substNames (((second, secondFresh') :: substitutions) ++ [(secondFresh', secondNew)])) :
    piToPattern (substList (((second, secondFresh) ::
        (((first, firstFresh) :: substitutions) ++ [(firstFresh, firstNew)])) ++ [(secondFresh, secondNew)]) inner) =
      piToPattern (substList (((first, firstFresh') ::
        (((second, secondFresh') :: substitutions) ++ [(secondFresh', secondNew)])) ++ [(firstFresh', firstNew)]) inner) := by
  rw [piToPattern_substList, piToPattern_substList,
    patternSubstList_eq_mapFVars _ _ (piToPattern_noExplicitSubst _),
    patternSubstList_eq_mapFVars _ _ (piToPattern_noExplicitSubst _)]
  refine mapFVars_congr _ fun name member => ?_
  have present : name ∈ inner.freeNames := (freeVars_piToPattern _ _).mp member
  have sFirst : secondFresh ≠ first := fun h => secondFreshAway (by simp [substNames_append, substNames, h])
  have sFirstFresh : secondFresh ≠ firstFresh := fun h => secondFreshAway (by simp [substNames_append, substNames, h])
  have sAway : secondFresh ∉ substNames substitutions := fun h =>
    secondFreshAway (by simp [substNames_append, substNames, h])
  have sFirstNew : secondFresh ≠ firstNew := fun h => secondFreshAway (by simp [substNames_append, substNames, h])
  have fSecond : firstFresh' ≠ second := fun h => firstFreshAway' (by simp [substNames_append, substNames, h])
  have fSecondFresh : firstFresh' ≠ secondFresh' := fun h =>
    firstFreshAway' (by simp [substNames_append, substNames, h])
  have fAway : firstFresh' ∉ substNames substitutions := fun h =>
    firstFreshAway' (by simp [substNames_append, substNames, h])
  have fSecondNew : firstFresh' ≠ secondNew := fun h => firstFreshAway' (by simp [substNames_append, substNames, h])
  simp only [substName_append, substName]
  have neFirstFresh : name ≠ firstFresh := fun same => firstFreshFree (same ▸ present)
  have neSecondFresh : name ≠ secondFresh := fun same => secondFreshFree (same ▸ present)
  have neFirstFresh' : name ≠ firstFresh' := fun same => firstFreshFree' (same ▸ present)
  have neSecondFresh' : name ≠ secondFresh' := fun same => secondFreshFree' (same ▸ present)
  have facts := And.intro sFirstFresh (And.intro sFirstNew (And.intro fSecond (And.intro fSecondFresh
    (And.intro fSecondNew news))))
  by_cases isFirst : name = first
  · subst isFirst
    simp [different, substName_of_not_mem firstFreshAway, substName_of_not_mem fAway, facts, Ne.symm sFirstNew]
  · by_cases isSecond : name = second
    · subst isSecond
      simp [isFirst, sFirst, substName_of_not_mem sAway, substName_of_not_mem secondFreshAway', facts,
        Ne.symm fSecondNew]
    · simp only [if_neg isFirst, if_neg isSecond]
      rcases substName_mem substitutions name with stays | named
      · rw [stays]
        simp [neFirstFresh, neSecondFresh, neFirstFresh', neSecondFresh']
      · have h1 : substName substitutions name ≠ firstFresh := fun same => firstFreshAway (same ▸ named)
        have h2 : substName substitutions name ≠ secondFresh := fun same => sAway (same ▸ named)
        have h3 : substName substitutions name ≠ secondFresh' := fun same => secondFreshAway' (same ▸ named)
        have h4 : substName substitutions name ≠ firstFresh' := fun same => fAway (same ▸ named)
        simp [h1, h2, h3, h4]

/-- **Exchanging two restrictions relates the liftings.** -/
theorem liftsRel_nu_swap (first second : Name) (inner : Process) (substitutions : List (Name × Name)) :
    LiftsRel (substList substitutions (.nu first (.nu second inner)))
      (substList substitutions (.nu second (.nu first inner))) := by
  by_cases same : first = second
  · subst same; exact LiftsRel.refl _
  have namesEq := freeNames_substList_congruent (.nu_swap first second inner) substitutions
  have nuFree : ∀ {binder fresh : Name}, fresh ∉ inner.freeNames → fresh ∉ (Process.nu binder inner).freeNames :=
    fun notFree inside => notFree (by simp only [Process.freeNames, Finset.mem_sdiff] at inside; exact inside.1)
  obtain ⟨b, body, shape⟩ := substList_nu_shape substitutions first (.nu second inner)
  obtain ⟨b', body', shape'⟩ := substList_nu_shape substitutions second (.nu first inner)
  intro avoid scope lifted lifts
  rw [shape] at lifts
  obtain ⟨firstNew, rest, outerLifts, firstOut, firstFree, rfl⟩ := lifts_nu_inv lifts
  obtain ⟨firstFresh, firstNot⟩ := exists_fresh (inner.freeNames ∪ substNames substitutions)
  rw [Finset.mem_union, not_or] at firstNot
  obtain ⟨images, shapes⟩ := substList_nu_open_any (new := firstNew) shape (nuFree firstNot.1) firstNot.2
  obtain ⟨body₀, lifts₀, related₀⟩ := lifts_of_piToPattern_eq _ _ _ le_rfl shapes images outerLifts
  obtain ⟨c, middle, shapeMiddle⟩ :=
    substList_nu_shape (((first, firstFresh) :: substitutions) ++ [(firstFresh, firstNew)]) second inner
  rw [shapeMiddle] at lifts₀
  obtain ⟨secondNew, rest₂, innerLifts, secondOut, secondFree, rfl⟩ := lifts_nu_inv lifts₀
  obtain ⟨secondFresh, secondNot⟩ := exists_fresh (inner.freeNames ∪
    substNames (((first, firstFresh) :: substitutions) ++ [(firstFresh, firstNew)]))
  rw [Finset.mem_union, not_or] at secondNot
  obtain ⟨imagesMiddle, shapesMiddle⟩ :=
    substList_nu_open_any (new := secondNew) shapeMiddle secondNot.1 secondNot.2
  obtain ⟨body₁, lifts₁, related₁⟩ := lifts_of_piToPattern_eq _ _ _ le_rfl shapesMiddle imagesMiddle innerLifts
  obtain ⟨secondFresh', secondNot'⟩ := exists_fresh (inner.freeNames ∪ substNames substitutions)
  rw [Finset.mem_union, not_or] at secondNot'
  obtain ⟨images', shapes'⟩ := substList_nu_open_any (new := secondNew) shape' (nuFree secondNot'.1) secondNot'.2
  obtain ⟨c', middle', shapeMiddle'⟩ :=
    substList_nu_shape (((second, secondFresh') :: substitutions) ++ [(secondFresh', secondNew)]) first inner
  obtain ⟨firstFresh', firstNot'⟩ := exists_fresh (inner.freeNames ∪
    substNames (((second, secondFresh') :: substitutions) ++ [(secondFresh', secondNew)]))
  rw [Finset.mem_union, not_or] at firstNot'
  obtain ⟨imagesMiddle', shapesMiddle'⟩ :=
    substList_nu_open_any (new := firstNew) shapeMiddle' firstNot'.1 firstNot'.2
  have news : firstNew ≠ secondNew := fun equal => firstOut (equal ▸ Finset.mem_insert_self _ _)
  have swapped := piToPattern_open_twice same news firstNot.1 firstNot.2 secondNot.1 secondNot.2 secondNot'.1
    secondNot'.2 firstNot'.1 firstNot'.2
  obtain ⟨body₂, lifts₂, related₂⟩ := lifts_of_piToPattern_eq _ _ _ le_rfl
    (by rw [parShape_substList, parShape_substList]) swapped lifts₁
  obtain ⟨body₃, lifts₃, related₃⟩ :=
    lifts_of_piToPattern_eq _ _ _ le_rfl shapesMiddle'.symm imagesMiddle'.symm lifts₂
  have outerNames : (Process.nu b' body').freeNames = (Process.nu b body).freeNames := by
    rw [← shape', ← namesEq, shape]
  have secondFree' : secondNew ∉ (Process.nu b' body').freeNames := by
    rw [outerNames]
    intro inside
    apply secondFree
    rw [← shapeMiddle, ← freeNames_of_piToPattern_eq images]
    exact freeNames_nu_subset _ _ _ inside
  have firstFree' : firstNew ∉ (Process.nu c' middle').freeNames := by
    intro inside
    rw [← shapeMiddle', ← freeNames_of_piToPattern_eq images'] at inside
    rcases Finset.mem_insert.mp (freeNames_open_subset _ _ _ inside) with equal | free
    · exact news equal
    · rw [outerNames] at free; exact firstFree free
  have middleLifts : Lifts (substList (((second, secondFresh') :: substitutions) ++ [(secondFresh', secondNew)])
      (.nu first inner)) (insert firstNew rest₂) body₃ := by
    rw [shapeMiddle']
    exact .nu lifts₃ (fun inside => firstOut (Finset.mem_insert_of_mem inside)) firstFree'
  obtain ⟨body₄, lifts₄, related₄⟩ := lifts_of_piToPattern_eq _ _ _ le_rfl shapes'.symm images'.symm middleLifts
  have secondOut' : secondNew ∉ insert firstNew rest₂ := by
    rw [Finset.mem_insert, not_or]; exact ⟨Ne.symm news, secondOut⟩
  have chain : BodyEquiv lifted body₄ :=
    .trans _ _ _ related₀.bodyEquiv (.trans _ _ _ related₁.bodyEquiv (.trans _ _ _ related₂.bodyEquiv
      (.trans _ _ _ related₃.bodyEquiv related₄.bodyEquiv)))
  have scopes : insert secondNew (insert firstNew rest₂) = insert firstNew (insert secondNew rest₂) :=
    Finset.insert_comm _ _ _
  refine ⟨insert secondNew (insert firstNew rest₂), body₄, by rw [shape']; exact .nu lifts₄ secondOut' secondFree',
    ?_, chain, fun name inside => Or.inl (scopes ▸ inside)⟩
  simp only [Molecule.trim]
  rw [scopes, chain.bodyNames (insert firstNew (insert secondNew rest₂)) (insert firstNew (insert secondNew rest₂))]

/-! ## Structural congruence relates liftings -/

/-- **Congruent processes have related liftings**, both ways and under every list of substitutions. -/
theorem liftsRel_of_congruent {first second : Process} (congruence : first ≡ second) :
    ∀ substitutions : List (Name × Name),
      LiftsRel (substList substitutions first) (substList substitutions second) ∧
        LiftsRel (substList substitutions second) (substList substitutions first) := by
  induction congruence with
  | refl => exact fun _ => ⟨.refl _, .refl _⟩
  | symm _ _ _ holds => exact fun substitutions => (holds substitutions).symm
  | trans _ _ _ _ _ firstSecond secondThird =>
    exact fun substitutions => ⟨(firstSecond substitutions).1.trans (secondThird substitutions).1,
      (secondThird substitutions).2.trans (firstSecond substitutions).2⟩
  | par_cong _ _ _ _ left right leftRel rightRel =>
    intro substitutions
    rw [substList_par, substList_par]
    exact ⟨liftsRel_par (leftRel substitutions).1 (rightRel substitutions).1
        (freeNames_substList_congruent left substitutions) (freeNames_substList_congruent right substitutions),
      liftsRel_par (leftRel substitutions).2 (rightRel substitutions).2
        (freeNames_substList_congruent left substitutions).symm
        (freeNames_substList_congruent right substitutions).symm⟩
  | input_cong _ _ _ _ inner =>
    exact fun substitutions => ⟨liftsRel_input_cong inner substitutions,
      liftsRel_input_cong (.symm _ _ inner) substitutions⟩
  | nu_cong _ _ _ inner innerRel =>
    exact fun substitutions => ⟨liftsRel_nu inner (fun others => (innerRel others).1) substitutions,
      liftsRel_nu (.symm _ _ inner) (fun others => (innerRel others).2) substitutions⟩
  | replicate_cong _ _ _ _ inner =>
    exact fun substitutions => ⟨liftsRel_replicate_cong inner substitutions,
      liftsRel_replicate_cong (.symm _ _ inner) substitutions⟩
  | par_comm =>
    intro substitutions
    rw [substList_par, substList_par]
    exact ⟨liftsRel_par_comm _ _, liftsRel_par_comm _ _⟩
  | par_assoc =>
    intro substitutions
    simp only [substList_par]
    exact ⟨liftsRel_par_assoc _ _ _, liftsRel_par_assoc' _ _ _⟩
  | par_nil_left =>
    intro substitutions
    rw [substList_par, substList_nil]
    exact ⟨liftsRel_par_nil_left _, liftsRel_par_nil_left' _⟩
  | par_nil_right =>
    intro substitutions
    rw [substList_par, substList_nil]
    exact ⟨liftsRel_par_nil_right _, liftsRel_par_nil_right' _⟩
  | nu_nil binder => exact liftsRel_nu_nil binder
  | nu_par _ _ _ absent =>
    exact fun substitutions => ⟨liftsRel_nu_par absent substitutions, liftsRel_nu_par' absent substitutions⟩
  | nu_swap first second inner =>
    exact fun substitutions => ⟨liftsRel_nu_swap first second inner substitutions,
      liftsRel_nu_swap second first inner substitutions⟩
  | alpha_input channel old new inner fresh =>
    exact fun substitutions =>
      ⟨liftsRel_substList_of_piToPattern_eq substitutions rfl (piToPattern_alpha_input channel old new inner fresh),
        liftsRel_substList_of_piToPattern_eq substitutions rfl
          (piToPattern_alpha_input channel old new inner fresh).symm⟩
  | alpha_nu old new inner fresh =>
    have shape : parShape (Process.nu old inner) = parShape (Process.nu new (inner.substitute old new)) := by
      simp only [parShape, parShape_substitute]
    exact fun substitutions =>
      ⟨liftsRel_substList_of_piToPattern_eq substitutions shape (piToPattern_alpha_nu old new inner fresh),
        liftsRel_substList_of_piToPattern_eq substitutions shape.symm (piToPattern_alpha_nu old new inner fresh).symm⟩
  | alpha_replicate channel old new inner fresh =>
    exact fun substitutions =>
      ⟨liftsRel_substList_of_piToPattern_eq substitutions rfl
          (piToPattern_alpha_replicate channel old new inner fresh),
        liftsRel_substList_of_piToPattern_eq substitutions rfl
          (piToPattern_alpha_replicate channel old new inner fresh).symm⟩
  | replicate_unfold channel binder inner => exact liftsRel_unfold channel binder inner

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners
