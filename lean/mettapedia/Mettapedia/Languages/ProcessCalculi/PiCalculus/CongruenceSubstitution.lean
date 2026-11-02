import Mettapedia.Languages.ProcessCalculi.PiCalculus.CongruenceKeys
import Mettapedia.OSLF.MeTTaIL.FreeNameMaps

/-!
# Structural congruence is closed under substitution

Substitutions are applied in order (`substList`); on locally nameless translations they act as the corresponding
pattern substitutions (`piToPattern_substList`). So processes with equal translations stay congruent under any
substitutions (`substList_congruent_of_piToPattern_eq`), a binder renamed to a name fresh for the substitutions passes
through them unchanged (`substList_input_fresh`, `substList_nu_fresh`, `substList_replicate_fresh`), and every
binder can be renamed so first (`substList_input`, `substList_nu`, `substList_replicate`). With these, each law of
structural congruence survives substitution (`congruent_substList`, `congruent_substitute`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open PiCalcInstance (piToPattern piToPattern_substitute piToPattern_noExplicitSubst piToPattern_alpha_input
  piToPattern_alpha_nu piToPattern_alpha_replicate freeVars_piToPattern)

/-! ## Two renamings commute -/

theorem applySubst_comm_single {x y v w : String} (hxy : x ≠ y) (hvy : v ≠ y) (hwx : w ≠ x) (p : Pattern)
    (hnes : noExplicitSubst p = true) :
    applySubst [(y, .fvar w)] (applySubst [(x, .fvar v)] p) =
      applySubst [(x, .fvar v)] (applySubst [(y, .fvar w)] p) := by
  induction p using Pattern.inductionOn with
  | hbvar _ => simp [applySubst]
  | hfvar name =>
    rw [applySubst_fvar_single, applySubst_fvar_single, applySubst_fvar_single, applySubst_fvar_single]
    by_cases isX : name = x
    · subst isX
      simp [hxy, hvy]
    · by_cases isY : name = y
      · subst isY
        simp [isX, hwx]
      · simp [isX, isY]
  | happly c args ih =>
    simp only [applySubst, List.map_map]
    congr 1
    exact List.map_congr_left fun a member => ih a member (allNoExplicitSubst_mem hnes member)
  | hlambda _ body ih =>
    simp only [applySubst]
    congr 1
    exact ih hnes
  | hmultiLambda _ _ body ih =>
    simp only [applySubst]
    congr 1
    exact ih hnes
  | hsubst body replacement _ _ =>
    have : noExplicitSubst (.subst body replacement) = false := rfl
    rw [this] at hnes
    exact absurd hnes Bool.false_ne_true
  | hcollection ct elements rest ih =>
    simp only [applySubst, List.map_map]
    congr 1
    exact List.map_congr_left fun a member => ih a member (allNoExplicitSubst_mem hnes member)

/-! ## Substitutions in order -/

/-- **Substitutions applied in order.** -/
def substList : List (Name × Name) → Process → Process
  | [], process => process
  | (old, new) :: rest, process => substList rest (process.substitute old new)

/-- The pattern substitutions in order. -/
def patternSubstList : List (Name × Name) → Pattern → Pattern
  | [], pattern => pattern
  | (old, new) :: rest, pattern => patternSubstList rest (applySubst [(old, .fvar new)] pattern)

/-- What the substitutions do to a name. -/
def substName : List (Name × Name) → Name → Name
  | [], name => name
  | (old, new) :: rest, name => substName rest (if name = old then new else name)

/-- The names the substitutions mention. -/
def substNames : List (Name × Name) → Finset Name
  | [] => ∅
  | (old, new) :: rest => insert old (insert new (substNames rest))

theorem piToPattern_substList : ∀ (substitutions : List (Name × Name)) (process : Process),
    piToPattern (substList substitutions process) = patternSubstList substitutions (piToPattern process)
  | [], _ => rfl
  | (old, new) :: rest, process => by
    simp only [substList, patternSubstList]
    rw [piToPattern_substList rest, piToPattern_substitute]

theorem substList_nil (substitutions : List (Name × Name)) : substList substitutions .nil = .nil := by
  induction substitutions with
  | nil => rfl
  | cons pair rest holds => obtain ⟨old, new⟩ := pair; simp [substList, holds]

theorem substList_par (substitutions : List (Name × Name)) (left right : Process) :
    substList substitutions (.par left right) = .par (substList substitutions left) (substList substitutions right) := by
  induction substitutions generalizing left right with
  | nil => rfl
  | cons pair rest holds => obtain ⟨old, new⟩ := pair; simp [substList, holds]

theorem freeNames_substList : ∀ (substitutions : List (Name × Name)) (process : Process),
    (substList substitutions process).freeNames ⊆ process.freeNames ∪ substNames substitutions
  | [], _ => by simp [substList]
  | (old, new) :: rest, process => by
    intro name member
    have outer := freeNames_substList rest _ member
    simp only [substNames, Finset.mem_union, Finset.mem_insert] at outer ⊢
    rcases outer with inner | named
    · have := Process.substitute_freeNames process old new inner
      simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at this
      tauto
    · tauto

/-- **Equal translations stay congruent under any substitutions.** -/
theorem substList_congruent_of_piToPattern_eq (substitutions : List (Name × Name)) {first second : Process}
    (same : piToPattern first = piToPattern second) :
    Congruent (substList substitutions first) (substList substitutions second) :=
  congruent_of_piToPattern_eq _ _ _ le_rfl (by rw [piToPattern_substList, piToPattern_substList, same])

theorem substList_input_fresh : ∀ (substitutions : List (Name × Name)) (x binder : Name) (body : Process),
    binder ∉ substNames substitutions →
      substList substitutions (.input x binder body) =
        .input (substName substitutions x) binder (substList substitutions body)
  | [], _, _, _, _ => rfl
  | (old, new) :: rest, x, binder, body, fresh => by
    simp only [substNames, Finset.mem_insert, not_or] at fresh
    simp only [substList, substName]
    rw [Process.substitute_input_of_disjoint x binder body old new fresh.1 fresh.2.1,
      substList_input_fresh rest _ binder _ fresh.2.2]
    rfl

theorem substList_replicate_fresh : ∀ (substitutions : List (Name × Name)) (x binder : Name) (body : Process),
    binder ∉ substNames substitutions →
      substList substitutions (.replicate x binder body) =
        .replicate (substName substitutions x) binder (substList substitutions body)
  | [], _, _, _, _ => rfl
  | (old, new) :: rest, x, binder, body, fresh => by
    simp only [substNames, Finset.mem_insert, not_or] at fresh
    simp only [substList, substName]
    rw [Process.substitute_replicate_of_disjoint x binder body old new fresh.1 fresh.2.1,
      substList_replicate_fresh rest _ binder _ fresh.2.2]
    rfl

theorem substList_nu_fresh : ∀ (substitutions : List (Name × Name)) (binder : Name) (body : Process),
    binder ∉ substNames substitutions →
      substList substitutions (.nu binder body) = .nu binder (substList substitutions body)
  | [], _, _, _ => rfl
  | (old, new) :: rest, binder, body, fresh => by
    simp only [substNames, Finset.mem_insert, not_or] at fresh
    simp only [substList]
    rw [Process.substitute_nu_of_disjoint binder body old new fresh.1 fresh.2.1, substList_nu_fresh rest binder _ fresh.2.2]

/-- **A binder renamed first**: substitutions on an input act on its body renamed to a fresh binder. -/
theorem substList_input (substitutions : List (Name × Name)) (x binder fresh : Name) (body : Process)
    (notFree : fresh ∉ body.freeNames) (away : fresh ∉ substNames substitutions) :
    Congruent (substList substitutions (.input x binder body))
      (.input (substName substitutions x) fresh (substList ((binder, fresh) :: substitutions) body)) := by
  rw [show substList ((binder, fresh) :: substitutions) body = substList substitutions (body.substitute binder fresh)
    from rfl, ← substList_input_fresh _ _ _ _ away]
  exact substList_congruent_of_piToPattern_eq _ (piToPattern_alpha_input x binder fresh body notFree)

theorem substList_replicate (substitutions : List (Name × Name)) (x binder fresh : Name) (body : Process)
    (notFree : fresh ∉ body.freeNames) (away : fresh ∉ substNames substitutions) :
    Congruent (substList substitutions (.replicate x binder body))
      (.replicate (substName substitutions x) fresh (substList ((binder, fresh) :: substitutions) body)) := by
  rw [show substList ((binder, fresh) :: substitutions) body = substList substitutions (body.substitute binder fresh)
    from rfl, ← substList_replicate_fresh _ _ _ _ away]
  exact substList_congruent_of_piToPattern_eq _ (piToPattern_alpha_replicate x binder fresh body notFree)

theorem substList_nu (substitutions : List (Name × Name)) (binder fresh : Name) (body : Process)
    (notFree : fresh ∉ body.freeNames) (away : fresh ∉ substNames substitutions) :
    Congruent (substList substitutions (.nu binder body))
      (.nu fresh (substList ((binder, fresh) :: substitutions) body)) := by
  rw [show substList ((binder, fresh) :: substitutions) body = substList substitutions (body.substitute binder fresh)
    from rfl, ← substList_nu_fresh _ _ _ away]
  exact substList_congruent_of_piToPattern_eq _ (piToPattern_alpha_nu binder fresh body notFree)

/-- Substituting a name that does not occur free changes nothing, up to congruence. -/
theorem substList_absent (substitutions : List (Name × Name)) {process : Process} {old : Name} (new : Name)
    (absent : old ∉ process.freeNames) :
    Congruent (substList ((old, new) :: substitutions) process) (substList substitutions process) := by
  refine substList_congruent_of_piToPattern_eq substitutions ?_
  rw [piToPattern_substitute]
  refine applySubst_fresh_single ?_ (piToPattern_noExplicitSubst process)
  rw [isFresh_iff_not_mem]
  exact fun inside => absent ((freeVars_piToPattern process old).mp inside)

/-! ## Each law survives substitution -/

/-- **Structural congruence is closed under substitutions.** -/
theorem congruent_substList {first second : Process} (congruence : first ≡ second) :
    ∀ substitutions : List (Name × Name),
      Congruent (substList substitutions first) (substList substitutions second) := by
  induction congruence with
  | refl process => exact fun _ => Congruent.refl _
  | symm _ _ _ holds => exact fun substitutions => (holds substitutions).symm
  | trans _ _ _ _ _ first second => exact fun substitutions => (first substitutions).trans (second substitutions)
  | par_cong _ _ _ _ _ _ left right =>
    intro substitutions
    rw [substList_par, substList_par]
    exact Congruent.par (left substitutions) (right substitutions)
  | input_cong x binder body body' _ holds =>
    intro substitutions
    obtain ⟨fresh, freshNot⟩ := exists_fresh (body.freeNames ∪ body'.freeNames ∪ substNames substitutions)
    simp only [Finset.mem_union, not_or] at freshNot
    obtain ⟨⟨notBody, notBody'⟩, away⟩ := freshNot
    exact (substList_input substitutions x binder fresh body notBody away).trans
      ((Congruent.input _ fresh (holds ((binder, fresh) :: substitutions))).trans
        (substList_input substitutions x binder fresh body' notBody' away).symm)
  | replicate_cong x binder body body' _ holds =>
    intro substitutions
    obtain ⟨fresh, freshNot⟩ := exists_fresh (body.freeNames ∪ body'.freeNames ∪ substNames substitutions)
    simp only [Finset.mem_union, not_or] at freshNot
    obtain ⟨⟨notBody, notBody'⟩, away⟩ := freshNot
    exact (substList_replicate substitutions x binder fresh body notBody away).trans
      ((Congruent.replicate _ fresh (holds ((binder, fresh) :: substitutions))).trans
        (substList_replicate substitutions x binder fresh body' notBody' away).symm)
  | nu_cong binder body body' _ holds =>
    intro substitutions
    obtain ⟨fresh, freshNot⟩ := exists_fresh (body.freeNames ∪ body'.freeNames ∪ substNames substitutions)
    simp only [Finset.mem_union, not_or] at freshNot
    obtain ⟨⟨notBody, notBody'⟩, away⟩ := freshNot
    exact (substList_nu substitutions binder fresh body notBody away).trans
      ((Congruent.nu fresh (holds ((binder, fresh) :: substitutions))).trans
        (substList_nu substitutions binder fresh body' notBody' away).symm)
  | par_comm left right =>
    intro substitutions
    rw [substList_par, substList_par]
    exact Congruent.comm _ _
  | par_assoc first second third =>
    intro substitutions
    rw [substList_par, substList_par, substList_par, substList_par]
    exact Congruent.assoc _ _ _
  | par_nil_left process =>
    intro substitutions
    rw [substList_par, substList_nil]
    exact Congruent.nilLeft _
  | par_nil_right process =>
    intro substitutions
    rw [substList_par, substList_nil]
    exact Congruent.nilRight _
  | nu_nil binder =>
    intro substitutions
    obtain ⟨fresh, away⟩ := exists_fresh (substNames substitutions)
    refine (substList_nu substitutions binder fresh .nil (by simp [Process.freeNames]) away).trans ?_
    rw [substList_nil, substList_nil]
    exact ⟨.nu_nil fresh⟩
  | nu_par binder left right absent =>
    intro substitutions
    obtain ⟨fresh, freshNot⟩ := exists_fresh (left.freeNames ∪ right.freeNames ∪ substNames substitutions ∪
      (substList substitutions right).freeNames)
    simp only [Finset.mem_union, not_or] at freshNot
    obtain ⟨⟨⟨notLeft, notRight⟩, away⟩, notRest⟩ := freshNot
    have notBoth : fresh ∉ (Process.par left right).freeNames := by
      simp only [Process.freeNames, Finset.mem_union, not_or]
      exact ⟨notLeft, notRight⟩
    refine (substList_nu substitutions binder fresh _ notBoth away).trans ?_
    rw [substList_par, substList_par]
    refine (Congruent.nu fresh (Congruent.par (Congruent.refl _) (substList_absent substitutions fresh absent))).trans
      (Congruent.trans ⟨.nu_par fresh _ _ notRest⟩ ?_)
    exact Congruent.par (substList_nu substitutions binder fresh left notLeft away).symm (Congruent.refl _)
  | nu_swap outer inner body =>
    intro substitutions
    by_cases same : outer = inner
    · subst same
      exact Congruent.refl _
    obtain ⟨first, firstNot⟩ := exists_fresh (body.freeNames ∪ substNames substitutions ∪ {outer, inner})
    obtain ⟨second, secondNot⟩ :=
      exists_fresh (body.freeNames ∪ substNames substitutions ∪ {outer, inner, first})
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at firstNot secondNot
    obtain ⟨⟨firstBody, firstAway⟩, firstOuter, firstInner⟩ := firstNot
    obtain ⟨⟨secondBody, secondAway⟩, secondOuter, secondInner, secondFirst⟩ := secondNot
    have notNuInner : first ∉ (Process.nu inner body).freeNames := by
      simp only [Process.freeNames, Finset.mem_sdiff, not_and, not_not]
      exact fun inside => absurd inside firstBody
    have notNuOuter : second ∉ (Process.nu outer body).freeNames := by
      simp only [Process.freeNames, Finset.mem_sdiff, not_and, not_not]
      exact fun inside => absurd inside secondBody
    have awayFirst : second ∉ substNames ((outer, first) :: substitutions) := by
      simp only [substNames, Finset.mem_insert, not_or]
      exact ⟨secondOuter, secondFirst, secondAway⟩
    have awaySecond : first ∉ substNames ((inner, second) :: substitutions) := by
      simp only [substNames, Finset.mem_insert, not_or]
      exact ⟨firstInner, Ne.symm secondFirst, firstAway⟩
    have commute : Congruent (substList ((inner, second) :: (outer, first) :: substitutions) body)
        (substList ((outer, first) :: (inner, second) :: substitutions) body) := by
      refine congruent_of_piToPattern_eq _ _ _ le_rfl ?_
      simp only [substList]
      rw [piToPattern_substList, piToPattern_substList]
      simp only [piToPattern_substitute]
      rw [applySubst_comm_single (Ne.symm same) secondOuter firstInner _ (piToPattern_noExplicitSubst body)]
    refine (substList_nu substitutions outer first _ notNuInner firstAway).trans ?_
    refine (Congruent.nu first (substList_nu _ inner second body secondBody awayFirst)).trans ?_
    refine Congruent.trans ?_ ((substList_nu substitutions inner second _ notNuOuter secondAway).trans
      (Congruent.nu second (substList_nu _ outer first body firstBody awaySecond))).symm
    exact (Congruent.nu first (Congruent.nu second commute)).trans ⟨.nu_swap first second _⟩
  | alpha_input x binder fresh body notFree _ =>
    exact fun substitutions => substList_congruent_of_piToPattern_eq substitutions
      (piToPattern_alpha_input x binder fresh body notFree)
  | alpha_nu binder fresh body notFree =>
    exact fun substitutions => substList_congruent_of_piToPattern_eq substitutions
      (piToPattern_alpha_nu binder fresh body notFree)
  | alpha_replicate x binder fresh body notFree _ =>
    exact fun substitutions => substList_congruent_of_piToPattern_eq substitutions
      (piToPattern_alpha_replicate x binder fresh body notFree)
  | replicate_unfold x binder body =>
    intro substitutions
    obtain ⟨fresh, freshNot⟩ := exists_fresh (body.freeNames ∪ substNames substitutions)
    simp only [Finset.mem_union, not_or] at freshNot
    obtain ⟨notBody, away⟩ := freshNot
    refine (substList_replicate substitutions x binder fresh body notBody away).trans ?_
    rw [substList_par]
    refine Congruent.trans ⟨.replicate_unfold _ _ _⟩ ?_
    exact Congruent.par (substList_input substitutions x binder fresh body notBody away).symm
      (substList_replicate substitutions x binder fresh body notBody away).symm

/-- **Structural congruence is closed under substitution.** -/
theorem congruent_substitute {first second : Process} (congruent : Congruent first second) (old new : Name) :
    Congruent (first.substitute old new) (second.substitute old new) :=
  match congruent with
  | ⟨congruence⟩ => congruent_substList congruence [(old, new)]

/-! ## Substitutions as maps of free names -/

theorem patternSubstList_eq_mapFVars : ∀ (substitutions : List (Name × Name)) (pattern : Pattern),
    noExplicitSubst pattern = true → patternSubstList substitutions pattern = mapFVars (substName substitutions) pattern
  | [], pattern, _ => (mapFVars_id pattern).symm
  | (old, new) :: rest, pattern, normal => by
    simp only [patternSubstList]
    rw [applySubst_single_eq_mapFVars old new pattern normal,
      patternSubstList_eq_mapFVars rest _ (by rw [noExplicitSubst_mapFVars]; exact normal), mapFVars_mapFVars]
    rfl

theorem substName_of_not_mem : ∀ {substitutions : List (Name × Name)} {name : Name},
    name ∉ substNames substitutions → substName substitutions name = name
  | [], _, _ => rfl
  | (old, new) :: rest, name, absent => by
    simp only [substNames, Finset.mem_insert, not_or] at absent
    simp only [substName, if_neg absent.1]
    exact substName_of_not_mem absent.2.2

theorem substName_mem : ∀ (substitutions : List (Name × Name)) (name : Name),
    substName substitutions name = name ∨ substName substitutions name ∈ substNames substitutions
  | [], _ => Or.inl rfl
  | (old, new) :: rest, name => by
    simp only [substName, substNames, Finset.mem_insert]
    by_cases same : name = old
    · simp only [if_pos same]
      rcases substName_mem rest new with stays | named
      · exact Or.inr (Or.inr (Or.inl stays))
      · exact Or.inr (Or.inr (Or.inr named))
    · simp only [if_neg same]
      rcases substName_mem rest name with stays | named
      · exact Or.inl stays
      · exact Or.inr (Or.inr (Or.inr named))

theorem substList_output : ∀ (substitutions : List (Name × Name)) (x z : Name),
    substList substitutions (.output x z) = .output (substName substitutions x) (substName substitutions z)
  | [], _, _ => rfl
  | (old, new) :: rest, x, z => by
    simp only [substList, substName, Process.substitute_output]
    exact substList_output rest _ _

/-- **A continuation through a fresh binder**: renaming the input's binder to a fresh name, applying the
substitutions, and then receiving is receiving and then applying the substitutions. -/
theorem substList_receive (substitutions : List (Name × Name)) (body : Process) (binder fresh payload : Name)
    (notFree : fresh ∉ body.freeNames) (away : fresh ∉ substNames substitutions) :
    Congruent ((substList ((binder, fresh) :: substitutions) body).substitute fresh (substName substitutions payload))
      (substList substitutions (body.substitute binder payload)) := by
  refine congruent_of_piToPattern_eq _ _ _ le_rfl ?_
  have normal := piToPattern_noExplicitSubst body
  simp only [piToPattern_substitute, piToPattern_substList, patternSubstList]
  have renamedNormal : noExplicitSubst (mapFVars (fun name => if name = binder then fresh else name)
      (piToPattern body)) = true := by rw [noExplicitSubst_mapFVars]; exact normal
  have receivedNormal : noExplicitSubst (mapFVars (fun name => if name = binder then payload else name)
      (piToPattern body)) = true := by rw [noExplicitSubst_mapFVars]; exact normal
  rw [applySubst_single_eq_mapFVars binder fresh _ normal, applySubst_single_eq_mapFVars binder payload _ normal,
    patternSubstList_eq_mapFVars substitutions _ renamedNormal,
    patternSubstList_eq_mapFVars substitutions _ receivedNormal]
  simp only [mapFVars_mapFVars]
  rw [applySubst_single_eq_mapFVars fresh (substName substitutions payload) _
    (by rw [noExplicitSubst_mapFVars]; exact normal)]
  simp only [mapFVars_mapFVars]
  refine mapFVars_congr _ fun name member => ?_
  have notFresh : name ≠ fresh := fun same =>
    notFree ((freeVars_piToPattern body fresh).mp (same ▸ member))
  simp only [Function.comp]
  by_cases isBinder : name = binder
  · simp only [if_pos isBinder, substName_of_not_mem away, if_true]
  · simp only [if_neg isBinder]
    rcases substName_mem substitutions name with stays | named
    · rw [stays, if_neg notFresh]
    · rw [if_neg (fun (same : substName substitutions name = fresh) => away (same ▸ named))]

end Mettapedia.Languages.ProcessCalculi.PiCalculus
