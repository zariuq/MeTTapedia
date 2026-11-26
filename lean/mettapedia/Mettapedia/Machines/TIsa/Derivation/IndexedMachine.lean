import Mettapedia.Machines.TIsa.Derivation.Instructions
import Mettapedia.Machines.TIsa.Derivation.CandidateSearch

/-!
# Installing an index in the derived machine

Only opening a premise changes. A poised scan and every saved retry
agree on the ordered matches that can still succeed. Skipping failed
comparisons is silent at this observation; taking or making an
occurrence is not. The original evaluation proof gives a complete
run of the machine using any such index.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation

universe u v w

variable {T : Type u} {V : Type v} {B : Type w}

inductive SameRetry (M : Matcher T V B) : Failure T V B → Failure T V B → Prop
  | scan {role pattern next before after m older other} :
    before.filterMap (attempt M role pattern m) = after.filterMap (attempt M role pattern m) →
    SameRetry M older other →
    SameRetry M (.scan role pattern next before m older) (.scan role pattern next after m other)
  | rules {rest older other} : SameRetry M older other → SameRetry M (.rules rest older) (.rules rest other)
  | quiescent : SameRetry M .quiescent .quiescent

theorem SameRetry.refl (M : Matcher T V B) : (resume : Failure T V B) → SameRetry M resume resume
  | .scan _ _ _ _ _ older => .scan rfl (SameRetry.refl M older)
  | .rules _ older => .rules (SameRetry.refl M older)
  | .quiescent => .quiescent

inductive SameSearch (M : Matcher T V B) : Config T V B → Config T V B → Prop
  | run {a s} : SameSearch M (.run a s) (.run a s)
  | rules {a s rs before after} : SameRetry M before after →
    SameSearch M (.rules a s rs before) (.rules a s rs after)
  | solve {a s gs m sk before after} : SameRetry M before after →
    SameSearch M (.solve a s gs m sk before) (.solve a s gs m sk after)
  | scan {a s role pattern next before after m older other} :
    before.filterMap (attempt M role pattern m) = after.filterMap (attempt M role pattern m) →
    SameRetry M older other →
    SameSearch M (.scan a s role pattern next before m older) (.scan a s role pattern next after m other)
  | succeed {a s sk m before after} : SameRetry M before after →
    SameSearch M (.succeed a s sk m before) (.succeed a s sk m after)
  | fail {a s before after} : SameRetry M before after → SameSearch M (.fail a s before) (.fail a s after)
  | taking {a s os ws} : SameSearch M (.taking a s os ws) (.taking a s os ws)
  | making {a s ws} : SameSearch M (.making a s ws) (.making a s ws)
  | halt {o} : SameSearch M (.halt o) (.halt o)

theorem SameSearch.refl (M : Matcher T V B) : (c : Config T V B) → SameSearch M c c
  | .run .. => .run
  | .rules _ _ _ r => .rules (SameRetry.refl M r)
  | .solve _ _ _ _ _ r => .solve (SameRetry.refl M r)
  | .scan _ _ _ _ _ _ _ r => .scan rfl (SameRetry.refl M r)
  | .succeed _ _ _ _ r => .succeed (SameRetry.refl M r)
  | .fail _ _ r => .fail (SameRetry.refl M r)
  | .taking .. => .taking
  | .making .. => .making
  | .halt .. => .halt

variable [DecidableEq V] (M : Matcher T V B) (P : List (Rule T)) (access : CandidateAccess M)

def stepUsing (c : Config T V B) : Option (Config T V B) :=
  match c with
  | .solve a s (.premise role pattern :: gs) m sk fk =>
    some (.scan a s role pattern (.goals gs sk) (access.read s m.bindings pattern) m fk)
  | _ => step M P c

def Instruction.executeUsing (i : Instruction T) (c : Config T V B) : Option (Config T V B) :=
  match i, c with
  | .premise role pattern, .solve a s (.premise _ _ :: gs) m sk fk =>
    some (.scan a s role pattern (.goals gs sk) (access.read s m.bindings pattern) m fk)
  | _, _ => i.execute M P c

theorem stepUsing_eq_execute (c : Config T V B) :
    stepUsing M P access c = c.current.bind fun i => i.executeUsing M P access c := by
  cases c with
  | run => rfl
  | rules a s rs fk => cases rs <;> rfl
  | solve a s gs m sk fk =>
    cases gs with
    | nil => rfl
    | cons goal rest => cases goal <;> rfl
  | scan a s role pattern next cands m fk => cases cands <;> rfl
  | succeed a s sk m fk =>
    cases sk with
    | goals => rfl
    | fire => cases a <;> rfl
  | fail a s fk => cases fk <;> rfl
  | taking a s os ws => cases os <;> rfl
  | making a s ws => cases ws <;> rfl
  | halt => rfl

abbrev StepsUsing : Config T V B → Config T V B → Prop :=
  Relation.ReflTransGen fun before after => stepUsing M P access before = some after

private theorem scan_exhausts {a : ℕ} {s : Store V} {role : Role} {pattern : T} {next : Success T}
    {m : Match V B} {fk : Failure T V B} (cs : List (ℕ × V))
    (none : cs.filterMap (attempt M role pattern m) = []) :
    StepsUsing M P access (.scan a s role pattern next cs m fk) (.fail a s fk) := by
  induction cs with
  | nil => exact .single rfl
  | cons first rest ih =>
    cases tried : attempt M role pattern m first with
    | none =>
      exact .head (by simp [stepUsing, step, tried])
        (ih (by simpa only [List.filterMap_cons, tried] using none))
    | some matched => simp [tried] at none

private theorem scan_reaches_next {a : ℕ} {s : Store V} {role : Role} {pattern : T} {next : Success T}
    {m hit : Match V B} {fk : Failure T V B} {answers : List (Match V B)}
    (cs : List (ℕ × V)) (hits : cs.filterMap (attempt M role pattern m) = hit :: answers) :
    ∃ rest, rest.filterMap (attempt M role pattern m) = answers ∧
      StepsUsing M P access (.scan a s role pattern next cs m fk)
        (.succeed a s next hit (.scan role pattern next rest m fk)) := by
  induction cs with
  | nil => cases hits
  | cons first rest ih =>
    cases tried : attempt M role pattern m first with
    | none =>
      obtain ⟨tail, remaining, progressed⟩ := ih (by simpa only [List.filterMap_cons, tried] using hits)
      exact ⟨tail, remaining, .head (by simp [stepUsing, step, tried]) progressed⟩
    | some matched =>
      simp only [List.filterMap_cons, tried, List.cons.injEq] at hits
      obtain ⟨rfl, later⟩ := hits
      exact ⟨rest, later, .single (by simp [stepUsing, step, tried])⟩

private theorem eval_through_index {c : Config T V B} {o : Outcome V} (ev : Eval M P c o) :
    ∀ {other : Config T V B}, SameSearch M c other → StepsUsing M P access other (.halt o) := by
  induction ev with
  | run _ ih =>
    intro _ related
    cases related
    exact .head rfl (ih (.rules .quiescent))
  | rulesNil _ ih =>
    intro _ related
    cases related with
    | rules retry => exact .head rfl (ih (.fail retry))
  | rulesCons _ ih =>
    intro _ related
    cases related with
    | rules retry => exact .head rfl (ih (.solve (.rules retry)))
  | solveNil _ ih =>
    intro _ related
    cases related with
    | solve retry => exact .head rfl (ih (.succeed retry))
  | solvePremise _ ih =>
    intro _ related
    cases related with
    | solve retry =>
      exact .head rfl (ih (.scan (access.exact _ _ _ _).symm retry))
  | solvePass applied _ ih =>
    intro _ related
    cases related with
    | solve retry => exact .head (by simp [stepUsing, step, applied]) (ih (.solve retry))
  | solveFail applied _ ih =>
    intro _ related
    cases related with
    | solve retry => exact .head (by simp [stepUsing, step, applied]) (ih (.fail retry))
  | scanNil _ ih =>
    intro _ related
    cases related with
    | scan equal retry =>
      exact (scan_exhausts M P access _ equal.symm).trans (ih (.fail retry))
  | scanHit tried _ ih =>
    intro _ related
    cases related with
    | scan equal retry =>
      have found := equal.symm
      simp only [List.filterMap_cons, tried] at found
      obtain ⟨_, tail, reached⟩ := scan_reaches_next M P access _ found
      exact reached.trans (ih (.succeed (.scan tail.symm retry)))
  | scanMiss tried _ ih =>
    intro _ related
    cases related with
    | scan equal retry =>
      simp only [List.filterMap_cons, tried] at equal
      exact ih (.scan equal retry)
  | succeedGoals _ ih =>
    intro _ related
    cases related with
    | succeed retry => exact .head rfl (ih (.solve retry))
  | succeedExhausted =>
    intro _ related
    cases related
    exact .single rfl
  | succeedFire _ ih =>
    intro _ related
    cases related
    exact .head rfl (ih .taking)
  | failScan _ ih =>
    intro _ related
    cases related with
    | fail retry =>
      cases retry with
      | scan equal older => exact .head rfl (ih (.scan equal older))
  | failRules _ ih =>
    intro _ related
    cases related with
    | fail retry =>
      cases retry with
      | rules older => exact .head rfl (ih (.rules older))
  | failQuiescent =>
    intro _ related
    cases related with
    | fail retry => cases retry; exact .single rfl
  | takingCons _ ih =>
    intro _ related
    cases related
    exact .head rfl (ih .taking)
  | takingNil _ ih =>
    intro _ related
    cases related
    exact .head rfl (ih .making)
  | makingCons _ ih =>
    intro _ related
    cases related
    exact .head rfl (ih .making)
  | makingNil _ ih =>
    intro _ related
    cases related
    exact .head rfl (ih .run)
  | halt =>
    intro _ related
    cases related
    exact .refl

theorem complete_using (c : Config T V B) :
    StepsUsing M P access c (.halt (c.meaning M P)) :=
  eval_through_index M P access (eval_meaning M P c) (SameSearch.refl M c)

theorem outcome_using_iff (c : Config T V B) (o : Outcome V) :
    StepsUsing M P access c (.halt o) ↔ o = c.meaning M P := by
  constructor
  · intro ran
    obtain ⟨first, one⟩ := BoundedDeterministicRun.run_suffix_of_path (stepUsing M P access) ran
    obtain ⟨second, two⟩ :=
      BoundedDeterministicRun.run_suffix_of_path (stepUsing M P access) (complete_using M P access c)
    have left := one second
    have right := two first
    rw [BoundedDeterministicRun.run_of_none (stepUsing M P access) (.halt o) rfl second] at left
    rw [BoundedDeterministicRun.run_of_none (stepUsing M P access) (.halt (c.meaning M P)) rfl first] at right
    rw [Nat.add_comm second first] at right
    exact Config.halt.inj (left.symm.trans right)
  · rintro rfl
    exact complete_using M P access c

theorem indexed_machine_run_iff (a : ℕ) (s : Store V) (o : Outcome V) :
    StepsUsing M P access (.run a s) (.halt o) ↔ o = run M P a s :=
  (outcome_using_iff M P access (.run a s) o).trans
    (Iff.of_eq (congrArg (o = ·) (runK_eq M P a s)))

end Mettapedia.Machines.TIsa.Derivation
