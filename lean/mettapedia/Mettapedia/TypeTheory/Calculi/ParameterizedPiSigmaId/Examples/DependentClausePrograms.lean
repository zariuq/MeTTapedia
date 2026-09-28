import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.Telescopes

/-!
# Dependent application and identity-evidence equations

These programs use the same dependent telescope abstraction and simultaneous
substitution as ordinary equation admission. Application accepts separately
leveled types and a function argument; identity evidence has a value-indexed
result. The execution laws retain the actual substituted function or witness.

The typing laws require a typed context morphism. They do not promote an
arbitrary raw match, or a C implementation, to that evidence.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace DependentEquationPrograms

open TelescopeAbstraction

def applicationContext (sourceLevel targetLevel : LevelExpr) : Tower.Ctx 4 :=
  .snoc (.snoc (.snoc (.snoc .nil (sortTm sourceLevel)) (sortTm targetLevel))
    (.pi (.var 1) (.var 1))) (.var 2)

def applicationType (sourceLevel targetLevel : LevelExpr) : Tower.Tm 0 :=
  closeType (applicationContext sourceLevel targetLevel) (.var 2)

def applicationTerm (sourceLevel targetLevel : LevelExpr) : Tower.Tm 0 :=
  closeTerm (applicationContext sourceLevel targetLevel) (.app (.var 1) (.var 0))

theorem application_body_typed (sourceLevel targetLevel : LevelExpr) :
    Tower.HasType (applicationContext sourceLevel targetLevel)
      (.app (.var 1) (.var 0)) (.var 2) := by
  have function : Tower.HasType (applicationContext sourceLevel targetLevel)
      (.var 1) (.pi (.var 3) (.var 3)) := by
    exact .var 1
  have argument : Tower.HasType (applicationContext sourceLevel targetLevel)
      (.var 0) (.var 3) := by
    exact .var 0
  exact .appElim function argument

theorem application_typed (sourceLevel targetLevel : LevelExpr) :
    Tower.HasType .nil (applicationTerm sourceLevel targetLevel)
      (applicationType sourceLevel targetLevel) :=
  close_typed (application_body_typed sourceLevel targetLevel)

theorem application_type_formed (sourceLevel targetLevel : LevelExpr) :
    Tower.HasType .nil (applicationType sourceLevel targetLevel)
      (sortTm (.max (.succ sourceLevel) (.max (.succ targetLevel)
        (.max (.max sourceLevel targetLevel) (.max sourceLevel targetLevel))))) := by
  apply HasType.piForm (u := .sort (.succ sourceLevel))
    (v := .sort (.max (.succ targetLevel)
      (.max (.max sourceLevel targetLevel) (.max sourceLevel targetLevel))))
  · exact .headType (.sort sourceLevel)
  · exact .sort _
  · apply HasType.piForm (u := .sort (.succ targetLevel))
      (v := .sort (.max (.max sourceLevel targetLevel) (.max sourceLevel targetLevel)))
    · exact .headType (.sort targetLevel)
    · exact .sort _
    · apply HasType.piForm (u := .sort (.max sourceLevel targetLevel))
        (v := .sort (.max sourceLevel targetLevel))
      · apply HasType.piForm (u := .sort sourceLevel) (v := .sort targetLevel)
        · exact .var 1
        · exact .sort _
        · exact .var 1
        · exact .sort _
        · exact .sorts _ _
      · exact .sort _
      · apply HasType.piForm (u := .sort sourceLevel) (v := .sort targetLevel)
        · exact .var 2
        · exact .sort _
        · exact .var 2
        · exact .sort _
        · exact .sorts _ _
      · exact .sort _
      · exact .sorts _ _
    · exact .sort _
    · exact .sorts _ _
  · exact .sort _
  · exact .sorts _ _

theorem application_instance_typed {sourceLevel targetLevel : LevelExpr}
    {target : Tower.Ctx m} {sigma : Sub Tower.Head 4 m}
    (typed : Presentation.CtxMor Tower.rules
      (applicationContext sourceLevel targetLevel) target sigma) :
    Tower.HasType target (.app (sigma 1) (sigma 0)) (sigma 2) := by
  simpa only [subst] using
    (application_body_typed sourceLevel targetLevel).substitute typed

theorem application_executes (sourceLevel targetLevel : LevelExpr)
    (sigma : Sub Tower.Head 4 m) :
    BetaSteps
      (applyClosed (applicationContext sourceLevel targetLevel) sigma
        (liftClosed (applicationTerm sourceLevel targetLevel)))
      (.app (sigma 1) (sigma 0)) := by
  simpa only [subst, applicationTerm] using
    (applyClosed_beta (applicationContext sourceLevel targetLevel) sigma
      (.app (.var 1) (.var 0)))

def reflexivityType (level : LevelExpr) : Tower.Tm 0 :=
  closeType (identityContext level) (.id (.var 1) (.var 0) (.var 0))

def reflexivityTerm (level : LevelExpr) : Tower.Tm 0 :=
  closeTerm (identityContext level) (.refl (.var 0))

theorem reflexivity_body_typed (level : LevelExpr) :
    Tower.HasType (identityContext level) (.refl (.var 0))
      (.id (.var 1) (.var 0) (.var 0)) := by
  apply HasType.reflIntro
  simpa [identityContext, Ctx.lookup, rename, wk] using
    (HasType.var (R := Tower.rules) (Γ := identityContext level) 0)

theorem reflexivity_typed (level : LevelExpr) :
    Tower.HasType .nil (reflexivityTerm level) (reflexivityType level) :=
  close_typed (reflexivity_body_typed level)

theorem reflexivity_type_formed (level : LevelExpr) :
    Tower.HasType .nil (reflexivityType level)
      (sortTm (.max (.succ level) (.max level level))) := by
  apply HasType.piForm (u := .sort (.succ level)) (v := .sort (.max level level))
  · exact .headType (.sort level)
  · exact .sort _
  · apply HasType.piForm (u := .sort level) (v := .sort level)
    · exact .var 0
    · exact .sort _
    · exact .idForm (.var 1) (.sort _) (.var 0) (.var 0)
    · exact .sort _
    · exact .sorts _ _
  · exact .sort _
  · exact .sorts _ _

theorem reflexivity_instance_typed {level : LevelExpr} {target : Tower.Ctx m}
    {sigma : Sub Tower.Head 2 m}
    (typed : Presentation.CtxMor Tower.rules (identityContext level) target sigma) :
    Tower.HasType target (.refl (sigma 0))
      (.id (sigma 1) (sigma 0) (sigma 0)) := by
  simpa only [subst] using (reflexivity_body_typed level).substitute typed

theorem reflexivity_executes (level : LevelExpr) (sigma : Sub Tower.Head 2 m) :
    BetaSteps
      (applyClosed (identityContext level) sigma (liftClosed (reflexivityTerm level)))
      (.refl (sigma 0)) := by
  simpa only [subst, reflexivityTerm] using
    (applyClosed_beta (identityContext level) sigma (.refl (.var 0)))

def familyContext (sourceLevel familyLevel : LevelExpr) : Tower.Ctx 4 :=
  .snoc (.snoc (identityContext sourceLevel) (.pi (.var 1) (sortTm familyLevel)))
    (.app (.var 0) (.var 1))

def familyType (sourceLevel familyLevel : LevelExpr) : Tower.Tm 0 :=
  closeType (familyContext sourceLevel familyLevel) (.app (.var 1) (.var 2))

def familyTerm (sourceLevel familyLevel : LevelExpr) : Tower.Tm 0 :=
  closeTerm (familyContext sourceLevel familyLevel) (.var 0)

theorem family_body_typed (sourceLevel familyLevel : LevelExpr) :
    Tower.HasType (familyContext sourceLevel familyLevel) (.var 0)
      (.app (.var 1) (.var 2)) := by
  exact .var 0

theorem family_typed (sourceLevel familyLevel : LevelExpr) :
    Tower.HasType .nil (familyTerm sourceLevel familyLevel)
      (familyType sourceLevel familyLevel) :=
  close_typed (family_body_typed sourceLevel familyLevel)

theorem family_type_formed (sourceLevel familyLevel : LevelExpr) :
    Tower.HasType .nil (familyType sourceLevel familyLevel)
      (sortTm (.max (.succ sourceLevel) (.max sourceLevel
        (.max (.max sourceLevel (.succ familyLevel)) (.max familyLevel familyLevel))))) := by
  apply HasType.piForm (u := .sort (.succ sourceLevel))
    (v := .sort (.max sourceLevel
      (.max (.max sourceLevel (.succ familyLevel)) (.max familyLevel familyLevel))))
  · exact .headType (.sort sourceLevel)
  · exact .sort _
  · apply HasType.piForm (u := .sort sourceLevel)
      (v := .sort (.max (.max sourceLevel (.succ familyLevel)) (.max familyLevel familyLevel)))
    · exact .var 0
    · exact .sort _
    · apply HasType.piForm (u := .sort (.max sourceLevel (.succ familyLevel)))
        (v := .sort (.max familyLevel familyLevel))
      · apply HasType.piForm (u := .sort sourceLevel) (v := .sort (.succ familyLevel))
        · exact .var 1
        · exact .sort _
        · exact .headType (.sort familyLevel)
        · exact .sort _
        · exact .sorts _ _
      · exact .sort _
      · apply HasType.piForm (u := .sort familyLevel) (v := .sort familyLevel)
        · have function : Tower.HasType
              (.snoc (identityContext sourceLevel) (.pi (.var 1) (sortTm familyLevel)))
              (.var 0) (.pi (.var 2) (sortTm familyLevel)) := .var 0
          have argument : Tower.HasType
              (.snoc (identityContext sourceLevel) (.pi (.var 1) (sortTm familyLevel)))
              (.var 1) (.var 2) := .var 1
          exact .appElim function argument
        · exact .sort _
        · have function : Tower.HasType (familyContext sourceLevel familyLevel)
              (.var 1) (.pi (.var 3) (sortTm familyLevel)) := .var 1
          have argument : Tower.HasType (familyContext sourceLevel familyLevel)
              (.var 2) (.var 3) := .var 2
          exact .appElim function argument
        · exact .sort _
        · exact .sorts _ _
      · exact .sort _
      · exact .sorts _ _
    · exact .sort _
    · exact .sorts _ _
  · exact .sort _
  · exact .sorts _ _

theorem family_instance_typed {sourceLevel familyLevel : LevelExpr}
    {target : Tower.Ctx m} {sigma : Sub Tower.Head 4 m}
    (typed : Presentation.CtxMor Tower.rules
      (familyContext sourceLevel familyLevel) target sigma) :
    Tower.HasType target (sigma 0) (.app (sigma 1) (sigma 2)) := by
  simpa only [subst] using (family_body_typed sourceLevel familyLevel).substitute typed

theorem family_executes (sourceLevel familyLevel : LevelExpr) (sigma : Sub Tower.Head 4 m) :
    BetaSteps
      (applyClosed (familyContext sourceLevel familyLevel) sigma
        (liftClosed (familyTerm sourceLevel familyLevel))) (sigma 0) := by
  simpa only [subst, familyTerm] using
    (applyClosed_beta (familyContext sourceLevel familyLevel) sigma (.var 0))

/-- Identity evidence is not the transported type argument. -/
theorem reflexivity_result_is_not_a_sort (argument : Tower.Tm n) (level : LevelExpr) :
    (.refl argument : Tower.Tm n) ≠ sortTm level := by
  intro equality
  cases equality

#print axioms application_typed
#print axioms application_type_formed
#print axioms application_instance_typed
#print axioms application_executes
#print axioms reflexivity_typed
#print axioms reflexivity_type_formed
#print axioms reflexivity_instance_typed
#print axioms reflexivity_executes
#print axioms reflexivity_result_is_not_a_sort
#print axioms family_typed
#print axioms family_type_formed
#print axioms family_instance_typed
#print axioms family_executes

end DependentEquationPrograms
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
