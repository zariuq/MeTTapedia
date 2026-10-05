import Mettapedia.GSLT.LanguageDef.OracleExtension

/-!
# Specified oracle realizations

An admitted oracle library declares typed operations; a native realization
assigns each a backend operation. Neither says what the operation must return.
This module adds that obligation without changing the existing layer:

* a *meaning* of the library relates each declaration's arguments to the
  results it may return;
* a *model* of the backend says what each backend operation returns;
* a realization *meets* a meaning when, in the model, every implemented
  operation returns exactly the related results.

Two realizations that meet one meaning return the same results on every call,
so one may replace the other. A realization whose model returns a result
outside the meaning does not meet it.

`Meets` is a statement about the model. Whether a compiled implementation
agrees with its model is a separate dependency; a theorem about the running
code must carry it as an explicit hypothesis.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.OracleRealization

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.OracleExtension

variable {language : LanguageDef}

/-- The admitted declarations of a library. -/
abbrev Admitted (library : AdmittedLibrary language) :=
  {declaration : OracleDecl // declaration ∈ library.1}

/-- **The meaning of a library**: the results each declaration may return on
each argument list. -/
structure Meaning (library : AdmittedLibrary language) where
  relates : Admitted library → List Pattern → Pattern → Prop

/-- **A model of backend operations**: what each returns on argument lists. -/
structure BackendModel (Backend : Type*) where
  run : Backend → List Pattern → Option Pattern

variable {library : AdmittedLibrary language} {Backend : Type*}

/-- **A realization meets a meaning** when the model of each implemented
operation returns exactly the related results. -/
def Meets (realization : NativeRealization language library Backend)
    (model : BackendModel Backend) (meaning : Meaning library) : Prop :=
  ∀ declaration arguments result,
    model.run (realization.implementation declaration) arguments = some result ↔
      meaning.relates declaration arguments result

/-- **A realization returning a result outside the meaning does not meet
it.** -/
theorem not_meets_of_wrong_result {realization : NativeRealization language library Backend}
    {model : BackendModel Backend} {meaning : Meaning library} {declaration : Admitted library}
    {arguments : List Pattern} {result : Pattern}
    (returns : model.run (realization.implementation declaration) arguments = some result)
    (wrong : ¬ meaning.relates declaration arguments result) :
    ¬ Meets realization model meaning :=
  fun meets => wrong ((meets declaration arguments result).mp returns)

/-- **Realizations meeting one meaning are interchangeable**: their models
return the same result on every call. -/
theorem meets_agree {Backend' : Type*} {realization : NativeRealization language library Backend}
    {model : BackendModel Backend} {realization' : NativeRealization language library Backend'}
    {model' : BackendModel Backend'} {meaning : Meaning library}
    (meets : Meets realization model meaning) (meets' : Meets realization' model' meaning)
    (declaration : Admitted library) (arguments : List Pattern) :
    model.run (realization.implementation declaration) arguments =
      model'.run (realization'.implementation declaration) arguments := by
  cases first : model.run (realization.implementation declaration) arguments with
  | some result =>
      exact ((meets' declaration arguments result).mpr
        ((meets declaration arguments result).mp first)).symm
  | none =>
      cases second : model'.run (realization'.implementation declaration) arguments with
      | none => rfl
      | some result =>
          have returned := (meets declaration arguments result).mpr
            ((meets' declaration arguments result).mp second)
          rw [first] at returned
          cases returned

end Mettapedia.GSLT.LanguageDef.OracleRealization
