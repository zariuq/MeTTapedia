import Mettapedia.TypeTheory.Calculi.SealedCode.Syntax
import Mettapedia.TypeTheory.Calculi.SealedCode.Reduction
import Mettapedia.TypeTheory.Calculi.SealedCode.Confluence
import Mettapedia.TypeTheory.Calculi.SealedCode.Freshness
import Mettapedia.TypeTheory.Calculi.SealedCode.Boundary

/-!
# Lambda terms with sealed names

An untyped lambda calculus with symbols and three forms for code: the sealed
name `quote M` of closed code, the construction `lift M`, which substitution
enters and which becomes a name once its code is closed and normal, and
`drop K`, which runs the code of a name.

* `Step.subst`: reduction is stable under substitution.
* `church_rosser`, `normal_form_unique`, `name_unique`: reduction is confluent,
  so a program has at most one name.
* `no_self_code`, `fresh_of_size_le`: no program reduces to a term containing
  its own name, and a name of larger code is fresh.
* `asWritten_incoherent`, `unwaited_incoherent`, `unwaited_self_code`,
  `premature_incoherent`, `premature_not_substitution_stable`: sealing code as
  written, naming before a normal form, and naming open code each fail.
* `fill_church_rosser`, `fill_quine`: filling a sealed template with a value as
  written is confluent, and a program built from it steps to its own name.
-/

namespace Mettapedia.TypeTheory.Calculi.SealedCode

#print axioms Step.subst
#print axioms church_rosser
#print axioms name_unique
#print axioms no_self_code
#print axioms fresh_of_size_le
#print axioms letFoo_names
#print axioms twoPath_outer_first
#print axioms twoPath_inner_first
#print axioms asWritten_incoherent
#print axioms unwaited_incoherent
#print axioms unwaited_self_code
#print axioms premature_incoherent
#print axioms premature_not_substitution_stable
#print axioms fill_church_rosser
#print axioms fill_quine

end Mettapedia.TypeTheory.Calculi.SealedCode
