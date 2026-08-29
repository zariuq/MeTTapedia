import Mettapedia.GSLT.LanguageDef.MultiSortedClone
import Mettapedia.GSLT.LanguageDef.CertificateGSLTDAGTransport

/-!
# The internal proof calculus of a CertificateGSLT

For each validated semantic definition, open derivations form a multisorted
clone.  The sorts are ground judgment patterns; operations are derivations
from an ordered premise context; variables are premise occurrences; and clone
substitution is proof plugging.

This is the framework-level internal logic.  It supplies the cartesian/Horn
structural core while leaving logical connectives, binders, conversion, and
side judgments to the presented object theory.  Chronological DAGs are compact
evidence for these operations, but their sharing-sensitive artifact identity
is retained separately from the clone equations on expanded derivations.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Open derivations of one definition satisfy the multisorted clone laws. -/
def derivationClone (object : Object) :
    Mettapedia.GSLT.LanguageDef.MultiSortedClone Pattern where
  Hom context goal := OpenDerivation object.definition context goal
  project index := .assumption index
  substitute operation environment :=
    operation.bind (OpenDerivationList.ofFn _ environment)
  substitute_project environment index := by
    simp [OpenDerivation.bind, OpenDerivationList.get_ofFn]
  substitute_projects operation :=
    OpenDerivation.bind_assumptionEnvironment operation
  substitute_assoc operation first second := by
    rw [OpenDerivation.bind_assoc, OpenDerivationList.ofFn_bind]

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
