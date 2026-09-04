import Mettapedia.Languages.KIF.DeclarationDecode
import Mettapedia.Languages.KIF.NestingAudit
import Mettapedia.Languages.KIF.LogicalSyntaxAudit
import Mettapedia.Languages.KIF.BindingAudit
import Mettapedia.Languages.KIF.SignatureAudit
import Mettapedia.Languages.KIF.TaxonomyInference

/-!
# SUO-KIF language support

The current checked layer is a lossless lexer, recovering structural parser,
source-located decoder for core symbol-table declarations, explicit
quantifier-binding audit, and source-derived fixed-arity checking. Logical
elaboration, ontology validation, and inference remain separate stages so
parsed syntax is never mistaken for a validated theory.
-/
