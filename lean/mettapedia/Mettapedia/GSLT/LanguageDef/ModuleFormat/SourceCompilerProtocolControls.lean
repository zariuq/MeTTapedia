import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCompilerProtocol

/-! Complete writer/reader controls for the source-provider value protocol.
Host truth recognition must not strand Boolean fields in otherwise ordinary
module data. Literal strings retain their separate value kind. -/

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCompilerProtocol

#guard value? (renderValue (.boolean true)) = .ok (.boolean true)
#guard value? (renderValue (.boolean false)) = .ok (.boolean false)
#guard value? (renderValue (.string "True")) = .ok (.string "True")
#guard value? (renderValue (.record [("flag", .boolean true),
    ("nested", .list [.boolean false, .string "λ\\q\u0000", .integer (-12), .nil])] )) =
  .ok (.record [("flag", .boolean true),
    ("nested", .list [.boolean false, .string "λ\\q\u0000", .integer (-12), .nil])])
#guard (value? "(Record (Field \"bad\" $unbound))").toOption.isNone

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCompilerProtocol
