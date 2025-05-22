import Loda.Ast

namespace Circuit

/-- Circuit Declaration. -/
structure Circuit where
  name    : String
  inputs  : String × Ast.Ty
  output  : String × Ast.Ty
  body    : Ast.Expr

end Circuit
