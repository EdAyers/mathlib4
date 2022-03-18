import Lean
open Lean

def Lean.BinderInfo.brackets : BinderInfo → String × String
| BinderInfo.implicit => ("{", "}")
| BinderInfo.strictImplicit => ("⦃", "⦄")
| BinderInfo.instImplicit => ("[", "]")
| _ => ("(",")")

structure Binder :=
  (name : Name)
  (info : BinderInfo := BinderInfo.default)
  (type : Expr)
  deriving Inhabited

namespace Binder

  protected def toString (b : Binder) : String :=
    let (l,r) := b.info.brackets
    s!"{l}{b.name} : {b.type}{r}"

  def toForall : Binder → Expr → Expr
    | ⟨name, info, type⟩, body => mkForall name info type body

  def toLambda : Binder → Expr → Expr
    | ⟨name, info, type⟩, body => mkLambda name info type body

  def ofExpr! : Expr → Binder
    | e@(Expr.forallE n y _ _) => ⟨n, e.binderInfo, y⟩
    | e@(Expr.lam n y _ _) => ⟨n, e.binderInfo, y⟩
    | e@(Expr.letE n y v b _) => ⟨n, e.binderInfo, y⟩
    | _ => panic! "expression with binder expected"

end Binder
