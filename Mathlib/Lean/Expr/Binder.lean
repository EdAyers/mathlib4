import Lean
import Mathlib.Lean.Expr.Basic
open Lean

structure Binder :=
  (name : Name)
  (info : BinderInfo := BinderInfo.default)
  (type : Expr)
  deriving Inhabited

namespace Binder

  protected def toString (b : Binder) : String :=
    let (l,r) := b.info.brackets
    s!"{l}{b.name} : {b.type}{r}"

  def pp (b : Binder) : MetaM Format := do
    let (l,r) := b.info.brackets
    let type ← Meta.ppExpr b.type
    return f!"{l}{b.name} : {type}{r}"

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
