import Lean
import Mathlib.Lean.Expr.Binder

namespace Lean.Expr

#check Expr

inductive Coord where
| appFn | appArg
| lamType | lamBody
| forallType | forallBody
| letType | letValue | letBody
| mdata
| proj


/-- Returns the set of coordinates that are valid for a given expression. -/
def coords : Expr → List Coord
| Expr.app _ _ _       => [Coord.appFn, Coord.appArg]
| Expr.lam _ _ _ _     => [Coord.lamType, Coord.lamBody]
| Expr.forallE _ _ _ _ => [Coord.forallType, Coord.forallBody]
| Expr.letE _ _ _ _ _  => [Coord.letType, Coord.letValue, Coord.letBody]
| Expr.mdata _ _ _     => [Coord.mdata]
| Expr.proj _ _ _ _    => [Coord.proj]
| _                    => []

/-- Perform `g` on the subexpression specified by the coordinate and return the parent expression with this modified child.
The list of binders provided to `g` has the most recently followed binder as the head,
so `Expr.var 0` corresponds to the head of the binder list. -/
def Coord.modify {T} [Alternative T] (g : Array Binder → Expr → T Expr): Coord → Expr → T Expr
| Coord.appFn,      e@(app f a _)         => pure e.updateApp!     <*> g #[] f <*> pure a
| Coord.appArg,     e@(app f a _)         => pure e.updateApp!     <*> pure f  <*> g #[] a
| Coord.lamType,    e@(lam _ y b _)       => pure e.updateLambdaE! <*> g #[] y <*> pure b
| Coord.lamBody,    e@(lam _ y b _)       => pure e.updateLambdaE! <*> pure y  <*> g #[Binder.ofExpr! e] b
| Coord.forallType, e@(forallE _ y b _)   => pure e.updateForallE! <*> g #[] y <*> pure b
| Coord.forallBody, e@(forallE _ y b _)   => pure e.updateForallE! <*> pure y  <*> g #[Binder.ofExpr! e] b
| Coord.letType,    e@(letE _ y a b _)    => pure e.updateLet!     <*> g #[] a <*> pure a  <*> pure b
| Coord.letValue,   e@(letE _ y a b _)    => pure e.updateLet!     <*> pure y  <*> g #[] a <*> pure b
| Coord.letBody,    e@(letE _ y a b _)    => pure e.updateLet!     <*> pure y  <*> pure a  <*> g #[Binder.ofExpr! e] b
| Coord.mdata,      e@(Expr.mdata _ a _)  => e.updateMData!        <$> g #[] a
| Coord.proj,       e@(Expr.proj _ _ b _) => e.updateProj!         <$> g #[] b
| _,                    _                 => failure

end Lean.Expr
