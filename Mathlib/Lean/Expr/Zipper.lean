import Lean
import Mathlib.Lean.Expr.Binder

namespace Lean.Expr

open Lean.Meta

/-- An enum for each recursive argument in the Expr constructors.
Note the mdata constructor is considered transparent. -/
inductive Coord where
  | appFn | appArg
  | lamDomain | lamBody
  | forallDomain | forallBody
  | letVarType | letValue | letBody
  | proj
  deriving Repr

/-- Returns the set of coordinates that are valid for a given expression. -/
def coords : Expr → List Coord
  | Expr.app _ _ _       => [Coord.appFn, Coord.appArg]
  | Expr.lam _ _ _ _     => [Coord.lamDomain, Coord.lamBody]
  | Expr.forallE _ _ _ _ => [Coord.forallDomain, Coord.forallBody]
  | Expr.letE _ _ _ _ _  => [Coord.letVarType, Coord.letValue, Coord.letBody]
  | Expr.mdata _ e _     => coords e
  | Expr.proj _ _ _ _    => [Coord.proj]
  | _                    => []

/-- Convert a coordinate to a delaborator position. -/
def Coord.toPos : Coord → Lean.PrettyPrinter.Delaborator.Pos
  | Coord.appFn => 0
  | Coord.appArg => 1
  | Coord.lamDomain => 0
  | Coord.lamBody => 1
  | Coord.forallDomain => 0
  | Coord.forallBody => 1
  | Coord.letVarType => 0
  | Coord.letValue => 1
  | Coord.letBody => 2
  | Coord.proj => 0

/-- Perform `g` on the subexpression specified by the coordinate and return the parent expression with this modified child.
If the traversal occurs under a binder, this is converted to a free variable and instantiated before running `g` and is re-abstracted afterward.
The list of binders provided to `g` has the most recently followed binder as the head,
so `Expr.var 0` corresponds to the head of the binder list. -/
def Coord.traverse {M} [Monad M] [MonadLiftT MetaM M] [MonadControlT MetaM M] [MonadError M] (g : Expr → M Expr): Coord → Expr → M Expr
| Coord.appFn,      e@(app f a _)         => pure e.updateApp!     <*> g f <*> pure a
| Coord.appArg,     e@(app f a _)         => pure e.updateApp!     <*> pure f  <*> g a
| Coord.lamDomain,    e@(lam _ y b _)       => pure e.updateLambdaE! <*> g y <*> pure b
| Coord.lamBody,    e@(lam n y b c)       => pure e.updateLambdaE! <*> pure y  <*> withLocalDecl n c.binderInfo y fun x => do mkLambdaFVars #[x] (← g (b.instantiateRev #[x]))
| Coord.forallDomain, e@(forallE _ y b _)   => pure e.updateForallE! <*> g y <*> pure b
| Coord.forallBody, e@(forallE n y b c)   => pure e.updateForallE! <*> pure y  <*> withLocalDecl n c.binderInfo y fun x => do mkForallFVars #[x] (← g (b.instantiateRev #[x]))
| Coord.letVarType,    e@(letE _ y a b _)    => pure e.updateLet!     <*> g a <*> pure a  <*> pure b
| Coord.letValue,   e@(letE _ y a b _)    => pure e.updateLet!     <*> pure y  <*> g a <*> pure b
| Coord.letBody,    e@(letE n y a b c)    => pure e.updateLet!     <*> pure y  <*> pure a  <*> withLetDecl n y a fun x => do mkLetFVars #[x] (← g (b.instantiateRev #[x]))
| Coord.proj,       e@(Expr.proj _ _ b _) => e.updateProj!         <$> g b
| c,                    e                 => throwError "Invalid coordinate {repr c} for expression {e}"

/-- An address is a set of instructions to recover a subexpression from a given expression.
It performs the same role as Pos in Lean.PrettyPrinter.Delaborator -/
def Address := List Coord

end Lean.Expr
