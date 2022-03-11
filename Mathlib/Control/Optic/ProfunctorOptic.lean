/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: E.W.Ayers
-/
import Mathlib.Control.Profunctor
import Mathlib.Data.Prod
import Mathlib.Control.Optic.Concrete
import Mathlib.Control.Traversable
/-!
# Profunctor optics
Definitions of profunctor optics.

One way to think about profunctor optics is to look at traversal:

```
traverse : (f : α → M β) → (l : List α) → M (List β)
```

`traverse` selects all the objects in `l` and performs `f` to them under
the monad `M`, then wraps all these up back in to a list.

Optics generalise this notion of unpacking a datastructure, performing some arbitrary action and then repackaging the datastructure.
Let's define `P α β := α → M β`, then we have `traverse : P α β → P (List α) (List β)`.


### References:
- https://hackage.haskell.org/package/profunctor-optics-0.0.2/docs/index.html
- https://dl.acm.org/doi/pdf/10.1145/3236779
- https://golem.ph.utexas.edu/category/2020/01/profunctor_optics_the_categori.html
- http://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/poptics.pdf
- https://github.com/hablapps/DontFearTheProfunctorOptics
-/

namespace Control

open Profunctor

set_option checkBinderAnnotations false in
/-- A general profunctor optic. -/
def Optic (π : (Type → Type → Type) → Type 1) (α β σ τ : Type) :=
∀ ⦃P⦄ [c : π P], P α β → P σ τ

namespace Optic

def Iso := Optic Profunctor

def Lens               := Optic Strong
def Lens' (α β)        := Lens α α β β

def Prism              := Optic Choice
def Prism' (α β)       := Prism α α β β

/-- Also known as an affine traversal or a traversal0. -/
def Affinal            := Optic Affine
def Affinal' (α β)     := Affinal α α β β

def Traversal          := Optic Traversing

namespace Iso
  def mk (g : σ → α) (f : β → τ) : Iso α β σ τ
  | _, _, p => Profunctor.dimap g f p
end Iso

namespace Lens
  def mk (g : σ → α) (s : β → σ → τ) : Lens α β σ τ
  | _, _, f => dimap (Prod.intro g id) (Prod.elim s) $ first σ $ f

  def view (l : Lens α β σ τ) : σ → α :=
  Concrete.Lens.view $ l $ Concrete.Lens.id

  def update (l : Lens α β σ τ) : β → σ → τ :=
  Concrete.Lens.update $ l $ Concrete.Lens.id

  def matching (sca : σ → γ × α) (cbt : γ × β → τ) : Lens α β σ τ :=
  mk (Prod.snd ∘ sca) (fun b s => cbt (Prod.fst $ sca s,b))

  def united : Lens Unit Unit α α := mk (fun a => Unit.unit) (fun x a => a)
  def voided : Lens α α Empty Empty := mk (fun e => by cases e) (fun a e => e)

  protected def id : Lens α β α β := mk (λ a => a) (λ b _ => b)
end Lens

namespace Prism

  def view (p : Prism α β σ τ) : σ → τ ⊕ α :=
  Concrete.Prism.get $ p $ Concrete.Prism.id

  def update (p : Prism α β σ τ) : β → τ :=
  Concrete.Prism.review $ p $ Concrete.Prism.id

  def mk (g : σ → τ ⊕ α) (s : β → τ) : Prism α β σ τ
  | _, _, f => dimap g (Sum.elim id s) $ right _ $ f

end Prism

namespace Affinal
  def mk (f : σ → τ ⊕ α) (g : σ → β → τ) : Affinal α β σ τ
  | _, _, p => dimap (Prod.intro id f) (Function.uncurry $ Sum.elim id ∘ g) $ second σ $ right τ p

end Affinal

def traversing [Traversable F] : Traversal σ τ (F σ) (F τ)
| P, t => Representable.lift (@traverse _ _ _ t.a _ _)

end Optic

end Control
