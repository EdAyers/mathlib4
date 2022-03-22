/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: E.W.Ayers
-/
import Mathlib.Data.Sum
import Mathlib.Data.Equiv.Basic

/-!
# Profunctors

Definitions for (non-lawful) profunctors.

-/

/-- A profunctor `P` is a function `Type u → Type u → Type v` that is a functor
on the second argument and a contravariant functor on the first.

Reference: https://en.wikipedia.org/wiki/Profunctor
 -/
class Profunctor (P : Type u → Type v → Type w) where
  dimap {α α' β β'} : (α' → α) → (β → β') → P α β → P α' β'

export Profunctor (dimap)

namespace Profunctor

class StrongCore (P : Type u → Type u → Type v) where
  first {α β : Type u} (χ : Type u) : P α β → P (α × χ) (β × χ)
  second {α β : Type u} (χ : Type u) : P α β → P (χ × α) (χ × β)

export StrongCore (first second)

class ChoiceCore (P : Type u → Type u → Type v) where
  left  {α β} (χ : Type u) : P α β → P (α ⊕ χ) (β ⊕ χ)
  right {α β} (χ : Type u) : P α β → P (χ ⊕ α) (χ ⊕ β)

export ChoiceCore (left right)

class ClosedCore (P : Type u → Type u → Type v) where
  close {α β} : ∀ (X : Type u), P α β → P (X → α) (X → β)

class CostrongCore (P : Type u → Type u → Type v) where
  unfirst  {α β : Type u} (χ : Type u) : P (α × χ) (β × χ) → P α β
  unsecond {α β : Type u} (χ : Type u) : P (χ × α) (χ × β) → P α β

class Affine (P : Type u → Type u → Type v) extends Profunctor P, StrongCore P, ChoiceCore P
/-- A strong profunctor is one that 'plays nice' with products.-/
class Strong (P : Type u → Type u → Type v) extends Profunctor P, StrongCore P
class Costrong (P : Type u → Type u → Type v) extends Profunctor P, CostrongCore P
/-- A strong profunctor is one that 'plays nice' with sums.-/
class Choice (P : Type u → Type u → Type v) extends Profunctor P, ChoiceCore P
class Closed (P : Type u → Type u → Type v) extends Profunctor P, ClosedCore P

/-- `Star F α β = α → F β`-/
def Star (F : Type u → Type v) (α : Type w) (β : Type u) :=
  α → F β

/-- A profunctor is representable when there is a functor `Rep` such there is a
natural isomorphism between  `P α β` and `α → Rep β`.

Contrast this with the definition of a representable functor `F`, where there is a `R : Type` such that `F α ≃ R → α`
  -/
class Representable (P : Type u → Type u → Type v) where
  Rep : Type u → Type v
  eqv {α β} : P α β ≃ Star Rep α β

export Representable (Rep)

/-- Sends an element of `P α β` to its representative `α → Rep P β`. Inverse of `Representable.tabulate` -/
def Representable.sieve [Representable P] : P α β → (α → Rep P β) := Representable.eqv.toFun
/-- Inverse of `Representable.sieve`.-/
def Representable.tabulate [Representable P] : (α → Rep P β) → P α β := Representable.eqv.invFun

/-- Lists a transform `f : Star Rep ⇒ Star Rep` to `P ⇒ P`-/
def Representable.lift [Representable P] {α β σ τ}
  (f : (α → Rep P β) → σ → Rep P τ) : P α β → P σ τ :=
  tabulate ∘ f ∘ sieve

/-- A traversing profunctor is a representable functor where `Rep` is applicative. -/
class Traversing (P) extends (Representable P) where
  [a : Applicative (Rep)]

namespace Star

  variable {F : Type u → Type v}

  instance [Functor F] : Profunctor (Star F) where
    dimap f g h a := g <$> (h $ f a)

  instance [Pure F] [Functor F] : Choice (Star F) where
    left  := fun χ afb => Sum.elim (Functor.map Sum.inl ∘ afb)  (Functor.map Sum.inr ∘ pure)
    right := fun χ afb => Sum.elim (Functor.map Sum.inl ∘ pure) (Functor.map Sum.inr ∘ afb)

  instance [Functor F] : Strong (Star F) where
    first  := fun χ f (a,c) => (fun a => (a, c)) <$> f a
    second := fun χ f (c,a) => (fun a => (c, a)) <$> f a

  instance {F : Type u → Type u} : Representable (Star F) where
    Rep := F
    eqv := Equiv.refl _

end Star

def Yoneda (P : Type u → Type u → Type v) (α β : Type u) :=
  ⦃φ χ : Type u⦄ → (φ → α) → (β → χ) → P φ χ

namespace Yoneda

  def extract : Yoneda P α β → P α β
  | y => y id id

end Yoneda

end Profunctor
