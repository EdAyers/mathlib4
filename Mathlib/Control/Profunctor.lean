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

class Profunctor (P : Type → Type → Type) :=
  (dimap {α α' β β'} : (α' → α) → (β → β') → P α β → P α' β')

export Profunctor (dimap)

namespace Profunctor

class StrongCore (P : Type → Type → Type) :=
(first {α β} (χ) : P α β → P (α × χ) (β × χ))
(second {α β} (χ) : P α β → P (χ × α) (χ × β))

export StrongCore (first second)

class ChoiceCore (P : Type → Type → Type) :=
(left  {α β} (χ) : P α β → P (α ⊕ χ) (β ⊕ χ))
(right {α β} (χ) : P α β → P (χ ⊕ α) (χ ⊕ β))

export ChoiceCore (left right)

class ClosedCore (P : Type → Type → Type) :=
(close {α β : Type} : ∀ (X : Type), P α β → P (X → α) (X → β))

class CostrongCore (P : Type → Type → Type) :=
(unfirst  {α β} (χ : Type) : P (α × χ) (β × χ) → P α β)
(unsecond {α β} (χ : Type) : P (χ × α) (χ × β) → P α β)

class Affine (P : Type → Type → Type) extends Profunctor P, StrongCore P, ChoiceCore P
class Strong (P : Type → Type → Type) extends Profunctor P, StrongCore P
class Costrong (P : Type → Type → Type) extends Profunctor P, CostrongCore P
class Choice (P : Type → Type → Type) extends Profunctor P, ChoiceCore P
class Closed (P : Type → Type → Type) extends Profunctor P, ClosedCore P

def Star (F : Type → Type) (α β : Type) := α → F β

class Representable (P : Type → Type → Type) :=
(Rep : Type → Type)
(eqv {α β} : P α β ≃ Star Rep α β)

export Representable (Rep)

def Representable.sieve [Representable P] : P α β → (α → Rep P β) := Representable.eqv.toFun
def Representable.tabulate [Representable P] : (α → Rep P β) → P α β := Representable.eqv.invFun

def Representable.lift [Representable P] {α β σ τ}
  (f : (α → Rep P β) → σ → Rep P τ) : P α β → P σ τ
  := tabulate ∘ f ∘ sieve

class Traversing (P : Type → Type → Type) extends (Representable P) :=
[a : Applicative (Rep)]

namespace Star

  variable {F : Type → Type} [Functor F]

  instance : Profunctor (Star F) where
    dimap f g h a := g <$> (h $ f a)

  instance [Pure F] [Functor F] : Choice (Star F) where
    left := fun χ afb => Sum.elim (Functor.map Sum.inl ∘ afb) (Functor.map Sum.inr ∘ pure)
    right := fun χ afb => Sum.elim  (Functor.map Sum.inl ∘ pure) (Functor.map Sum.inr ∘ afb)

  instance [Functor F] : Strong (Star F) where
    first := fun χ f (a,c) =>  (fun a => (a, c)) <$> f a
    second := fun χ f (c,a) => (fun a => (c, a)) <$> f a

  instance : Representable (Star F) where
    Rep := F
    eqv := Equiv.refl _

end Star

def Yoneda (P : Type → Type → Type) (α β : Type) :=
  {φ χ : Type} → (φ → α) → (β → χ) → P φ χ

namespace Yoneda

  def extract : Yoneda P α β → P α β
  | y => y id id

end Yoneda

end Profunctor
