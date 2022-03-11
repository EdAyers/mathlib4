/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: E.W.Ayers
-/
import Mathlib.Control.Profunctor
import Mathlib.Data.Sum
import Mathlib.Data.Vector
open Profunctor
namespace Control.Optic.Concrete

/-!
# Concrete optics

This file contains definitions of 'concrete' optics.
These are the definitions that don't include any fancy monads or abstractions.
It's just the concrete datastructure that defines a lens or a prism.
-/

variable {α β C σ τ : Type}

structure Lens (α β σ τ : Type) :=
  (view : σ → α)
  (update : β → σ → τ)

namespace Lens

  protected def id : Lens α β α β := ⟨id, fun b a => b⟩

  instance : Strong (Lens α β) where
    dimap ts uv := fun ⟨v,u⟩ => ⟨v ∘ ts, fun b t => uv $ u b $ ts t⟩
    first := fun C ⟨v,u⟩ => ⟨fun ⟨x,c⟩ => v x , fun b ⟨x,c⟩ => ⟨u b x,c⟩⟩
    second := fun C ⟨v,u⟩ => ⟨fun ⟨c,x⟩ => v x , fun b ⟨c,x⟩ => ⟨c, u b x⟩⟩

  instance is_strong : Strong (Lens α β) := {}

end Lens

structure Prism (α β σ τ : Type) :=
  (get : σ → τ ⊕ α)
  (review : β → τ)

namespace Prism

  def preview (p : Prism α β σ τ) (s : σ) : Option α :=
    match p.get s with
    | (Sum.inl x) => none
    | (Sum.inr y) => some y

  protected def id : Prism α β α β := ⟨Sum.inr, id⟩

  open Sum

  instance : Choice (Prism α β) where
    dimap ts uv p := ⟨Sum.map uv id ∘ p.get ∘ ts, uv ∘ p.review⟩
    left := fun C ⟨g,r⟩ => ⟨elim (elim (inl ∘ inl) inr ∘ g) (inl ∘ inr), inl ∘ r⟩
    right := fun C ⟨g,r⟩ => ⟨elim (inl ∘ inl) (elim (inl ∘ inr) inr ∘ g), inr ∘ r⟩

end Prism

inductive FunOpt (α β τ : Type)
| zero (t : τ)
| one (get : α) (set : β → τ)

namespace FunOpt
  instance : Functor (FunOpt α β) where
    map f := fun
              | zero t => zero $ f t
              | one g s => one g (f ∘ s)

  instance : Pure (FunOpt α β) where
    pure := zero

  -- [note] FunOpt α β is not applicative.

end FunOpt

def Affinal (α β : Type) := Star (FunOpt α β)

namespace Affinal
  instance : Profunctor (Affinal α β) :=
    show Profunctor (Star _) by infer_instance

  instance {α β : Type} : Choice (Affinal α β) :=
    show Choice (Star _) by infer_instance

  instance : Strong (Affinal α β) :=
    show Strong (Star _) by infer_instance

  instance : Affine (Affinal α β) := Affine.mk
end Affinal

/-- FunList is the concrete datastructure that makes
`Star (Funlist α β) σ τ` a Traversing profunctor. -/
structure FunList (α β τ : Type) :=
  (n : Nat)
  (get : Vector α n)
  (set : (Vector β n) → τ)

namespace FunList
  instance : Functor (FunList α β) where
    map f a := {n := a.n, get := a.get, set := f ∘ a.set}
  instance : Applicative (FunList α β) where
    pure t := {n := 0, get := Vector.nil, set := fun _ => t}
    seq f a :=
      let a := a ()
      { n := (f.n + a.n)
      , get := Vector.append f.get a.get
      , set := fun bs =>
          let (l, r) := Vector.split f.n bs
          f.set l $ a.set r
      }

  def zero : τ → FunList α β τ := pure
  def one (a : α) (f : β → τ) : FunList α β τ:=
    { n   := 1
    , get := Vector.singleton a
    , set := f ∘ Vector.head
    }

end FunList

def Traversal (α β) := Star (FunList α β)

namespace Traversal
  instance : Representable (Traversal α β) :=
    show Representable (Star _) by infer_instance

  instance : Traversing (Traversal α β) where
    a := FunList.instApplicativeFunList

end Traversal


end Control.Optic.Concrete
