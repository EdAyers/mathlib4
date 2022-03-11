/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: E.W.Ayers

This should be replaced eventually with Simon Hudon's mathlib3 version.
-/
class Traversable (T : Type u → Type u) extends Functor T :=
  (traverse ⦃M : Type u → Type u⦄ [Applicative M] {α β} : (α → M β) → T α → M (T β))

variable {T : Type u → Type u} [Traversable T]
variable {M : Type u → Type u} [Applicative M]

export Traversable (traverse)
def sequence : T (M α) → M (T α) := traverse id
