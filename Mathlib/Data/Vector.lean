/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
Ported by: E.W.Ayers

Tuples are lists of a fixed size.
It is implemented as a subtype.
-/
import Mathlib.Data.List.Basic
universe u v w

def Vector (α : Type u) (n : Nat) :=
{ l : List α // l.length = n }

namespace Vector
variable {α : Type u} {β : Type v} {φ : Type w}
variable {n : Nat}

instance [DecidableEq α] : DecidableEq (Vector α n) :=
show DecidableEq (Subtype _) by infer_instance

def nil : Vector α 0 := ⟨[],  rfl⟩

def cons : α → Vector α n → Vector α (Nat.succ n)
| a, ⟨ v, h ⟩ => ⟨a::v, congrArg Nat.succ h⟩

@[reducible] def length (v : Vector α n) : Nat := n

open Nat

def head : Vector α (Nat.succ n) → α
| ⟨ [],    h ⟩ => by contradiction
| ⟨ a :: v, h ⟩ => a

theorem head_cons (a : α) : (v : Vector α n) → head (cons a v) = a
| ⟨ l, h ⟩ => rfl

def tail : Vector α n → Vector α (n - 1)
| ⟨ [],     h ⟩ => ⟨ [], congrArg pred h ⟩
| ⟨ a :: v, h ⟩ => ⟨ v, congrArg pred h ⟩

theorem tail_cons (a : α) : (v : Vector α n) → tail (cons a v) = v
| ⟨ l, h ⟩ => rfl

@[simp] theorem cons_head_tail : ∀ v : Vector α (succ n), (cons (head v) (tail v)) = v
| ⟨ [],     h ⟩ => by contradiction
| ⟨ a :: v, h ⟩ => rfl

def to_list (v : Vector α n) : List α := v.1

def singleton (a : α) : Vector α 1 := cons a nil

-- def nth : (v : Vector α n) → Fin n → α
-- | ⟨ l, h ⟩, i  => l.nth_le i.1 (by rw [h]; exact i.2)

def append {n m : Nat} : Vector α n → Vector α m → Vector α (n + m)
| ⟨ l₁, h₁ ⟩, ⟨ l₂, h₂ ⟩  => ⟨ l₁ ++ l₂, by simp [h₁, h₂]⟩

-- @[elab_as_eliminator]
def elim {α} {C : {n : Nat} → Vector α n → Sort u} (H : ∀ (l : List α), C ⟨l, rfl⟩)
  {n : Nat} : (v : Vector α n) → C v
| ⟨l, h⟩  => match n, h with | _, rfl => H l

-- /- map -/

-- def map (f : α → β) : Vector α n → Vector β n
-- | ⟨ l, h ⟩  => ⟨ List.map f l, by simp;  ⟩

-- @[simp] theorem map_nil (f : α → β) : map f nil = nil := rfl

-- theorem map_cons (f : α → β) (a : α) : Π (v : Vector α n), map f (cons a v) = cons (f a) (map f v)
-- | ⟨l,h⟩ := rfl

-- def map₂ (f : α → β → φ) : Vector α n → Vector β n → Vector φ n
-- | ⟨ x, _ ⟩, ⟨ y, _ ⟩ => ⟨ list.map₂ f x y, by simp * ⟩

-- def repeat (a : α) (n : Nat) : Vector α n :=
-- ⟨ list.repeat a n, list.length_repeat a n ⟩

def drop (i : Nat) : Vector α n → Vector α (n - i)
| ⟨l, p⟩ => ⟨ List.drop i l, by simp [*]⟩

def take (i : Nat) : Vector α n → Vector α (min i n)
| ⟨l, p⟩ => ⟨ List.take i l, by simp [*]⟩

def split (i : Nat) : Vector α (i + n) → Vector α i × Vector α n
| ⟨l, p⟩ =>
  have e₁ : (min i (i + n)) = i := (Nat.min_eq_left $ Nat.le_add_right _ _)
  have e₂: (i + n - i) = n := (Nat.add_sub_cancel_left _ _)
  (⟨List.take i l, by simp [p, e₁]⟩, ⟨List.drop i l, by simp [p, e₂]⟩)

-- def remove_nth (i : fin n) : Vector α n → Vector α (n - 1)
-- | ⟨l, p⟩ => ⟨ list.remove_nth l i.1, by rw [l.length_remove_nth i.1]; rw [p]; exact i.2 ⟩

def of_fn : {n : Nat} → (Fin n → α) → Vector α n
| 0, f => nil
| (n+1), f => cons (f 0) (of_fn (λ i => f i.succ))

-- protected theorem eq {n : Nat} : ∀ (a1 a2 : Vector α n), to_list a1 = to_list a2 → a1 = a2
-- | ⟨x, h1⟩, ⟨_, h2⟩, rfl => rfl

-- protected theorem eq_nil (v : Vector α 0) : v = nil :=
-- v.eq nil (list.eq_nil_of_length_eq_zero v.2)

-- @[simp] theorem to_list_mk (v : list α) (P : list.length v = n) : to_list (subtype.mk v P) = v :=
-- rfl

-- @[simp] theorem to_list_nil : to_list nil = @list.nil α :=
-- rfl

-- @[simp] theorem to_list_length (v : Vector α n) : (to_list v).length = n := v.2

-- @[simp] theorem to_list_cons (a : α) (v : Vector α n) : to_list (cons a v) = a :: to_list v :=
-- begin cases v, reflexivity end

-- @[simp] theorem to_list_append {n m : nat} (v : Vector α n) (w : Vector α m) : to_list (append v w) = to_list v ++ to_list w :=
-- begin cases v, cases w, reflexivity end

-- @[simp] theorem to_list_drop {n m : Nat} (v : Vector α m) : to_list (drop n v) = list.drop n (to_list v) :=
-- begin cases v, reflexivity end

-- @[simp] theorem to_list_take {n m : Nat} (v : Vector α m) : to_list (take n v) = list.take n (to_list v) :=
-- begin cases v, reflexivity end

end Vector
