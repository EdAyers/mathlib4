


namespace Sum

def map (f : A → B) (g : S → T) : (A ⊕ S) → (B ⊕ T)
| (Sum.inl a) => Sum.inl $ f a
| (Sum.inr s) => Sum.inr $ g s

def elim : (A → C) → (B → C) → (A ⊕ B) → C
| l, r, (Sum.inl a) => l a
| l, r, (Sum.inr b) => r b

def Double (A : Type u) := A ⊕ A

def codelta {A} : A ⊕ A → A
| (Sum.inl a) => a
| (Sum.inr a) => a

end Sum
