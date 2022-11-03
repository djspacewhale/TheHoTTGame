module 0Trinitarianism.Quest2 where

open import 0Trinitarianism.Preambles.P2

isEven : ℕ → Type
isEven zero = ⊤
isEven (suc zero) = ⊥
isEven (suc (suc n)) = isEven n

{-
This is a comment block.
Remove this comment block and formulate
'there exists an even natural' here.
-}

existsEven : Σ ℕ λ n → isEven n
existsEven = zero , tt

_×_ : Type → Type → Type
A × C = Σ A (λ a → C)

div2 : Σ ℕ isEven → ℕ
div2 (zero , p) = zero
div2 (suc (suc x) , p) = div2 (x , p)

private
  postulate
    A B C : Type

uncurry : (A → B → C) → (A × B → C)
uncurry f x = f (fst x) (snd x)

curry : (A × B → C) → (A → B → C)
curry f a b = f (a , b)
