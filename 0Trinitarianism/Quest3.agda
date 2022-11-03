module 0Trinitarianism.Quest3 where

open import 0Trinitarianism.Preambles.P3

_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)

{-
Write here you proof that the sum of
even naturals is even.
-}

evenAdd : (m n : ℕ) → isEven m → isEven n → isEven (m + n)
evenAdd zero n p q = q
evenAdd (suc m) zero p q = {!!}
evenAdd (suc m) (suc n) p q = {!!}

data _⊕_ (A : Type) (B : Type) : Type where
  inl : A → A ⊕ B
  inr : B → A ⊕ B

EvenOrOdd : (n : ℕ) → isEven n ⊕ (isEven n → ⊥)
EvenOrOdd zero = inl tt
EvenOrOdd (suc zero) = inr (λ x → x)
EvenOrOdd (suc (suc n)) = EvenOrOdd n
