The syntactic order and addition on Brouwer ordinal codes.

This is the base of the development. We define the constructive order `_≤_` on
the Brouwer codes of Ordinals.BrouwerCodes, for which the successor is
monotone by construction, and ordinal addition `_⊕_`. Everything here is
ordinal arithmetic and concerns Brouwer codes alone. The module Constructive
adds the height function on top of it and re-exports the order.

The module takes function extensionality as a parameter for uniformity with
the rest of the development. It is first used in the module Multiplication.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.BrouwerOrdinals.Order
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)

\end{code}

The four constructors of the order say that `Z` is least, that the successor
is monotone, that `L f` is above each `f n`, which is the cocone `≤-ℓ`, and
that `L f` is below every upper bound of the family, which is the limiting
property `≤-L`. A limit is therefore the least upper bound of its family, and
the successor is monotone for arbitrary codes.

\begin{code}

infix 4 _≤_

data _≤_ : 𝓑 → 𝓑 → 𝓤₀ ̇ where
 ≤-Z : {b : 𝓑} → Z ≤ b
 ≤-S : {a b : 𝓑} → a ≤ b → S a ≤ S b
 ≤-ℓ : {a : 𝓑} {f : ℕ → 𝓑} (n : ℕ) → a ≤ f n → a ≤ L f
 ≤-L : {f : ℕ → 𝓑} {b : 𝓑} → ((n : ℕ) → f n ≤ b) → L f ≤ b

≤-refl : (a : 𝓑) → a ≤ a
≤-refl Z     = ≤-Z
≤-refl (S a) = ≤-S (≤-refl a)
≤-refl (L f) = ≤-L (λ n → ≤-ℓ n (≤-refl (f n)))

\end{code}

Transitivity is proved by a lexicographic recursion. When the left proof is a
limit `≤-L p` we recurse on the strictly smaller `p n`, keeping the right
proof fixed, and otherwise we recurse on a strictly smaller right proof.

\begin{code}

≤-trans : {a b c : 𝓑} → a ≤ b → b ≤ c → a ≤ c
≤-trans ≤-Z       _         = ≤-Z
≤-trans (≤-L p)   q         = ≤-L (λ n → ≤-trans (p n) q)
≤-trans (≤-S p)   (≤-S q)   = ≤-S (≤-trans p q)
≤-trans (≤-S p)   (≤-ℓ n q) = ≤-ℓ n (≤-trans (≤-S p) q)
≤-trans (≤-ℓ n p) (≤-ℓ m q) = ≤-ℓ m (≤-trans (≤-ℓ n p) q)
≤-trans (≤-ℓ n p) (≤-L q)   = ≤-trans p (q n)

\end{code}

Two derived facts: a limit is monotone in its family, and the cocone
`f n ≤ L f` holds.

\begin{code}

≤-L-mono : {f g : ℕ → 𝓑} → ((n : ℕ) → f n ≤ g n) → L f ≤ L g
≤-L-mono p = ≤-L (λ n → ≤-ℓ n (p n))

≤-L-upper-bound : (f : ℕ → 𝓑) (n : ℕ) → f n ≤ L f
≤-L-upper-bound f n = ≤-ℓ n (≤-refl (f n))

\end{code}

Addition of Brouwer codes is defined by recursion on the right argument. The
equation `a ⊕ S b = S (a ⊕ b)` makes addition on the left commute with
successors and limits definitionally, which is what the later inductions rely
on.

\begin{code}

infixl 6 _⊕_

_⊕_ : 𝓑 → 𝓑 → 𝓑
a ⊕ Z   = a
a ⊕ S b = S (a ⊕ b)
a ⊕ L f = L (λ n → a ⊕ f n)

\end{code}
