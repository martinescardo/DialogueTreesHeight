Ordinal multiplication, `ω`, the numerals, and the laws of the product.

We build on the module Order with the numeral embedding `ι[_]`, the first
limit `ω`, ordinal multiplication `_⊗_`, the monotonicity and associativity
laws that the bounds are moved by, and the arithmetic of the numerals.

The product distributes over the sum on the left,
`c ⊗ (x ⊕ y) = (c ⊗ x) ⊕ (c ⊗ y)`, and is associative. Both are proved by
induction on the right argument, the limit case of each using function
extensionality, which is the module parameter `fe` carried throughout the
development.

Distributivity on the right fails for the ordinal product, since
`(1 ⊕ ω) ⊗ 2 = 1 ⊕ ω ⊕ 1 ⊕ ω` while `1 ⊗ 2 ⊕ ω ⊗ 2 = 1 ⊕ 1 ⊕ ω ⊕ ω`. For that
reason every bound in the development keeps its constant inside the product,
in the form `(b ⊕ d) ⊗ m`, for which composition needs left distributivity
alone.

This module concerns Brouwer codes alone.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.BrouwerOrdinals.Multiplication
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import DialogueTreesHeight.BrouwerOrdinals.Order fe

\end{code}

The numeral embedding, the limit `ω` of the numerals, and ordinal
multiplication, which recurses on the right argument as addition does.

\begin{code}

ι[_] : ℕ → 𝓑
ι[ zero ]   = Z
ι[ succ n ] = S ι[ n ]

ω : 𝓑
ω = L ι[_]

infixl 7 _⊗_

_⊗_ : 𝓑 → 𝓑 → 𝓑
a ⊗ Z   = Z
a ⊗ S b = (a ⊗ b) ⊕ a
a ⊗ L f = L (λ n → a ⊗ f n)

\end{code}

Three facts about addition: monotonicity in the left argument, associativity,
and that addition on the left is inflationary.

\begin{code}

⊕-mono-left : {a a′ : 𝓑} → a ≤ a′ → (c : 𝓑) → (a ⊕ c) ≤ (a′ ⊕ c)
⊕-mono-left p Z     = p
⊕-mono-left p (S c) = ≤-S (⊕-mono-left p c)
⊕-mono-left p (L f) = ≤-L-mono (λ n → ⊕-mono-left p (f n))

⊕-assoc : (a b c : 𝓑) → ((a ⊕ b) ⊕ c) ＝ (a ⊕ (b ⊕ c))
⊕-assoc a b Z     = refl
⊕-assoc a b (S c) = ap S (⊕-assoc a b c)
⊕-assoc a b (L f) = ap L (dfunext fe (λ n → ⊕-assoc a b (f n)))

⊕-increasing-left : (d x : 𝓑) → x ≤ (d ⊕ x)
⊕-increasing-left d Z     = ≤-Z
⊕-increasing-left d (S x) = ≤-S (⊕-increasing-left d x)
⊕-increasing-left d (L f) = ≤-L-mono (λ n → ⊕-increasing-left d (f n))

\end{code}

Left distributivity, and associativity of the product, whose proof uses it.

\begin{code}

⊗-left-distrib : (c x y : 𝓑) → (c ⊗ (x ⊕ y)) ＝ ((c ⊗ x) ⊕ (c ⊗ y))
⊗-left-distrib c x Z     = refl
⊗-left-distrib c x (S y) = ap (_⊕ c) (⊗-left-distrib c x y)
                         ∙ ⊕-assoc (c ⊗ x) (c ⊗ y) c
⊗-left-distrib c x (L f) = ap L (dfunext fe (λ n → ⊗-left-distrib c x (f n)))

⊗-assoc : (a b c : 𝓑) → ((a ⊗ b) ⊗ c) ＝ (a ⊗ (b ⊗ c))
⊗-assoc a b Z     = refl
⊗-assoc a b (S c) = ap (_⊕ (a ⊗ b)) (⊗-assoc a b c)
                  ∙ (⊗-left-distrib a (b ⊗ c) b) ⁻¹
⊗-assoc a b (L f) = ap L (dfunext fe (λ n → ⊗-assoc a b (f n)))

\end{code}

The numeral embedding is a homomorphism for addition and for multiplication.

\begin{code}

_+ℕ_ : ℕ → ℕ → ℕ
m +ℕ zero   = m
m +ℕ succ n = succ (m +ℕ n)

ι-+-homo : (m n : ℕ) → ι[ m +ℕ n ] ＝ (ι[ m ] ⊕ ι[ n ])
ι-+-homo m zero     = refl
ι-+-homo m (succ n) = ap S (ι-+-homo m n)

_·ℕ_ : ℕ → ℕ → ℕ
m ·ℕ zero   = zero
m ·ℕ succ n = (m ·ℕ n) +ℕ m

ι-*-homo : (m n : ℕ) → (ι[ m ] ⊗ ι[ n ]) ＝ ι[ m ·ℕ n ]
ι-*-homo m zero     = refl
ι-*-homo m (succ n) = ap (_⊕ ι[ m ]) (ι-*-homo m n) ∙ (ι-+-homo (m ·ℕ n) m) ⁻¹

\end{code}
