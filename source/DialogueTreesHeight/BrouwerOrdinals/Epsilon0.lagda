Brouwer-code arithmetic up to ε₀.

We add to the order and the product the base-`ω` exponentiation `ω^_`, the
tower of its iterates, the strict order, and the closure of `ε₀` under
addition, under multiplication by one more power, under the successor and
under exponentiation. This is ordinal arithmetic of the usual kind, carried
out on explicit codes rather than cited from the literature, because the
development needs it in that form.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.BrouwerOrdinals.Epsilon0
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import DialogueTreesHeight.BrouwerOrdinals.Order fe
open import DialogueTreesHeight.BrouwerOrdinals.Multiplication fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left)

\end{code}

The successor is increasing, and so is the right summand of a sum: `a ≤ S a`
and `a ≤ a ⊕ b`.

\begin{code}

S-increasing : (a : 𝓑) → a ≤ S a
S-increasing Z     = ≤-Z
S-increasing (S a) = ≤-S (S-increasing a)
S-increasing (L f) = ≤-L (λ n → ≤-trans (S-increasing (f n))
                                         (≤-S (≤-L-upper-bound f n)))

⊕-increasing-right : (a b : 𝓑) → a ≤ (a ⊕ b)
⊕-increasing-right a Z     = ≤-refl a
⊕-increasing-right a (S b) = ≤-trans (⊕-increasing-right a b) (S-increasing (a ⊕ b))
⊕-increasing-right a (L f) = ≤-ℓ 0 (⊕-increasing-right a (f 0))

\end{code}

Addition is monotone in its right argument, and `Z` is its left unit.

\begin{code}

⊕-mono-right : (a : 𝓑) {b c : 𝓑} → b ≤ c → (a ⊕ b) ≤ (a ⊕ c)
⊕-mono-right a {b}     {c}   ≤-Z       = ⊕-increasing-right a c
⊕-mono-right a         (≤-S p)         = ≤-S (⊕-mono-right a p)
⊕-mono-right a         (≤-ℓ n p)       = ≤-ℓ n (⊕-mono-right a p)
⊕-mono-right a         (≤-L p)         = ≤-L (λ n → ⊕-mono-right a (p n))

Z-left-unit : (a : 𝓑) → (Z ⊕ a) ＝ a
Z-left-unit Z     = refl
Z-left-unit (S a) = ap S (Z-left-unit a)
Z-left-unit (L f) = ap L (dfunext fe (λ n → Z-left-unit (f n)))

\end{code}

The product is monotone in each argument.

\begin{code}

⊗-mono-left : {a a′ : 𝓑} → a ≤ a′ → (c : 𝓑) → (a ⊗ c) ≤ (a′ ⊗ c)
⊗-mono-left p Z     = ≤-Z
⊗-mono-left {a} {a′} p (S c) =
 ≤-trans (⊕-mono-left (⊗-mono-left p c) a) (⊕-mono-right (a′ ⊗ c) p)
⊗-mono-left p (L f) = ≤-L-mono (λ n → ⊗-mono-left p (f n))

⊗-mono-right : (a : 𝓑) {b c : 𝓑} → b ≤ c → (a ⊗ b) ≤ (a ⊗ c)
⊗-mono-right a ≤-Z       = ≤-Z
⊗-mono-right a (≤-S p)   = ⊕-mono-left (⊗-mono-right a p) a
⊗-mono-right a (≤-ℓ n p) = ≤-ℓ n (⊗-mono-right a p)
⊗-mono-right a (≤-L p)   = ≤-L (λ n → ⊗-mono-right a (p n))

\end{code}

Base-`ω` exponentiation, and the tower whose supremum is `ε₀`.

\begin{code}

ω^_ : 𝓑 → 𝓑
ω^ Z     = S Z
ω^ (S a) = (ω^ a) ⊗ ω
ω^ (L f) = L (λ n → ω^ (f n))

tower : ℕ → 𝓑
tower zero     = ω
tower (succ n) = ω^ (tower n)

ε₀ : 𝓑
ε₀ = L tower

\end{code}

The strict order, and the entry point used throughout: a code below some
finite tower level is below `ε₀`.

\begin{code}

_<_ : 𝓑 → 𝓑 → 𝓤₀ ̇
a < b = S a ≤ b

infix 4 _<_

\end{code}

One is below every power of `ω`, and `ω^_` is monotone in the exponent.

\begin{code}

one-≤-ω^ : (b : 𝓑) → S Z ≤ ω^ b
one-≤-ω^ Z     = ≤-refl (S Z)
one-≤-ω^ (S b) = ≤-ℓ 1 (transport (S Z ≤_) ((Z-left-unit (ω^ b)) ⁻¹) (one-≤-ω^ b))
one-≤-ω^ (L f) = ≤-ℓ 0 (one-≤-ω^ (f 0))

ω^-mono : {a b : 𝓑} → a ≤ b → ω^ a ≤ ω^ b
ω^-mono {Z}    {b} ≤-Z       = one-≤-ω^ b
ω^-mono            (≤-S p)   = ⊗-mono-left (ω^-mono p) ω
ω^-mono            (≤-ℓ n p) = ≤-ℓ n (ω^-mono p)
ω^-mono            (≤-L p)   = ≤-L (λ n → ω^-mono (p n))

\end{code}

The numerals are below `ω`, so that `ω^ ι[ m ] ≤ ω^ ω = tower 1`. Every finite
power of `ω` is therefore below the first tower level.

\begin{code}

ι[_]≤ω : (m : ℕ) → ι[ m ] ≤ ω
ι[ m ]≤ω = ≤-L-upper-bound ι[_] m

\end{code}

Exponentiation is inflationary: `a ≤ ω^ a`. The successor step uses that a
single power of `ω` dominates its predecessor doubled,
`S (ω^ a) ≤ ω^ a ⊕ ω^ a ≤ ω^ a ⊗ ω`, which avoids the successor-of-a-limit
case that a direct proof meets.

\begin{code}

S-ω^-step : (a : 𝓑) → S (ω^ a) ≤ (ω^ a ⊗ ω)
S-ω^-step a = ≤-trans h1 h2
 where
  h1 : S (ω^ a) ≤ (ω^ a ⊕ ω^ a)
  h1 = ⊕-mono-right (ω^ a) (one-≤-ω^ a)

  eq2 : (ω^ a ⊗ ι[ 2 ]) ＝ (ω^ a ⊕ ω^ a)
  eq2 = ap (_⊕ ω^ a) (Z-left-unit (ω^ a))

  h2 : (ω^ a ⊕ ω^ a) ≤ (ω^ a ⊗ ω)
  h2 = transport (_≤ (ω^ a ⊗ ω)) eq2
                 (≤-L-upper-bound (λ n → ω^ a ⊗ ι[ n ]) 2)

≤-ω^ : (a : 𝓑) → a ≤ ω^ a
≤-ω^ Z     = ≤-Z
≤-ω^ (S a) = ≤-trans (≤-S (≤-ω^ a)) (S-ω^-step a)
≤-ω^ (L f) = ≤-L-mono (λ n → ≤-ω^ (f n))

\end{code}

The limit `ω` is `ω^ ι[ 1 ]`, and is strictly below `ω^ ω`, the first place
where the tower increases.

\begin{code}

one-⊗-ι : (n : ℕ) → (S Z ⊗ ι[ n ]) ＝ ι[ n ]
one-⊗-ι zero     = refl
one-⊗-ι (succ n) = ap (_⊕ S Z) (one-⊗-ι n)

ω^-ι1 : ω^ ι[ 1 ] ＝ ω
ω^-ι1 = ap L (dfunext fe one-⊗-ι)

ω<ω^ω : S ω ≤ ω^ ω
ω<ω^ω = transport (λ z → S z ≤ ω^ ω) ω^-ι1
                  (≤-trans (S-ω^-step ι[ 1 ])
                           (ω^-mono (≤-L-upper-bound ι[_] 2)))

\end{code}

The tower is strictly increasing, `tower n < tower (succ n)`, so every level
is below `ε₀`. The successor-of-a-limit obstruction is removed by a descent:
strictness at `ω^ b` reduces, through `S-ω^-step` and `ω^-mono`, to strictness
at `b`, and the descent stops at the proved base `ω < ω^ ω`.

\begin{code}

tower-strict : (n : ℕ) → S (tower n) ≤ ω^ (tower n)
tower-strict zero     = ω<ω^ω
tower-strict (succ m) = ≤-trans (S-ω^-step (tower m))
                                (ω^-mono (tower-strict m))

tower-<-ε₀ : (n : ℕ) → tower n < ε₀
tower-<-ε₀ n = ≤-ℓ (succ n) (tower-strict n)

\end{code}

The towers are closed under doubling, by `ω^ a ⊕ ω^ a ≤ ω^ a ⊗ ω`, and
monotone in their index. Two ordinals below `ε₀` can therefore be pushed to a
common tower level and their sum absorbed one level up.

\begin{code}

ω^-double : (a : 𝓑) → (ω^ a ⊕ ω^ a) ≤ (ω^ a ⊗ ω)
ω^-double a =
 transport (_≤ (ω^ a ⊗ ω)) (ap (_⊕ ω^ a) (Z-left-unit (ω^ a)))
           (≤-L-upper-bound (λ n → ω^ a ⊗ ι[ n ]) 2)

tower-mono-step : (n : ℕ) → tower n ≤ tower (succ n)
tower-mono-step n = ≤-trans (S-increasing (tower n)) (tower-strict n)

tower-double : (n : ℕ) → (tower n ⊕ tower n) ≤ tower (succ n)
tower-double zero =
 transport (λ z → (z ⊕ z) ≤ tower 1) ω^-ι1
           (≤-trans (ω^-double ι[ 1 ]) (ω^-mono (≤-L-upper-bound ι[_] 2)))
tower-double (succ m) =
 ≤-trans (ω^-double (tower m)) (ω^-mono (tower-strict m))

\end{code}

A maximum on the natural numbers with its order, used to reach a common tower
level.

\begin{code}

maxℕ : ℕ → ℕ → ℕ
maxℕ zero     n        = n
maxℕ (succ m) zero     = succ m
maxℕ (succ m) (succ n) = succ (maxℕ m n)

_≤ℕ_ : ℕ → ℕ → 𝓤₀ ̇
zero   ≤ℕ n      = 𝟙
succ m ≤ℕ zero   = 𝟘
succ m ≤ℕ succ n = m ≤ℕ n

≤ℕ-refl : (n : ℕ) → n ≤ℕ n
≤ℕ-refl zero     = ⋆
≤ℕ-refl (succ n) = ≤ℕ-refl n

≤ℕ-maxL : (m n : ℕ) → m ≤ℕ maxℕ m n
≤ℕ-maxL zero     n        = ⋆
≤ℕ-maxL (succ m) zero     = ≤ℕ-refl (succ m)
≤ℕ-maxL (succ m) (succ n) = ≤ℕ-maxL m n

≤ℕ-maxR : (m n : ℕ) → n ≤ℕ maxℕ m n
≤ℕ-maxR zero     n        = ≤ℕ-refl n
≤ℕ-maxR (succ m) zero     = ⋆
≤ℕ-maxR (succ m) (succ n) = ≤ℕ-maxR m n

tower-mono-ℕ : (m n : ℕ) → m ≤ℕ n → tower m ≤ tower n
tower-mono-ℕ zero     zero     p = ≤-refl (tower 0)
tower-mono-ℕ zero     (succ n) p = ≤-trans (tower-mono-ℕ zero n ⋆) (tower-mono-step n)
tower-mono-ℕ (succ m) zero     p = 𝟘-elim p
tower-mono-ℕ (succ m) (succ n) p = ω^-mono (tower-mono-ℕ m n p)

\end{code}

The closure of `ε₀` under addition: `a < ε₀` and `b < ε₀` give `a ⊕ b < ε₀`. A
proof of `a < ε₀` can be inverted to a tower level by a single pattern match,
since `≤-ℓ` is the only constructor that puts a successor below the limit
`ε₀`.

\begin{code}

⊕-<-ε₀ : (a b : 𝓑) → a < ε₀ → b < ε₀ → (a ⊕ b) < ε₀
⊕-<-ε₀ a b (≤-ℓ j qa) (≤-ℓ j′ qb) =
 ≤-trans (≤-S ab-≤) (tower-<-ε₀ (succ Jm))
 where
  Jm : ℕ
  Jm = maxℕ j j′

  a≤Jm : a ≤ tower Jm
  a≤Jm = ≤-trans (S-increasing a) (≤-trans qa (tower-mono-ℕ j Jm (≤ℕ-maxL j j′)))

  b≤Jm : b ≤ tower Jm
  b≤Jm = ≤-trans (S-increasing b) (≤-trans qb (tower-mono-ℕ j′ Jm (≤ℕ-maxR j j′)))

  ab-≤ : (a ⊕ b) ≤ tower (succ Jm)
  ab-≤ = ≤-trans (≤-trans (⊕-mono-left a≤Jm b) (⊕-mono-right (tower Jm) b≤Jm))
                 (tower-double Jm)

\end{code}

Two further closures, needed once the exponent of a tower step is an ordinal
rather than a numeral. The ordinal `ε₀` is closed under the successor, and
under `ω^_`: if `a < ε₀` then some tower level dominates `a`, so that
`ω^ a ≤ ω^ (tower n) = tower (succ n) < ε₀`. Both invert `a < ε₀` by the same
single constructor.

\begin{code}

S-<-ε₀ : (a : 𝓑) → a < ε₀ → S a < ε₀
S-<-ε₀ a (≤-ℓ n q) = ≤-trans (≤-S q) (tower-<-ε₀ n)

ω^-<-ε₀ : (a : 𝓑) → a < ε₀ → ω^ a < ε₀
ω^-<-ε₀ a (≤-ℓ n q) =
 ≤-trans (≤-S (ω^-mono (≤-trans (S-increasing a) q))) (tower-<-ε₀ (succ n))

\end{code}

A product by `S Z` on the left is the identity, and a code is below itself
times a positive code on either side.

\begin{code}

SZ-⊗ : (y : 𝓑) → ((S Z) ⊗ y) ＝ y
SZ-⊗ Z     = refl
SZ-⊗ (S y) = ap S (SZ-⊗ y)
SZ-⊗ (L f) = ap L (dfunext fe (λ n → SZ-⊗ (f n)))

x-≤-x⊗ : (x y : 𝓑) → S Z ≤ y → x ≤ (x ⊗ y)
x-≤-x⊗ x y y+ =
 ≤-trans (transport (x ≤_) ((Z-left-unit x) ⁻¹) (≤-refl x)) (⊗-mono-right x y+)

y-≤-⊗ : (x y : 𝓑) → S Z ≤ x → y ≤ (x ⊗ y)
y-≤-⊗ x y x+ = transport (_≤ (x ⊗ y)) (SZ-⊗ y) (⊗-mono-left x+ y)

\end{code}

Every numeral is below `ε₀`, and so is `ω`, the first tower level.

\begin{code}

ι<ε₀ : (m : ℕ) → ι[ m ] < ε₀
ι<ε₀ m = ≤-trans (≤-S (≤-L-upper-bound ι[_] m)) (tower-<-ε₀ 0)

Z<ε₀ : Z < ε₀
Z<ε₀ = ι<ε₀ 0

ω<ε₀ : ω < ε₀
ω<ε₀ = tower-<-ε₀ 0

\end{code}

