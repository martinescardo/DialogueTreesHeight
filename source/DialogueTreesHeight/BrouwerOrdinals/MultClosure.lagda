The closure of ε₀ under multiplication.

This is the multiplicative counterpart of `⊕-<-ε₀`, and the bounds of the
development need it, being products of the shape `(a ⊕ d) ⊗ m`. A tower level
squares into the next, `tower n ⊗ tower n ≤ tower (succ n)`, by the exponent
homomorphism `ω^ a ⊗ ω^ b = ω^ (a ⊕ b)` together with
`tower n ⊕ tower n ≤ tower (succ n)`. Two ordinals below `ε₀` are then pushed
to a common tower level and their product absorbed one level up, as in the
proof for addition.

The exponent homomorphism is used on its own wherever a product of two powers
of `ω` is to be read as a single power, which happens at every point where a
multiplier is merged into an exponent.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.BrouwerOrdinals.MultClosure
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import DialogueTreesHeight.BrouwerOrdinals.Order fe
open import DialogueTreesHeight.BrouwerOrdinals.Multiplication fe
 using (ι[_] ; ω ; _⊗_ ; ⊗-assoc)
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
 using (S-increasing ; Z-left-unit ; ⊗-mono-left ; ⊗-mono-right ; ω^_ ;
        ω^-mono ; ω^-ι1 ; tower ; tower-<-ε₀ ; _<_ ; ε₀ ; tower-double ;
        tower-mono-ℕ ; maxℕ ; ≤ℕ-maxL ; ≤ℕ-maxR)

\end{code}

First the absorption of a one on the left, `S Z ⊕ β ≤ S β`, by which a
successor is moved past a code it is added to, and then the exponent
homomorphism.

\begin{code}

S⊕≤S : (β : 𝓑) → (S Z ⊕ β) ≤ S β
S⊕≤S Z     = ≤-refl (S Z)
S⊕≤S (S β) = ≤-S (S⊕≤S β)
S⊕≤S (L f) = ≤-L (λ n → ≤-trans (S⊕≤S (f n)) (≤-S (≤-L-upper-bound f n)))

ω^⊗ : (a b : 𝓑) → (ω^ a ⊗ ω^ b) ＝ ω^ (a ⊕ b)
ω^⊗ a Z     = Z-left-unit (ω^ a)
ω^⊗ a (S b) = (⊗-assoc (ω^ a) (ω^ b) ω) ⁻¹ ∙ ap (_⊗ ω) (ω^⊗ a b)
ω^⊗ a (L f) = ap L (dfunext fe (λ n → ω^⊗ a (f n)))

\end{code}

The squaring of a tower level, and the closure itself.

\begin{code}

tower-sq : (n : ℕ) → (tower n ⊗ tower n) ≤ tower (succ n)
tower-sq zero =
 transport (_≤ tower 1) (eq ⁻¹) (ω^-mono (≤-L-upper-bound ι[_] 2))
 where
  eq : (ω ⊗ ω) ＝ ω^ (ι[ 1 ] ⊕ ι[ 1 ])
  eq = ap (λ z → z ⊗ z) ((ω^-ι1) ⁻¹) ∙ ω^⊗ ι[ 1 ] ι[ 1 ]
tower-sq (succ m) =
 transport (_≤ tower (succ (succ m))) ((ω^⊗ (tower m) (tower m)) ⁻¹)
           (ω^-mono (tower-double m))

⊗-<-ε₀ : (a b : 𝓑) → a < ε₀ → b < ε₀ → (a ⊗ b) < ε₀
⊗-<-ε₀ a b (≤-ℓ j qa) (≤-ℓ j′ qb) =
 ≤-trans (≤-S ab-≤) (tower-<-ε₀ (succ Jm))
 where
  Jm : ℕ
  Jm = maxℕ j j′

  a≤Jm : a ≤ tower Jm
  a≤Jm = ≤-trans (S-increasing a) (≤-trans qa (tower-mono-ℕ j Jm (≤ℕ-maxL j j′)))

  b≤Jm : b ≤ tower Jm
  b≤Jm = ≤-trans (S-increasing b) (≤-trans qb (tower-mono-ℕ j′ Jm (≤ℕ-maxR j j′)))

  ab-≤ : (a ⊗ b) ≤ tower (succ Jm)
  ab-≤ = ≤-trans (≤-trans (⊗-mono-left a≤Jm b) (⊗-mono-right (tower Jm) b≤Jm))
                 (tower-sq Jm)

\end{code}
