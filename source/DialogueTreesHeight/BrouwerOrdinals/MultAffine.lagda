Iterating `b ↦ (b ⊕ c) ⊗ M` for a limit multiplier `M`.

An affine map with a finite multiplier iterates by the fold
`b ⊗ ι[m] ⊕ d ≤ (b ⊕ d) ⊗ ι[m]`, which puts the constant of the orbit outside
the multiplier. The fold fails for a limit multiplier, since
`1 ⊗ ω ⊕ 1 = ω + 1 > ω = 2 ⊗ ω`, and the tower over the type levels arises
from that failure.

We iterate a body with a limit multiplier without the fold. The body is
`mbody c b = (b ⊕ c) ⊗ M` for a multiplier `M` that is positive and absorbs
doubling, `ι[2] ⊗ M ≤ M`, as every principal limit does, among them `ω`,
`ω ⊗ 2` and `ω^ω`. Instead of moving `c` out of the multiplier we move `⊗ M`
inward, using one arithmetic fact,

    crux : c ≤ Y → (Y ⊕ c) ⊗ M ≤ Y ⊗ M,

a `c` below `Y` being absorbed on iterating because `Y ⊕ c ≤ Y ⊕ Y = Y ⊗ ι[2]`
and `ι[2] ⊗ M ≤ M`. The orbit then telescopes against the powers of `M`,

    orbit-inv : iter (mbody c) a k ≤ (a ⊕ c) ⊗ pw M k,

which is the form the later bounds take. We also prove that doubling is
absorbed by every power `ω^ (X ⊗ ω)` with `X` positive, which is the shape of
every multiplier built later in the development.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.BrouwerOrdinals.MultAffine
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import DialogueTreesHeight.BrouwerOrdinals.Order fe
open import DialogueTreesHeight.BrouwerOrdinals.Multiplication fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left ; ⊗-assoc ; _·ℕ_ ; ι-*-homo ;
        ⊕-increasing-left)
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
 using (ω^_ ; ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right ; Z-left-unit ;
        ⊕-increasing-right ; ω^-mono ; ω^-ι1)
open import DialogueTreesHeight.BrouwerOrdinals.MultClosure fe
 using (ω^⊗ ; S⊕≤S)

\end{code}

The powers of the multiplier, with `pw m 0 = 1` and `pw m (k+1) = pw m k ⊗ m`,
against which the orbit telescopes, and the bound on a power whose factor is
itself a power of `ω`. The second keeps the exponent at `δ` rather than at
`ω^ δ`, so that the orbit of a body with such a multiplier stays within one
tower level.

\begin{code}

pw : 𝓑 → ℕ → 𝓑
pw m zero     = S Z
pw m (succ k) = pw m k ⊗ m

\end{code}

For a factor that is a power of `ω`, say `m = ω^ δ`, the bound that replaces
the trailing factor by `ω^ m` through the inflationary law `m ≤ ω^ m` gives
the exponent `ω^ δ` where the exact value has `δ`. The sharp bound keeps `δ`,
by the exponent homomorphism alone. Its supremum is `ω^ (δ ⊗ ω)`, one factor
of `ω` on the exponent, rather than `ω^ (ω^ δ ⊗ ω)`, which is a whole tower
level higher.

\begin{code}

pw-ω^ : (δ : 𝓑) (k : ℕ) → pw (ω^ δ) k ≤ ω^ (δ ⊗ ι[ k ])
pw-ω^ δ zero     = ≤-refl (S Z)
pw-ω^ δ (succ k) =
 transport (pw (ω^ δ) (succ k) ≤_)
           (ω^⊗ (δ ⊗ ι[ k ]) δ)
           (⊗-mono-left (pw-ω^ δ k) (ω^ δ))

\end{code}

A finite multiple of `ω` is below `ω`, since each `ι[n] ⊗ ι[j] = ι[n ·ℕ j]` is
a numeral and is dominated by `ω = L ι[_]` at its own index. In particular
`ι[2] ⊗ ω ≤ ω`, which is the absorption of doubling for `M = ω`.

\begin{code}

ιn⊗ω-≤-ω : (n : ℕ) → (ι[ n ] ⊗ ω) ≤ ω
ιn⊗ω-≤-ω n =
 ≤-L (λ j → transport (_≤ ω) ((ι-*-homo n j) ⁻¹)
                      (≤-L-upper-bound ι[_] (n ·ℕ j)))

\end{code}

Doubling is absorbed by every power `ω^ (X ⊗ ω)` with `X` positive, and those
are the multipliers the orbit itself produces. We have
`ω^ (X ⊗ ω) = L (λ k → ω^ (X ⊗ ι[k]))`, and each
`ι[2] ⊗ ω^ (X ⊗ ι[k]) ≤ ω ⊗ ω^ (X ⊗ ι[k]) = ω^ (ι[1] ⊕ X ⊗ ι[k])` is below
`ω^ (X ⊗ ι[succ k])`, because `ι[1] ⊕ β ≤ S β ≤ β ⊕ X` for positive `X`, by
`S⊕≤S`, and the right-hand side is the next index of the limit. Hence
`ι[2] ⊗ ω^ (X ⊗ ω) ≤ ω^ (X ⊗ ω)`.

\begin{code}

dbl-ω^ : (X : 𝓑) → S Z ≤ X → (ι[ 2 ] ⊗ ω^ (X ⊗ ω)) ≤ ω^ (X ⊗ ω)
dbl-ω^ X X+ = ≤-L per
 where
  per : (k : ℕ) → (ι[ 2 ] ⊗ ω^ (X ⊗ ι[ k ])) ≤ ω^ (X ⊗ ω)
  per k = ≤-trans step-a
            (transport (λ z → z ≤ ω^ (X ⊗ ω)) (step-b ⁻¹)
                       (≤-trans step-c step-d))
   where
    A : 𝓑
    A = ω^ (X ⊗ ι[ k ])

    step-a : (ι[ 2 ] ⊗ A) ≤ (ω ⊗ A)
    step-a = ⊗-mono-left (≤-L-upper-bound ι[_] 2) A

    step-b : (ω ⊗ A) ＝ ω^ (ι[ 1 ] ⊕ (X ⊗ ι[ k ]))
    step-b = ap (_⊗ A) ((ω^-ι1) ⁻¹) ∙ ω^⊗ ι[ 1 ] (X ⊗ ι[ k ])

    exp-le : (ι[ 1 ] ⊕ (X ⊗ ι[ k ])) ≤ (X ⊗ ι[ succ k ])
    exp-le = ≤-trans (S⊕≤S (X ⊗ ι[ k ]))
                     (⊕-mono-right (X ⊗ ι[ k ]) X+)

    step-c : ω^ (ι[ 1 ] ⊕ (X ⊗ ι[ k ])) ≤ ω^ (X ⊗ ι[ succ k ])
    step-c = ω^-mono exp-le

    step-d : ω^ (X ⊗ ι[ succ k ]) ≤ ω^ (X ⊗ ω)
    step-d = ≤-L-upper-bound (λ j → ω^ (X ⊗ ι[ j ])) (succ k)

\end{code}

Fix a multiplier `M` that is positive, `S Z ≤ M`, and absorbs doubling,
`ι[2] ⊗ M ≤ M`.

\begin{code}

module _ (M : 𝓑) (M+ : S Z ≤ M) (dbl : (ι[ 2 ] ⊗ M) ≤ M) where

\end{code}

If `c ≤ Y` then `(Y ⊕ c) ⊗ M ≤ Y ⊗ M`. Bound `Y ⊕ c` by `Y ⊕ Y = Y ⊗ ι[2]`,
associate, and absorb `ι[2] ⊗ M` back to `M`. The multiplier remains `M`
throughout, and the argument uses the absorption of doubling alone.

\begin{code}

 crux : (Y c : 𝓑) → c ≤ Y → ((Y ⊕ c) ⊗ M) ≤ (Y ⊗ M)
 crux Y c c≤Y = ≤-trans (⊗-mono-left step12 M) final
  where
   Yι2=YY : (Y ⊗ ι[ 2 ]) ＝ (Y ⊕ Y)
   Yι2=YY = ap (_⊕ Y) (Z-left-unit Y)

   step12 : (Y ⊕ c) ≤ (Y ⊗ ι[ 2 ])
   step12 = transport ((Y ⊕ c) ≤_) (Yι2=YY ⁻¹) (⊕-mono-right Y c≤Y)

   final : ((Y ⊗ ι[ 2 ]) ⊗ M) ≤ (Y ⊗ M)
   final = transport (_≤ (Y ⊗ M)) ((⊗-assoc Y ι[ 2 ] M) ⁻¹)
                     (⊗-mono-right Y dbl)

\end{code}

The body with a limit multiplier, and its orbit invariant: the `k`-th iterate
is below the start plus the constant, times the `k`-th power of `M`. At
`k = 0` the power is the left unit. At a successor the incoming `c` is below
`Y = (a ⊕ c) ⊗ pw M k`, since `pw M k ≥ 1`, so that `crux` absorbs it and
associativity turns `Y ⊗ M` into `(a ⊕ c) ⊗ pw M (k+1)`.

\begin{code}

 mbody : 𝓑 → 𝓑 → 𝓑
 mbody c b = (b ⊕ c) ⊗ M

 pw-pos : (k : ℕ) → S Z ≤ pw M k
 pw-pos zero     = ≤-refl (S Z)
 pw-pos (succ k) = ≤-trans (pw-pos k)
                    (transport (_≤ (pw M k ⊗ M)) (Z-left-unit (pw M k))
                       (⊗-mono-right (pw M k) M+))

 orbit-inv : (a c : 𝓑) (k : ℕ) → iter (mbody c) a k ≤ ((a ⊕ c) ⊗ pw M k)
 orbit-inv a c zero     =
  transport (a ≤_) ((Z-left-unit (a ⊕ c)) ⁻¹) (⊕-increasing-right a c)
 orbit-inv a c (succ k) =
  transport (λ z → iter (mbody c) a (succ k) ≤ z) step-eq
            (≤-trans body-mono (crux Y c c≤Y))
  where
   Y : 𝓑
   Y = (a ⊕ c) ⊗ pw M k

   body-mono : ((iter (mbody c) a k ⊕ c) ⊗ M) ≤ ((Y ⊕ c) ⊗ M)
   body-mono = ⊗-mono-left (⊕-mono-left (orbit-inv a c k) c) M

   c≤Y : c ≤ Y
   c≤Y = ≤-trans (⊕-increasing-left a c)
                 (transport (_≤ Y) (Z-left-unit (a ⊕ c))
                    (⊗-mono-right (a ⊕ c) (pw-pos k)))

   step-eq : (Y ⊗ M) ＝ ((a ⊕ c) ⊗ pw M (succ k))
   step-eq = ⊗-assoc (a ⊕ c) (pw M k) M

\end{code}

The instance `M = ω` needs only the positivity of `ω`.

\begin{code}

ω-pos : S Z ≤ ω
ω-pos = ≤-L-upper-bound ι[_] 1

\end{code}
