Scalar graded maps whose exponents are graded maps in their turn.

A move acts on a code by `a ↦ (a ⊕ t) ⊗ ω^ s` with a fixed exponent `s`. That
suffices at ground type, and the module MoveTuple iterates a graded tuple of
such moves. The combinator `S` requires more. The datum of `f a` is obtained
from the datum of `a`, so the exponents in it vary with `a`, and the datum of
`f a (g a)` therefore carries an exponent which is a map of `a` rather than a
constant.

We therefore let the exponent be a map of the same kind, one grade up. A
scalar graded map on a tuple of width `k` is

    valSc (c , E) (a , t) = ((a ⊕ tsum t) ⊕ c) ⊗ ω^ (valSc E t) ,

which reads the whole tuple in its base and only the tail in its exponent, the
exponent being again a scalar graded map, on the tail. The recursion is on the
width, and at width zero it ends at a free constant,

    valSc c ⋆ = c .

The last case is the one that decides the construction. A cascade whose
exponent at the last grade were read off a grade below it has no grade below
to read, so that exponent would be `Z`, and since `ω^ Z = S Z` and
`x ⊗ S Z = x` the last grade would act by a translation. A translation cannot
absorb a doubling: with `x` the entry and `t` the translation, `x ⊕ x ≤ x ⊕ t`
fails at `x = t ⊕ 1`, whatever `t` is, since `x` is chosen after it. Ending
the recursion at a constant that the map carries itself removes the
difficulty, and a doubling is then paid at every grade, the last included, by
one successor on the grade above, which the lemma `valSc-join` below makes
precise.

Three facts are proved here: a scalar graded map takes codes below `ε₀` to
codes below `ε₀`, it is monotone, and the sum of two of them at one tuple is
below a single one. The third is the repeated argument of `S`, and its proof
uses the first form of the successor, `valSc-suc`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.BrouwerOrdinals.Cascade
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import DialogueTreesHeight.BrouwerOrdinals.Order fe
 using (_≤_ ; _⊕_ ; ≤-Z ; ≤-S ; ≤-refl ; ≤-trans ; ≤-L-mono)
open import DialogueTreesHeight.BrouwerOrdinals.Multiplication fe
 using (ω ; _⊗_ ; ⊕-mono-left ; ⊗-assoc ; ⊕-increasing-left)
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ω^_ ; ω^-mono ; ω^-<-ε₀ ; one-≤-ω^ ; S-increasing ;
        ≤-ω^ ; ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right ;
        ⊕-increasing-right ; ⊕-<-ε₀ ; S-<-ε₀ ; x-≤-x⊗ ; Z<ε₀ ; ω<ε₀)
open import DialogueTreesHeight.BrouwerOrdinals.MultClosure fe
 using (⊗-<-ε₀)
open import DialogueTreesHeight.BrouwerOrdinals.MoveTuple fe
 using (Tup ; tsum ; _⊑_ ; All< ; tsum-mono ; tsum-<-ε₀ ; dup-ω)

\end{code}

The datum of a scalar graded map on a tuple of width `k`: one translation per
grade, and a constant at the bottom.

\begin{code}

Sc : ℕ → 𝓤₀ ̇
Sc zero     = 𝓑
Sc (succ k) = 𝓑 × Sc k

valSc : (k : ℕ) → Sc k → Tup k → 𝓑
valSc zero     c       t       = c
valSc (succ k) (c , E) (a , t) = ((a ⊕ tsum k t) ⊕ c) ⊗ ω^ (valSc k E t)

ScAll< : (k : ℕ) → Sc k → 𝓤₀ ̇
ScAll< zero     c       = c < ε₀
ScAll< (succ k) (c , E) = (c < ε₀) × ScAll< k E

\end{code}

Values below `ε₀`, and monotonicity in the tuple.

\begin{code}

valSc-<-ε₀ : (k : ℕ) (E : Sc k) (t : Tup k) → ScAll< k E → All< k t
           → valSc k E t < ε₀
valSc-<-ε₀ zero     c       t       p         all        = p
valSc-<-ε₀ (succ k) (c , E) (a , t) (c< , p) (a< , all) =
 ⊗-<-ε₀ ((a ⊕ tsum k t) ⊕ c) (ω^ (valSc k E t))
   (⊕-<-ε₀ (a ⊕ tsum k t) c (tsum-<-ε₀ (succ k) (a , t) (a< , all)) c<)
   (ω^-<-ε₀ (valSc k E t) (valSc-<-ε₀ k E t p all))

valSc-mono : (k : ℕ) (E : Sc k) (t u : Tup k) → t ⊑ u
           → valSc k E t ≤ valSc k E u
valSc-mono zero     c       t       u       p       = ≤-refl c
valSc-mono (succ k) (c , E) (a , t) (b , u) (p , q) =
 ≤-trans (⊗-mono-left base≤ (ω^ (valSc k E t)))
         (⊗-mono-right ((b ⊕ tsum k u) ⊕ c)
                       (ω^-mono (valSc-mono k E t u q)))
 where
  base≤ : ((a ⊕ tsum k t) ⊕ c) ≤ ((b ⊕ tsum k u) ⊕ c)
  base≤ = ⊕-mono-left (≤-trans (⊕-mono-left p (tsum k t))
                               (⊕-mono-right b (tsum-mono k t u q))) c

valSc-increasing : (k : ℕ) (c : 𝓑) (E : Sc k) (a : 𝓑) (t : Tup k)
                 → a ≤ valSc (succ k) (c , E) (a , t)
valSc-increasing k c E a t =
 ≤-trans (⊕-increasing-right a (tsum k t))
  (≤-trans (⊕-increasing-right (a ⊕ tsum k t) c)
           (x-≤-x⊗ ((a ⊕ tsum k t) ⊕ c) (ω^ (valSc k E t))
                   (one-≤-ω^ (valSc k E t))))

\end{code}

A successor is absorbed by a successor on each translation. The value of the
map is then positive, so the successor is below a doubling, and the doubling
is below the multiplier of the grade above raised by one.

\begin{code}

sucSc : (k : ℕ) → Sc k → Sc k
sucSc zero     c       = S c
sucSc (succ k) (c , E) = S c , sucSc k E

valSc-suc : (k : ℕ) (E : Sc k) (t : Tup k)
          → S (valSc k E t) ≤ valSc k (sucSc k E) t
valSc-suc zero     c       t       = ≤-refl (S c)
valSc-suc (succ k) (c , E) (a , t) =
 ≤-trans (≤-S V≥) (≤-trans S≤dup (≤-trans (dup-ω V) grow))
 where
  s : 𝓑
  s = a ⊕ tsum k t

  X : 𝓑
  X = valSc k E t

  V : 𝓑
  V = S (s ⊕ c) ⊗ ω^ X

  V≥ : ((s ⊕ c) ⊗ ω^ X) ≤ V
  V≥ = ⊗-mono-left (S-increasing (s ⊕ c)) (ω^ X)

  V≥1 : S Z ≤ V
  V≥1 = ≤-trans (≤-S ≤-Z) (x-≤-x⊗ (S (s ⊕ c)) (ω^ X) (one-≤-ω^ X))

  S≤dup : S V ≤ (V ⊕ V)
  S≤dup = ⊕-mono-right V V≥1

  grow : (V ⊗ ω) ≤ (S (s ⊕ c) ⊗ ω^ (valSc k (sucSc k E) t))
  grow = transport (_≤ (S (s ⊕ c) ⊗ ω^ (valSc k (sucSc k E) t)))
                   ((⊗-assoc (S (s ⊕ c)) (ω^ X) ω) ⁻¹)
                   (⊗-mono-right (S (s ⊕ c))
                                 (ω^-mono (valSc-suc k E t)))

\end{code}

The repeated argument. Two scalar graded maps at one tuple sum to below a
single one, whose translations are the sums of the given ones and whose
exponent is the sum of the two exponents with one successor, the successor
being the cost of the doubling.

\begin{code}

joinSc : (k : ℕ) → Sc k → Sc k → Sc k
joinSc zero     c₁        c₂        = c₁ ⊕ c₂
joinSc (succ k) (c₁ , E₁) (c₂ , E₂) =
 (c₁ ⊕ c₂) , sucSc k (joinSc k E₁ E₂)

valSc-join : (k : ℕ) (E₁ E₂ : Sc k) (t : Tup k)
           → (valSc k E₁ t ⊕ valSc k E₂ t) ≤ valSc k (joinSc k E₁ E₂) t
valSc-join zero     c₁        c₂        t       = ≤-refl (c₁ ⊕ c₂)
valSc-join (succ k) (c₁ , E₁) (c₂ , E₂) (a , t) =
 ≤-trans (⊕-mono-left b₁ ((s ⊕ c₂) ⊗ ω^ X₂))
  (≤-trans (⊕-mono-right W b₂)
           (≤-trans (dup-ω W) grow))
 where
  s : 𝓑
  s = a ⊕ tsum k t

  X₁ X₂ : 𝓑
  X₁ = valSc k E₁ t
  X₂ = valSc k E₂ t

  W : 𝓑
  W = (s ⊕ (c₁ ⊕ c₂)) ⊗ ω^ (X₁ ⊕ X₂)

  b₁ : ((s ⊕ c₁) ⊗ ω^ X₁) ≤ W
  b₁ = ≤-trans (⊗-mono-left (⊕-mono-right s (⊕-increasing-right c₁ c₂))
                            (ω^ X₁))
               (⊗-mono-right (s ⊕ (c₁ ⊕ c₂))
                             (ω^-mono (⊕-increasing-right X₁ X₂)))

  b₂ : ((s ⊕ c₂) ⊗ ω^ X₂) ≤ W
  b₂ = ≤-trans (⊗-mono-left (⊕-mono-right s (⊕-increasing-left c₁ c₂))
                            (ω^ X₂))
               (⊗-mono-right (s ⊕ (c₁ ⊕ c₂))
                             (ω^-mono (⊕-increasing-left X₁ X₂)))

  exp≤ : S (X₁ ⊕ X₂) ≤ valSc k (sucSc k (joinSc k E₁ E₂)) t
  exp≤ = ≤-trans (≤-S (valSc-join k E₁ E₂ t))
                 (valSc-suc k (joinSc k E₁ E₂) t)

  grow : (W ⊗ ω) ≤ ((s ⊕ (c₁ ⊕ c₂))
                     ⊗ ω^ (valSc k (sucSc k (joinSc k E₁ E₂)) t))
  grow = transport (_≤ ((s ⊕ (c₁ ⊕ c₂))
                         ⊗ ω^ (valSc k (sucSc k (joinSc k E₁ E₂)) t)))
                   ((⊗-assoc (s ⊕ (c₁ ⊕ c₂)) (ω^ (X₁ ⊕ X₂)) ω) ⁻¹)
                   (⊗-mono-right (s ⊕ (c₁ ⊕ c₂)) (ω^-mono exp≤))

\end{code}

Widening. A scalar graded map on a tuple of width `k` is also one on a tuple
of width `k + 1`, reading the new grade in its base and nowhere else. The
widened map is the larger of the two, and the increase is by a translation of
one, which makes the base positive, so that the multiplier `ω^ X` is below the
value because `X ≤ ω^ X`.

\begin{code}

one-≤-⊗-left : (x y : 𝓑) → S Z ≤ x → y ≤ (x ⊗ y)
one-≤-⊗-left x Z     p = ≤-Z
one-≤-⊗-left x (S y) p =
 ≤-trans (⊕-mono-left (one-≤-⊗-left x y p) (S Z))
         (⊕-mono-right (x ⊗ y) p)
one-≤-⊗-left x (L f) p = ≤-L-mono (λ n → one-≤-⊗-left x (f n) p)

upSc : (k : ℕ) → Sc k → Sc (succ k)
upSc k E = S Z , E

valSc-up : (k : ℕ) (E : Sc k) (a : 𝓑) (t : Tup k)
         → valSc k E t ≤ valSc (succ k) (upSc k E) (a , t)
valSc-up k E a t =
 ≤-trans (≤-ω^ (valSc k E t))
         (≤-trans (one-≤-⊗-left (S (a ⊕ tsum k t)) (ω^ (valSc k E t))
                                (≤-S ≤-Z))
                  (≤-refl (S (a ⊕ tsum k t) ⊗ ω^ (valSc k E t))))

upSc-All< : (k : ℕ) (E : Sc k) → ScAll< k E → ScAll< (succ k) (upSc k E)
upSc-All< k E p = S-<-ε₀ Z Z<ε₀ , p

\end{code}

The data built by the two constructions stay below `ε₀`, so that a bound can
be used as a datum in its turn.

\begin{code}

sucSc-All< : (k : ℕ) (E : Sc k) → ScAll< k E → ScAll< k (sucSc k E)
sucSc-All< zero     c       p        = S-<-ε₀ c p
sucSc-All< (succ k) (c , E) (c< , p) = S-<-ε₀ c c< , sucSc-All< k E p

joinSc-All< : (k : ℕ) (E₁ E₂ : Sc k) → ScAll< k E₁ → ScAll< k E₂
            → ScAll< k (joinSc k E₁ E₂)
joinSc-All< zero     c₁        c₂        p         q         =
 ⊕-<-ε₀ c₁ c₂ p q
joinSc-All< (succ k) (c₁ , E₁) (c₂ , E₂) (c₁< , p) (c₂< , q) =
 ⊕-<-ε₀ c₁ c₂ c₁< c₂< , sucSc-All< k (joinSc k E₁ E₂) (joinSc-All< k E₁ E₂ p q)

\end{code}

The zero map, the constant below a value, and multiplication by `ω`. A value
multiplied by `ω` is again a value, by one successor on the exponent, and at
the bottom of the recursion by the multiplication itself.

\begin{code}

zeroSc : (k : ℕ) → Sc k
zeroSc zero     = Z
zeroSc (succ k) = Z , zeroSc k

zeroSc-All< : (k : ℕ) → ScAll< k (zeroSc k)
zeroSc-All< zero     = Z<ε₀
zeroSc-All< (succ k) = Z<ε₀ , zeroSc-All< k

valSc-const : (k : ℕ) (c : 𝓑) (E : Sc k) (a : 𝓑) (t : Tup k)
            → c ≤ valSc (succ k) (c , E) (a , t)
valSc-const k c E a t =
 ≤-trans (⊕-increasing-left (a ⊕ tsum k t) c)
         (x-≤-x⊗ ((a ⊕ tsum k t) ⊕ c) (ω^ (valSc k E t))
                 (one-≤-ω^ (valSc k E t)))

bumpSc : (k : ℕ) → Sc k → Sc k
bumpSc zero     c       = c ⊗ ω
bumpSc (succ k) (c , E) = c , sucSc k E

valSc-bump : (k : ℕ) (E : Sc k) (t : Tup k)
           → (valSc k E t ⊗ ω) ≤ valSc k (bumpSc k E) t
valSc-bump zero     c       t       = ≤-refl (c ⊗ ω)
valSc-bump (succ k) (c , E) (a , t) =
 transport (_≤ (((a ⊕ tsum k t) ⊕ c) ⊗ ω^ (valSc k (sucSc k E) t)))
           ((⊗-assoc ((a ⊕ tsum k t) ⊕ c) (ω^ (valSc k E t)) ω) ⁻¹)
           (⊗-mono-right ((a ⊕ tsum k t) ⊕ c)
                         (ω^-mono (valSc-suc k E t)))

bumpSc-All< : (k : ℕ) (E : Sc k) → ScAll< k E → ScAll< k (bumpSc k E)
bumpSc-All< zero     c       p        = ⊗-<-ε₀ c ω p ω<ε₀
bumpSc-All< (succ k) (c , E) (c< , p) = c< , sucSc-All< k E p

\end{code}
