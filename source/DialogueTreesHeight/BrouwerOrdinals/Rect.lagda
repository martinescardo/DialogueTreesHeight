Rectangular graded maps, at every pair of widths.

A datum is a tuple graded by order: order `0` is a translation, order `1` an
exponent, order `2` the exponent of an exponent, and so on. A map from data of
width `p` to data of width `q` is given, for each output order `j`, by a
scalar cascade reading the input orders `j` and above. One constraint governs
the whole construction: an exponent is raised only by entries of its own order
or higher, which is the property that iterating `x ↦ ω^ x` violates. The same
rule governs equal and unequal widths alike.

The datum of such a map is held as the triangular array it is, rather than
compressed: one cascade per output order, each shorter than the last, and a
bare constant once the input orders are exhausted. The action is `rect`.

For the datum of a map to be a datum in its turn it has to be a tuple as well,
and `rdOf` reads a map out of one. The width needed is
`WD p q = mx (succ p) q`, since the first cascade needs one order more than
the input has and the output
needs one order per slot. Every width used here is a successor, the width of a
datum for a type being `wd σ = succ (ord σ)`, so this reads
`mx (succ p) (succ q′)` for `q = succ q′`. The recursion lowers that width by
one at each step, which is why the maximum is written with the clause
`mx (succ m) (succ n) = succ (mx m n)`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.BrouwerOrdinals.Rect
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀)
open import DialogueTreesHeight.BrouwerOrdinals.MoveTuple fe
 using (Tup ; All<)
open import DialogueTreesHeight.BrouwerOrdinals.Order fe
 using (_≤_ ; ≤-refl)
open import DialogueTreesHeight.BrouwerOrdinals.MoveTuple fe
 using (_⊑_)
open import DialogueTreesHeight.BrouwerOrdinals.Cascade fe
 using (Sc ; valSc ; ScAll< ; valSc-increasing ; valSc-const ; valSc-<-ε₀)
open import DialogueTreesHeight.BrouwerOrdinals.CascadeLevel fe
 using (tupToSc ; tupToSc-All< ; _⊑Sc_ ; valSc-⊑)

\end{code}

The maximum, written so that it takes successors apart.

\begin{code}

mx : ℕ → ℕ → ℕ
mx zero     n        = n
mx (succ m) zero     = succ m
mx (succ m) (succ n) = succ (mx m n)

pre : (a b : ℕ) → Tup (mx a b) → Tup a
pre zero     b        t       = ⋆
pre (succ a) zero     t       = t
pre (succ a) (succ b) (x , t) = x , pre a b t

\end{code}

The datum of a graded map, and its action.

\begin{code}

RD : ℕ → ℕ → 𝓤₀ ̇
RD p        zero     = 𝟙 {𝓤₀}
RD zero     (succ q) = 𝓑 × RD zero q
RD (succ p) (succ q) = Sc (succ p) × RD p q

rect : (p q : ℕ) → RD p q → Tup p → Tup q
rect p        zero     D       x       = ⋆
rect zero     (succ q) (c , D) x       = c , rect zero q D x
rect (succ p) (succ q) (E , D) (a , t) =
 valSc (succ p) E (a , t) , rect p q D t

\end{code}

Reading a graded map out of a tuple: the cascade for output order `j` is the
suffix of the tuple from `j`. The sharing of entries is what makes the datum
of a map fit into one order more than the map's two sides.

\begin{code}

WD : ℕ → ℕ → ℕ
WD p q = mx (succ p) q

rdOf : (p q : ℕ) → Tup (WD p q) → RD p q
rdOf p        zero            d = ⋆
rdOf zero     (succ zero)     d = pr₁ d , ⋆
rdOf zero     (succ (succ q)) d = pr₁ d , rdOf zero (succ q) (pr₂ d)
rdOf (succ p) (succ q)        d =
 tupToSc (succ p) (pre (succ (succ p)) (succ q) d) , rdOf p q (pr₂ d)

\end{code}

The data a reading produces stay below `ε₀`.

\begin{code}

RDAll< : (p q : ℕ) → RD p q → 𝓤₀ ̇
RDAll< p        zero     D       = 𝟙 {𝓤₀}
RDAll< zero     (succ q) (c , D) = (c < ε₀) × RDAll< zero q D
RDAll< (succ p) (succ q) (E , D) = ScAll< (succ p) E × RDAll< p q D

rect-All< : (p q : ℕ) (D : RD p q) (x : Tup p) → RDAll< p q D → All< p x
          → All< q (rect p q D x)
rect-All< p        zero     D         x       h        hx       = ⋆
rect-All< zero     (succ q) (c , D) x       (h , h′) hx       =
 h , rect-All< zero q D x h′ hx
rect-All< (succ p) (succ q) (E , D) (a , t) (h , h′) (a< , hx) =
 valSc-<-ε₀ (succ p) E (a , t) h (a< , hx) , rect-All< p q D t h′ hx

pre-All< : (a b : ℕ) (t : Tup (mx a b)) → All< (mx a b) t → All< a (pre a b t)
pre-All< zero     b        t       p        = ⋆
pre-All< (succ a) zero     t       p        = p
pre-All< (succ a) (succ b) (x , t) (x< , p) = x< , pre-All< a b t p

rdOf-All< : (p q : ℕ) (d : Tup (WD p q)) → All< (WD p q) d
          → RDAll< p q (rdOf p q d)
rdOf-All< p        zero            d p′ = ⋆
rdOf-All< zero     (succ zero)     d p′ = pr₁ p′ , ⋆
rdOf-All< zero     (succ (succ q)) d p′ =
 pr₁ p′ , rdOf-All< zero (succ q) (pr₂ d) (pr₂ p′)
rdOf-All< (succ p) (succ q)        d p′ =
 tupToSc-All< (succ p) (pre (succ (succ p)) (succ q) d)
   (pre-All< (succ (succ p)) (succ q) d p′) ,
 rdOf-All< p q (pr₂ d) (pr₂ p′)

\end{code}

Monotonicity, in the datum and in the argument, and that a square action is
inflationary.

\begin{code}

_⊑RD_ : {p q : ℕ} → RD p q → RD p q → 𝓤₀ ̇
_⊑RD_ {p}      {zero}   D         D′         = 𝟙 {𝓤₀}
_⊑RD_ {zero}   {succ q} (c , D) (c′ , D′) = (c ≤ c′) × (D ⊑RD D′)
_⊑RD_ {succ p} {succ q} (E , D) (E′ , D′) = (E ⊑Sc E′) × (D ⊑RD D′)

rect-⊑RD : (p q : ℕ) (D D′ : RD p q) → D ⊑RD D′ → (x : Tup p)
         → rect p q D x ⊑ rect p q D′ x
rect-⊑RD p        zero     D         D′          h       x       = ⋆
rect-⊑RD zero     (succ q) (c , D) (c′ , D′) (h , h′) x       =
 h , rect-⊑RD zero q D D′ h′ x
rect-⊑RD (succ p) (succ q) (E , D) (E′ , D′) (h , h′) (a , t) =
 valSc-⊑ (succ p) E E′ h (a , t) , rect-⊑RD p q D D′ h′ t

rect-increasing : (p : ℕ) (D : RD p p) (x : Tup p) → x ⊑ rect p p D x
rect-increasing zero     D         x       = ⋆
rect-increasing (succ p) (E , D) (a , t) =
 valSc-increasing p (pr₁ E) (pr₂ E) a t , rect-increasing p D t

\end{code}

Monotonicity of the reading.

\begin{code}

tupToSc-mono : (j : ℕ) (t u : Tup (succ j)) → t ⊑ u
             → tupToSc j t ⊑Sc tupToSc j u
tupToSc-mono zero     (a , t) (b , u) (h , h′) = h
tupToSc-mono (succ j) (a , t) (b , u) (h , h′) =
 h , tupToSc-mono j t u h′

pre-mono : (a b : ℕ) (t u : Tup (mx a b)) → t ⊑ u → pre a b t ⊑ pre a b u
pre-mono zero     b        t       u       h       = ⋆
pre-mono (succ a) zero     t       u       h       = h
pre-mono (succ a) (succ b) (x , t) (y , u) (h , h′) =
 h , pre-mono a b t u h′

rdOf-mono : (p q : ℕ) (d d′ : Tup (WD p q)) → d ⊑ d′
          → rdOf p q d ⊑RD rdOf p q d′
rdOf-mono p        zero            d d′ h = ⋆
rdOf-mono zero     (succ zero)     d d′ h = pr₁ h , ⋆
rdOf-mono zero     (succ (succ q)) d d′ h =
 pr₁ h , rdOf-mono zero (succ q) (pr₂ d) (pr₂ d′) (pr₂ h)
rdOf-mono (succ p) (succ q)        d d′ h =
 tupToSc-mono (succ p) (pre (succ (succ p)) (succ q) d)
                       (pre (succ (succ p)) (succ q) d′)
   (pre-mono (succ (succ p)) (succ q) d d′ h) ,
 rdOf-mono p q (pr₂ d) (pr₂ d′) (pr₂ h)

\end{code}

An action dominates the datum it was read from, slot by slot, as far as the
output reaches. At each output order the translation of the cascade is that
slot of the datum, and a cascade is above its translation. This is the clause
for `K`, a function constant in its argument keeping the datum it had.

\begin{code}

topq : (p q : ℕ) → Tup (WD p q) → Tup q
topq p        zero            d = ⋆
topq zero     (succ zero)     d = pr₁ d , ⋆
topq zero     (succ (succ q)) d = pr₁ d , topq zero (succ q) (pr₂ d)
topq (succ p) (succ q)        d = pr₁ d , topq p q (pr₂ d)

rect-rdOf-≥ : (p q : ℕ) (d : Tup (WD p q)) (x : Tup p)
            → topq p q d ⊑ rect p q (rdOf p q d) x
rect-rdOf-≥ p        zero            d x       = ⋆
rect-rdOf-≥ zero     (succ zero)     d x       = ≤-refl (pr₁ d) , ⋆
rect-rdOf-≥ zero     (succ (succ q)) d x       =
 ≤-refl (pr₁ d) , rect-rdOf-≥ zero (succ q) (pr₂ d) x
rect-rdOf-≥ (succ p) (succ q)        d (a , t) =
 valSc-const p (pr₁ d)
   (pr₂ (tupToSc (succ p) (pre (succ (succ p)) (succ q) d))) a t ,
 rect-rdOf-≥ p q (pr₂ d) t

\end{code}

Symmetrically, an action dominates its argument, again as far as the output
reaches, since at each output order the cascade is applied to the suffix of
the argument from that order and a cascade is above the head of what it is
applied to. The same projection `topq` appears in both statements, which
allows them to compose, and the width at which they meet is `WD r p`, the
width of a datum for a map from `r` to `p`.

\begin{code}

rect-arg-≥ : (r p : ℕ) (D : RD p (WD r p)) (e : Tup p)
           → e ⊑ topq r p (rect p (WD r p) D e)
rect-arg-≥ r        zero            D       e       = ⋆
rect-arg-≥ zero     (succ zero)     (E , D) (a , t) =
 valSc-increasing 0 (pr₁ E) (pr₂ E) a t , ⋆
rect-arg-≥ zero     (succ (succ p)) (E , D) (a , t) =
 valSc-increasing (succ p) (pr₁ E) (pr₂ E) a t ,
 rect-arg-≥ zero (succ p) D t
rect-arg-≥ (succ r) (succ p)        (E , D) (a , t) =
 valSc-increasing p (pr₁ E) (pr₂ E) a t , rect-arg-≥ r p D t

\end{code}
