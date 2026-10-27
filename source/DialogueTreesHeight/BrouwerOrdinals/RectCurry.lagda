Binding a variable: a map of two tuples as a map of one, twice over.

A term in a context has one datum per variable, and the predicate asks of an
abstraction that the datum of the body, which is a map of all of them at once,
be read back as a map of the remaining ones whose output, read as the datum of
a map, acts on the bound one. That is currying, and we prove it here.

The variables are held in one tuple, the datum of each variable being below
it, so that monotonicity of `Dom` allows a variable to use the combined datum
in place of its own. The combination is slotwise addition, and the order of
the two tuples matters: the variable about to be bound comes first, because
the curried form puts the slots of that variable first and no summand can be
moved left past another. With the order reversed the statement already fails
at one slot of each, where it asks for `(x₀ ⊕ y₀) ⊕ c ≤ y₀ ⊕ (x₀ ⊕ c)`.

With the order as given, one slot of each is an associativity, and two are
not: the sum of the combined tuple interleaves, as `y₀ ⊕ x₀ ⊕ y₁ ⊕ x₁`,
whereas the curried form cannot interleave, since the shape of a value on the
tuple `y` puts `y₀ ⊕ tsum y` first and everything concerning `x` after it. The
bases are therefore not compared directly. Each piece of the interleaving is
below the curried base, so the interleaving is below a finite multiple of that
base, and the module Absorb turns a finite multiple into one successor on the
exponent. The induction has such a successor to spare, because it proves the
stronger statement that the curried value dominates the successor of the
combined value times `ω`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.BrouwerOrdinals.RectCurry
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import DialogueTreesHeight.BrouwerOrdinals.Order fe
 using (_≤_ ; _⊕_ ; ≤-Z ; ≤-S ; ≤-refl ; ≤-trans)
open import DialogueTreesHeight.BrouwerOrdinals.Multiplication fe
 using (ω ; _⊗_ ; ⊗-assoc ; ⊕-increasing-left)
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
 using (ω^_ ; ω^-mono ; ⊗-mono-left ; ⊗-mono-right ; ⊕-increasing-right ;
        S-increasing ; one-≤-ω^ ; S-<-ε₀ ; ⊕-<-ε₀ ; x-≤-x⊗)
open import DialogueTreesHeight.BrouwerOrdinals.MoveTuple fe
 using (Tup ; tsum ; _⊑_ ; ⊑-trans ; All<)
open import DialogueTreesHeight.BrouwerOrdinals.Cascade fe
 using (Sc ; valSc ; ScAll< ; sucSc ; sucSc-All< ; valSc-suc ; bumpSc ;
        bumpSc-All< ; valSc-bump ; zeroSc ; zeroSc-All< ;
        valSc-increasing)
open import DialogueTreesHeight.BrouwerOrdinals.CascadeLevel fe
 using (tupToSc ; scToTup ; scToTup-All< ; valSc-⊑)
open import DialogueTreesHeight.BrouwerOrdinals.Rect fe
open import DialogueTreesHeight.BrouwerOrdinals.RectAdd fe
 using (pair＝)
open import DialogueTreesHeight.BrouwerOrdinals.RectAlgebra fe
 using (_⊴_ ; ⊴-refl ; zeroRD ; zeroRD-All< ; joinRD ; joinRD-left ;
        joinRD-right ; joinRD-All< ; padRD ; rect-padRD ; padRD-All< ;
        flatRD ; flatRD-⊒ ; flatRD-All<)
open import DialogueTreesHeight.BrouwerOrdinals.MultAffine fe
 using (ω-pos)
open import DialogueTreesHeight.BrouwerOrdinals.Absorb fe

\end{code}

The combined tuple, slotwise, with the variable to be bound first.

\begin{code}

cmb : (p n : ℕ) → Tup p → Tup n → Tup (mx p n)
cmb zero     n        y        x        = x
cmb (succ p) zero     y        x        = y
cmb (succ p) (succ n) (y₀ , y) (x₀ , x) = (y₀ ⊕ x₀) , cmb p n y x

\end{code}

Each of the two tuples is contained in it, and its entries stay below `ε₀`.

\begin{code}

cmb-⊴-left : (p n : ℕ) (y : Tup p) (x : Tup n) → y ⊴ cmb p n y x
cmb-⊴-left zero     n        y        x        = ⋆
cmb-⊴-left (succ p) zero     y        x        = ⊴-refl (succ p) y
cmb-⊴-left (succ p) (succ n) (y₀ , y) (x₀ , x) =
 ⊕-increasing-right y₀ x₀ , cmb-⊴-left p n y x

cmb-⊴-right : (p n : ℕ) (y : Tup p) (x : Tup n) → x ⊴ cmb p n y x
cmb-⊴-right zero     n        y        x        = ⊴-refl n x
cmb-⊴-right (succ p) zero     y        x        = ⋆
cmb-⊴-right (succ p) (succ n) (y₀ , y) (x₀ , x) =
 ⊕-increasing-left y₀ x₀ , cmb-⊴-right p n y x

cmb-All< : (p n : ℕ) (y : Tup p) (x : Tup n) → All< p y → All< n x
         → All< (mx p n) (cmb p n y x)
cmb-All< zero     n        y        x        hy hx = hx
cmb-All< (succ p) zero     y        x        hy hx = hy
cmb-All< (succ p) (succ n) (y₀ , y) (x₀ , x) hy hx =
 ⊕-<-ε₀ y₀ x₀ (pr₁ hy) (pr₁ hx) , cmb-All< p n y x (pr₂ hy) (pr₂ hx)

\end{code}

Its sum is below a finite multiple of any code that both sums are below.

\begin{code}

tsum-cmb-⋖ : (p n : ℕ) (y : Tup p) (x : Tup n) (M : 𝓑)
           → tsum p y ≤ M → tsum n x ≤ M
           → tsum (mx p n) (cmb p n y x) ⋖ M
tsum-cmb-⋖ zero     n        y        x        M hy hx =
 ⋖-base M (tsum n x) hx
tsum-cmb-⋖ (succ p) zero     y        x        M hy hx =
 ⋖-base M (tsum (succ p) y) hy
tsum-cmb-⋖ (succ p) (succ n) (y₀ , y) (x₀ , x) M hy hx =
 ⋖-⊕ M (y₀ ⊕ x₀) (tsum (mx p n) (cmb p n y x))
   (⋖-⊕ M y₀ x₀ (⋖-base M y₀ y₀≤) (⋖-base M x₀ x₀≤))
   (tsum-cmb-⋖ p n y x M
      (≤-trans (⊕-increasing-left y₀ (tsum p y)) hy)
      (≤-trans (⊕-increasing-left x₀ (tsum n x)) hx))
 where
  y₀≤ : y₀ ≤ M
  y₀≤ = ≤-trans (⊕-increasing-right y₀ (tsum p y)) hy

  x₀≤ : x₀ ≤ M
  x₀≤ = ≤-trans (⊕-increasing-right x₀ (tsum n x)) hx

\end{code}

Two readings, each one half of an identity: a cascade as a map with one output
order, and a tuple as a map out of a tuple of width zero.

\begin{code}

hdOf : (n : ℕ) → Sc n → RD n 1
hdOf zero     c = c , ⋆
hdOf (succ n) E = E , ⋆

hdOf-val : (n : ℕ) (E : Sc n) (x : Tup n)
         → pr₁ (rect n 1 (hdOf n E) x) ＝ valSc n E x
hdOf-val zero     c x = refl
hdOf-val (succ n) E x = refl

tupToRD0 : (k : ℕ) → Tup k → RD 0 k
tupToRD0 zero     t       = ⋆
tupToRD0 (succ k) (a , t) = a , tupToRD0 k t

rect-tupToRD0 : (k : ℕ) (t : Tup k) (x : Tup 0)
              → rect 0 k (tupToRD0 k t) x ＝ t
rect-tupToRD0 zero     t       x = refl
rect-tupToRD0 (succ k) (a , t) x = pair＝ refl (rect-tupToRD0 k t x)

tupToSc-scToTup : (j : ℕ) (E : Sc j) → tupToSc j (scToTup j E) ＝ E
tupToSc-scToTup zero     c       = refl
tupToSc-scToTup (succ j) (c , E) = pair＝ refl (tupToSc-scToTup j E)

\end{code}

A value is above its own base.

\begin{code}

valSc-base : (k : ℕ) (c : 𝓑) (E : Sc k) (a : 𝓑) (t : Tup k)
           → ((a ⊕ tsum k t) ⊕ c) ≤ valSc (succ k) (c , E) (a , t)
valSc-base k c E a t =
 x-≤-x⊗ ((a ⊕ tsum k t) ⊕ c) (ω^ (valSc k E t)) (one-≤-ω^ (valSc k E t))

\end{code}

The scalar case of currying: one cascade on the combined tuple, read back as a
cascade of the bound variable whose translations are values of the other. The
bound is strict and carries a factor of `ω`, which the step above it spends on
the interleaving.

\begin{code}

scurryD : (p n : ℕ) → Sc (mx p n) → RD n (succ p)
scurryD zero     n        E       = hdOf n (bumpSc n (sucSc n E))
scurryD (succ p) zero     E       =
 tupToRD0 (succ (succ p))
   (scToTup (succ p) (bumpSc (succ p) (sucSc (succ p) E)))
scurryD (succ p) (succ n) (c , E) = (S c , zeroSc n) , scurryD p n E

valSc-scurry : (p n : ℕ) (E : Sc (mx p n)) (y : Tup p) (x : Tup n)
             → (S (valSc (mx p n) E (cmb p n y x)) ⊗ ω)
               ≤ valSc p (tupToSc p (rect n (succ p) (scurryD p n E) x)) y
valSc-scurry zero     n        E       y        x       =
 transport ((S (valSc n E x) ⊗ ω) ≤_)
           ((hdOf-val n (bumpSc n (sucSc n E)) x) ⁻¹)
           (≤-trans (⊗-mono-left (valSc-suc n E x) ω)
                    (valSc-bump n (sucSc n E) x))
valSc-scurry (succ p) zero     E       y        x       =
 transport (λ u → (S (valSc (succ p) E y) ⊗ ω)
                  ≤ valSc (succ p) (tupToSc (succ p) u) y)
           ((rect-tupToRD0 (succ (succ p)) (scToTup (succ p) F) x) ⁻¹)
           (transport (λ V → (S (valSc (succ p) E y) ⊗ ω)
                             ≤ valSc (succ p) V y)
                      ((tupToSc-scToTup (succ p) F) ⁻¹)
                      (≤-trans (⊗-mono-left (valSc-suc (succ p) E y) ω)
                               (valSc-bump (succ p) (sucSc (succ p) E) y)))
 where
  F : Sc (succ p)
  F = bumpSc (succ p) (sucSc (succ p) E)
valSc-scurry (succ p) (succ n) (c , E) (y₀ , y) (x₀ , x) =
 ≤-trans (⋖-ω Y (S (bL ⊗ ω^ XL)) sj) (≤-trans fin last)
 where
  T : 𝓑
  T = tsum (mx p n) (cmb p n y x)

  XL : 𝓑
  XL = valSc (mx p n) E (cmb p n y x)

  bL : 𝓑
  bL = ((y₀ ⊕ x₀) ⊕ T) ⊕ c

  A₀ : 𝓑
  A₀ = valSc (succ n) (S c , zeroSc n) (x₀ , x)

  R : Tup (succ p)
  R = rect n (succ p) (scurryD p n E) x

  XR : 𝓑
  XR = valSc p (tupToSc p R) y

  bR : 𝓑
  bR = (y₀ ⊕ tsum p y) ⊕ A₀

  Y : 𝓑
  Y = bR ⊗ ω^ (S XL)

  Ab : ((x₀ ⊕ tsum n x) ⊕ S c) ≤ A₀
  Ab = valSc-base n (S c) (zeroSc n) x₀ x

  A≤ : A₀ ≤ bR
  A≤ = ⊕-increasing-left (y₀ ⊕ tsum p y) A₀

  x₀≤ : x₀ ≤ bR
  x₀≤ = ≤-trans (valSc-increasing n (S c) (zeroSc n) x₀ x) A≤

  sumx≤ : tsum n x ≤ bR
  sumx≤ =
   ≤-trans (⊕-increasing-left x₀ (tsum n x))
           (≤-trans (⊕-increasing-right (x₀ ⊕ tsum n x) (S c))
                    (≤-trans Ab A≤))

  c≤ : c ≤ bR
  c≤ = ≤-trans (S-increasing c)
        (≤-trans (⊕-increasing-left (x₀ ⊕ tsum n x) (S c))
                 (≤-trans Ab A≤))

  one≤ : S Z ≤ bR
  one≤ = ≤-trans (≤-S ≤-Z)
          (≤-trans (⊕-increasing-left (x₀ ⊕ tsum n x) (S c))
                   (≤-trans Ab A≤))

  y₀≤ : y₀ ≤ bR
  y₀≤ = ≤-trans (⊕-increasing-right y₀ (tsum p y))
                (⊕-increasing-right (y₀ ⊕ tsum p y) A₀)

  sumy≤ : tsum p y ≤ bR
  sumy≤ = ≤-trans (⊕-increasing-left y₀ (tsum p y))
                  (⊕-increasing-right (y₀ ⊕ tsum p y) A₀)

  bL⋖ : bL ⋖ bR
  bL⋖ = ⋖-⊕ bR ((y₀ ⊕ x₀) ⊕ T) c
          (⋖-⊕ bR (y₀ ⊕ x₀) T
             (⋖-⊕ bR y₀ x₀ (⋖-base bR y₀ y₀≤) (⋖-base bR x₀ x₀≤))
             (tsum-cmb-⋖ p n y x bR sumy≤ sumx≤))
          (⋖-base bR c c≤)

  v≤ : (bL ⊗ ω^ XL) ≤ Y
  v≤ = ⋖-⊗ bR bL XL bL⋖

  oneY : S Z ≤ Y
  oneY = ≤-trans one≤ (x-≤-x⊗ bR (ω^ (S XL)) (one-≤-ω^ (S XL)))

  sj : S (bL ⊗ ω^ XL) ⋖ Y
  sj = ⋖-⊕ Y (bL ⊗ ω^ XL) (S Z)
         (⋖-base Y (bL ⊗ ω^ XL) v≤)
         (⋖-base Y (S Z) oneY)

  fin : (Y ⊗ ω) ≤ (bR ⊗ ω^ (S (S XL)))
  fin = transport (_≤ (bR ⊗ ω^ (S (S XL))))
                  ((⊗-assoc bR (ω^ (S XL)) ω) ⁻¹)
                  (≤-refl (bR ⊗ ω^ (S (S XL))))

  exp≤ : S (S XL) ≤ XR
  exp≤ = ≤-trans (⋖-⊗ω (S XL) (S (S XL))
                   (⋖-⊕ (S XL) (S XL) (S Z)
                      (⋖-base (S XL) (S XL) (≤-refl (S XL)))
                      (⋖-base (S XL) (S Z) (≤-S ≤-Z))))
                 (valSc-scurry p n E y x)

  last : (bR ⊗ ω^ (S (S XL))) ≤ ((y₀ ⊕ tsum p y) ⊕ A₀) ⊗ ω^ XR
  last = ⊗-mono-right bR (ω^-mono exp≤)

\end{code}

At width zero a reading returns the datum.

\begin{code}

rdOf-zero-id′ : (q : ℕ) (d : Tup (succ q)) (y : Tup zero)
              → d ⊑ rect zero (succ q) (rdOf zero (succ q) d) y
rdOf-zero-id′ zero     d y = ≤-refl (pr₁ d) , ⋆
rdOf-zero-id′ (succ q) d y = ≤-refl (pr₁ d) , rdOf-zero-id′ q (pr₂ d) y

\end{code}

Currying. At each output order `scurryD` turns the cascade of the combined
tuple into a cascade of the bound variable whose translations are values of
the rest, and the data producing those translations are joined with the data
that the recursion asks for, the same slots serving both.

\begin{code}

curryD : (p n q : ℕ) → RD (mx p n) q → RD n (WD p q)
curryD p        n        zero     D             = zeroRD n (succ p)
curryD zero     n        (succ q) D             = D
curryD (succ p) zero     (succ q) D             =
 tupToRD0 (WD (succ p) (succ q)) (flatRD (succ p) (succ q) D)
curryD (succ p) (succ n) (succ q) ((c , E) , D) =
 joinRD (succ n) (succ (WD p q))
   (padRD (succ n) (succ (succ p)) (succ q)
      (scurryD (succ p) (succ n) (c , E)))
   (zeroSc (succ n) , curryD p n q D)

rect-curry : (p n q : ℕ) (D : RD (mx p n) q) (y : Tup p) (x : Tup n)
           → rect (mx p n) q D (cmb p n y x)
             ⊑ rect p q (rdOf p q (rect n (WD p q) (curryD p n q D) x)) y
rect-curry p        n        zero     D             y        x       = ⋆
rect-curry zero     n        (succ q) D             y        x       =
 rdOf-zero-id′ q (rect n (succ q) D x) y
rect-curry (succ p) zero     (succ q) D             y        x       =
 transport (λ u → rect (succ p) (succ q) D y
                  ⊑ rect (succ p) (succ q) (rdOf (succ p) (succ q) u) y)
           ((rect-tupToRD0 (WD (succ p) (succ q))
               (flatRD (succ p) (succ q) D) x) ⁻¹)
           (rect-⊑RD (succ p) (succ q) D
              (rdOf (succ p) (succ q) (flatRD (succ p) (succ q) D))
              (flatRD-⊒ (succ p) (succ q) D) y)
rect-curry (succ p) (succ n) (succ q) ((c , E) , D) (y₀ , y) (x₀ , x) =
 head , tail
 where
  Es : Sc (succ (mx p n))
  Es = c , E

  P : RD (succ n) (succ (WD p q))
  P = padRD (succ n) (succ (succ p)) (succ q) (scurryD (succ p) (succ n) Es)

  C : RD (succ n) (succ (WD p q))
  C = zeroSc (succ n) , curryD p n q D

  Dj : RD (succ n) (succ (WD p q))
  Dj = joinRD (succ n) (succ (WD p q)) P C

  d : Tup (succ (WD p q))
  d = rect (succ n) (succ (WD p q)) Dj (x₀ , x)

  Rs : Tup (succ (succ p))
  Rs = rect (succ n) (succ (succ p)) (scurryD (succ p) (succ n) Es) (x₀ , x)

  V : 𝓑
  V = valSc (succ (mx p n)) Es (cmb (succ p) (succ n) (y₀ , y) (x₀ , x))

  Rs⊑ : Rs ⊑ pre (succ (succ p)) (succ q) d
  Rs⊑ =
   transport (_⊑ pre (succ (succ p)) (succ q) d)
     (rect-padRD (succ n) (succ (succ p)) (succ q)
        (scurryD (succ p) (succ n) Es) (x₀ , x))
     (pre-mono (succ (succ p)) (succ q)
        (rect (succ n) (succ (WD p q)) P (x₀ , x)) d
        (rect-⊑RD (succ n) (succ (WD p q)) P Dj
           (joinRD-left (succ n) (succ (WD p q)) P C) (x₀ , x)))

  head : V ≤ valSc (succ p)
               (tupToSc (succ p) (pre (succ (succ p)) (succ q) d))
               (y₀ , y)
  head =
   ≤-trans (≤-trans (S-increasing V) (x-≤-x⊗ (S V) ω ω-pos))
    (≤-trans (valSc-scurry (succ p) (succ n) Es (y₀ , y) (x₀ , x))
             (valSc-⊑ (succ p) (tupToSc (succ p) Rs)
                (tupToSc (succ p) (pre (succ (succ p)) (succ q) d))
                (tupToSc-mono (succ p) Rs
                   (pre (succ (succ p)) (succ q) d) Rs⊑)
                (y₀ , y)))

  tail : rect (mx p n) q D (cmb p n y x)
         ⊑ rect p q (rdOf p q (pr₂ d)) y
  tail =
   ⊑-trans q _ _ _
     (rect-curry p n q D y x)
     (rect-⊑RD p q (rdOf p q (rect n (WD p q) (curryD p n q D) x))
        (rdOf p q (pr₂ d))
        (rdOf-mono p q (rect n (WD p q) (curryD p n q D) x) (pr₂ d)
           (rect-⊑RD n (WD p q) (curryD p n q D) (pr₂ Dj)
              (joinRD-right n (WD p q) (pr₂ P) (curryD p n q D)) x))
        y)

\end{code}

The data stay below `ε₀`.

\begin{code}

hdOf-All< : (n : ℕ) (E : Sc n) → ScAll< n E → RDAll< n 1 (hdOf n E)
hdOf-All< zero     c h = h , ⋆
hdOf-All< (succ n) E h = h , ⋆

tupToRD0-All< : (k : ℕ) (t : Tup k) → All< k t → RDAll< 0 k (tupToRD0 k t)
tupToRD0-All< zero     t       h = ⋆
tupToRD0-All< (succ k) (a , t) h = pr₁ h , tupToRD0-All< k t (pr₂ h)

scurryD-All< : (p n : ℕ) (E : Sc (mx p n)) → ScAll< (mx p n) E
             → RDAll< n (succ p) (scurryD p n E)
scurryD-All< zero     n        E       h =
 hdOf-All< n (bumpSc n (sucSc n E))
   (bumpSc-All< n (sucSc n E) (sucSc-All< n E h))
scurryD-All< (succ p) zero     E       h =
 tupToRD0-All< (succ (succ p))
   (scToTup (succ p) (bumpSc (succ p) (sucSc (succ p) E)))
   (scToTup-All< (succ p) (bumpSc (succ p) (sucSc (succ p) E))
      (bumpSc-All< (succ p) (sucSc (succ p) E)
         (sucSc-All< (succ p) E h)))
scurryD-All< (succ p) (succ n) (c , E) h =
 (S-<-ε₀ c (pr₁ h) , zeroSc-All< n) , scurryD-All< p n E (pr₂ h)

curryD-All< : (p n q : ℕ) (D : RD (mx p n) q) → RDAll< (mx p n) q D
            → RDAll< n (WD p q) (curryD p n q D)
curryD-All< p        n        zero     D             h = zeroRD-All< n (succ p)
curryD-All< zero     n        (succ q) D             h = h
curryD-All< (succ p) zero     (succ q) D             h =
 tupToRD0-All< (WD (succ p) (succ q)) (flatRD (succ p) (succ q) D)
   (flatRD-All< (succ p) (succ q) D h)
curryD-All< (succ p) (succ n) (succ q) ((c , E) , D) h =
 joinRD-All< (succ n) (succ (WD p q))
   (padRD (succ n) (succ (succ p)) (succ q)
      (scurryD (succ p) (succ n) (c , E)))
   (zeroSc (succ n) , curryD p n q D)
   (padRD-All< (succ n) (succ (succ p)) (succ q)
      (scurryD (succ p) (succ n) (c , E))
      (scurryD-All< (succ p) (succ n) (c , E) (pr₁ h)))
   (zeroSc-All< (succ n) , curryD-All< p n q D (pr₂ h))

\end{code}
