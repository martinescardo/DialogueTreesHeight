The iterates of a graded map, bounded by an action of the context.

Every iterate of a square action is below one tuple, and that tuple can be
given existentially. The clause for the recursor needs more: the bound has to
be an action of the tuple that holds the data of the context, since only then
does currying turn it into a datum for the recursor itself. We prove that
here, with a datum `rorbitD` depending on the two widths alone.

An existential bound cannot be rearranged into an action as it stands, since
its head is `(x₀ ⊕ (T ⊕ d₀)) ⊗ ω^ (((S X) ⊗ ω) ⊗ ω)`, where `T` is the sum of
the bound one order down and is therefore a tower, while the base of a value
at the context holds only the entries of the context. A different comparison
serves. For `A′ ≥ 1`

    A ⊗ ω^ B  ≤  A′ ⊗ ω^ (T ⊕ S B)

holds whenever `A` is below a finite multiple of `A′ ⊗ ω^ T`, which it is,
because `x₀` and `d₀` are below `A′` and `T` is below `ω^ T`. The tower
therefore moves into the exponent, where the exponent of a cascade is a value
at the tail of the context and can hold it. The pieces are bounded by
RectSum.tsum-rect for `T` and by RectApply.valSc-ssh for `X`, the latter being
a cascade read off one action of the context and applied to another, and they
are combined by `joinSc`, `sucSc` and `bumpSc`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.BrouwerOrdinals.RectOrbitAct
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import DialogueTreesHeight.BrouwerOrdinals.Order fe
 using (_≤_ ; _⊕_ ; ≤-Z ; ≤-S ; ≤-refl ; ≤-trans)
open import DialogueTreesHeight.BrouwerOrdinals.Multiplication fe
 using (_⊗_ ; ω ; ⊕-assoc ; ⊕-mono-left ; ⊗-assoc)
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ω^_ ; ω^-mono ; S-increasing ; S-<-ε₀ ; ⊕-<-ε₀ ;
        ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right ; ⊕-increasing-right ;
        one-≤-ω^ ; ≤-ω^ ; x-≤-x⊗ ; y-≤-⊗)
open import DialogueTreesHeight.BrouwerOrdinals.MultClosure fe
 using (ω^⊗)
open import DialogueTreesHeight.BrouwerOrdinals.MultAffine fe
 using (ω-pos)
open import DialogueTreesHeight.BrouwerOrdinals.Move fe
open import DialogueTreesHeight.BrouwerOrdinals.MoveTuple fe
 using (Tup ; tsum ; _⊑_ ; All< ; tsum-mono ; tsum-<-ε₀)
open import DialogueTreesHeight.BrouwerOrdinals.Cascade fe
 using (Sc ; valSc ; ScAll< ; valSc-mono ; valSc-<-ε₀ ; joinSc ;
        joinSc-All< ; valSc-join ; sucSc ; sucSc-All< ; valSc-suc ;
        bumpSc ; bumpSc-All< ; valSc-bump)
open import DialogueTreesHeight.BrouwerOrdinals.CascadeLevel fe
 using (tupToSc ; tupToSc-All< ; valSc-⊑)
open import DialogueTreesHeight.BrouwerOrdinals.Rect fe
open import DialogueTreesHeight.BrouwerOrdinals.RectSum fe
 using (sumRD ; sumRD-All< ; tsum-rect)
open import DialogueTreesHeight.BrouwerOrdinals.RectApply fe
 using (ssh ; ssh-All< ; valSc-ssh)
open import DialogueTreesHeight.BrouwerOrdinals.RectAlgebra fe
 using (_⊴_ ; ⊴-trans ; ⊴-All< ; pre-⊴ ; zeroRD ; zeroRD-All< ; rect-⊴)
open import DialogueTreesHeight.BrouwerOrdinals.Absorb fe

\end{code}

The datum. At each order the translation is one, so that the base of the value
is positive, and the exponent carries the sum of the orders below together
with the exponent that the iteration asks for, raised twice by `ω` and twice
by a successor.

\begin{code}

orbEI : (n p : ℕ) → RD n p → Sc n
orbEI n p D =
 joinSc n (sumRD n p D)
   (sucSc n (bumpSc n (bumpSc n
      (sucSc n (ssh n p (zeroRD n (succ p)) D)))))

rorbitD : (n p : ℕ) → RD n p
rorbitD n        zero     = ⋆
rorbitD zero     (succ p) = zeroRD zero (succ p)
rorbitD (succ n) (succ p) = (S Z , orbEI n p (rorbitD n p)) , rorbitD n p

orbEI-All< : (n p : ℕ) (D : RD n p) → RDAll< n p D → ScAll< n (orbEI n p D)
orbEI-All< n p D h =
 joinSc-All< n (sumRD n p D)
   (sucSc n (bumpSc n (bumpSc n
      (sucSc n (ssh n p (zeroRD n (succ p)) D)))))
   (sumRD-All< n p D h)
   (sucSc-All< n _
     (bumpSc-All< n _
       (bumpSc-All< n _
         (sucSc-All< n _
           (ssh-All< n p (zeroRD n (succ p)) D
              (zeroRD-All< n (succ p)) h)))))

rorbitD-All< : (n p : ℕ) → RDAll< n p (rorbitD n p)
rorbitD-All< n        zero     = ⋆
rorbitD-All< zero     (succ p) = zeroRD-All< zero (succ p)
rorbitD-All< (succ n) (succ p) =
 (S-<-ε₀ Z Z<ε₀ , orbEI-All< n p (rorbitD n p) (rorbitD-All< n p)) ,
 rorbitD-All< n p
 where
  open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
   using (Z<ε₀)

\end{code}

The tail of an iterate is the iterate of the tail, which is the grading read
as a computation rather than as a condition. The induction below uses it to
bound the tail of every iterate before anything is said about the head.

\begin{code}

rtail-iter : (k : ℕ) (d : Tup (WD (succ k) (succ k))) (x : Tup (succ k))
             (n : ℕ)
           → pr₂ (iter (rect (succ k) (succ k)
                             (rdOf (succ k) (succ k) d)) x n)
             ＝ iter (rect k k (rdOf k k (pr₂ d))) (pr₂ x) n
rtail-iter k d x zero     = refl
rtail-iter k d x (succ n) =
 ap (rect k k (rdOf k k (pr₂ d))) (rtail-iter k d x n)

\end{code}

The theorem.

\begin{code}

rorbit-act : (n p : ℕ) (d : Tup (WD p p)) (x : Tup p) (u : Tup n)
           → All< n u → d ⊴ u → x ⊴ u
           → (j : ℕ)
           → iter (rect p p (rdOf p p d)) x j ⊑ rect n p (rorbitD n p) u
rorbit-act n        zero     d x       u        hu hd hx j = ⋆
rorbit-act zero     (succ k) d x       u        hu hd hx j = 𝟘-elim hx
rorbit-act (succ n) (succ k) d (a , t) (u₀ , u) hu hd hx   =
 λ j → ≤-trans (hbd j) fin , tl j
 where
  R : Tup (succ k) → Tup (succ k)
  R = rect (succ k) (succ k) (rdOf (succ k) (succ k) d)

  R′ : Tup k → Tup k
  R′ = rect k k (rdOf k k (pr₂ d))

  E : Sc (succ k)
  E = tupToSc (succ k) (pre (succ (succ k)) (succ k) d)

  dA : All< (WD (succ k) (succ k)) d
  dA = ⊴-All< (WD (succ k) (succ k)) (succ n) d (u₀ , u) hd hu

  Ep : ScAll< (succ k) E
  Ep = tupToSc-All< (succ k) (pre (succ (succ k)) (succ k) d)
         (pre-All< (succ (succ k)) (succ k) d dA)

  Dt : Tup k
  Dt = rect n k (rorbitD n k) u

  DtA : All< k Dt
  DtA = rect-All< n k (rorbitD n k) u (rorbitD-All< n k) (pr₂ hu)

  tbd : (j : ℕ) → iter R′ t j ⊑ Dt
  tbd = rorbit-act n k (pr₂ d) t u (pr₂ hu) (pr₂ hd) (pr₂ hx)

  tl : (j : ℕ) → pr₂ (iter R (a , t) j) ⊑ Dt
  tl j = transport (_⊑ Dt) ((rtail-iter k d (a , t) j) ⁻¹) (tbd j)

  T : 𝓑
  T = tsum k Dt

  T< : T < ε₀
  T< = tsum-<-ε₀ k Dt DtA

  X : 𝓑
  X = valSc k (pr₂ E) Dt

  X< : X < ε₀
  X< = valSc-<-ε₀ k (pr₂ E) Dt (pr₂ Ep) DtA

  mv : Move
  mv = padMove (T ⊕ pr₁ E) (S X)
                (⊕-<-ε₀ T (pr₁ E) T< (pr₁ Ep)) (≤-S ≤-Z) (S-<-ε₀ X X<)

  hdf : ℕ → 𝓑
  hdf j = pr₁ (iter R (a , t) j)

  padle : (y : 𝓑) → y ≤ (S y ⊗ ω)
  padle y = ≤-trans (S-increasing y) (x-≤-x⊗ (S y) ω ω-pos)

  step : (j : ℕ) → hdf (succ j) ≤ img mv (hdf j)
  step j =
   ≤-trans (⊗-mono-left base
              (ω^ (valSc k (pr₂ E) (pr₂ (iter R (a , t) j)))))
           (⊗-mono-right (hdf j ⊕ (T ⊕ pr₁ E))
             (ω^-mono (≤-trans (valSc-mono k (pr₂ E) _ Dt (tl j))
                               (padle X))))
   where
    base : ((hdf j ⊕ tsum k (pr₂ (iter R (a , t) j))) ⊕ pr₁ E)
         ≤ (hdf j ⊕ (T ⊕ pr₁ E))
    base = transport (((hdf j ⊕ tsum k (pr₂ (iter R (a , t) j))) ⊕ pr₁ E) ≤_)
                     (⊕-assoc (hdf j) T (pr₁ E))
                     (⊕-mono-left
                       (⊕-mono-right (hdf j)
                         (tsum-mono k _ Dt (tl j))) (pr₁ E))

  hbd : (j : ℕ) → hdf j ≤ img (orbit mv) a
  hbd = move-orbit-rec mv hdf a (≤-refl a) step

\end{code}

The head of the bound on the iterates is below the head of the action.

\begin{code}

  VT : 𝓑
  VT = valSc n (sumRD n k (rorbitD n k)) u

  T≤ : T ≤ VT
  T≤ = tsum-rect n k (rorbitD n k) u

  Dd : RD n (succ k)
  Dd = zeroRD n (succ k)

  dpre⊑ : pre (succ k) k (pr₂ d) ⊑ rect n (succ k) Dd u
  dpre⊑ = rect-⊴ n (succ k) u (pre (succ k) k (pr₂ d))
            (⊴-trans (succ k) (mx (succ k) k) n (pre (succ k) k (pr₂ d))
               (pr₂ d) u (pre-⊴ (succ k) k (pr₂ d)) (pr₂ hd))

  Ex : Sc n
  Ex = ssh n k Dd (rorbitD n k)

  VX : 𝓑
  VX = valSc n Ex u

  X≤ : X ≤ VX
  X≤ = ≤-trans (valSc-⊑ k (pr₂ E) (tupToSc k (rect n (succ k) Dd u))
                  (tupToSc-mono k (pre (succ k) k (pr₂ d))
                     (rect n (succ k) Dd u) dpre⊑)
                  Dt)
               (valSc-ssh n k Dd (rorbitD n k) u)

  A′ : 𝓑
  A′ = (u₀ ⊕ tsum n u) ⊕ S Z

  one-A′ : S Z ≤ A′
  one-A′ = ≤-S ≤-Z

  M : 𝓑
  M = A′ ⊗ ω^ VT

  A′≤M : A′ ≤ M
  A′≤M = x-≤-x⊗ A′ (ω^ VT) (one-≤-ω^ VT)

  a≤M : a ≤ M
  a≤M = ≤-trans (pr₁ hx)
         (≤-trans (≤-trans (⊕-increasing-right u₀ (tsum n u))
                           (S-increasing (u₀ ⊕ tsum n u)))
                  A′≤M)

  T≤M : T ≤ M
  T≤M = ≤-trans T≤ (≤-trans (≤-ω^ VT) (y-≤-⊗ A′ (ω^ VT) one-A′))

  E₀≤M : pr₁ E ≤ M
  E₀≤M = ≤-trans (pr₁ hd)
          (≤-trans (≤-trans (⊕-increasing-right u₀ (tsum n u))
                            (S-increasing (u₀ ⊕ tsum n u)))
                   A′≤M)

  A⋖ : (a ⊕ (T ⊕ pr₁ E)) ⋖ M
  A⋖ = ⋖-⊕ M a (T ⊕ pr₁ E) (⋖-base M a a≤M)
         (⋖-⊕ M T (pr₁ E) (⋖-base M T T≤M) (⋖-base M (pr₁ E) E₀≤M))

  BB : 𝓑
  BB = ((S X) ⊗ ω) ⊗ ω

  Eb : Sc n
  Eb = sucSc n (bumpSc n (bumpSc n (sucSc n Ex)))

  SBB≤ : S BB ≤ valSc n Eb u
  SBB≤ =
   ≤-trans (≤-S (≤-trans (⊗-mono-left (⊗-mono-left (≤-S X≤) ω) ω) v3))
           (valSc-suc n (bumpSc n (bumpSc n (sucSc n Ex))) u)
   where
    v1 : (S VX) ≤ valSc n (sucSc n Ex) u
    v1 = valSc-suc n Ex u

    v2 : ((S VX) ⊗ ω) ≤ valSc n (bumpSc n (sucSc n Ex)) u
    v2 = ≤-trans (⊗-mono-left v1 ω) (valSc-bump n (sucSc n Ex) u)

    v3 : (((S VX) ⊗ ω) ⊗ ω)
       ≤ valSc n (bumpSc n (bumpSc n (sucSc n Ex))) u
    v3 = ≤-trans (⊗-mono-left v2 ω)
                 (valSc-bump n (bumpSc n (sucSc n Ex)) u)

  expbd : (VT ⊕ S BB) ≤ valSc n (orbEI n k (rorbitD n k)) u
  expbd = ≤-trans (⊕-mono-right VT SBB≤)
                  (valSc-join n (sumRD n k (rorbitD n k)) Eb u)

  eqM : (M ⊗ ω^ (S BB)) ＝ (A′ ⊗ ω^ (VT ⊕ S BB))
  eqM = ⊗-assoc A′ (ω^ VT) (ω^ (S BB)) ∙ ap (A′ ⊗_) (ω^⊗ VT (S BB))

  fin : img (orbit mv) a
      ≤ valSc (succ n) (S Z , orbEI n k (rorbitD n k)) (u₀ , u)
  fin = ≤-trans (⋖-⊗ M (a ⊕ (T ⊕ pr₁ E)) BB A⋖)
         (transport (_≤ (A′ ⊗ ω^ (valSc n (orbEI n k (rorbitD n k)) u)))
                    (eqM ⁻¹)
                    (⊗-mono-right A′ (ω^-mono expbd)))

\end{code}
