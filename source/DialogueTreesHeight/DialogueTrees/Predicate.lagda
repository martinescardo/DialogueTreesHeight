The hereditary predicate over the types of System T.

The module MajorantAll reduces the conjecture to the ordinal statement
`μᵀ t < ε₀` for closed `t : TΩ ι`, where `μᵀ` is built from six constants and
application. We define here, by recursion on the type, the predicate with
which that statement is proved, using the graded maps of the module Rect.

A datum for a type is a tuple graded by order, of width one more than the
order of the type, where

    ord ι = 0 ,   ord (σ ⇒ τ) = mx (succ (ord σ)) (ord τ) .

The two definitions agree: the width of a datum for `σ ⇒ τ` is the width that
Rect.WD asks of a map from width `wd σ` to width `wd τ`, so the clause for an
arrow reads the datum as such a map and applies it, the two widths agreeing
exactly. At ground type the datum is a single ordinal and the predicate says
that the majorant is below it.

We prove here the part that is common to all the constants: the predicate is
monotone in the datum, it is closed under the pointwise supremum that the
majorant of the recursor takes, and at ground type it gives a bound below
`ε₀`. Then come the three constants whose clauses follow from those properties
alone.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.DialogueTrees.Predicate
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT
open import DialogueTreesHeight.BrouwerOrdinals.Order fe
 using (_≤_ ; ≤-Z ; ≤-S ; ≤-L ; ≤-trans)
open import DialogueTreesHeight.BrouwerOrdinals.Multiplication fe
 using (⊕-mono-left)
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ω^_ ; one-≤-ω^ ; ⊕-mono-right ; x-≤-x⊗)
open import DialogueTreesHeight.BrouwerOrdinals.MoveTuple fe
 using (Tup ; tsum ; _⊑_ ; ⊑-trans ; All< ; tsum-mono ; tsum-<-ε₀)
open import DialogueTreesHeight.BrouwerOrdinals.Rect fe
open import DialogueTreesHeight.BrouwerOrdinals.RectAdd fe
 using (addν ; rect-addν)
open import DialogueTreesHeight.DialogueTrees.Majorant fe
 using (Maj ; μ-Zero ; μ-Succ ; μ-Ω ; μ-K)
open import DialogueTreesHeight.DialogueTrees.MajorantAll fe
 using (Maj-sup ; Maj-⊕)

\end{code}

The order of a type, and the width of its data.

\begin{code}

ord : type → ℕ
ord ι       = 0
ord (σ ⇒ τ) = mx (succ (ord σ)) (ord τ)

wd : type → ℕ
wd σ = succ (ord σ)

\end{code}

The predicate. At an arrow the datum is read as a graded map from the data of
the argument to the data of the result, and applied.

\begin{code}

Dom : (σ : type) → Maj σ → Tup (wd σ) → 𝓤₀ ̇
Dom ι       a d = a ≤ tsum 1 d
Dom (σ ⇒ τ) F d = (x : Maj σ) (e : Tup (wd σ)) → All< (wd σ) e → Dom σ x e
                → Dom τ (F x)
                        (rect (wd σ) (wd τ) (rdOf (wd σ) (wd τ) d) e)

\end{code}

The predicate is monotone in the datum, at every type. At an arrow this is
monotonicity of the reading followed by monotonicity of the action in its
datum.

\begin{code}

Dom-mono : (σ : type) (x : Maj σ) (d d′ : Tup (wd σ))
         → Dom σ x d → d ⊑ d′ → Dom σ x d′
Dom-mono ι       a d d′ h p = ≤-trans h (tsum-mono 1 d d′ p)
Dom-mono (σ ⇒ τ) F d d′ h p x e ae he =
 Dom-mono τ (F x) _ _ (h x e ae he)
   (rect-⊑RD (wd σ) (wd τ) (rdOf (wd σ) (wd τ) d) (rdOf (wd σ) (wd τ) d′)
             (rdOf-mono (wd σ) (wd τ) d d′ p) e)

\end{code}

It is closed under the pointwise supremum, which the majorant of the recursor
takes over all iteration counts. At ground type this is the upper-bound
property of `L`, and at an arrow the supremum passes under the argument on
both sides.

\begin{code}

Dom-sup : (σ : type) (h : ℕ → Maj σ) (d : Tup (wd σ))
        → ((n : ℕ) → Dom σ (h n) d) → Dom σ (Maj-sup h) d
Dom-sup ι       h d hs = ≤-L hs
Dom-sup (σ ⇒ τ) h d hs x e ae he =
 Dom-sup τ (λ n → h n x) _ (λ n → hs n x e ae he)

\end{code}

It is closed under the right translation that the majorant of the recursor
applies after the supremum. The code is added at order zero and a successor is
taken at every order above, which is what RectAdd.addν does. A translation
alone would not do, since absorbing a code into a translation under a limit
multiplier is the fold `b ⊗ m ⊕ d ≤ (b ⊕ d) ⊗ m`, which is false.

\begin{code}

Dom-⊕ : (σ : type) (x : Maj σ) (ν dν : 𝓑) (d : Tup (wd σ))
      → Dom σ x d → ν ≤ dν → Dom σ (Maj-⊕ x ν) (addν (wd σ) d dν)
Dom-⊕ ι       a ν dν (z , ⋆) h hν =
 ≤-trans (⊕-mono-left h ν) (⊕-mono-right z hν)
Dom-⊕ (σ ⇒ τ) F ν dν d       h hν x e ae he =
 Dom-mono τ (Maj-⊕ (F x) ν) _ _
   (Dom-⊕ τ (F x) ν dν _ (h x e ae he) hν)
   (rect-addν (wd σ) (wd τ) d e dν)

\end{code}

At ground type the predicate gives what the conjecture asks for.

\begin{code}

Dom-<-ε₀ : (a : 𝓑) (d : Tup 1) → Dom ι a d → All< 1 d → a < ε₀
Dom-<-ε₀ a d h p = ≤-trans (≤-S h) (tsum-<-ε₀ 1 d p)

\end{code}

The three constants whose clauses follow from the properties of the predicate
alone: zero, the successor on heights, which is the identity, and the generic
oracle, which adds one query and therefore asks for a datum whose slot of
order zero is positive.

\begin{code}

Zero-clause : (d : Tup 1) → Dom ι μ-Zero d
Zero-clause d = ≤-Z

Succ-clause : (d : Tup 2) → Dom (ι ⇒ ι) μ-Succ d
Succ-clause d x e ae hx =
 ≤-trans hx (tsum-mono 1 e _ (rect-increasing 1 (rdOf 1 1 d) e))

Ω-clause : (s : 𝓑) → Dom (ι ⇒ ι) μ-Ω (S Z , (s , ⋆))
Ω-clause s x (a , ⋆) ae hx =
 ≤-trans (≤-S hx) (x-≤-x⊗ (S a) (ω^ s) (one-≤-ω^ s))

\end{code}

Application is the clause for an arrow, read in the forward direction.

\begin{code}

app-clause : (σ τ : type) (F : Maj (σ ⇒ τ)) (x : Maj σ)
             (d : Tup (wd (σ ⇒ τ))) (e : Tup (wd σ))
           → Dom (σ ⇒ τ) F d → All< (wd σ) e → Dom σ x e
           → Dom τ (F x) (rect (wd σ) (wd τ) (rdOf (wd σ) (wd τ) d) e)
app-clause σ τ F x d e hF ae hx = hF x e ae hx

\end{code}

The clause for `K`, whose majorant is `μ-K a b = a`, so that the datum of the
first argument has to survive two applications, the second of which discards
its own argument. The two halves meet at the width `WD r p` of a datum for a
map from the width of the discarded argument to the width of the kept one. The
lemma `rect-arg-≥` says that the output of the first application still
dominates the datum of `x`, as far as `topq` reaches, and `rect-rdOf-≥` says
that the output of the second application still dominates the datum it was
read from. Composing the two under `Dom-mono` is the whole proof, and any
datum for `K` itself will do.

\begin{code}

K-clause : (σ τ : type) (d : Tup (wd (σ ⇒ (τ ⇒ σ))))
         → Dom (σ ⇒ (τ ⇒ σ)) (μ-K {σ} {τ}) d
K-clause σ τ d x e ae he y f af hf =
 Dom-mono σ x e _ he
  (⊑-trans (wd σ) e (topq (wd τ) (wd σ) g) _
     (rect-arg-≥ (wd τ) (wd σ) (rdOf (wd σ) (wd (τ ⇒ σ)) d) e)
     (rect-rdOf-≥ (wd τ) (wd σ) g f))
 where
  g : Tup (wd (τ ⇒ σ))
  g = rect (wd σ) (wd (τ ⇒ σ)) (rdOf (wd σ) (wd (τ ⇒ σ)) d) e

\end{code}
