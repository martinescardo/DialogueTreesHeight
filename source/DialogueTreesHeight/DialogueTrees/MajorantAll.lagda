The height majorant at every type level, and the reduction of the conjecture
to ordinal arithmetic.

The module Majorant gives every combinator but the recursor its majorant,
which settles the fragment whose recursor is confined to ground type. The
obstruction to the full language was the majorant of the recursor at higher
types: at ground type it is the supremum of the iterates of a family of
Brouwer codes, and at a type `σ ⇒ τ` there was no majorant at all. The project
notes record the gap as a higher-order recursor majorant, and an unsoundness
in a pointwise supremum would have appeared there.

We close the gap. The dialogue interpretation of the recursor,

    iter' f x = Kleisli-extension (iter f x),

puts the tree argument under the function arguments, by
`Kleisli-extension g d s = Kleisli-extension (λ k → g k s) d`, and the
majorant does the same. We equip `Maj` with a hereditary pointwise supremum
`Maj-sup` and a hereditary right translation `Maj-⊕`, and prove the hereditary
Kleisli bound `R-Kleisli` by induction on the type, whose ground case is the
grafting lemma `height-kleisli-extension` and whose arrow case is
definitional. The majorant of the recursor at every type is then the supremum
of the iterates under `Maj-sup`, and the fundamental theorem extends to the
whole of `TΩ`, the recursor at every type included:

    height B⟦ t ⟧ ≤ μᵀ t          for every closed  t : TΩ ι ,

and in particular, for a closed `t : (ι⇒ι)⇒ι`,

    height (dialogue-tree t) ≤ μᵀ (embedding t · Ω).

The conjecture `height (dialogue-tree t) < ε₀` follows from the purely ordinal
statement

    μᵀ (embedding t · Ω) < ε₀ ,

which concerns Brouwer codes alone, `μᵀ t` being a hereditary functional over
Brouwer codes built from `⊕`, suprema and suprema of iterates. The corollary
`dialogue-height-<-ε₀` below records the implication with the ordinal
statement as an explicit hypothesis.

Three remarks on what is and is not established.

* The inequality `h ≤ μ` at all types was observed on paper in Part I of
  `dialogue-tree-height-epsilon0-ordinal-analysis.md`. The construction
  `Maj-sup`, `Maj-⊕`, `R-Kleisli` and `R-Iterᵀ` is new, and the notes had
  recorded it as unbuilt and possibly unsound. It is sound, the arrow case of
  `R-Kleisli` being definitional.

* Part IV of the same analysis argued that the reduction is useless,
  exhibiting a witness term whose majorant was claimed to reach `ε₀`, which
  would make `μᵀ t < ε₀` false in general. The claim rests on a slip in
  ordinal arithmetic, and a module MajorantWitness of the wider development
  from which this one was extracted checks that the majorant of the witness
  is at most `tower 2 = ω^(ω^ω)`, well below `ε₀`. As far as is known the
  ordinal statement above is open rather than refuted, and it implies the
  conjecture.

* The bound `μᵀ t < ε₀` for closed `t` is the subject of the module Predicate
  and of the modules SClause, IterClause and Fundamental that build on it,
  which prove it by a hereditary predicate graded by the order of a type.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.DialogueTrees.MajorantAll
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.CombinatoryT
open import EffectfulForcing.MFPSAndVariations.MFPS-XXIX
 using (B-Set⟦_⟧ ; B⟦_⟧ ; iter' ; Kleisli-extension ; dialogue-tree)
open import DialogueTreesHeight.DialogueTrees.Constructive fe
open import DialogueTreesHeight.DialogueTrees.Majorant fe
 using (Maj ; R ; μ-Zero ; μ-Succ ; μ-Ω ; μ-K ; μ-S ; R-Zero ; R-Succ ;
        R-Ω ; R-K ; R-S)
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
 using (⊕-mono-right ; ε₀ ; _<_)

\end{code}

The hereditary pointwise supremum and the hereditary right translation on
majorants. At ground type they are `L` and `⊕`, and at an arrow they act under
the argument.

\begin{code}

Maj-sup : {σ : type} → (ℕ → Maj σ) → Maj σ
Maj-sup {ι}     h = L h
Maj-sup {σ ⇒ τ} h = λ a → Maj-sup {τ} (λ k → h k a)

Maj-⊕ : {σ : type} → Maj σ → 𝓑 → Maj σ
Maj-⊕ {ι}     a ν = a ⊕ ν
Maj-⊕ {σ ⇒ τ} φ ν = λ a → Maj-⊕ {τ} (φ a) ν

μ-Kleisli : {σ : type} → (ℕ → Maj σ) → 𝓑 → Maj σ
μ-Kleisli h ν = Maj-⊕ (Maj-sup h) ν

\end{code}

The hereditary Kleisli bound. If each grafted object `g k` is majorized by
`h k`, and the tree `n` has height at most `ν`, then the Kleisli extension is
majorized by the pointwise supremum of the `h k`, translated by `ν`. The
ground case is the grafting lemma together with the upper-bound property of
the supremum, and the arrow case is definitional on both sides, because
`Kleisli-extension`, `Maj-sup` and `Maj-⊕` all pass under the argument in the
same way.

\begin{code}

R-Kleisli : {σ : type} (g : ℕ → B-Set⟦ σ ⟧) (h : ℕ → Maj σ)
          → ((k : ℕ) → R σ (g k) (h k))
          → (n : B ℕ) (ν : 𝓑)
          → height n ≤ ν
          → R σ (Kleisli-extension g n) (μ-Kleisli h ν)
R-Kleisli {ι} g h rg n ν rn =
 ≤-trans
  (height-kleisli-extension g (L h)
    (λ k → ≤-trans (rg k) (≤-L-upper-bound h k))
    n)
  (⊕-mono-right (L h) rn)
R-Kleisli {σ ⇒ τ} g h rg n ν rn x a rx =
 R-Kleisli {τ} (λ k → g k x) (λ k → h k a) (λ k → rg k x a rx) n ν rn

\end{code}

The majorant of the recursor at an arbitrary type: the supremum of the
iterates under `Maj-sup`, translated by the height of the count.

\begin{code}

μ-Iterᵀ : {σ : type} → Maj ((σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ)
μ-Iterᵀ φ a ν = μ-Kleisli (iter φ a) ν

R-Iterᵀ : {σ : type} → R ((σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ) iter' μ-Iterᵀ
R-Iterᵀ {σ} f φ rf x a rx n ν rn =
 R-Kleisli (iter f x) (iter φ a) orbit n ν rn
 where
  orbit : (k : ℕ) → R σ (iter f x k) (iter φ a k)
  orbit zero     = rx
  orbit (succ k) = rf (iter f x k) (iter φ a k) (orbit k)

\end{code}

The majorant of a term of the full language `TΩ`, and the fundamental theorem
by induction on the term. Every case except the recursor is the corresponding
lemma of the module Majorant.

\begin{code}

μᵀ : {σ : type} → TΩ σ → Maj σ
μᵀ Ω       = μ-Ω
μᵀ Zero    = μ-Zero
μᵀ Succ    = μ-Succ
μᵀ Iter    = μ-Iterᵀ
μᵀ K       = μ-K
μᵀ S       = μ-S
μᵀ (t · u) = μᵀ t (μᵀ u)

fundamentalᵀ : {σ : type} (t : TΩ σ) → R σ B⟦ t ⟧ (μᵀ t)
fundamentalᵀ Ω       = R-Ω
fundamentalᵀ Zero    = R-Zero
fundamentalᵀ Succ    = R-Succ
fundamentalᵀ Iter    = R-Iterᵀ
fundamentalᵀ K       = R-K
fundamentalᵀ S       = R-S
fundamentalᵀ (t · u) = fundamentalᵀ t B⟦ u ⟧ (μᵀ u) (fundamentalᵀ u)

\end{code}

Consequences. Every closed ground term of the full language has its dialogue
height bounded by its majorant, and in particular the dialogue tree of a
closed `t : (ι⇒ι)⇒ι` of System T is bounded by the majorant of
`embedding t · Ω`. The conjecture is thereby reduced to the ordinal statement
`μᵀ (embedding t · Ω) < ε₀`, which is the hypothesis of the final corollary.

\begin{code}

dialogue-tree-height-≤-μᵀ : (t : T ((ι ⇒ ι) ⇒ ι))
                          → height (dialogue-tree t) ≤ μᵀ (embedding t · Ω)
dialogue-tree-height-≤-μᵀ t = fundamentalᵀ (embedding t · Ω)

dialogue-height-<-ε₀ : (t : T ((ι ⇒ ι) ⇒ ι))
                     → μᵀ (embedding t · Ω) < ε₀   -- the open ordinal statement
                     → height (dialogue-tree t) < ε₀
dialogue-height-<-ε₀ t hμ = ≤-trans (≤-S (dialogue-tree-height-≤-μᵀ t)) hμ

\end{code}
