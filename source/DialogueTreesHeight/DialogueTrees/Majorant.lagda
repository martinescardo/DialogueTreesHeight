The height majorant for the combinators, and the logical relation it is proved
against.

We use a height-indexed logical relation in the style of MFPS-XXIX.main-lemma,
with `height(·) ≤ ·` in place of the correctness statement `decode`:

* `Maj ι = 𝓑`, a Brouwer code bounding the height, and
  `Maj (σ⇒τ) = Maj σ → Maj τ`;
* `R ι x a` is `height x ≤ a`, and `R (σ⇒τ) F φ` is
  `(x : B-Set⟦ σ ⟧) (a : Maj σ) → R σ x a → R τ (F x) (φ a)`.

Every combinator but the recursor is given its majorant here, together with
the proof that the two are related. The recursor at an arbitrary type, and the
fundamental theorem over the whole of System T, are in the module MajorantAll.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.DialogueTrees.Majorant
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators
 using (Ķ ; Ş)
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import EffectfulForcing.MFPSAndVariations.MFPS-XXIX
 using (B-Set⟦_⟧ ; zero' ; succ')
open import DialogueTreesHeight.DialogueTrees.Constructive fe

\end{code}

The hereditary majorant and the majorization relation.

\begin{code}

Maj : type → 𝓤₀ ̇
Maj ι       = 𝓑
Maj (σ ⇒ τ) = Maj σ → Maj τ

R : (σ : type) → B-Set⟦ σ ⟧ → Maj σ → 𝓤₀ ̇
R ι       x a = height x ≤ a
R (σ ⇒ τ) F φ = (x : B-Set⟦ σ ⟧) (a : Maj σ) → R σ x a → R τ (F x) (φ a)

\end{code}

The majorants of the combinators. The constant `Zero` has majorant `0`, the
successor has the identity, since relabelling preserves the height, the oracle
has the successor, and `K` and `S` have the projection and the substitution.

\begin{code}

μ-Zero : 𝓑
μ-Zero = Z

μ-Succ : 𝓑 → 𝓑
μ-Succ a = a

μ-Ω : 𝓑 → 𝓑
μ-Ω a = S a

μ-K : {σ τ : type} → Maj σ → Maj τ → Maj σ
μ-K a b = a

μ-S : {ρ σ τ : type} → Maj (ρ ⇒ σ ⇒ τ) → Maj (ρ ⇒ σ) → Maj ρ → Maj τ
μ-S φ γ a = φ a (γ a)

\end{code}

Each of these combinators is majorized by its majorant.

\begin{code}

R-Zero : R ι zero' μ-Zero
R-Zero = ≤-Z

R-Succ : R (ι ⇒ ι) succ' μ-Succ
R-Succ d b hd = transport (_≤ b) ((height-B-functor-succ d) ⁻¹) hd

R-Ω : R (ι ⇒ ι) generic μ-Ω
R-Ω d b hd = ≤-trans (height-generic d) (≤-S hd)

R-K : {σ τ : type} → R (σ ⇒ τ ⇒ σ) Ķ μ-K
R-K x a rx y b ry = rx

R-S : {ρ σ τ : type} → R ((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ) Ş μ-S
R-S φ φ′ rφ γ γ′ rγ x a rx = rφ x a rx (γ x) (γ′ a) (rγ x a rx)

\end{code}

