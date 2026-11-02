Martin Escardo, 2nd November 2026.

This is an Agda companion for the paper

   The dialogue trees of system T have height below ε₀,
   and this bound is sharp
   ----------------------------------------------------

   https://martinescardo.github.io/DialogueTreesHeight/dialogue-tree-height.pdf

   Martín Hötzel Escardó
   https://www.cs.bham.ac.uk/~mhe/

   This file is
   https://github.com/martinescardo/DialogueTreesHeight/blob/master/source/DialogueTreesHeight/Article.lagda

This file follows the definitions, lemmas, propositions, theorems,
corollaries, examples, remarks and the question of the paper above, in
the same order and with the same numbering, so that a reader of the
paper can walk this file alongside it. The name of each entry is the
number the item has in the paper, and the comment above it is the
LaTeX label of that item. Where an item has several parts, the entries
carry the number of the part, and where a part has several claims, or
a definition several components, the entries carry a suffix naming
each. Where the paper states an equation that holds by definition, the
entry proves it by refl, so that the reader can see that the paper's
equations are the ones the development computes with.

Claims that the paper makes in running prose, outside proofs, appear
here too, under names beginning with Prose. Each of them is named in
the LaTeX source by \claim{name}, placed where the claim is made, and
the names are written out in order to the file
dialogue-tree-height.claims when the paper is typeset, so that the two
lists can be compared. The remarks and the question of the paper
assert nothing that the development proves, and are recorded as
comments.

Function extensionality is the only assumption, taken as the module
parameter fe as in every other module of the development. The one
exception is a prose claim about the ordinals of the univalent
library, which needs univalence to be stated, and takes it as a local
parameter.

Cite as

@misc{Escardo2026DialogueTreesHeight,
  author       = {H{\"o}tzel Escard{\'o}, Mart{\'\i}n},
  title        = {The dialogue trees of system {T} have height below
                  $\varepsilon_0$, and this bound is sharp},
  year         = {2026},
  month        = nov,
  howpublished = {\url{https://martinescardo.github.io/DialogueTreesHeight/dialogue-tree-height.pdf}},
  note         = {Agda formalization, and full information, available
                  at \url{https://github.com/martinescardo/DialogueTreesHeight}},
}

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DialogueTreesHeight.Article (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Univalence
open import UF.UA-FunExt
open import UF.ClassicalLogic using (typal-WEM)
open import Ordinals.Type using (Ordinal)
import Ordinals.Arithmetic
import Ordinals.OrdinalOfOrdinals
import Ordinals.AdditionProperties
import Ordinals.ChurchEncoding

open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter ; Ķ ; Ş)
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.CombinatoryT
open import EffectfulForcing.MFPSAndVariations.MFPS-XXIX
     using (B-Set⟦_⟧ ; B⟦_⟧ ; Kleisli-extension ; iter' ; dialogue-tree)

-- The module Constructive re-exports the module Order, so Order is not
-- opened here.
open import DialogueTreesHeight.BrouwerOrdinals.Multiplication fe
open import DialogueTreesHeight.BrouwerOrdinals.Epsilon0 fe
open import DialogueTreesHeight.BrouwerOrdinals.MultClosure fe
open import DialogueTreesHeight.BrouwerOrdinals.MultAffine fe
open import DialogueTreesHeight.BrouwerOrdinals.Absorb fe
open import DialogueTreesHeight.BrouwerOrdinals.Move fe
open import DialogueTreesHeight.BrouwerOrdinals.MoveTuple fe
open import DialogueTreesHeight.BrouwerOrdinals.Cascade fe
open import DialogueTreesHeight.BrouwerOrdinals.CascadeLevel fe
open import DialogueTreesHeight.BrouwerOrdinals.Rect fe
open import DialogueTreesHeight.BrouwerOrdinals.RectAdd fe
open import DialogueTreesHeight.BrouwerOrdinals.RectAlgebra fe
open import DialogueTreesHeight.BrouwerOrdinals.RectSum fe
open import DialogueTreesHeight.BrouwerOrdinals.RectApply fe
open import DialogueTreesHeight.BrouwerOrdinals.RectCurry fe
open import DialogueTreesHeight.BrouwerOrdinals.RectOrbitAct fe
open import DialogueTreesHeight.DialogueTrees.Constructive fe
open import DialogueTreesHeight.DialogueTrees.Majorant fe
open import DialogueTreesHeight.DialogueTrees.MajorantAll fe
open import DialogueTreesHeight.DialogueTrees.Predicate fe
open import DialogueTreesHeight.DialogueTrees.SClause fe
     using (dS ; dS-All< ; S-clause)
open import DialogueTreesHeight.DialogueTrees.IterClause fe
     using (dI ; dI-All< ; Iter-clause)
open import DialogueTreesHeight.DialogueTrees.Fundamental fe
open import DialogueTreesHeight.DialogueTrees.Examples fe
open import DialogueTreesHeight.DialogueTrees.Sharpness fe
open import DialogueTreesHeight.DialogueTrees.Main fe

\end{code}

Section 2. Dialogue trees and their heights

Labels: Section 2 = sec:dialogue.

\begin{code}

-- def:dialogue-tree-type
Definition-2-1 : 𝓤 ̇ → 𝓤 ̇
Definition-2-1 = B

Definition-2-1-η : {X : 𝓤 ̇ } → X → B X
Definition-2-1-η = η

Definition-2-1-β : {X : 𝓤 ̇ } → (ℕ → B X) → ℕ → B X
Definition-2-1-β = β

Definition-2-1-dialogue : {X : 𝓤 ̇ } → B X → (ℕ → ℕ) → X
Definition-2-1-dialogue = dialogue

Definition-2-1-dialogue-η : {X : 𝓤 ̇ } (x : X) (α : ℕ → ℕ)
                          → dialogue (η x) α ＝ x
Definition-2-1-dialogue-η x α = refl

Definition-2-1-dialogue-β : {X : 𝓤 ̇ } (φ : ℕ → B X) (i : ℕ) (α : ℕ → ℕ)
                          → dialogue (β φ i) α ＝ dialogue (φ (α i)) α
Definition-2-1-dialogue-β φ i α = refl

-- def:kleisli-generic
Definition-2-2 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → B Y) → B X → B Y
Definition-2-2 = kleisli-extension

Definition-2-2-leaf : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (g : X → B Y) (x : X)
                    → kleisli-extension g (η x) ＝ g x
Definition-2-2-leaf g x = refl

Definition-2-2-node : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (g : X → B Y) (φ : ℕ → B X) (i : ℕ)
                    → kleisli-extension g (β φ i)
                    ＝ β (kleisli-extension g ∘ φ) i
Definition-2-2-node g φ i = refl

Definition-2-2-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → B X → B Y
Definition-2-2-functor = B-functor

Definition-2-2-generic : B ℕ → B ℕ
Definition-2-2-generic = generic

Definition-2-2-generic-is-an-extension : generic ＝ kleisli-extension (β η)
Definition-2-2-generic-is-an-extension = refl

Definition-2-2-generic-leaf : (i : ℕ) → generic (η i) ＝ β η i
Definition-2-2-generic-leaf i = refl

Definition-2-2-generic-node : (φ : ℕ → B ℕ) (i : ℕ)
                            → generic (β φ i) ＝ β (generic ∘ φ) i
Definition-2-2-generic-node φ i = refl

Definition-2-2-generic-dialogue : (d : B ℕ) (α : ℕ → ℕ)
                                → dialogue (generic d) α ＝ α (dialogue d α)
Definition-2-2-generic-dialogue d α = (generic-diagram α d)⁻¹

-- claim iteration
Prose-iteration : {X : 𝓤 ̇ } → (X → X) → X → ℕ → X
Prose-iteration = iter

Prose-iteration-zero : {X : 𝓤 ̇ } (f : X → X) (x : X) → iter f x 0 ＝ x
Prose-iteration-zero f x = refl

Prose-iteration-succ : {X : 𝓤 ̇ } (f : X → X) (x : X) (n : ℕ)
                     → iter f x (succ n) ＝ f (iter f x n)
Prose-iteration-succ f x n = refl

-- def:dialogue-interpretation
Definition-2-3 : type → 𝓤₀ ̇
Definition-2-3 = T

Definition-2-3-TΩ : type → 𝓤₀ ̇
Definition-2-3-TΩ = TΩ

Definition-2-3-embedding : {σ : type} → T σ → TΩ σ
Definition-2-3-embedding = embedding

Definition-2-3-types : type → 𝓤₀ ̇
Definition-2-3-types = B-Set⟦_⟧

Definition-2-3-types-ι : B-Set⟦ ι ⟧ ＝ B ℕ
Definition-2-3-types-ι = refl

Definition-2-3-types-⇒ : (σ τ : type)
                       → B-Set⟦ σ ⇒ τ ⟧ ＝ (B-Set⟦ σ ⟧ → B-Set⟦ τ ⟧)
Definition-2-3-types-⇒ σ τ = refl

Definition-2-3-terms : {σ : type} → TΩ σ → B-Set⟦ σ ⟧
Definition-2-3-terms = B⟦_⟧

Definition-2-3-Ω : B⟦ Ω ⟧ ＝ generic
Definition-2-3-Ω = refl

Definition-2-3-Zero : B⟦ Zero ⟧ ＝ η 0
Definition-2-3-Zero = refl

Definition-2-3-Succ : B⟦ Succ ⟧ ＝ B-functor succ
Definition-2-3-Succ = refl

Definition-2-3-K : {σ τ : type} → B⟦ K {σ} {τ} ⟧ ＝ Ķ
Definition-2-3-K = refl

Definition-2-3-S : {ρ σ τ : type} → B⟦ S {ρ} {σ} {τ} ⟧ ＝ Ş
Definition-2-3-S = refl

Definition-2-3-recursor : {σ : type} (f : B-Set⟦ σ ⟧ → B-Set⟦ σ ⟧)
                          (x : B-Set⟦ σ ⟧)
                        → B⟦ Iter ⟧ f x ＝ Kleisli-extension (iter f x)
Definition-2-3-recursor f x = refl

Definition-2-3-tree : T ((ι ⇒ ι) ⇒ ι) → B ℕ
Definition-2-3-tree = dialogue-tree

Definition-2-3-tree-unfolds : (t : T ((ι ⇒ ι) ⇒ ι))
                            → dialogue-tree t ＝ B⟦ embedding t · Ω ⟧
Definition-2-3-tree-unfolds t = refl

-- claim kleisli-extension-at-higher-types
Prose-kleisli-extension-at-higher-types
 : {X : 𝓤₀ ̇ } {σ : type} → (X → B-Set⟦ σ ⟧) → B X → B-Set⟦ σ ⟧
Prose-kleisli-extension-at-higher-types = Kleisli-extension

Prose-kleisli-extension-at-higher-types-ground
 : {X : 𝓤₀ ̇ } (g : X → B ℕ) (d : B X)
 → Kleisli-extension {X} {ι} g d ＝ kleisli-extension g d
Prose-kleisli-extension-at-higher-types-ground g d = refl

Prose-kleisli-extension-at-higher-types-arrow
 : {X : 𝓤₀ ̇ } {σ τ : type} (g : X → B-Set⟦ σ ⇒ τ ⟧) (d : B X) (s : B-Set⟦ σ ⟧)
 → Kleisli-extension g d s ＝ Kleisli-extension (λ k → g k s) d
Prose-kleisli-extension-at-higher-types-arrow g d s = refl

\end{code}

Section 3. Brouwer codes and their arithmetic

The paper opens the section by saying that a classical treatment,
through the ordinals of the univalent library, would need excluded
middle at the grafting and generic lemmas, because the successor on
those ordinals is not monotone without it. What the library proves is
that monotonicity of the successor gives weak excluded middle. The
module that proves it takes univalence as a parameter, which the
development does not assume, so the claim is stated here under a local
univalence hypothesis.

Labels: Section 3 = sec:codes.

\begin{code}

module _ (ua : Univalence) where

 open Ordinals.Arithmetic (Univalence-gives-FunExt ua) using (_+ₒ_ ; 𝟙ₒ)
 open Ordinals.OrdinalOfOrdinals ua using () renaming (_⊴_ to _⊴ₒ_)
 open Ordinals.AdditionProperties ua using (succ-not-necessarily-monotone)

 -- claim successor-not-monotone
 Prose-successor-not-monotone
  : ((α γ : Ordinal 𝓤) → α ⊴ₒ γ → (α +ₒ 𝟙ₒ) ⊴ₒ (γ +ₒ 𝟙ₒ)) → typal-WEM 𝓤
 Prose-successor-not-monotone = succ-not-necessarily-monotone

-- def:codes
Definition-3-1 : 𝓤₀ ̇
Definition-3-1 = 𝓑

Definition-3-1-Z : 𝓑
Definition-3-1-Z = Z

Definition-3-1-S : 𝓑 → 𝓑
Definition-3-1-S a = S a

Definition-3-1-L : (ℕ → 𝓑) → 𝓑
Definition-3-1-L = L

Definition-3-1-order : 𝓑 → 𝓑 → 𝓤₀ ̇
Definition-3-1-order = _≤_

Definition-3-1-least : {b : 𝓑} → Z ≤ b
Definition-3-1-least = ≤-Z

Definition-3-1-successor : {a b : 𝓑} → a ≤ b → S a ≤ S b
Definition-3-1-successor = ≤-S

Definition-3-1-cocone : {a : 𝓑} {f : ℕ → 𝓑} (n : ℕ) → a ≤ f n → a ≤ L f
Definition-3-1-cocone = ≤-ℓ

Definition-3-1-limit : {f : ℕ → 𝓑} {b : 𝓑} → ((n : ℕ) → f n ≤ b) → L f ≤ b
Definition-3-1-limit = ≤-L

Definition-3-1-strict : 𝓑 → 𝓑 → 𝓤₀ ̇
Definition-3-1-strict = _<_

Definition-3-1-strict-unfolds : (a b : 𝓑) → (a < b) ＝ (S a ≤ b)
Definition-3-1-strict-unfolds a b = refl

-- lem:order (1), item:refl
Lemma-3-2-1 : (a : 𝓑) → a ≤ a
Lemma-3-2-1 = ≤-refl

-- lem:order (2), item:trans
Lemma-3-2-2 : {a b c : 𝓑} → a ≤ b → b ≤ c → a ≤ c
Lemma-3-2-2 = ≤-trans

-- lem:order (3), item:S-incr
Lemma-3-2-3 : (a : 𝓑) → a ≤ S a
Lemma-3-2-3 = S-increasing

-- lem:order (4), item:L-mono
Lemma-3-2-4 : (f : ℕ → 𝓑) (n : ℕ) → f n ≤ L f
Lemma-3-2-4 = ≤-L-upper-bound

Lemma-3-2-4' : {f g : ℕ → 𝓑} → ((n : ℕ) → f n ≤ g n) → L f ≤ L g
Lemma-3-2-4' = ≤-L-mono

\end{code}

Remark 3.3 observes that a lower bound a ≤ L f holds as soon as a is
below a single member of the family, while an upper bound L f ≤ b asks
for every member, which is what shapes the lower bounds of Section 7.
It asserts nothing beyond the rules of Definition 3.1.

Labels: Remark 3.3 = rem:one-branch, Section 7 = sec:sharp,
Definition 3.1 = def:codes.

\begin{code}

-- lem:irrefl
Lemma-3-4 : (a : 𝓑) → ¬ (S a ≤ a)
Lemma-3-4 = S-irrefl

-- def:arithmetic
Definition-3-5-⊕ : 𝓑 → 𝓑 → 𝓑
Definition-3-5-⊕ = _⊕_

Definition-3-5-⊕-Z : (a : 𝓑) → (a ⊕ Z) ＝ a
Definition-3-5-⊕-Z a = refl

Definition-3-5-⊕-S : (a b : 𝓑) → (a ⊕ S b) ＝ S (a ⊕ b)
Definition-3-5-⊕-S a b = refl

Definition-3-5-⊕-L : (a : 𝓑) (f : ℕ → 𝓑) → (a ⊕ L f) ＝ L (λ n → a ⊕ f n)
Definition-3-5-⊕-L a f = refl

Definition-3-5-⊗ : 𝓑 → 𝓑 → 𝓑
Definition-3-5-⊗ = _⊗_

Definition-3-5-⊗-Z : (a : 𝓑) → (a ⊗ Z) ＝ Z
Definition-3-5-⊗-Z a = refl

Definition-3-5-⊗-S : (a b : 𝓑) → (a ⊗ S b) ＝ ((a ⊗ b) ⊕ a)
Definition-3-5-⊗-S a b = refl

Definition-3-5-⊗-L : (a : 𝓑) (f : ℕ → 𝓑) → (a ⊗ L f) ＝ L (λ n → a ⊗ f n)
Definition-3-5-⊗-L a f = refl

Definition-3-5-ω^ : 𝓑 → 𝓑
Definition-3-5-ω^ = ω^_

Definition-3-5-ω^-Z : ω^ Z ＝ S Z
Definition-3-5-ω^-Z = refl

Definition-3-5-ω^-S : (a : 𝓑) → ω^ (S a) ＝ ((ω^ a) ⊗ ω)
Definition-3-5-ω^-S a = refl

Definition-3-5-ω^-L : (f : ℕ → 𝓑) → ω^ (L f) ＝ L (λ n → ω^ (f n))
Definition-3-5-ω^-L f = refl

Definition-3-5-numeral : ℕ → 𝓑
Definition-3-5-numeral = ι[_]

Definition-3-5-numeral-zero : ι[ 0 ] ＝ Z
Definition-3-5-numeral-zero = refl

Definition-3-5-numeral-succ : (n : ℕ) → ι[ succ n ] ＝ S ι[ n ]
Definition-3-5-numeral-succ n = refl

Definition-3-5-ω : 𝓑
Definition-3-5-ω = ω

Definition-3-5-ω-unfolds : ω ＝ L (λ n → ι[ n ])
Definition-3-5-ω-unfolds = refl

Definition-3-5-tower : ℕ → 𝓑
Definition-3-5-tower = tower

Definition-3-5-tower-base : tower 0 ＝ ω
Definition-3-5-tower-base = refl

Definition-3-5-tower-step : (n : ℕ) → tower (succ n) ＝ ω^ (tower n)
Definition-3-5-tower-step n = refl

Definition-3-5-ε₀ : 𝓑
Definition-3-5-ε₀ = ε₀

Definition-3-5-ε₀-unfolds : ε₀ ＝ L (λ n → tower n)
Definition-3-5-ε₀-unfolds = refl

-- lem:add (1), item:Z-unit
Lemma-3-6-1 : (a : 𝓑) → (Z ⊕ a) ＝ a
Lemma-3-6-1 = Z-left-unit

-- lem:add (2), item:add-incr
Lemma-3-6-2 : (a b : 𝓑) → a ≤ (a ⊕ b)
Lemma-3-6-2 = ⊕-increasing-right

Lemma-3-6-2' : (a b : 𝓑) → b ≤ (a ⊕ b)
Lemma-3-6-2' = ⊕-increasing-left

-- lem:add (3), item:add-mono
Lemma-3-6-3 : {a a′ : 𝓑} → a ≤ a′ → (c : 𝓑) → (a ⊕ c) ≤ (a′ ⊕ c)
Lemma-3-6-3 = ⊕-mono-left

Lemma-3-6-3' : (a : 𝓑) {b c : 𝓑} → b ≤ c → (a ⊕ b) ≤ (a ⊕ c)
Lemma-3-6-3' = ⊕-mono-right

-- lem:add (4), item:add-assoc
Lemma-3-6-4 : (a b c : 𝓑) → ((a ⊕ b) ⊕ c) ＝ (a ⊕ (b ⊕ c))
Lemma-3-6-4 = ⊕-assoc

-- lem:mult (1), item:one-unit
Lemma-3-7-1 : (y : 𝓑) → (ι[ 1 ] ⊗ y) ＝ y
Lemma-3-7-1 = SZ-⊗

Lemma-3-7-1' : (x : 𝓑) → (x ⊗ ι[ 1 ]) ＝ x
Lemma-3-7-1' = Z-left-unit

-- lem:mult (2), item:mult-mono
Lemma-3-7-2 : {a a′ : 𝓑} → a ≤ a′ → (c : 𝓑) → (a ⊗ c) ≤ (a′ ⊗ c)
Lemma-3-7-2 = ⊗-mono-left

Lemma-3-7-2' : (a : 𝓑) {b c : 𝓑} → b ≤ c → (a ⊗ b) ≤ (a ⊗ c)
Lemma-3-7-2' = ⊗-mono-right

-- lem:mult (3), item:distrib
Lemma-3-7-3 : (c x y : 𝓑) → (c ⊗ (x ⊕ y)) ＝ ((c ⊗ x) ⊕ (c ⊗ y))
Lemma-3-7-3 = ⊗-left-distrib

-- lem:mult (4), item:mult-assoc
Lemma-3-7-4 : (a b c : 𝓑) → ((a ⊗ b) ⊗ c) ＝ (a ⊗ (b ⊗ c))
Lemma-3-7-4 = ⊗-assoc

-- lem:exp (1), item:exp-pos
Lemma-3-8-1 : (b : 𝓑) → ι[ 1 ] ≤ ω^ b
Lemma-3-8-1 = one-≤-ω^

-- lem:exp (2), item:exp-mono
Lemma-3-8-2 : {a b : 𝓑} → a ≤ b → ω^ a ≤ ω^ b
Lemma-3-8-2 = ω^-mono

-- lem:exp (3), item:exp-double
Lemma-3-8-3 : (b : 𝓑) → (ω^ b ⊕ ω^ b) ≤ (ω^ b ⊗ ω)
Lemma-3-8-3 = ω^-double

Lemma-3-8-3' : (b : 𝓑) → S (ω^ b) ≤ ω^ (S b)
Lemma-3-8-3' = S-ω^-step

-- lem:exp (4), item:exp-incr
Lemma-3-8-4 : (a : 𝓑) → a ≤ ω^ a
Lemma-3-8-4 = ≤-ω^

-- lem:exp (5), item:exp-hom
Lemma-3-8-5 : ω^ ι[ 1 ] ＝ ω
Lemma-3-8-5 = ω^-ι1

Lemma-3-8-5' : (a b : 𝓑) → (ω^ a ⊗ ω^ b) ＝ ω^ (a ⊕ b)
Lemma-3-8-5' = ω^⊗

-- lem:tower
Lemma-3-9 : (n : ℕ) → tower n < tower (succ n)
Lemma-3-9 = tower-strict

Lemma-3-9' : (n : ℕ) → tower n < ε₀
Lemma-3-9' = tower-<-ε₀

-- lem:tower-absorb
Lemma-3-10 : (m n : ℕ) → m ≤ℕ n → tower m ≤ tower n
Lemma-3-10 = tower-mono-ℕ

Lemma-3-10-step : (n : ℕ) → tower n ≤ tower (succ n)
Lemma-3-10-step = tower-mono-step

Lemma-3-10-sum : (n : ℕ) → (tower n ⊕ tower n) ≤ tower (succ n)
Lemma-3-10-sum = tower-double

Lemma-3-10-product : (n : ℕ) → (tower n ⊗ tower n) ≤ tower (succ n)
Lemma-3-10-product = tower-sq

-- prop:closure
Proposition-3-11-successor : (a : 𝓑) → a < ε₀ → S a < ε₀
Proposition-3-11-successor = S-<-ε₀

Proposition-3-11-exponential : (a : 𝓑) → a < ε₀ → ω^ a < ε₀
Proposition-3-11-exponential = ω^-<-ε₀

Proposition-3-11-sum : (a b : 𝓑) → a < ε₀ → b < ε₀ → (a ⊕ b) < ε₀
Proposition-3-11-sum = ⊕-<-ε₀

Proposition-3-11-product : (a b : 𝓑) → a < ε₀ → b < ε₀ → (a ⊗ b) < ε₀
Proposition-3-11-product = ⊗-<-ε₀

-- lem:absorb (1), item:exp-law
Lemma-3-12-1 : (a b : 𝓑) → (ω^ a ⊗ ω^ b) ＝ ω^ (a ⊕ b)
Lemma-3-12-1 = ω^⊗

Lemma-3-12-1' : (a : 𝓑) → ι[ 1 ] ≤ ω^ a
Lemma-3-12-1' = one-≤-ω^

-- lem:absorb (2), item:mult-incr
Lemma-3-12-2 : (x y : 𝓑) → ι[ 1 ] ≤ y → x ≤ (x ⊗ y)
Lemma-3-12-2 = x-≤-x⊗

Lemma-3-12-2' : (x y : 𝓑) → ι[ 1 ] ≤ y → x ≤ (y ⊗ x)
Lemma-3-12-2' x y = y-≤-⊗ y x

-- lem:absorb (3), item:double
Lemma-3-12-3 : (x : 𝓑) → (x ⊕ x) ≤ (x ⊗ ω)
Lemma-3-12-3 = dup-ω

Lemma-3-12-3' : (x : 𝓑) → (ι[ 1 ] ⊕ x) ≤ S x
Lemma-3-12-3' = S⊕≤S

-- lem:absorb (4), item:multiple
Lemma-3-12-4 : 𝓑 → 𝓑 → 𝓤₀ ̇
Lemma-3-12-4 = _⋖_

Lemma-3-12-4-unfolds : (x M : 𝓑) → (x ⋖ M) ＝ (Σ n ꞉ ℕ , x ≤ (M ⊗ ι[ n ]))
Lemma-3-12-4-unfolds x M = refl

Lemma-3-12-4-below : (M x : 𝓑) → x ≤ M → x ⋖ M
Lemma-3-12-4-below = ⋖-base

Lemma-3-12-4-sum : (M x y : 𝓑) → x ⋖ M → y ⋖ M → (x ⊕ y) ⋖ M
Lemma-3-12-4-sum = ⋖-⊕

Lemma-3-12-4-numeral : (n : ℕ) (e : 𝓑) → (ι[ n ] ⊗ ω^ e) ≤ ω^ (S e)
Lemma-3-12-4-numeral = ι⊗ω^

Lemma-3-12-4-exponent : (M x e : 𝓑) → x ⋖ M → (x ⊗ ω^ e) ≤ (M ⊗ ω^ (S e))
Lemma-3-12-4-exponent = ⋖-⊗

Lemma-3-12-4-ω : (M x : 𝓑) → x ⋖ M → x ≤ (M ⊗ ω)
Lemma-3-12-4-ω = ⋖-⊗ω

Lemma-3-12-4-ω' : (M x : 𝓑) → x ⋖ M → (x ⊗ ω) ≤ (M ⊗ ω)
Lemma-3-12-4-ω' = ⋖-ω

-- lem:absorb (5), item:iterate
Lemma-3-12-5 : (a c s : 𝓑) → ι[ 1 ] ≤ s → (k : ℕ)
             → iter (λ b → (b ⊕ c) ⊗ ω^ (s ⊗ ω)) a k
             ≤ ((a ⊕ c) ⊗ ω^ ((s ⊗ ω) ⊗ ω))
Lemma-3-12-5 a c s s+ k =
 ≤-trans (orbit-inv (ω^ (s ⊗ ω)) (one-≤-ω^ (s ⊗ ω)) (dbl-ω^ s s+) a c k)
         (⊗-mono-right (a ⊕ c)
           (≤-trans (pw-ω^ (s ⊗ ω) k)
                    (ω^-mono (⊗-mono-right (s ⊗ ω) (ι[ k ]≤ω)))))

-- def:height
Definition-3-13 : B ℕ → 𝓑
Definition-3-13 = height

Definition-3-13-leaf : (n : ℕ) → height (η n) ＝ Z
Definition-3-13-leaf n = refl

Definition-3-13-node : (φ : ℕ → B ℕ) (i : ℕ)
                     → height (β φ i) ＝ L (λ n → S (height (φ n)))
Definition-3-13-node φ i = refl

-- lem:height-three (1), item:relabel
Lemma-3-14-1 : (f : ℕ → ℕ) (d : B ℕ) → height (B-functor f d) ＝ height d
Lemma-3-14-1 = height-relabel

-- lem:height-three (2), item:graft
Lemma-3-14-2 : (g : ℕ → B ℕ) (b : 𝓑)
             → ((k : ℕ) → height (g k) ≤ b)
             → (d : B ℕ)
             → height (kleisli-extension g d) ≤ (b ⊕ height d)
Lemma-3-14-2 = height-kleisli-extension

-- lem:height-three (3), item:generic
Lemma-3-14-3 : (d : B ℕ) → height (generic d) ≤ S (height d)
Lemma-3-14-3 = height-generic

\end{code}

Section 4. Majorants and the reduction to ordinal arithmetic

Labels: Section 4 = sec:majorant.

\begin{code}

-- def:majorant
Definition-4-1 : type → 𝓤₀ ̇
Definition-4-1 = Maj

Definition-4-1-ι : Maj ι ＝ 𝓑
Definition-4-1-ι = refl

Definition-4-1-⇒ : (σ τ : type) → Maj (σ ⇒ τ) ＝ (Maj σ → Maj τ)
Definition-4-1-⇒ σ τ = refl

Definition-4-1-majorized : (σ : type) → B-Set⟦ σ ⟧ → Maj σ → 𝓤₀ ̇
Definition-4-1-majorized = R

Definition-4-1-majorized-ι : (x : B ℕ) (a : 𝓑) → R ι x a ＝ (height x ≤ a)
Definition-4-1-majorized-ι x a = refl

Definition-4-1-majorized-⇒ : (σ τ : type) (F : B-Set⟦ σ ⇒ τ ⟧) (φ : Maj (σ ⇒ τ))
                           → R (σ ⇒ τ) F φ
                           ＝ ((x : B-Set⟦ σ ⟧) (a : Maj σ)
                                → R σ x a → R τ (F x) (φ a))
Definition-4-1-majorized-⇒ σ τ F φ = refl

-- def:majorant-combinators
Definition-4-2-Zero : 𝓑
Definition-4-2-Zero = μ-Zero

Definition-4-2-Succ : 𝓑 → 𝓑
Definition-4-2-Succ = μ-Succ

Definition-4-2-Ω : 𝓑 → 𝓑
Definition-4-2-Ω = μ-Ω

Definition-4-2-K : {σ τ : type} → Maj σ → Maj τ → Maj σ
Definition-4-2-K = μ-K

Definition-4-2-S : {ρ σ τ : type}
                 → Maj (ρ ⇒ σ ⇒ τ) → Maj (ρ ⇒ σ) → Maj ρ → Maj τ
Definition-4-2-S = μ-S

Definition-4-2-Zero-majorized : R ι (η 0) μ-Zero
Definition-4-2-Zero-majorized = R-Zero

Definition-4-2-Succ-majorized : R (ι ⇒ ι) (B-functor succ) μ-Succ
Definition-4-2-Succ-majorized = R-Succ

Definition-4-2-Ω-majorized : R (ι ⇒ ι) generic μ-Ω
Definition-4-2-Ω-majorized = R-Ω

Definition-4-2-K-majorized : {σ τ : type} → R (σ ⇒ τ ⇒ σ) Ķ μ-K
Definition-4-2-K-majorized = R-K

Definition-4-2-S-majorized : {ρ σ τ : type}
                           → R ((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ) Ş μ-S
Definition-4-2-S-majorized = R-S

-- def:maj-sup
Definition-4-3 : {σ : type} → (ℕ → Maj σ) → Maj σ
Definition-4-3 = Maj-sup

Definition-4-3-ι : (h : ℕ → 𝓑) → Maj-sup {ι} h ＝ L h
Definition-4-3-ι h = refl

Definition-4-3-⇒ : {σ τ : type} (h : ℕ → Maj (σ ⇒ τ)) (a : Maj σ)
                 → Maj-sup h a ＝ Maj-sup (λ k → h k a)
Definition-4-3-⇒ h a = refl

Definition-4-3' : {σ : type} → Maj σ → 𝓑 → Maj σ
Definition-4-3' = Maj-⊕

Definition-4-3'-ι : (a ν : 𝓑) → Maj-⊕ {ι} a ν ＝ (a ⊕ ν)
Definition-4-3'-ι a ν = refl

Definition-4-3'-⇒ : {σ τ : type} (φ : Maj (σ ⇒ τ)) (ν : 𝓑) (a : Maj σ)
                  → Maj-⊕ φ ν a ＝ Maj-⊕ (φ a) ν
Definition-4-3'-⇒ φ ν a = refl

Definition-4-3'' : {σ : type} → (ℕ → Maj σ) → 𝓑 → Maj σ
Definition-4-3'' = μ-Kleisli

Definition-4-3''-unfolds : {σ : type} (h : ℕ → Maj σ) (ν : 𝓑)
                         → μ-Kleisli h ν ＝ Maj-⊕ (Maj-sup h) ν
Definition-4-3''-unfolds h ν = refl

-- lem:kleisli-bound
Lemma-4-4 : {σ : type} (g : ℕ → B-Set⟦ σ ⟧) (h : ℕ → Maj σ)
          → ((k : ℕ) → R σ (g k) (h k))
          → (d : B ℕ) (ν : 𝓑)
          → height d ≤ ν
          → R σ (Kleisli-extension g d) (Maj-⊕ (Maj-sup h) ν)
Lemma-4-4 = R-Kleisli

-- def:majorant-term
Definition-4-5 : {σ : type} → Maj ((σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ)
Definition-4-5 = μ-Iterᵀ

Definition-4-5-unfolds : {σ : type} (φ : Maj (σ ⇒ σ)) (a : Maj σ) (ν : 𝓑)
                       → μ-Iterᵀ φ a ν ＝ Maj-⊕ (Maj-sup (λ k → iter φ a k)) ν
Definition-4-5-unfolds φ a ν = refl

Definition-4-5-majorized : {σ : type} → R ((σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ) iter' μ-Iterᵀ
Definition-4-5-majorized = R-Iterᵀ

Definition-4-5' : {σ : type} → TΩ σ → Maj σ
Definition-4-5' = μᵀ

Definition-4-5'-application : {σ τ : type} (t : TΩ (σ ⇒ τ)) (u : TΩ σ)
                            → μᵀ (t · u) ＝ μᵀ t (μᵀ u)
Definition-4-5'-application t u = refl

-- thm:fundamental-majorant
Theorem-4-6 : {σ : type} (t : TΩ σ) → R σ B⟦ t ⟧ (μᵀ t)
Theorem-4-6 = fundamentalᵀ

Theorem-4-6' : (t : T ((ι ⇒ ι) ⇒ ι))
             → height (dialogue-tree t) ≤ μᵀ (embedding t · Ω)
Theorem-4-6' = dialogue-tree-height-≤-μᵀ

-- thm:reduction
Theorem-4-7 : (t : T ((ι ⇒ ι) ⇒ ι))
            → μᵀ (embedding t · Ω) < ε₀
            → height (dialogue-tree t) < ε₀
Theorem-4-7 = dialogue-height-<-ε₀

\end{code}

Section 5. Graded maps

Labels: Section 5 = sec:graded.

\begin{code}

-- claim data-and-their-grading
Prose-data-and-their-grading : ℕ → 𝓤₀ ̇
Prose-data-and-their-grading = Tup

Prose-data-and-their-grading-zero : Tup 0 ＝ 𝟙
Prose-data-and-their-grading-zero = refl

Prose-data-and-their-grading-succ : (n : ℕ) → Tup (succ n) ＝ (𝓑 × Tup n)
Prose-data-and-their-grading-succ n = refl

Prose-data-and-their-grading-sum : (n : ℕ) → Tup n → 𝓑
Prose-data-and-their-grading-sum = tsum

Prose-data-and-their-grading-order : {n : ℕ} → Tup n → Tup n → 𝓤₀ ̇
Prose-data-and-their-grading-order = _⊑_

Prose-data-and-their-grading-small : (n : ℕ) → Tup n → 𝓤₀ ̇
Prose-data-and-their-grading-small = All<

Prose-data-and-their-grading-sum-mono : (n : ℕ) (t u : Tup n) → t ⊑ u
                                      → tsum n t ≤ tsum n u
Prose-data-and-their-grading-sum-mono = tsum-mono

Prose-data-and-their-grading-sum-small : (n : ℕ) (t : Tup n) → All< n t
                                       → tsum n t < ε₀
Prose-data-and-their-grading-sum-small = tsum-<-ε₀

Prose-data-and-their-grading-inside : {k n : ℕ} → Tup k → Tup n → 𝓤₀ ̇
Prose-data-and-their-grading-inside = _⊴_

\end{code}

Remark 5.1 states the rule that an entry of the output is raised only
by entries of the input of its own order or higher, which the
constructions below obey and which keeps them below ε₀. It is a
reading of those constructions rather than a statement about them.

The paragraph opening Section 5.2 says that the maps needed at the
ground type are a ↦ (a ⊕ t) ⊗ ω^ s, and that the combinator S asks
for an exponent that varies with the argument. The maps with a fixed
exponent are the moves of the development, whose iterates are bounded
by a single move with the exponent multiplied by ω.

Labels: Remark 5.1 = rem:grading-rule, Section 5.2 = sec:cascades.

\begin{code}

-- claim scalar-maps
Prose-scalar-maps : 𝓤₀ ̇
Prose-scalar-maps = Move

Prose-scalar-maps-action : Move → 𝓑 → 𝓑
Prose-scalar-maps-action = img

Prose-scalar-maps-action-unfolds : (mv : Move) (a : 𝓑)
                                 → img mv a ＝ ((a ⊕ mt mv) ⊗ ω^ (ms mv))
Prose-scalar-maps-action-unfolds mv a = refl

Prose-scalar-maps-orbit : Move → Move
Prose-scalar-maps-orbit = orbit

Prose-scalar-maps-orbit-bounds : (mv : Move) (a : 𝓑) (k : ℕ)
                               → iter (img mv) a k ≤ img (orbit mv) a
Prose-scalar-maps-orbit-bounds = move-orbit

Prose-scalar-maps-from-codes : (t s : 𝓑) → t < ε₀ → ι[ 1 ] ≤ s → s < ε₀ → Move
Prose-scalar-maps-from-codes = padMove

-- def:cascade
Definition-5-2 : ℕ → 𝓤₀ ̇
Definition-5-2 = Sc

Definition-5-2-zero : Sc 0 ＝ 𝓑
Definition-5-2-zero = refl

Definition-5-2-succ : (k : ℕ) → Sc (succ k) ＝ (𝓑 × Sc k)
Definition-5-2-succ k = refl

Definition-5-2-action : (k : ℕ) → Sc k → Tup k → 𝓑
Definition-5-2-action = valSc

Definition-5-2-action-zero : (c : 𝓑) → valSc 0 c ⋆ ＝ c
Definition-5-2-action-zero c = refl

Definition-5-2-action-succ : (k : ℕ) (c : 𝓑) (E : Sc k) (a : 𝓑) (t : Tup k)
                           → valSc (succ k) (c , E) (a , t)
                           ＝ (((a ⊕ tsum k t) ⊕ c) ⊗ ω^ (valSc k E t))
Definition-5-2-action-succ k c E a t = refl

Definition-5-2-small : (k : ℕ) → Sc k → 𝓤₀ ̇
Definition-5-2-small = ScAll<

Definition-5-2-as-tuple : (j : ℕ) → Sc j → Tup (succ j)
Definition-5-2-as-tuple = scToTup

Definition-5-2-from-tuple : (j : ℕ) → Tup (succ j) → Sc j
Definition-5-2-from-tuple = tupToSc

\end{code}

Remark 5.3 explains why the recursion of Definition 5.2 ends at a free
constant rather than at a translation: a translation cannot absorb a
doubling, while a constant pays for one by a successor on the grade
above. The absorption it refers to is Lemma 5.6.

Labels: Remark 5.3 = rem:last-grade, Definition 5.2 = def:cascade,
Lemma 5.6 = lem:cascade-ops.

\begin{code}

-- lem:cascade-basic
Lemma-5-4 : (k : ℕ) (E : Sc k) (t : Tup k) → ScAll< k E → All< k t
          → valSc k E t < ε₀
Lemma-5-4 = valSc-<-ε₀

Lemma-5-4-mono : (k : ℕ) (E : Sc k) (t u : Tup k) → t ⊑ u
               → valSc k E t ≤ valSc k E u
Lemma-5-4-mono = valSc-mono

Lemma-5-4-mono' : (k : ℕ) (E E′ : Sc k) → E ⊑Sc E′ → (t : Tup k)
                → valSc k E t ≤ valSc k E′ t
Lemma-5-4-mono' = valSc-⊑

Lemma-5-4-increasing : (k : ℕ) (c : 𝓑) (E : Sc k) (a : 𝓑) (t : Tup k)
                     → a ≤ valSc (succ k) (c , E) (a , t)
Lemma-5-4-increasing = valSc-increasing

Lemma-5-4-increasing' : (k : ℕ) (c : 𝓑) (E : Sc k) (a : 𝓑) (t : Tup k)
                      → c ≤ valSc (succ k) (c , E) (a , t)
Lemma-5-4-increasing' = valSc-const

-- def:cascade-ops
Definition-5-5-successor : (k : ℕ) → Sc k → Sc k
Definition-5-5-successor = sucSc

Definition-5-5-join : (k : ℕ) → Sc k → Sc k → Sc k
Definition-5-5-join = joinSc

Definition-5-5-bump : (k : ℕ) → Sc k → Sc k
Definition-5-5-bump = bumpSc

Definition-5-5-widening : (k : ℕ) → Sc k → Sc (succ k)
Definition-5-5-widening = upSc

Definition-5-5-widening-unfolds : (k : ℕ) (E : Sc k) → upSc k E ＝ (ι[ 1 ] , E)
Definition-5-5-widening-unfolds k E = refl

Definition-5-5-zero : (k : ℕ) → Sc k
Definition-5-5-zero = zeroSc

-- lem:cascade-ops (1), item:suc
Lemma-5-6-1 : (k : ℕ) (E : Sc k) (t : Tup k)
            → S (valSc k E t) ≤ valSc k (sucSc k E) t
Lemma-5-6-1 = valSc-suc

-- lem:cascade-ops (2), item:join
Lemma-5-6-2 : (k : ℕ) (E₁ E₂ : Sc k) (t : Tup k)
            → (valSc k E₁ t ⊕ valSc k E₂ t) ≤ valSc k (joinSc k E₁ E₂) t
Lemma-5-6-2 = valSc-join

-- lem:cascade-ops (3), item:bump
Lemma-5-6-3 : (k : ℕ) (E : Sc k) (t : Tup k)
            → (valSc k E t ⊗ ω) ≤ valSc k (bumpSc k E) t
Lemma-5-6-3 = valSc-bump

-- lem:cascade-ops (4), item:up
Lemma-5-6-4 : (k : ℕ) (E : Sc k) (a : 𝓑) (t : Tup k)
            → valSc k E t ≤ valSc (succ k) (upSc k E) (a , t)
Lemma-5-6-4 = valSc-up

-- lem:cascade-ops (5), item:fold
Lemma-5-6-5 : (k : ℕ) (c : 𝓑) (E : Sc k) (t : Tup (succ k)) (v : 𝓑)
            → (valSc (succ k) (c , E) t ⊕ v)
            ≤ valSc (succ k) ((c ⊕ v) , sucSc k E) t
Lemma-5-6-5 = valSc-fold

-- lem:cascade-ops, smallness
Lemma-5-6-small-successor : (k : ℕ) (E : Sc k) → ScAll< k E
                          → ScAll< k (sucSc k E)
Lemma-5-6-small-successor = sucSc-All<

Lemma-5-6-small-join : (k : ℕ) (E₁ E₂ : Sc k) → ScAll< k E₁ → ScAll< k E₂
                     → ScAll< k (joinSc k E₁ E₂)
Lemma-5-6-small-join = joinSc-All<

Lemma-5-6-small-bump : (k : ℕ) (E : Sc k) → ScAll< k E → ScAll< k (bumpSc k E)
Lemma-5-6-small-bump = bumpSc-All<

Lemma-5-6-small-widening : (k : ℕ) (E : Sc k) → ScAll< k E
                         → ScAll< (succ k) (upSc k E)
Lemma-5-6-small-widening = upSc-All<

Lemma-5-6-small-zero : (k : ℕ) → ScAll< k (zeroSc k)
Lemma-5-6-small-zero = zeroSc-All<

-- def:rect
Definition-5-7 : ℕ → ℕ → 𝓤₀ ̇
Definition-5-7 = RD

Definition-5-7-to-zero : (p : ℕ) → RD p 0 ＝ 𝟙
Definition-5-7-to-zero p = refl

Definition-5-7-from-zero : (q : ℕ) → RD 0 (succ q) ＝ (𝓑 × RD 0 q)
Definition-5-7-from-zero q = refl

Definition-5-7-positive : (p q : ℕ)
                        → RD (succ p) (succ q) ＝ (Sc (succ p) × RD p q)
Definition-5-7-positive p q = refl

Definition-5-7-action : (p q : ℕ) → RD p q → Tup p → Tup q
Definition-5-7-action = rect

Definition-5-7-action-unfolds : (p q : ℕ) (E : Sc (succ p)) (D : RD p q)
                                (a : 𝓑) (t : Tup p)
                              → rect (succ p) (succ q) (E , D) (a , t)
                              ＝ (valSc (succ p) E (a , t) , rect p q D t)
Definition-5-7-action-unfolds p q E D a t = refl

Definition-5-7-small : (p q : ℕ) → RD p q → 𝓤₀ ̇
Definition-5-7-small = RDAll<

Definition-5-7-small-action : (p q : ℕ) (D : RD p q) (x : Tup p)
                            → RDAll< p q D → All< p x
                            → All< q (rect p q D x)
Definition-5-7-small-action = rect-All<

Definition-5-7-increasing : (p : ℕ) (D : RD p p) (x : Tup p) → x ⊑ rect p p D x
Definition-5-7-increasing = rect-increasing

Definition-5-7-order : {p q : ℕ} → RD p q → RD p q → 𝓤₀ ̇
Definition-5-7-order = _⊑RD_

Definition-5-7-order-action : (p q : ℕ) (D D′ : RD p q) → D ⊑RD D′ → (x : Tup p)
                            → rect p q D x ⊑ rect p q D′ x
Definition-5-7-order-action = rect-⊑RD

-- claim reading-a-tuple-as-a-map
Prose-reading-a-tuple-as-a-map-width : ℕ → ℕ → ℕ
Prose-reading-a-tuple-as-a-map-width = WD

Prose-reading-a-tuple-as-a-map-width-unfolds : (p q : ℕ)
                                             → WD p q ＝ mx (succ p) q
Prose-reading-a-tuple-as-a-map-width-unfolds p q = refl

Prose-reading-a-tuple-as-a-map : (p q : ℕ) → Tup (WD p q) → RD p q
Prose-reading-a-tuple-as-a-map = rdOf

Prose-reading-a-tuple-as-a-map-prefix : (a b : ℕ) → Tup (mx a b) → Tup a
Prose-reading-a-tuple-as-a-map-prefix = pre

Prose-reading-a-tuple-as-a-map-small : (p q : ℕ) (d : Tup (WD p q))
                                     → All< (WD p q) d
                                     → RDAll< p q (rdOf p q d)
Prose-reading-a-tuple-as-a-map-small = rdOf-All<

Prose-reading-a-tuple-as-a-map-mono : (p q : ℕ) (d d′ : Tup (WD p q)) → d ⊑ d′
                                    → rdOf p q d ⊑RD rdOf p q d′
Prose-reading-a-tuple-as-a-map-mono = rdOf-mono

-- def:rect-ops
Definition-5-8-zero : (p q : ℕ) → RD p q
Definition-5-8-zero = zeroRD

Definition-5-8-join : (p q : ℕ) → RD p q → RD p q → RD p q
Definition-5-8-join = joinRD

Definition-5-8-sum : (p q : ℕ) → RD p q → Sc p
Definition-5-8-sum = sumRD

Definition-5-8-cut : (p q q′ : ℕ) → RD p (mx q q′) → RD p q
Definition-5-8-cut = preRD

Definition-5-8-widening : (p q q′ : ℕ) → RD p q → RD p (mx q q′)
Definition-5-8-widening = padRD

Definition-5-8-flattening : (p q : ℕ) → RD p q → Tup (WD p q)
Definition-5-8-flattening = flatRD

Definition-5-8-translation : (p q : ℕ) → RD p q → RD p q
Definition-5-8-translation = addRDc

Definition-5-8-successor : (p q : ℕ) → RD p q → RD p q
Definition-5-8-successor = sucRD

Definition-5-8-datum-translation : (n : ℕ) → Tup n → 𝓑 → Tup n
Definition-5-8-datum-translation = addν

-- lem:rect-ops (1), item:rjoin
Lemma-5-9-1 : (p q : ℕ) (F G : RD p q) → F ⊑RD joinRD p q F G
Lemma-5-9-1 = joinRD-left

Lemma-5-9-1' : (p q : ℕ) (F G : RD p q) → G ⊑RD joinRD p q F G
Lemma-5-9-1' = joinRD-right

-- lem:rect-ops (2), item:rsum
Lemma-5-9-2 : (p q : ℕ) (F : RD p q) (x : Tup p)
            → tsum q (rect p q F x) ≤ valSc p (sumRD p q F) x
Lemma-5-9-2 = tsum-rect

-- lem:rect-ops (3), item:rcut
Lemma-5-9-3 : (p q q′ : ℕ) (F : RD p q) (x : Tup p)
            → pre q q′ (rect p (mx q q′) (padRD p q q′ F) x) ＝ rect p q F x
Lemma-5-9-3 = rect-padRD

Lemma-5-9-3' : (p q q′ : ℕ) (F : RD p (mx q q′)) (x : Tup p)
             → rect p q (preRD p q q′ F) x ＝ pre q q′ (rect p (mx q q′) F x)
Lemma-5-9-3' = rect-preRD

-- lem:rect-ops (4), item:rflat
Lemma-5-9-4 : (p q : ℕ) (F : RD p q) → F ⊑RD rdOf p q (flatRD p q F)
Lemma-5-9-4 = flatRD-⊒

-- lem:rect-ops (5), item:rtrans
Lemma-5-9-5 : (p q : ℕ) (F : RD p q) (x : Tup p) (v : 𝓑)
            → (v , ⋆) ⊴ x
            → addν q (rect p q F x) v ⊑ rect p q (addRDc p q F) x
Lemma-5-9-5 = rect-addνc

Lemma-5-9-5' : (p q : ℕ) (F : RD p q) (x : Tup p)
             → sucTup q (rect p q F x) ⊑ rect p q (sucRD p q F) x
Lemma-5-9-5' = rect-sucRD

-- lem:rect-ops (6), item:rread
Lemma-5-9-6 : (p q : ℕ) (d : Tup (WD p q)) (x : Tup p) (v : 𝓑)
            → addν q (rect p q (rdOf p q d) x) v
            ⊑ rect p q (rdOf p q (addν (WD p q) d v)) x
Lemma-5-9-6 = rect-addν

-- lem:rect-ops, smallness
Lemma-5-9-small-zero : (p q : ℕ) → RDAll< p q (zeroRD p q)
Lemma-5-9-small-zero = zeroRD-All<

Lemma-5-9-small-join : (p q : ℕ) (F G : RD p q) → RDAll< p q F → RDAll< p q G
                     → RDAll< p q (joinRD p q F G)
Lemma-5-9-small-join = joinRD-All<

Lemma-5-9-small-sum : (p q : ℕ) (F : RD p q) → RDAll< p q F
                    → ScAll< p (sumRD p q F)
Lemma-5-9-small-sum = sumRD-All<

Lemma-5-9-small-cut : (p q q′ : ℕ) (F : RD p (mx q q′)) → RDAll< p (mx q q′) F
                    → RDAll< p q (preRD p q q′ F)
Lemma-5-9-small-cut = preRD-All<

Lemma-5-9-small-widening : (p q q′ : ℕ) (F : RD p q) → RDAll< p q F
                         → RDAll< p (mx q q′) (padRD p q q′ F)
Lemma-5-9-small-widening = padRD-All<

Lemma-5-9-small-flattening : (p q : ℕ) (F : RD p q) → RDAll< p q F
                           → All< (WD p q) (flatRD p q F)
Lemma-5-9-small-flattening = flatRD-All<

Lemma-5-9-small-translation : (p q : ℕ) (F : RD p q) → RDAll< p q F
                            → RDAll< p q (addRDc p q F)
Lemma-5-9-small-translation = addRDc-All<

-- lem:calculus, the slotwise sum y ⊔ x
Lemma-5-10-slotwise-sum : (p n : ℕ) → Tup p → Tup n → Tup (mx p n)
Lemma-5-10-slotwise-sum = cmb

-- lem:calculus (1), item:apply
Lemma-5-10-1 : (m p q : ℕ) → RD m (WD p q) → RD m p → RD m q
Lemma-5-10-1 = sh

Lemma-5-10-1-bound : (m p q : ℕ) (F : RD m (WD p q)) (G : RD m p) (x : Tup m)
                   → rect p q (rdOf p q (rect m (WD p q) F x)) (rect m p G x)
                   ⊑ rect m q (sh m p q F G) x
Lemma-5-10-1-bound = rect-ssub

Lemma-5-10-1-small : (m p q : ℕ) (F : RD m (WD p q)) (G : RD m p)
                   → RDAll< m (WD p q) F → RDAll< m p G
                   → RDAll< m q (sh m p q F G)
Lemma-5-10-1-small = sh-All<

-- lem:calculus (2), item:curry
Lemma-5-10-2 : (p n q : ℕ) → RD (mx p n) q → RD n (WD p q)
Lemma-5-10-2 = curryD

Lemma-5-10-2-bound : (p n q : ℕ) (D : RD (mx p n) q) (y : Tup p) (x : Tup n)
                   → rect (mx p n) q D (cmb p n y x)
                   ⊑ rect p q (rdOf p q (rect n (WD p q) (curryD p n q D) x)) y
Lemma-5-10-2-bound = rect-curry

Lemma-5-10-2-small : (p n q : ℕ) (D : RD (mx p n) q) → RDAll< (mx p n) q D
                   → RDAll< n (WD p q) (curryD p n q D)
Lemma-5-10-2-small = curryD-All<

-- lem:calculus (3), item:var
Lemma-5-10-3 : (n k : ℕ) (u : Tup n) (t : Tup k) → t ⊴ u
             → t ⊑ rect n k (zeroRD n k) u
Lemma-5-10-3 = rect-⊴

-- lem:calculus (4), item:orbit
Lemma-5-10-4 : (n p : ℕ) → RD n p
Lemma-5-10-4 = rorbitD

Lemma-5-10-4-bound : (n p : ℕ) (e : Tup (WD p p)) (x : Tup p) (u : Tup n)
                   → All< n u → e ⊴ u → x ⊴ u
                   → (j : ℕ)
                   → iter (rect p p (rdOf p p e)) x j ⊑ rect n p (rorbitD n p) u
Lemma-5-10-4-bound = rorbit-act

Lemma-5-10-4-small : (n p : ℕ) → RDAll< n p (rorbitD n p)
Lemma-5-10-4-small = rorbitD-All<

\end{code}

Section 6. The bound on the majorant

Labels: Section 6 = sec:bound.

\begin{code}

-- def:dom
Definition-6-1-order : type → ℕ
Definition-6-1-order = ord

Definition-6-1-order-ι : ord ι ＝ 0
Definition-6-1-order-ι = refl

Definition-6-1-order-⇒ : (σ τ : type) → ord (σ ⇒ τ) ＝ mx (succ (ord σ)) (ord τ)
Definition-6-1-order-⇒ σ τ = refl

Definition-6-1-width : type → ℕ
Definition-6-1-width = wd

Definition-6-1-width-unfolds : (σ : type) → wd σ ＝ succ (ord σ)
Definition-6-1-width-unfolds σ = refl

Definition-6-1 : (σ : type) → Maj σ → Tup (wd σ) → 𝓤₀ ̇
Definition-6-1 = Dom

Definition-6-1-ι : (a : 𝓑) (d : Tup 1) → Dom ι a d ＝ (a ≤ tsum 1 d)
Definition-6-1-ι a d = refl

Definition-6-1-⇒ : (σ τ : type) (F : Maj (σ ⇒ τ)) (d : Tup (wd (σ ⇒ τ)))
                 → Dom (σ ⇒ τ) F d
                 ＝ ((x : Maj σ) (e : Tup (wd σ)) → All< (wd σ) e → Dom σ x e
                      → Dom τ (F x)
                             (rect (wd σ) (wd τ) (rdOf (wd σ) (wd τ) d) e))
Definition-6-1-⇒ σ τ F d = refl

-- lem:widths
Lemma-6-2 : (σ τ : type) → wd (σ ⇒ τ) ＝ WD (wd σ) (wd τ)
Lemma-6-2 σ τ = refl

-- lem:dom-closure (1), item:dom-mono
Lemma-6-3-1 : (σ : type) (x : Maj σ) (d d′ : Tup (wd σ))
            → Dom σ x d → d ⊑ d′ → Dom σ x d′
Lemma-6-3-1 = Dom-mono

-- lem:dom-closure (2), item:dom-sup
Lemma-6-3-2 : (σ : type) (h : ℕ → Maj σ) (d : Tup (wd σ))
            → ((n : ℕ) → Dom σ (h n) d) → Dom σ (Maj-sup h) d
Lemma-6-3-2 = Dom-sup

-- lem:dom-closure (3), item:dom-add
Lemma-6-3-3 : (σ : type) (x : Maj σ) (ν ν′ : 𝓑) (d : Tup (wd σ))
            → Dom σ x d → ν ≤ ν′ → Dom σ (Maj-⊕ x ν) (addν (wd σ) d ν′)
Lemma-6-3-3 = Dom-⊕

-- lem:dom-closure (4), item:dom-eps
Lemma-6-3-4 : (a : 𝓑) (d : Tup 1) → Dom ι a d → All< 1 d → a < ε₀
Lemma-6-3-4 = Dom-<-ε₀

-- lem:easy-clauses
Lemma-6-4-Zero : (d : Tup 1) → Dom ι μ-Zero d
Lemma-6-4-Zero = Zero-clause

Lemma-6-4-Succ : (d : Tup 2) → Dom (ι ⇒ ι) μ-Succ d
Lemma-6-4-Succ = Succ-clause

Lemma-6-4-Ω : (s : 𝓑) → Dom (ι ⇒ ι) μ-Ω (ι[ 1 ] , (s , ⋆))
Lemma-6-4-Ω = Ω-clause

Lemma-6-4-K : (σ τ : type) (d : Tup (wd (σ ⇒ τ ⇒ σ)))
            → Dom (σ ⇒ τ ⇒ σ) (μ-K {σ} {τ}) d
Lemma-6-4-K = K-clause

Lemma-6-4-application : (σ τ : type) (F : Maj (σ ⇒ τ)) (x : Maj σ)
                        (d : Tup (wd (σ ⇒ τ))) (e : Tup (wd σ))
                      → Dom (σ ⇒ τ) F d → All< (wd σ) e → Dom σ x e
                      → Dom τ (F x)
                             (rect (wd σ) (wd τ) (rdOf (wd σ) (wd τ) d) e)
Lemma-6-4-application = app-clause

-- lem:s-clause
Lemma-6-5 : (ρ σ τ : type) → Tup (wd ((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ))
Lemma-6-5 = dS

Lemma-6-5-small : (ρ σ τ : type)
                → All< (wd ((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ)) (dS ρ σ τ)
Lemma-6-5-small = dS-All<

Lemma-6-5-dominates : (ρ σ τ : type)
                    → Dom ((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ)
                          (μ-S {ρ} {σ} {τ})
                          (dS ρ σ τ)
Lemma-6-5-dominates = S-clause

-- lem:iter-clause
Lemma-6-6 : (σ : type) → Tup (wd ((σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ))
Lemma-6-6 = dI

Lemma-6-6-small : (σ : type) → All< (wd ((σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ)) (dI σ)
Lemma-6-6-small = dI-All<

Lemma-6-6-dominates : (σ : type)
                    → Dom ((σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ) (μ-Iterᵀ {σ}) (dI σ)
Lemma-6-6-dominates = Iter-clause

-- thm:fundamental
Theorem-6-7 : {σ : type} (t : TΩ σ)
            → Σ d ꞉ Tup (wd σ) , (All< (wd σ) d × Dom σ (μᵀ t) d)
Theorem-6-7 = fundamental

-- cor:mu-below
Corollary-6-8 : (t : TΩ ι) → μᵀ t < ε₀
Corollary-6-8 = μᵀ-<-ε₀

-- thm:main
Theorem-6-9 : (t : T ((ι ⇒ ι) ⇒ ι)) → height (dialogue-tree t) < ε₀
Theorem-6-9 = dialogue-tree-height-<-ε₀

Theorem-6-9' : (t : T ((ι ⇒ ι) ⇒ ι)) → S (height (dialogue-tree t)) ≤ ε₀
Theorem-6-9' = restated

\end{code}

Section 7. Sharpness

Labels: Section 7 = sec:sharp.

\begin{code}

-- ex:small
Examples-7-1-leaf : T ((ι ⇒ ι) ⇒ ι)
Examples-7-1-leaf = leaf-term

Examples-7-1-query : T ((ι ⇒ ι) ⇒ ι)
Examples-7-1-query = query-term

Examples-7-1-iterated : T ((ι ⇒ ι) ⇒ ι)
Examples-7-1-iterated = iterated-term

Examples-7-1-leaf-tree : dialogue-tree leaf-term ＝ η 0
Examples-7-1-leaf-tree = leaf-tree

Examples-7-1-query-tree : dialogue-tree query-term ＝ β η 0
Examples-7-1-query-tree = query-tree

Examples-7-1-iterated-tree : dialogue-tree iterated-term
                           ＝ β (λ j → iter generic (β η 0) j) 0
Examples-7-1-iterated-tree = iterated-tree

Examples-7-1-leaf-height : height (dialogue-tree leaf-term) ＝ Z
Examples-7-1-leaf-height = leaf-height

Examples-7-1-query-height : height (dialogue-tree query-term) ≤ ι[ 1 ]
Examples-7-1-query-height = query-height-≤

Examples-7-1-query-height' : ι[ 1 ] ≤ height (dialogue-tree query-term)
Examples-7-1-query-height' = query-height-≥

-- prop:omega-attained
Proposition-7-2 : ω ≤ height (dialogue-tree iterated-term)
Proposition-7-2 = iterated-height-≥

Proposition-7-2' : height (dialogue-tree iterated-term) ≤ ω
Proposition-7-2' = iterated-height-≤

-- prop:tree-of
Proposition-7-3 : 𝓑 → B ℕ
Proposition-7-3 = tree-of

Proposition-7-3-bound : (a : 𝓑) → a ≤ height (tree-of a)
Proposition-7-3-bound = code-≤-height

Proposition-7-3-approximant : (n : ℕ) → tower n ≤ height (tree-of (tower n))
Proposition-7-3-approximant = approximant

Proposition-7-3-ε₀ : ε₀ ≤ height (tree-of ε₀)
Proposition-7-3-ε₀ = epsilon₀

Proposition-7-3-no-term : (t : T ((ι ⇒ ι) ⇒ ι))
                        → ¬ (dialogue-tree t ＝ tree-of ε₀)
Proposition-7-3-no-term = no-term-of-height-ε₀

-- def:church
Definition-7-4 : type → type
Definition-7-4 = 𝓞

Definition-7-4-unfolds : (σ : type) → 𝓞 σ ＝ (σ ⇒ (σ ⇒ σ) ⇒ ((ι ⇒ σ) ⇒ σ) ⇒ σ)
Definition-7-4-unfolds σ = refl

Definition-7-4-zer : {σ : type} → T (𝓞 σ)
Definition-7-4-zer = zerᵀ

Definition-7-4-suc : {σ : type} → T (𝓞 σ ⇒ 𝓞 σ)
Definition-7-4-suc = sucᵀ

Definition-7-4-lim : {σ : type} → T ((ι ⇒ 𝓞 σ) ⇒ 𝓞 σ)
Definition-7-4-lim = limᵀ

Definition-7-4-add : {σ : type} → T (𝓞 σ ⇒ 𝓞 σ ⇒ 𝓞 σ)
Definition-7-4-add = addᵀ

Definition-7-4-mul : {σ : type} → T (𝓞 σ ⇒ 𝓞 (𝓞 σ) ⇒ 𝓞 σ)
Definition-7-4-mul = mulᵀ

Definition-7-4-exp : {σ : type} → T (𝓞 (𝓞 σ) ⇒ 𝓞 (𝓞 σ) ⇒ 𝓞 σ)
Definition-7-4-exp = expᵀ

Definition-7-4-fin : {σ : type} → T (ι ⇒ 𝓞 σ)
Definition-7-4-fin = finᵀ

Definition-7-4-fin-unfolds : {σ : type} → finᵀ {σ} ＝ Iter · sucᵀ · zerᵀ
Definition-7-4-fin-unfolds = refl

Definition-7-4-ω : {σ : type} → T (𝓞 σ)
Definition-7-4-ω = ωᵀ

Definition-7-4-ω-unfolds : {σ : type} → ωᵀ {σ} ＝ limᵀ · finᵀ
Definition-7-4-ω-unfolds = refl

Definition-7-4-tower : ℕ → (σ : type) → T (𝓞 σ)
Definition-7-4-tower = towerᵀ

Definition-7-4-tower-base : (σ : type) → towerᵀ 0 σ ＝ ωᵀ
Definition-7-4-tower-base σ = refl

Definition-7-4-tower-step : (n : ℕ) (σ : type)
                          → towerᵀ (succ n) σ ＝ expᵀ · ωᵀ · towerᵀ n (𝓞 σ)
Definition-7-4-tower-step n σ = refl

Definition-7-4-in-type-theory : 𝓤₀ ̇ → 𝓤₀ ̇
Definition-7-4-in-type-theory = Ordinals.ChurchEncoding.O

\end{code}

Remark 7.5 says that every approximant of ε₀ is written in system T
in this way, each at its own type, while ε₀ itself calls for a uniform
type and stays out of reach, in accordance with Theorem 6.9. The
second half is that theorem, and the first is Definition 7.4.

Labels: Remark 7.5 = rem:no-eps, Theorem 6.9 = thm:main,
Definition 7.4 = def:church.

\begin{code}

-- def:fold
Definition-7-6 : 𝓑 → (𝓑 → 𝓑) → ((ℕ → 𝓑) → 𝓑) → 𝓑 → 𝓑
Definition-7-6 = fold

Definition-7-6-Z : (z : 𝓑) (s : 𝓑 → 𝓑) (l : (ℕ → 𝓑) → 𝓑) → fold z s l Z ＝ z
Definition-7-6-Z z s l = refl

Definition-7-6-S : (z : 𝓑) (s : 𝓑 → 𝓑) (l : (ℕ → 𝓑) → 𝓑) (a : 𝓑)
                 → fold z s l (S a) ＝ s (fold z s l a)
Definition-7-6-S z s l a = refl

Definition-7-6-L : (z : 𝓑) (s : 𝓑 → 𝓑) (l : (ℕ → 𝓑) → 𝓑) (f : ℕ → 𝓑)
                 → fold z s l (L f) ＝ l (λ n → fold z s l (f n))
Definition-7-6-L z s l f = refl

Definition-7-6-mul : 𝓑 → 𝓑 → 𝓑
Definition-7-6-mul = mulᶜ

Definition-7-6-mul-unfolds : (a b : 𝓑) → mulᶜ a b ＝ fold Z (λ r → a ⊕ r) L b
Definition-7-6-mul-unfolds a b = refl

Definition-7-6-exp : 𝓑 → 𝓑 → 𝓑
Definition-7-6-exp = expᶜ

Definition-7-6-exp-unfolds : (a b : 𝓑)
                           → expᶜ a b ＝ fold ι[ 1 ] (λ r → mulᶜ r a) L b
Definition-7-6-exp-unfolds a b = refl

Definition-7-6-tower : ℕ → 𝓑
Definition-7-6-tower = towerᶜ

Definition-7-6-tower-base : towerᶜ 0 ＝ ω
Definition-7-6-tower-base = refl

Definition-7-6-tower-step : (n : ℕ) → towerᶜ (succ n) ＝ expᶜ ω (towerᶜ n)
Definition-7-6-tower-step n = refl

-- lem:fold
Lemma-7-7 : (a : 𝓑) → fold Z S L a ＝ a
Lemma-7-7 = fold-id

Lemma-7-7' : (z : 𝓑) (s : 𝓑 → 𝓑) (l : (ℕ → 𝓑) → 𝓑) (a b : 𝓑)
           → fold z s l (a ⊕ b) ＝ fold (fold z s l a) s l b
Lemma-7-7' = fold-⊕

Lemma-7-7-numeral : (x : 𝓑) (n : ℕ) → mulᶜ x ι[ n ] ＝ (x ⊗ ι[ n ])
Lemma-7-7-numeral = mulᶜ-ι

Lemma-7-7-mul : (x : 𝓑) → mulᶜ x ω ＝ (x ⊗ ω)
Lemma-7-7-mul = mulᶜ-ω

Lemma-7-7-exp : (b : 𝓑) → expᶜ ω b ＝ ω^ b
Lemma-7-7-exp = expᶜ-ω^

Lemma-7-7-tower : (n : ℕ) → towerᶜ n ＝ tower n
Lemma-7-7-tower = towerᶜ-tower

-- claim fin-is-a-kleisli-extension
Prose-fin-is-a-kleisli-extension
 : {σ : type}
 → ⟪ finᵀ {σ} ⟫ ＝ Kleisli-extension (λ k → iter ⟪ sucᵀ {σ} ⟫ ⟪ zerᵀ {σ} ⟫ k)
Prose-fin-is-a-kleisli-extension = refl

-- claim kleisli-extension-under-arguments
Prose-kleisli-extension-under-arguments
 : {σ : type} (g : ℕ → B-Set⟦ 𝓞 σ ⟧) (d : B ℕ)
   (z : B-Set⟦ σ ⟧) (s : B-Set⟦ σ ⟧ → B-Set⟦ σ ⟧)
   (l : (B ℕ → B-Set⟦ σ ⟧) → B-Set⟦ σ ⟧)
 → Kleisli-extension g d z s l ＝ Kleisli-extension (λ k → g k z s l) d
Prose-kleisli-extension-under-arguments g d z s l = refl

Prose-kleisli-extension-under-arguments'
 : {σ : type} (g : ℕ → B-Set⟦ 𝓞 σ ⟧)
   (z : B-Set⟦ σ ⟧) (s : B-Set⟦ σ ⟧ → B-Set⟦ σ ⟧)
   (l : (B ℕ → B-Set⟦ σ ⟧) → B-Set⟦ σ ⟧)
 → ⟪ limᵀ {σ} ⟫ (Kleisli-extension g) z s l
 ＝ l (Kleisli-extension (λ k → g k z s l))
Prose-kleisli-extension-under-arguments' g z s l = refl

-- def:rel
Definition-7-8 : (σ : type) → (B-Set⟦ σ ⟧ → 𝓑 → 𝓤₀ ̇ ) → B-Set⟦ 𝓞 σ ⟧ → 𝓑 → 𝓤₀ ̇
Definition-7-8 = Rel

-- lem:rel (1), item:p-zs
Lemma-7-9-1 : (σ : type) (R : B-Set⟦ σ ⟧ → 𝓑 → 𝓤₀ ̇ ) → Rel σ R ⟪ zerᵀ {σ} ⟫ Z
Lemma-7-9-1 = zerᵀ-Rel

Lemma-7-9-1' : {σ : type} {R : B-Set⟦ σ ⟧ → 𝓑 → 𝓤₀ ̇ }
               (c : B-Set⟦ 𝓞 σ ⟧) (a : 𝓑)
             → Rel σ R c a → Rel σ R (⟪ sucᵀ ⟫ c) (S a)
Lemma-7-9-1' = sucᵀ-Rel

-- lem:rel (2), item:p-lim
Lemma-7-9-2 : {σ : type} {R : B-Set⟦ σ ⟧ → 𝓑 → 𝓤₀ ̇ }
              (g : ℕ → B-Set⟦ 𝓞 σ ⟧) (h : ℕ → 𝓑)
            → ((j : ℕ) → Rel σ R (g j) (h j))
            → Rel σ R (⟪ limᵀ ⟫ (Kleisli-extension g)) (L h)
Lemma-7-9-2 = limᵀ-Rel

-- lem:rel (3), item:p-add
Lemma-7-9-3 : {σ : type} {R : B-Set⟦ σ ⟧ → 𝓑 → 𝓤₀ ̇ }
              (a : B-Set⟦ 𝓞 σ ⟧) (a' : 𝓑) (b : B-Set⟦ 𝓞 σ ⟧) (b' : 𝓑)
            → Rel σ R a a' → Rel σ R b b'
            → Rel σ R (⟪ addᵀ ⟫ a b) (b' ⊕ a')
Lemma-7-9-3 = addᵀ-Rel

-- lem:rel (4), item:p-mul
Lemma-7-9-4 : {σ : type} {R : B-Set⟦ σ ⟧ → 𝓑 → 𝓤₀ ̇ }
              (a : B-Set⟦ 𝓞 σ ⟧) (a' : 𝓑) (b : B-Set⟦ 𝓞 (𝓞 σ) ⟧) (b' : 𝓑)
            → Rel σ R a a' → Rel (𝓞 σ) (Rel σ R) b b'
            → Rel σ R (⟪ mulᵀ ⟫ a b) (mulᶜ a' b')
Lemma-7-9-4 = mulᵀ-Rel

-- lem:rel (5), item:p-exp
Lemma-7-9-5 : {σ : type} {R : B-Set⟦ σ ⟧ → 𝓑 → 𝓤₀ ̇ }
              (a : B-Set⟦ 𝓞 (𝓞 σ) ⟧) (a' : 𝓑) (b : B-Set⟦ 𝓞 (𝓞 σ) ⟧) (b' : 𝓑)
            → Rel (𝓞 σ) (Rel σ R) a a' → Rel (𝓞 σ) (Rel σ R) b b'
            → Rel σ R (⟪ expᵀ ⟫ a b) (expᶜ a' b')
Lemma-7-9-5 = expᵀ-Rel

-- lem:rel (6), item:p-tower
Lemma-7-9-6 : (σ : type) (R : B-Set⟦ σ ⟧ → 𝓑 → 𝓤₀ ̇ ) → Rel σ R ⟪ ωᵀ {σ} ⟫ ω
Lemma-7-9-6 = ωᵀ-Rel

Lemma-7-9-6' : (n : ℕ) (σ : type) (R : B-Set⟦ σ ⟧ → 𝓑 → 𝓤₀ ̇ )
             → Rel σ R ⟪ towerᵀ n σ ⟫ (towerᶜ n)
Lemma-7-9-6' = towerᵀ-Rel

Lemma-7-9-6-numerals : (σ : type) (R : B-Set⟦ σ ⟧ → 𝓑 → 𝓤₀ ̇ ) (j : ℕ)
                     → Rel σ R (iter ⟪ sucᵀ {σ} ⟫ ⟪ zerᵀ {σ} ⟫ j) ι[ j ]
Lemma-7-9-6-numerals = finᵀ-Rel

-- def:tower-term
Definition-7-10 : ℕ → T ((ι ⇒ ι) ⇒ ι)
Definition-7-10 = tower-term

Definition-7-10-syntax : Cx → type → 𝓤₀ ̇
Definition-7-10-syntax = Tm

Definition-7-10-abstraction : {Γ : Cx} {σ τ : type}
                            → Tm (Γ ▸ σ) τ → Tm Γ (σ ⇒ τ)
Definition-7-10-abstraction = abs

Definition-7-10-closed : {σ : type} → Tm ε σ → T σ
Definition-7-10-closed = tm

-- thm:lower
Theorem-7-11 : (n : ℕ) → tower n ≤ height (dialogue-tree (tower-term n))
Theorem-7-11 = tower-attained

Theorem-7-11' : (n : ℕ) → tower n ≤ height (dialogue-tree (tower-term n))
Theorem-7-11' = attained

-- cor:least
Corollary-7-12 : (a : 𝓑) → a < ε₀
               → Σ t ꞉ T ((ι ⇒ ι) ⇒ ι) , a ≤ height (dialogue-tree t)
Corollary-7-12 = heights-cofinal

Corollary-7-12' : (b : 𝓑)
                → ((t : T ((ι ⇒ ι) ⇒ ι)) → height (dialogue-tree t) ≤ b)
                → ε₀ ≤ b
Corollary-7-12' = ε₀-least

Corollary-7-12-below : (n : ℕ) → height (dialogue-tree (tower-term n)) < ε₀
Corollary-7-12-below = tower-term-below-ε₀

Corollary-7-12-restated : (a : 𝓑) → S a ≤ L tower
                        → Σ t ꞉ T ((ι ⇒ ι) ⇒ ι) , a ≤ height (dialogue-tree t)
Corollary-7-12-restated = cofinal

Corollary-7-12-restated' : (b : 𝓑)
                         → ((t : T ((ι ⇒ ι) ⇒ ι))
                               → height (dialogue-tree t) ≤ b)
                         → L tower ≤ b
Corollary-7-12-restated' = least

\end{code}

Section 8. Discussion

Question 8.1 asks for the exact height of a term as a function of its
syntax, and for the least n with the height below tower n, for which
the number K(t) of Xiao and Sun is an upper bound. Neither is
determined by the development.

Labels: Section 8 = sec:discussion, Question 8.1 = q:exact.
