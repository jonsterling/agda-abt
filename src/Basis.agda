module Basis where

open import Agda.Primitive public
open import Prelude.List public
open import Prelude.Monoidal
open import Prelude.Families

Fam₀ : Set → Set₁
Fam₀ = Fam lzero

∫↓ : ∀ {a b} {X : Set a} → (X → Set b) → Set (a ⊔ b)
∫↓ {X = X} P = ∀ {x} → P x

∫↑ : ∀ {a b} {X : Set a} → (X → Set b) → Set (a ⊔ b)
∫↑ {X = X} P = Σ[ X ∋ x ] P x

syntax ∫↓ {X = X} (λ x → P) = ∫↓[ x ∶ X ] P
syntax ∫↑ {X = X} (λ x → P) = ∫↑[ x ∶ X ] P

_⇒₁_ : ∀ {X} → Fam₀ X → Fam₀ X → Set
F ⇒₁ G = ∫↓[ x ∶ _ ] (F x → G x)

_⇐₁_ : ∀ {X} → Fam₀ X → Fam₀ X → Set
F ⇐₁ G = G ⇒₁ F

infixr 2 _⇒₁_
infixl 2 _⇐₁_


open List using (◇; □; _++_) public
open Π using (_∘_) public
