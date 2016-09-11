module Syntax where

open import Agda.Primitive
open import Prelude.Monoidal
open import Prelude.List
open import Prelude.Families
open import Prelude.Path
open import Prelude.Natural

Fam₀ : Set → Set₁
Fam₀ = Fam lzero

open List using (◇; □; _++_)
open Π using (_∘_)

-- valences
record Vl (𝒮 : Set) : Set where
  constructor [_]·_
  field
    vars : List 𝒮
    sort : 𝒮

-- second-order arities
record Ar (𝒮 : Set) : Set where
  constructor ⟅_⟆·_
  field
    vls : List (Vl 𝒮)
    sort : 𝒮

open Vl public
open Ar public

-- Sign is the pullback of π : Fam → Set along Ar : Set → Set.
record Sign : Set₁ where
  no-eta-equality
  field
    𝒮 : Set₀
    𝒪 : Fam₀ (Ar 𝒮)

  2ctx : Set
  2ctx = List (Vl 𝒮)

  1ctx : Set
  1ctx = List 𝒮

open Sign public

mutual
  data _∣_▹_⊢_ (Σ : Sign) (Ω : 2ctx Σ) (Γ : 1ctx Σ) (τ : 𝒮 Σ) : Set where
    ⌞_⌟
      : ◇ (_≡ τ) Γ
      → Σ ∣ Ω ▹ Γ ⊢ τ

    #_[_]
      : {Δ : 1ctx Σ}
      → (𝔪 : ◇ (_≡ [ Δ ]· τ) Ω)
      → □ (Σ ∣ Ω ▹ Δ ++ Γ ⊢_) Δ
      → Σ ∣ Ω ▹ Γ ⊢ τ

    _$_
      : (Χ : 2ctx Σ)
      → 𝒪 Σ (⟅ Χ ⟆· τ)
      → □ (Σ ∣ Ω ▹ Γ ⊢[_]) Χ
      → Σ ∣ Ω ▹ Γ ⊢ τ

  _∣_▹_⊢[_] : (Σ : Sign) → 2ctx Σ → 1ctx Σ → Vl (𝒮 Σ) → Set
  Σ ∣ Ω ▹ Γ ⊢[ [ Δ ]· τ ] = Σ ∣ Ω ▹ Δ ++ Γ ⊢ τ
