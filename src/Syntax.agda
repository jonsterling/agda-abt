module Syntax where

open import Agda.Primitive
open import Prelude.Monoidal
open import Prelude.List
open import Prelude.Families
open import Prelude.Path
open import Prelude.Natural

Fam₀ : Set → Set₁
Fam₀ = Fam lzero

∫↓ : ∀ {a b} {X : Set a} → (X → Set b) → Set (a ⊔ b)
∫↓ {X = X} P = ∀ {x} → P x

∫↑ : ∀ {a b} {X : Set a} → (X → Set b) → Set (a ⊔ b)
∫↑ {X = X} P = Σ[ X ∋ x ] P x

syntax ∫↓ {X = X} (λ x → P) = ∫↓[ x ∶ X ] P
syntax ∫↑ {X = X} (λ x → P) = ∫↑[ x ∶ X ] P

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

_⁍_ : {𝒮 : Set} → List 𝒮 → Vl 𝒮 → Vl 𝒮
Γ ⁍ [ Δ ]· τ = [ Γ ++ Δ ]· τ

infix 2 _⁍_

open Sign public

-- Our semantic universe
𝓤 : Sign → Set₁
𝓤 Σ = Vl (𝒮 Σ) → Set

-- The signature endofunctor
data 𝓕[_] (Σ : Sign) (𝒜 : 𝓤 Σ) : 𝓤 Σ where
  app
    : ∀ {Ω Γ τ}
    → 𝒪 Σ (⟅ Ω ⟆· τ) 
    → □ (𝒜 ∘ Γ ⁍_) Ω
    → 𝓕[ Σ ] 𝒜 ([ Γ ]· τ)

-- The metavariable endofunctor
data 𝓥[_] (Σ : Sign) (Ω : 2ctx Σ) (𝒜 : 𝓤 Σ) : 𝓤 Σ where
  meta-app
    : ∀ {Γ Δ τ}
    → ◇ (_≡ [ Δ ]· τ) Ω
    → □ (𝒜 ∘ [ Γ ]·_) Δ
    → 𝓥[ Σ ] Ω 𝒜 ([ Γ ]· τ)

_⇒₁_ : ∀ {X} → Fam₀ X → Fam₀ X → Set
F ⇒₁ G = ∫↓[ x ∶ _ ] (F x → G x)

_⇐₁_ : ∀ {X} → Fam₀ X → Fam₀ X → Set
F ⇐₁ G = G ⇒₁ F

Var : ∀ {X : Set} → List X → X → Set
Var Γ τ = ◇ (_≡ τ) Γ

_∣_⊙_ : (Σ : Sign) → 𝓤 Σ → 𝓤 Σ → 𝓤 Σ
_∣_⊙_ Σ P Q ([ Γ ]· τ) = ∫↑[ Δ ∶ 1ctx Σ ] (P ([ Δ ]· τ) ⊗ □ (Q ∘ [ Γ ]·_) Δ)

-- The term endofunctor
data 𝓣[_] (Σ : Sign) (Ω : 2ctx Σ) (𝒜 : 𝓤 Σ) : 𝓤 Σ where
  var
    : ∀ {Γ τ}
    → Var Γ τ
    → 𝓣[ Σ ] Ω 𝒜 ([ Γ ]· τ)

  mvar
    : 𝓥[ Σ ] Ω 𝒜 
    ⇒₁ 𝓣[ Σ ] Ω 𝒜

  op
    : 𝓕[ Σ ] 𝒜
    ⇒₁ 𝓣[ Σ ] Ω 𝒜

-- The free language with explicit substitutions over a signature
data Free[_] (Σ : Sign) (Ω : 2ctx Σ) : 𝓤 Σ where
  roll
    : 𝓣[ Σ ] Ω (Free[ Σ ] Ω)
    ⇒₁ Free[ Σ ] Ω

  -- closures / explicit substitutions
  clo
    : (Σ ∣ Free[ Σ ] Ω ⊙ Free[ Σ ] Ω) 
    ⇒₁ Free[ Σ ] Ω

_∣_▹_⊢_ : (Σ : Sign) (Ω : 2ctx Σ) (Γ : 1ctx Σ) (τ : 𝒮 Σ) → Set
Σ ∣ Ω ▹ Γ ⊢ τ = Free[ Σ ] Ω ([ Γ ]· τ)


pattern ⌞_⌟ x = roll (var x)
pattern _#_ 𝔵 ms = roll (mvar (meta-app 𝔵 ms))
pattern _$_ ϑ ms = roll (op (app ϑ ms))
pattern ⟨_∣_◂_⟩ Δ m ρ = clo (Δ ▸ (m , ρ))

-- TODO: force explicit substitutions inward
unroll : {Σ : Sign} {Ω : 2ctx Σ} → Free[ Σ ] Ω ⇒₁ 𝓣[ Σ ] Ω (Free[ Σ ] Ω)
unroll (roll m) = m
unroll ⟨ Δ ∣ ⌞ x ⌟ ◂ ρ ⟩ = {!!}
unroll ⟨ Δ ∣ ϑ $ ms ◂ ρ ⟩ = {!!}
unroll ⟨ Δ ∣ 𝔵 # ms ◂ ρ ⟩ = {!!}
unroll ⟨ Δ ∣ m ◂ ρ ⟩ = {!!}


pattern vz = ◇.stop refl
pattern □[] = □.stop
pattern _□∷_ x y = □.step x y

pattern [_] x = x ∷ []

infix 2 _$_
infix 4 _□∷_

data Λ⊩_ : Ar 𝟙 → Set where
  lam : Λ⊩ ⟅ [ * ∷ [] ]· * ∷ [] ⟆· *
  tt ff : Λ⊩ ⟅ [] ⟆· *

Λ : Sign
𝒮 Λ = 𝟙
𝒪 Λ = Λ⊩_

id : Λ ∣ [] ▹ [] ⊢ *
id = lam $ ⌞ vz ⌟ □∷ □[]

tt′ : Λ ∣ [] ▹ [] ⊢ *
tt′ = ⟨ [ * ] ∣ ⌞ vz ⌟ ◂ (tt $ □[]) □∷ □[] ⟩
