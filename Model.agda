module Model where

open import CLC

open import Function using (_∘_)
open import Data.Unit  using (⊤ ; tt)
open import Data.Product  using (Σ ; _×_ ; _,_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_])

------------------
-- Model artifacts
------------------

variable
  A B C : Ctx → Set

-- family of maps between interpretations
_→̇_ : (Ctx → Set) → (Ctx → Set) → Set
_→̇_ A B = {Δ : Ctx} → A Δ → B Δ

infixr 10 _→̇_

-- exponential family
_⇒'_ : (Ctx → Set) → (Ctx → Set) → (Ctx → Set)
_⇒'_ A B Γ = {Γ' : Ctx} → Γ ⊆ Γ' → A Γ' → B Γ'

-- product family
_×'_ : (Ctx → Set) → (Ctx → Set) → (Ctx → Set)
_×'_ A B Γ = A Γ × B Γ

-- sum family
_+'_ : (Ctx → Set) → (Ctx → Set) → (Ctx → Set)
_+'_ A B Γ = A Γ ⊎ B Γ

-- unit family
⊤' : (Ctx → Set)
⊤' = λ Γ → ⊤

-------------
-- Evaluation
-------------

module Core
  -- these parameters interpret base types (Filinski's ℬ function)
  (String' : Ctx → Set)
  (wkString' : {Γ Γ' : Ctx} → Γ ⊆ Γ' → String' Γ → String' Γ')
  -- these parameters are that of a monad (Filinski's T monad)
  (𝒯 : (Ctx → Set) → (Ctx → Set))
  (wk𝒯 : {A : Ctx → Set} → ({Δ Δ' : Ctx} → Δ ⊆ Δ' → A Δ → A Δ') → {Γ Γ' : Ctx} → Γ ⊆ Γ' → 𝒯 A Γ → 𝒯 A Γ')
  (η  : {A : Ctx → Set} → A →̇ 𝒯 A)
  (bind-int : {A B : Ctx → Set} → (A ⇒' 𝒯 B) →̇ (𝒯 A ⇒' 𝒯 B))
  where

  -- Filinski's extension operator
  _⋆_ : 𝒯 A Γ → (A ⇒' 𝒯 B) Γ → 𝒯 B Γ
  w ⋆ f = bind-int f idWk w

  -- interpretation of types
  Tm'- : Ty → (Ctx → Set)
  Tm'- Unit    = ⊤'
  Tm'- String  = String'
  Tm'- (a ⇒ b) = (Tm'- a) ⇒' 𝒯 (Tm'- b)
  Tm'- (a + b) = Tm'- a +' Tm'- b

  -- interpretation of contexts
  Env'- : Ctx → (Ctx → Set)
  Env'- []       = ⊤'
  Env'- (Γ `, a) = Env'- Γ ×' 𝒯 (Tm'- a)

  -- monotonicity lemma
  wkTm'- : Γ ⊆ Γ' → Tm'- a Γ → Tm'- a Γ'
  wkTm'- {a = Unit}   w x = x
  wkTm'- {a = String} w x = wkString' w x
  wkTm'- {a = a ⇒ b}  w f = λ w' y → f (w ∙ w') y
  wkTm'- {a = a + b}  w x = [ inj₁ ∘ wkTm'- {a = a} w , inj₂ ∘ wkTm'- {a = b} w ] x

  -- monotonicity lemma
  wkEnv'- : Γ ⊆ Γ' → Env'- Δ Γ → Env'- Δ Γ'
  wkEnv'- {Δ = []}     w tt      = tt
  wkEnv'- {Δ = Δ `, a} w (s , x) = wkEnv'- {Δ = Δ} w s , wk𝒯 (wkTm'- {a = a}) w x

  -- interpretation of variables
  lookup' : Var Γ a → (Env'- Γ →̇ 𝒯 (Tm'- a))
  lookup' zero     (_ , x) = x
  lookup' (succ x) (γ , _) = lookup' x γ

  -- these parameters interpret constants, and correspond to Filinski's 𝒞 function
  module Eval (print' : {Γ : Ctx} → 𝒯 (Tm'- (String ⇒ Unit)) Γ) where

    -- interpretation of terms
    eval : Tm Γ a → (Env'- Γ →̇ 𝒯 (Tm'- a))
    eval {Γ} (var x)        s = lookup' x s
    eval {Γ} (lam t)        s = η (λ {_} w x → eval t ((wkEnv'- {Δ = Γ} w s) , η x))
    eval {Γ} (app t u)      s = eval t s ⋆ (λ w f → eval u (wkEnv'- {Δ = Γ} w s) ⋆ f)
    eval {Γ} (let-in t u)   s = eval t s ⋆ (λ w x → eval u (wkEnv'- {Δ = Γ} w s , η x))
    eval {Γ} unit           s = η tt
    eval {Γ} print          s = print'
    eval {Γ} (inl t)        s = eval t s ⋆ λ w x → η (inj₁ x)
    eval {Γ} (inr t)        s = eval t s ⋆ λ w x → η (inj₂ x)
    eval {Γ} (case t u₁ u₂) s = eval t s
      ⋆ λ { w (inj₁ x) → eval u₁ (wkEnv'- {Δ = Γ} w s , η x)
          ; w (inj₂ y) → eval u₂ (wkEnv'- {Δ = Γ} w s , η y) }
