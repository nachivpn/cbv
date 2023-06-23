module Norm where

open import CLC
open import Model

open import Function using (_∘_)
open import Data.Unit  using (⊤ ; tt)
open import Data.Product  using (Σ ; _×_ ; _,_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_])

------------
-- NbE model
------------

module NbEModel
  -- Parameters that require a "residualising" monad
  (𝒯ʳ : (Ctx → Set) → (Ctx → Set))
  (wk𝒯ʳ : {A : Ctx → Set} → ({Δ Δ' : Ctx} → Δ ⊆ Δ' → A Δ → A Δ') → {Γ Γ' : Ctx} → Γ ⊆ Γ' → 𝒯ʳ A Γ → 𝒯ʳ A Γ')
  (η   : {A : Ctx → Set} → A →̇ 𝒯ʳ A)
  (bind-int : {A B : Ctx → Set} → (A ⇒' 𝒯ʳ B) →̇ (𝒯ʳ A ⇒' 𝒯ʳ B))
  (register-let-app : {Γ : Ctx} {a b : Ty} → At Γ (a ⇒ b) → Nv Γ a → 𝒯ʳ (Var- b) Γ)
  (register-case : {Γ : Ctx} {a b : Ty} → At Γ (a + b) → 𝒯ʳ (Var- a +' Var- b) Γ)
  (run : {a : Ty} → 𝒯ʳ (Nv- a) →̇ Nc- a)
  where

  open Model.Core (At- String) wkAt 𝒯ʳ wk𝒯ʳ η bind-int

  reflect  : At- a →̇ 𝒯ʳ (Tm'- a)
  reifyVal : Tm'- a →̇ Nv- a

  reflect {Unit}   x = η tt
  reflect {String} x = η x
  reflect {a ⇒ b}  x = η
    λ {_} w xa → register-let-app (wkAt w x) (reifyVal xa)
    ⋆ λ w'' vb → reflect (var vb)
  reflect {a + b} x  = register-case x
    ⋆ λ { w (inj₁ v) → reflect (var v) ⋆ λ w' z → η (inj₁ z)
        ; w (inj₂ v) → reflect (var v) ⋆ λ w' z → η (inj₂ z) }

  reifyVal {Unit}   tt      = unit
  reifyVal {String} x       = str x
  reifyVal {a ⇒ b}  f       = lam (run
    (reflect (var zero)
      ⋆ λ w  xa → f (freshWk ∙ w) xa
      ⋆ λ w' xb → η (reifyVal xb)))
  reifyVal {a + b} (inj₁ x) = inl (reifyVal x)
  reifyVal {a + b} (inj₂ y) = inr (reifyVal y)

  reify : Tm'- a →̇ 𝒯ʳ (Nv- a)
  reify x = η (reifyVal x)

  idEnv'[_] : (Γ : Ctx) → Env'- Γ Γ
  idEnv'[ [] ]     = tt
  idEnv'[ Γ `, a ] = wkEnv'- {Δ = Γ} freshWk idEnv'[ Γ ] , reflect (var zero)

  quot : (Env'- Γ →̇ 𝒯ʳ (Tm'- a)) → Tm Γ a
  quot {Γ} f = embNc (run (f idEnv'[ Γ ] ⋆ λ w' x → reify x))

  open Eval (reflect print)

  norm : Tm Γ a → Tm Γ a
  norm = quot ∘ eval

module ResidualisingCoverMonad where

  -- data structure used to define a monad on families ('𝒞' for "cover", following Abel)
  -- (similar to Lindley's "free" monad)
  data 𝒞 (A : Ctx → Set) : Ctx → Set where
    ret        : A →̇ 𝒞 A
    let-app-in : At Γ (a ⇒ b) → Nv Γ a → 𝒞 A (Γ `, b) → 𝒞 A Γ
    case       : At Γ (a + b) → 𝒞 A (Γ `, a) → 𝒞 A (Γ `, b) → 𝒞 A Γ

  module _ (wkA : {Δ Δ' : Ctx} → Δ ⊆ Δ' → A Δ → A Δ') where
    wk𝒞 : Γ ⊆ Γ' → 𝒞 A Γ → 𝒞 A Γ'
    wk𝒞 w (ret x)            = ret (wkA w x)
    wk𝒞 w (let-app-in x n c) = let-app-in (wkAt w x) (wkNv w n) (wk𝒞 (keep w) c)
    wk𝒞 w (case x m₁ m₂)     = case (wkAt w x) (wk𝒞 (keep w) m₁) (wk𝒞 (keep w) m₂)

  join : 𝒞 (𝒞 A) →̇ 𝒞 A
  join (ret x)            = x
  join (let-app-in x n m) = let-app-in x n (join m)
  join (case x m₁ m₂)     = case x (join m₁) (join m₂)

  fmap : (A →̇ B) → (𝒞 A →̇ 𝒞 B)
  fmap f (ret x)            = ret (f x)
  fmap f (let-app-in x n m) = let-app-in x n (fmap f m)
  fmap f (case x m₁ m₂)     = case x (fmap f m₁) (fmap f m₂)

  bind : (A →̇ 𝒞 B) → (𝒞 A →̇ 𝒞 B)
  bind f x = join (fmap f x)

  join-int : ⊤' →̇ 𝒞 (𝒞 A) ⇒' 𝒞 A
  join-int t w (ret m)            = m
  join-int t w (let-app-in x n m) = let-app-in x n (join-int t (drop w) m)
  join-int t w (case x m₁ m₂)     = case x (join-int tt (drop w) m₁) (join-int t (drop w) m₂)

  fmap-int : (A ⇒' B) →̇ (𝒞 A ⇒' 𝒞 B)
  fmap-int f w (ret x)            = ret (f w x)
  fmap-int f w (let-app-in x n m) = let-app-in x n (fmap-int f (drop w) m)
  fmap-int f w (case x m₁ m₂)     = case x (fmap-int f (drop w) m₁) (fmap-int f (drop w) m₂)

  bind-int : (A ⇒' 𝒞 B) →̇ (𝒞 A ⇒' 𝒞 B)
  bind-int f w m = join-int tt w (fmap-int f w m)

  -- Filinski's collect
  run : 𝒞 (Nv- a) →̇ Nc- a
  run (ret nv)           = ret nv
  run (let-app-in x n m) = let-app-in x n (run m)
  run (case x m₁ m₂)     = case x (run m₁) (run m₂)

  -- Filinski's bind
  register-let-app : At Γ (a ⇒ b) → Nv Γ a → 𝒞 (Var- b) Γ
  register-let-app x nv = let-app-in x nv (ret zero)

  -- Filinski's binds
  register-case : At Γ (a + b) → 𝒞 (Var- a +' Var- b) Γ
  register-case x = case x (ret (inj₁ zero)) (ret (inj₂ zero))

open ResidualisingCoverMonad

open NbEModel 𝒞 wk𝒞 ret bind-int register-let-app register-case run public
