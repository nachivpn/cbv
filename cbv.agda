module cbv where

open import Function using (_∘_)

data Ty : Set where
  Unit   : Ty
  String : Ty
  _⇒_    : Ty → Ty → Ty
  _+_    : Ty → Ty → Ty

variable
    a b c d : Ty

infixl 6 _`,_
infix 5 _⊆_

data Ctx : Set where
  [] : Ctx
  _`,_ : Ctx → Ty → Ctx

private
  variable
    Γ Γ' Δ Δ' Θ Θ' : Ctx

---------------------------------
-- Variables, terms and weakening
---------------------------------

data Var : Ctx → Ty → Set where
  zero : Var (Γ `, a) a
  succ : (v : Var Γ a) → Var (Γ `, b) a

data Tm : Ctx → Ty → Set where

  var  : Var Γ a
         -------
       → Tm Γ a

  lam  : Tm (Γ `, a) b
         -------------
       → Tm Γ (a ⇒ b)

  app  : Tm Γ (a ⇒ b) → Tm Γ a
         ---------------------
       → Tm Γ b

  let-in : Tm Γ a → Tm (Γ `, a) b
           ----------------------
         → Tm Γ b

  unit  : Tm Γ Unit

  print : Tm Γ (String ⇒ Unit)

  inl   : Tm Γ a
          ------------
        → Tm Γ (a + b)

  inr   : Tm Γ b
          ------------
        → Tm Γ (a + b)

  case  : Tm Γ (a + b) → Tm (Γ `, a) c → Tm (Γ `, b) c
          --------------------------------------------
        → Tm Γ c

-- Order-preserving embeddings (OPEs)
data _⊆_  : Ctx → Ctx → Set where
  base : [] ⊆ []
  drop : (w : Γ ⊆ Δ) → Γ ⊆ Δ `, a
  keep : (w : Γ ⊆ Δ) → Γ `, a ⊆ Δ `, a

-- identity OPE
idWk[_] : (Γ : Ctx) → Γ ⊆ Γ
idWk[_] []        = base
idWk[_] (Γ `, _a) = keep  idWk[ Γ ]

idWk = λ {Γ} → idWk[ Γ ]

-- composition of OPEs
_∙_ : Θ ⊆ Δ → Δ ⊆ Γ → Θ ⊆ Γ
w       ∙ base     = w
w       ∙ drop  w' = drop  (w ∙ w')
drop  w ∙ keep  w' = drop  (w ∙ w')
keep  w ∙ keep  w' = keep  (w ∙ w')

-- OPE used to weaken the context with a fresh variable
freshWk : Γ ⊆ Γ `, a
freshWk = drop idWk

freshWk[_] = λ {Γ} a → freshWk {Γ} {a}

wkVar : Γ ⊆ Γ' → Var Γ a → Var Γ' a
wkVar (drop w) v        = succ (wkVar w v)
wkVar (keep w) zero     = zero
wkVar (keep w) (succ v) = succ (wkVar w v)

wkTm : Γ ⊆ Γ' → Tm Γ a → Tm Γ' a
wkTm w (var x)        = var (wkVar w x)
wkTm w (lam t)        = lam (wkTm (keep w) t)
wkTm w (app t u)      = app (wkTm w t) (wkTm w u)
wkTm w (let-in t u)   = let-in (wkTm w t) (wkTm (keep w) u)
wkTm w unit           = unit
wkTm w print          = print
wkTm w (inl t)        = inl (wkTm w t)
wkTm w (inr t)        = inr (wkTm w t)
wkTm w (case t u₁ u₂) = case (wkTm w t) (wkTm (keep w) u₁) (wkTm (keep w) u₂)

------------------
-- Model artifacts
------------------

open import Data.Unit  using (⊤ ; tt)
open import Data.Product  using (Σ ; _×_ ; _,_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_])

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
_⊎'_ : (Ctx → Set) → (Ctx → Set) → (Ctx → Set)
_⊎'_ A B Γ = A Γ ⊎ B Γ

-- unit family
⊤' : (Ctx → Set)
⊤' = λ Γ → ⊤

-------------
-- Evaluation
-------------

module Model
  -- these parameters interpret base types (Filinski's ℬ function)
  (String' : Ctx → Set)
  (wkString' : {Γ Γ' : Ctx} → Γ ⊆ Γ' → String' Γ → String' Γ')
  -- these parameters are that of the monad (Filinski's Tʳ monad)
  (𝒯 : (Ctx → Set) → (Ctx → Set))
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
  Tm'- (a + b) = Tm'- a ⊎' Tm'- b

  -- interpretation of contexts
  Sub'- : Ctx → (Ctx → Set)
  Sub'- []       = ⊤'
  Sub'- (Γ `, a) = Sub'- Γ ×' Tm'- a

  -- monotonicity lemma
  wkTm'- : Γ ⊆ Γ' → Tm'- a Γ → Tm'- a Γ'
  wkTm'- {a = Unit}   w x = x
  wkTm'- {a = String} w x = wkString' w x
  wkTm'- {a = a ⇒ b}  w f = λ w' y → f (w ∙ w') y
  wkTm'- {a = a + b}  w x = [ inj₁ ∘ wkTm'- {a = a} w , inj₂ ∘ wkTm'- {a = b} w ] x

  -- monotonicity lemma
  wkSub'- : Γ ⊆ Γ' → Sub'- Δ Γ → Sub'- Δ Γ'
  wkSub'- {Δ = []}     w tt      = tt
  wkSub'- {Δ = Δ `, a} w (s , x) = wkSub'- {Δ = Δ} w s , wkTm'- {a = a} w x

  -- interpretation of variables
  lookup' : Var Γ a → (Sub'- Γ →̇ Tm'- a)
  lookup' zero     (_ , x) = x
  lookup' (succ x) (γ , _) = lookup' x γ

  -- these parameters interpret constants, and correspond to Filinski's 𝒞 function
  module Eval (print' : {Γ : Ctx} → 𝒯 (Tm'- (String ⇒ Unit)) Γ) where

    -- interpretation of terms
    eval : Tm Γ a → (Sub'- Γ →̇ 𝒯 (Tm'- a))
    eval {Γ} (var x)        s = η (lookup' x s)
    eval {Γ} (lam t)        s = η (λ {_} w x → eval t ((wkSub'- {Δ = Γ} w s) , x))
    eval {Γ} (app t u)      s = eval t s ⋆ (λ w f → eval u (wkSub'- {Δ = Γ} w s) ⋆ f)
    eval {Γ} (let-in t u)   s = eval t s ⋆ (λ w x → eval u (wkSub'- {Δ = Γ} w s , x))
    eval {Γ} unit           s = η tt
    eval {Γ} print          s = print'
    eval {Γ} (inl t)        s = eval t s ⋆ λ w x → η (inj₁ x)
    eval {Γ} (inr t)        s = eval t s ⋆ λ w x → η (inj₂ x)
    eval {Γ} (case t u₁ u₂) s = eval t s
      ⋆ λ { w (inj₁ x) → eval u₁ (wkSub'- {Δ = Γ} w s , x)
          ; w (inj₂ y) → eval u₂ (wkSub'- {Δ = Γ} w s , y) }

---------------
-- Normal forms
---------------

data At : Ctx → Ty → Set
data Nv : Ctx → Ty → Set
data Nc : Ctx → Ty → Set

-- Atoms
data At where
  var   : Var Γ a → At Γ a
  print : At Γ (String ⇒ Unit)

-- Normal values
data Nv where
  str   : At Γ String → Nv Γ String
  unit  : Nv Γ Unit
  lam   : Nc (Γ `, a) b → Nv Γ (a ⇒ b)
  inl   : Nv Γ a → Nv Γ (a + b)
  inr   : Nv Γ b → Nv Γ (a + b)

-- Normal computations
data Nc where
  ret          : Nv Γ a → Nc Γ a
  let-app-in   : At Γ (a ⇒ b) → Nv Γ a → Nc (Γ `, b) c → Nc Γ c
  case         : At Γ (a + b) → Nc (Γ `, a) c → Nc (Γ `, b) c → Nc Γ c

embAt : At Γ a → Tm Γ a
embAt (var x) = var x
embAt print   = print

embNv : Nv Γ a → Tm Γ a
embNc : Nc Γ a → Tm Γ a

embNv (str x) = embAt x
embNv unit    = unit
embNv (lam m) = lam (embNc m)
embNv (inl n) = inl (embNv n)
embNv (inr n) = inr (embNv n)

embNc (ret x)            = embNv x
embNc (let-app-in x n c) = let-in (app (embAt x) (embNv n)) (embNc c)
embNc (case x m₁ m₂)     = case (embAt x) (embNc m₁) (embNc m₂)

wkAt : Γ ⊆ Γ' → At Γ a → At Γ' a
wkAt w (var x) = var (wkVar w x)
wkAt w print   = print

wkNv : Γ ⊆ Γ' → Nv Γ a → Nv Γ' a
wkNc : Γ ⊆ Γ' → Nc Γ a → Nc Γ' a

wkNv w (str x) = str (wkAt w x)
wkNv w unit    = unit
wkNv w (lam m) = lam (wkNc (keep w) m)
wkNv w (inl n) = inl (wkNv w n)
wkNv w (inr n) = inr (wkNv w n)

wkNc w (ret x)            = ret (wkNv w x)
wkNc w (let-app-in x n m) = let-app-in (wkAt w x) (wkNv w n) (wkNc (keep w) m)
wkNc w (case x m₁ m₂)     = case (wkAt w x) (wkNc (keep w) m₁) (wkNc (keep w) m₂)

-- some pretentious notation
Var- Tm- At- Nv- Nc- : Ty → Ctx → Set
Var- a Γ = Var Γ a
Tm- a Γ = Tm Γ a
At- a Γ = At Γ a
Nv- a Γ = Nv Γ a
Nc- a Γ = Nc Γ a

------------
-- NbE model
------------

module ResidualisingMonad where

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

  fmap-int : (A ⇒' B) →̇ (𝒞 A ⇒' 𝒞 B)
  fmap-int f w (ret x)            = ret (f w x)
  fmap-int f w (let-app-in x n m) = let-app-in x n (fmap-int f (drop w) m)
  fmap-int f w (case x m₁ m₂)     = case x (fmap-int f (drop w) m₁) (fmap-int f (drop w) m₂)

  bind-int : (A ⇒' 𝒞 B) →̇ (𝒞 A ⇒' 𝒞 B)
  bind-int f w (ret x)            = f w x
  bind-int f w (let-app-in x n m) = let-app-in x n (bind-int f (drop w) m)
  bind-int f w (case x m₁ m₂)     = case x (bind-int f (drop w) m₁) (bind-int f (drop w) m₂)

  -- (special case of) Filinski's γᵍʳ
  disperse : Nc- a →̇ 𝒞 (Nv- a)
  disperse (ret nv)           = ret nv
  disperse (let-app-in x n m) = let-app-in x n (disperse m)
  disperse (case x m₁ m₂)     = case x (disperse m₁) (disperse m₂)

  -- (special case of) Filinski's collect
  collect : 𝒞 (Nv- a) →̇ Nc- a
  collect (ret nv)           = ret nv
  collect (let-app-in x n m) = let-app-in x n (collect m)
  collect (case x m₁ m₂)     = case x (collect m₁) (collect m₂)

  -- Filinski's bind
  register-let-app : At Γ (a ⇒ b) → Nv Γ a → 𝒞 (Var- b) Γ
  register-let-app x nv = let-app-in x nv (ret zero)

  -- Filinski's binds
  register-case : At Γ (a + b) → 𝒞 (Var- a ⊎' Var- b) Γ
  register-case x = case x (ret (inj₁ zero)) (ret (inj₂ zero))

  --
  run : 𝒞 (Nc- a) →̇ Nc- a
  run m = collect (join (fmap disperse m))

-- A "residualising" monad has the following exported operations.
-- Observe that it can be defined in ways other than 𝒞.
-- For e.g., it could have been defined using continuations (as in Filinski)
open ResidualisingMonad
  using (𝒞 ; wk𝒞 ; bind-int
        ; register-let-app ; register-case
        ; disperse ; collect ; run)
  renaming (ret to η)

open Model (At- String) wkAt 𝒞 η bind-int

reflect : At- a →̇ 𝒞 (Tm'- a)
reify   : Tm'- a →̇ Nc- a

reflect {Unit}   x = η tt
reflect {String} x = η x
reflect {a ⇒ b}  x = η
  (λ w xa → disperse {a} (reify xa)
    ⋆ λ w'  nva → register-let-app (wkAt (w ∙ w') x) nva
    ⋆ λ w'' vb → reflect (var vb))
reflect {a + b} x  = register-case x
  ⋆ λ { w (inj₁ v) → reflect (var v) ⋆ λ w' z → η (inj₁ z)
      ; w (inj₂ v) → reflect (var v) ⋆ λ w' z → η (inj₂ z) }

reify {Unit}   tt      = ret unit
reify {String} x       = ret (str x)
reify {a ⇒ b}  f       = ret (lam (collect
  (reflect (var zero)
    ⋆ λ w  xa → f (freshWk ∙ w) xa
    ⋆ λ w' xb → disperse (reify xb))))
reify {a + b} (inj₁ x) = collect
  (disperse (reify {a} x)
  ⋆ (λ w nv → η (inl nv)))
reify {a + b} (inj₂ y) = collect
  (disperse (reify {b} y)
  ⋆ (λ w nv → η (inr nv)))

idₛ : 𝒞 (Sub'- Γ) Γ
idₛ {[]}     = η tt
idₛ {Γ `, a} = reflect (var zero)
  ⋆ λ w x → wk𝒞 (wkSub'- {Δ = Γ}) (freshWk ∙ w) idₛ
  ⋆ λ w' s → η (s , (wkTm'- {a = a} w' x))

open Eval (reflect print)

norm : Tm- a →̇ Nc- a
norm t = run
  (idₛ
  ⋆ λ w s → eval t s
  ⋆ λ w' x → η (reify x))

-------------------------
-- References and related
-------------------------

-- Filinski: Normalization by Evaluation for the Computational Lambda-Calculus (https://link.springer.com/chapter/10.1007/3-540-45413-6_15)
-- Abel & Sattler: Normalization by Evaluation for Call-By-Push-Value [...] (https://www.cse.chalmers.se/~abela/ppdp19.pdf)
-- Lindley: Normalisation by evaluation (https://homepages.inf.ed.ac.uk/slindley/nbe/nbe-cambridge2016.pdf)
-- Valliappan, Russo & Lindley: Practical NbE for EDSLs (https://nachivpn.me/nbe-edsl.pdf)
