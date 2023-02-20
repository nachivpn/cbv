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
  Tm'- (a + b) = Tm'- a ⊎' Tm'- b

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

module NbEModel
  -- Parameters that require a "residualising" monad
  (𝒯ʳ : (Ctx → Set) → (Ctx → Set))
  (wk𝒯ʳ : {A : Ctx → Set} → ({Δ Δ' : Ctx} → Δ ⊆ Δ' → A Δ → A Δ') → {Γ Γ' : Ctx} → Γ ⊆ Γ' → 𝒯ʳ A Γ → 𝒯ʳ A Γ')
  (η   : {A : Ctx → Set} → A →̇ 𝒯ʳ A)
  (bind-int : {A B : Ctx → Set} → (A ⇒' 𝒯ʳ B) →̇ (𝒯ʳ A ⇒' 𝒯ʳ B))
  (register-let-app : {Γ : Ctx} {a b : Ty} → At Γ (a ⇒ b) → Nv Γ a → 𝒯ʳ (Var- b) Γ)
  (register-case : {Γ : Ctx} {a b : Ty} → At Γ (a + b) → 𝒯ʳ (Var- a ⊎' Var- b) Γ)
  (run : {a : Ty} → 𝒯ʳ (Nv- a) →̇ Nc- a)
  where

  open Model (At- String) wkAt 𝒯ʳ wk𝒯ʳ η bind-int

  reflect : At- a →̇ 𝒯ʳ (Tm'- a)
  reify   : Tm'- a →̇ Nv- a

  reflect {Unit}   x = η tt
  reflect {String} x = η x
  reflect {a ⇒ b}  x = η
    λ {_} w xa → register-let-app (wkAt w x) (reify xa)
    ⋆ λ w'' vb → reflect (var vb)
  reflect {a + b} x  = register-case x
    ⋆ λ { w (inj₁ v) → reflect (var v) ⋆ λ w' z → η (inj₁ z)
        ; w (inj₂ v) → reflect (var v) ⋆ λ w' z → η (inj₂ z) }

  reify {Unit}   tt      = unit
  reify {String} x       = str x
  reify {a ⇒ b}  f       = lam (run
    (reflect (var zero)
      ⋆ λ w  xa → f (freshWk ∙ w) xa
      ⋆ λ w' xb → η (reify xb)))
  reify {a + b} (inj₁ x) = inl (reify x)
  reify {a + b} (inj₂ y) = inr (reify y)

  idEnv'[_] : (Γ : Ctx) → Env'- Γ Γ
  idEnv'[ [] ]     = tt
  idEnv'[ Γ `, a ] = wkEnv'- {Δ = Γ} freshWk idEnv'[ Γ ] , reflect (var zero)

  quot : (Env'- Γ →̇ 𝒯ʳ (Tm'- a)) → Tm Γ a
  quot {Γ} f = embNc (run
    (f idEnv'[ Γ ]
      ⋆ λ w' x → η (reify x)))

  open Eval (reflect print)

  norm : Tm- a →̇ Tm- a
  norm t = quot (eval t)

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
  register-case : At Γ (a + b) → 𝒞 (Var- a ⊎' Var- b) Γ
  register-case x = case x (ret (inj₁ zero)) (ret (inj₂ zero))

open ResidualisingCoverMonad

open NbEModel 𝒞 wk𝒞 ret bind-int register-let-app register-case run public

-----------
-- Examples
-----------

pattern Bool = Unit + Unit

-- a sample context
Gamma = [] `, Bool {- 2 -} `, String {- 1 -} `, String {- 0 -}

pattern x0 = zero
pattern x1 = succ x0
pattern x2 = succ x1
pattern x3 = succ x2
pattern x4 = succ x3

-- (λ. print x2) (print x0)
ex0 : Tm Gamma Unit
ex0 = app (lam (app print (var x2))) (app print (var x0))

-- λ. λ. λ. case x2 of { _ -> x1 ; _ -> x2 }
ifte : Tm Gamma (Bool ⇒ (a ⇒ (a ⇒ a)))
ifte = lam (lam (lam (case (var x2) (var x1) (var x2))))

-- let t in u
_︔_ : Tm Gamma a → Tm Gamma b → Tm Gamma b
t ︔ u = let-in t (wkTm freshWk u)

-- To understand the problem of "redundant case analysis", consider
-- the examples below:

red-case : Tm Gamma Unit
red-case = app (app (app ifte (var x2)) (app print (var x0))) (app print (var x1))

red-case' : Tm Gamma Unit
red-case' = app print (var x0) ︔ app print (var x1)

-- We would like for these examples to be equal when normalized, but
-- they currently aren't. This can be achieved by redefining normal
-- forms to avoid redundant branches and refining 𝒞. A tedious
-- endeavour in Agda, but achievable nevertheless.

-- Similarly, the problem of "repeated case analysis" is illustrated
-- below:

repeated-case : Tm Gamma Unit
repeated-case = case (var x2)
  (case (var x3)
    (app print (var x2))
    (app print (var x3))) -- never taken
  (case (var x3)
    (app print (var x2))  -- never taken
    (app print (var x3)))

repeated-case' : Tm Gamma Unit
repeated-case' = case (var x2)
  (app print (var x1))
  (app print (var x2))

-------------------------
-- References and related
-------------------------

-- Filinski: Normalization by Evaluation for the Computational Lambda-Calculus (https://link.springer.com/chapter/10.1007/3-540-45413-6_15)
-- Abel & Sattler: Normalization by Evaluation for Call-By-Push-Value [...] (https://www.cse.chalmers.se/~abela/ppdp19.pdf)
-- Lindley: Normalisation by evaluation (https://homepages.inf.ed.ac.uk/slindley/nbe/nbe-cambridge2016.pdf)
-- Valliappan, Russo & Lindley: Practical NbE for EDSLs (https://nachivpn.me/nbe-edsl.pdf)
