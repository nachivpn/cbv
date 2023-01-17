module cbv where

open import Function using (_∘_)

data Ty : Set where
  Unit   : Ty
  String : Ty
  _⇒_    : Ty → Ty → Ty

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

------------------------------------
-- Variables, terms and substituions
------------------------------------

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

data _⊆_  : Ctx → Ctx → Set where
  base   : [] ⊆ []
  drop   : (w : Γ ⊆ Δ) → Γ ⊆ Δ `, a
  keep   : (w : Γ ⊆ Δ) → Γ `, a ⊆ Δ `, a

-- weakening is reflexive
idWk[_] : (Γ : Ctx) → Γ ⊆ Γ
idWk[_] []        = base
idWk[_] (Γ `, _a) = keep  idWk[ Γ ]

idWk = λ {Γ} → idWk[ Γ ]

-- weakening is transitive (or can be composed)
_∙_ : Θ ⊆ Δ → Δ ⊆ Γ → Θ ⊆ Γ
w       ∙ base     = w
w       ∙ drop  w' = drop  (w ∙ w')
drop  w ∙ keep  w' = drop  (w ∙ w')
keep  w ∙ keep  w' = keep  (w ∙ w')

-- weakening that "generates a fresh variable"
fresh : Γ ⊆ Γ `, a
fresh = drop idWk

fresh[_] = λ {Γ} a → fresh {Γ} {a}

wkVar : Γ ⊆ Γ' → Var Γ a → Var Γ' a
wkVar (drop e) v        = succ (wkVar e v)
wkVar (keep e) zero     = zero
wkVar (keep e) (succ v) = succ (wkVar e v)

wkTm : Γ ⊆ Γ' → Tm Γ a → Tm Γ' a
wkTm w (var x)      = var (wkVar w x)
wkTm e (lam t)      = lam (wkTm (keep e) t)
wkTm e (app t t₁)   = app (wkTm e t) (wkTm e t₁)
wkTm e (let-in t u) = let-in (wkTm e t) (wkTm (keep e) u)
wkTm e unit         = unit
wkTm e print        = print

data At : Ctx → Ty → Set
data Nv : Ctx → Ty → Set
data Nc : Ctx → Ty → Set

data At where
  var   : Var Γ a → At Γ a
  print : At Γ (String ⇒ Unit)

data Nv where
  str   : At Γ String → Nv Γ String
  unit  : Nv Γ Unit
  lam   : Nc (Γ `, a) b → Nv Γ (a ⇒ b)

data Nc where
  ret          : Nv Γ a → Nc Γ a
  let-app-in   : At Γ (a ⇒ b) → Nv Γ a → Nc (Γ `, b) c → Nc Γ c

-- embedding into terms

embAt : At Γ a → Tm Γ a
embNv : Nv Γ a → Tm Γ a
embNc : Nc Γ a → Tm Γ a

embAt (var x) = var x
embAt print   = print

embNv (str x) = embAt x
embNv unit    = unit
embNv (lam x) = lam (embNc x)

embNc (ret x)            = embNv x
embNc (let-app-in x n c) = let-in (app (embAt x) (embNv n)) (embNc c)

-- weakening lemmas

wkAt : Γ ⊆ Γ' → At Γ a → At Γ' a
wkAt w (var x) = var (wkVar w x)
wkAt w print   = print

wkNv : Γ ⊆ Γ' → Nv Γ a → Nv Γ' a
wkNc : Γ ⊆ Γ' → Nc Γ a → Nc Γ' a

wkNv w (str x) = str (wkAt w x)
wkNv w unit    = unit
wkNv w (lam m) = lam (wkNc (keep w) m)

wkNc w (ret x)            = ret (wkNv w x)
wkNc w (let-app-in x n m) = let-app-in (wkAt w x) (wkNv w n) (wkNc (keep w) m)

Var- Tm- At- Nv- Nc- : Ty → Ctx → Set
Var- a Γ = Var Γ a
At- a Γ = At Γ a
Tm- a Γ = Tm Γ a
Nv- a Γ = Nv Γ a
Nc- a Γ = Nc Γ a

------------
-- NbE Model
------------
open import Data.Unit  using (⊤ ; tt)
open import Data.Product  using (Σ ; _×_ ; _,_)

variable
  A B C : Ctx → Set

-- family of maps between interpretations
_→̇_ : (Ctx → Set) → (Ctx → Set) → Set
_→̇_ A B = {Δ : Ctx} → A Δ → B Δ

infixr 10 _→̇_

-- constructions on context-indexed families of sets
_⇒'_ : (Ctx → Set) → (Ctx → Set) → (Ctx → Set)
_⇒'_ A B Γ = {Γ' : Ctx} → Γ ⊆ Γ' → A Γ' → B Γ'

_×'_ : (Ctx → Set) → (Ctx → Set) → (Ctx → Set)
_×'_ A B Γ = A Γ × B Γ

⊤' : (Ctx → Set)
⊤' = λ Γ → ⊤

data Lets (A : Ctx → Set) : Ctx → Set where
  ret        : A →̇ Lets A
  let-app-in : At Γ (a ⇒ b) → Nv Γ a → Lets A (Γ `, b) → Lets A Γ

module _ (wkA : {Δ Δ' : Ctx} → Δ ⊆ Δ' → A Δ → A Δ') where
  wkLets : Γ ⊆ Γ' → Lets A Γ → Lets A Γ'
  wkLets w (ret x)            = ret (wkA w x)
  wkLets w (let-app-in x n c) = let-app-in (wkAt w x) (wkNv w n) (wkLets (keep w) c)

Tm'- : Ty → (Ctx → Set)
Tm'- Unit    = ⊤'
Tm'- String  = At- String
Tm'- (a ⇒ b) = Tm'- a ⇒' Lets (Tm'- b)

Sub'- : Ctx → (Ctx → Set)
Sub'- []       = ⊤'
Sub'- (Γ `, a) = Sub'- Γ ×' Tm'- a

-- values in the model can be weakened
wkTm'- : Γ ⊆ Γ' → Tm'- a Γ → Tm'- a Γ'
wkTm'- {a = Unit}   w x = x
wkTm'- {a = String} w n = wkAt w n
wkTm'- {a = a ⇒ b}  w f = λ w' y → f (w ∙ w') y

-- substitutions in the model can be weakened
wkSub'- : Γ ⊆ Γ' → Sub'- Δ Γ → Sub'- Δ Γ'
wkSub'- {Δ = []}     w tt      = tt
wkSub'- {Δ = Δ `, a} w (s , x) = wkSub'- {Δ = Δ} w s , wkTm'- {a = a} w x

join : Lets (Lets A) →̇ Lets A
join (ret x)              = x
join (let-app-in x x₁ x₂) = let-app-in x x₁ (join x₂)

fmap : (A →̇ B) → (Lets A →̇ Lets B)
fmap f (ret x) = ret (f x)
fmap f (let-app-in x x₁ m) = let-app-in x x₁ (fmap f m)

bind : (A →̇ Lets B) → (Lets A →̇ Lets B)
bind f x = join (fmap f x)

_≫=_ : Lets A Γ → (A →̇ Lets B) → Lets B Γ
_≫=_ x f = bind f x

fmap-int : (A ⇒' B) →̇ (Lets A ⇒' Lets B)
fmap-int f e (ret x) = ret (f e x)
fmap-int f e (let-app-in x x₁ m) = let-app-in x x₁ (fmap-int f (drop e) m)

bind-int : (A ⇒' Lets B) →̇ (Lets A ⇒' Lets B)
bind-int f w (ret x) = f w x
bind-int f w (let-app-in x x₁ m) = let-app-in x x₁ (bind-int f (drop w) m)

[_]_⋆₂_ : Γ ⊆ Γ' → Lets A Γ' → (A ⇒' Lets B) Γ → Lets B Γ'
[ w ] e ⋆₂ f = bind-int f w e

-- Filinski's extension operator
_⋆_ : Lets A Γ → (A ⇒' Lets B) Γ → Lets B Γ
e ⋆ f = [ idWk ] e ⋆₂ f

reflect : At- a →̇ Lets (Tm'- a)
reify   : Tm'- a →̇ Nc- a

-- Filinski's bind
reg-let-app : At Γ (a ⇒ b) → Nv Γ a → Lets (Var- b) Γ
reg-let-app x nv = let-app-in x nv (ret zero)

-- (special case of) Filinski's γᵍʳ
disperse : Nc- a →̇ Lets (Nv- a)
disperse (ret nv)           = ret nv
disperse (let-app-in x n m) = let-app-in x n (disperse m)

-- (special case of) Filinski's collect
collect : Lets (Nv- a) →̇ Nc- a
collect (ret nv)           = ret nv
collect (let-app-in x n m) = let-app-in x n (collect m)

--
runLets : Lets (Nc- a) →̇ Nc- a
runLets m = collect (join (fmap disperse m))

reflect {Unit}   x = ret tt
reflect {String} x = ret x
reflect {a ⇒ b}  x = ret
  (λ w xa → disperse {a} (reify xa)
    ⋆ λ w'   nva → reg-let-app (wkAt (w ∙ w') x) nva
    ⋆ λ _w'' vb → reflect (var vb))

reify {Unit}   tt = ret unit
reify {String} x  = ret (str x)
reify {a ⇒ b}  f  = ret (lam (collect
  (reflect (var zero)
    ⋆ λ w  xa → f (fresh ∙ w) xa
    ⋆ λ w' xb → disperse (reify xb))))

-- interpretation of variables
lookup' : Var- a Γ → (Sub'- Γ →̇ Tm'- a)
lookup' zero     (_ , x) = x
lookup' (succ x) (γ , _) = lookup' x γ

-- interpretation of terms
eval : Tm Γ a → (Sub'- Γ →̇ Lets (Tm'- a))
eval {Γ} (var x)      s = ret (lookup' x s)
eval {Γ} (lam t)      s = ret (λ e x → eval t ((wkSub'- {Δ = Γ} e s) , x))
eval {Γ} (app t u)    s = eval t s ⋆ (λ w f → eval u (wkSub'- {Δ = Γ} w s) ⋆ f)
eval {Γ} (let-in t u) s = eval t s ⋆ (λ w x → eval u (wkSub'- {Δ = Γ} w s , x))
eval {Γ} unit         s = ret tt
eval {Γ} print        s = reflect print

idₛ : Lets (Sub'- Γ) Γ
idₛ {[]}     = ret tt
idₛ {Γ `, a} = reflect (var zero)
  ⋆ λ w x → wkLets (wkSub'- {Δ = Γ}) (fresh ∙ w) idₛ
  ⋆ λ w' s → ret (s , (wkTm'- {a = a} w' x))

norm : Tm- a →̇ Nc- a
norm t = runLets (fmap reify (bind (eval t) idₛ))
