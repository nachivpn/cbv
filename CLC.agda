module CLC where

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

