module Abstract where

import Concrete as C
open C public using (_◇_; Access); open Access public

variable
  x  y  : C.Name
  xs ys : C.QName

interleaved mutual

  data Scope : Set -- where
  data Decls (sc : Scope) : Set -- where
  data Decl  (sc : Scope) : Set -- where

  data Def   (sc : Scope) : Set where
    modl : (ds : Decls sc) → Def sc

  variable
    sc sc' : Scope
    ds ds' : Decls sc
    d  d'  : Decl sc
    v  v'  : Def sc

  constructor  -- Scope
    ε   : Scope
    _▷_ : (sc : Scope) (ds : Decls sc) → Scope

  constructor  -- Decls
    ε   : Decls sc
    _▷_ : (ds : Decls sc) (d : Decl (sc ▷ ds)) → Decls sc

  data _⊆_ : (sc sc' : Scope) → Set

  variable
    τ : sc ⊆ sc'

  data WkDecl  (τ : sc ⊆ sc') : Decl  sc → Decl  sc' → Set

  data WkDecls (τ : sc ⊆ sc') : Decls sc → Decls sc' → Set

  data WkDef   (τ : sc ⊆ sc') : Def sc   → Def sc'   → Set where
    modl : (ws : WkDecls τ ds ds') → WkDef τ (modl ds) (modl ds')

  constructor  -- _⊆_
    ε : ε ⊆ ε
    _▷_  : (τ : sc ⊆ sc') (ws : WkDecls τ ds ds') → (sc ▷ ds) ⊆ (sc' ▷ ds')
    _▷ʳ_ : (τ : sc ⊆ sc') (ds : Decls sc')        → sc        ⊆ (sc' ▷ ds)

  constructor  -- WkDecls
    ε     : WkDecls τ ε ε
    _▷_   : (ws : WkDecls τ ds ds') (w : WkDecl (τ ▷ ws) d d') → WkDecls τ (ds ▷ d) (ds' ▷ d')
    _▷ʳ_  : (ws : WkDecls τ ds ds') (d : Decl (_ ▷ ds'))       → WkDecls τ  ds      (ds' ▷ d)

  refl-⊆ : sc ⊆ sc

  wkDecl-refl-⊆  : WkDecl  refl-⊆ d  d

  wkDecls-refl-⊆ : WkDecls refl-⊆ ds ds
  wkDecls-refl-⊆ {ds = ε}      = ε
  wkDecls-refl-⊆ {ds = ds ▷ d} = wkDecls-refl-⊆ {ds = ds} ▷ {! wkDecl-refl-⊆ {d = d} !}
    -- refl-⊆ != (refl-⊆ ▷ wkDecls-refl-⊆) of type ((ds.sc ▷ ds) ⊆ (ds.sc ▷ ds))

  wkDef-refl-⊆   : WkDef   refl-⊆ v  v
  wkDef-refl-⊆ {v = modl ds} = modl wkDecls-refl-⊆

  refl-⊆ {sc = ε}       = ε
  refl-⊆ {sc = sc ▷ ds} = refl-⊆ {sc = sc} ▷ wkDecls-refl-⊆ {ds = ds}

  wk1 : sc ⊆ (sc ▷ ds)
  wk1 {ds = ds} = refl-⊆ ▷ʳ ds

  wk01 : (sc ▷ ds) ⊆ (sc ▷ (ds ▷ d))
  wk01 {d = d} = refl-⊆ ▷ (wkDecls-refl-⊆ ▷ʳ d)

  data ScName : (sc : Scope) → Def sc → Set -- where
  data DsName (sc : Scope) : (ds : Decls sc) → Def (sc ▷ ds) → Set -- where
  data DName  (sc : Scope) : Decl sc → Def sc → Set -- where

  variable
    nsc : ScName sc v

  constructor  -- Decl
    def  : (x : C.Name)   (v : Def sc) → Decl sc
    -- opn  : (n : ScName sc (modl ds))   → Decl sc

  constructor  -- WkDecl
    def  : (w : WkDef    τ v v') → WkDecl τ (def x v) (def x v')
    -- opn  : (w : WkScName τ n n') → WkDecl τ (opn n)   (opn n')

  wkDecl-refl-⊆ {d = def x v} = def wkDef-refl-⊆
  -- wkDecl-refl-⊆ {d = opn n} = wkDecl-refl-⊆ {ds = ds} ▷ wkDecl-refl-⊆ {d = d}

  constructor  -- ScName
    site   :                      (n : DsName sc ds v) → ScName (sc ▷ ds) v
    parent : (w : WkDef wk1 v v') (n : ScName sc    v) → ScName (sc ▷ ds) v'

  constructor  -- DsName
    here  : (w : WkDef wk01 v v') (n : DName (sc ▷ ds) d v) → DsName sc (ds ▷ d) v'
    there : (w : WkDef wk01 v v') (n : DsName sc      ds v) → DsName sc (ds ▷ d) v'

  constructor  -- DName
    def    :                  DName sc (def x v) v
    inside : (w : WkDef wk1 v' v) (n : DsName sc ds v) → DName sc (def x (modl ds)) v'
    -- imp    : (n : DsName sc ds v) → DName sc (opn nsc (modl ds)) v
