module Abstract where

import Concrete as C
open C public using (_◇_; Access); open Access public

variable
  x  y  : C.Name
  xs ys : C.QName

interleaved mutual

  -- Scope of a declaration.

  data Scope : Set
  variable
    sc sc' : Scope

  -- Declarations in a scope.

  data Decls (sc : Scope) : Set
  variable
    ds ds' : Decls sc

  -- A definition in a scope.
  -- So far, we can only define modules, which hold a list of declarations.

  data Def   (sc : Scope) : Set where
    modl : (ds : Decls sc) → Def sc

  variable
    v v' : Def sc

  -- A well-scoped name pointing to its definition.

  data ScName : (sc : Scope) → Def sc → Set

  variable
    nsc nsc' : ScName sc v

  -- A well-scoped declaration is one of
  --
  --   * A module definition.
  --   * Importing the declarations of another module via `open`.

  data Decl  (sc : Scope) : Set where
    def  : (x : C.Name)   (v : Def sc) → Decl sc
    opn  : (n : ScName sc (modl ds))   → Decl sc

  variable
    d  d'  : Decl sc

  -- A scope is a snoc list of lists of declarations.

  constructor  -- Scope
    ε   : Scope
    _▷_ : (sc : Scope) (ds : Decls sc) → Scope

  -- Lists of declarations are also given in snoc-form.

  constructor  -- Decls
    ε   : Decls sc
    _▷_ : (ds : Decls sc) (d : Decl (sc ▷ ds)) → Decls sc

  -- Weakning from one scope to an extended scope.

  data _⊆_ : (sc sc' : Scope) → Set

  variable
    τ : sc ⊆ sc'

  -- Relating entities defined in a scope to their weakenings.

  data WkDecl  (τ : sc ⊆ sc') : Decl  sc → Decl  sc' → Set

  data WkDecls : (τ : sc ⊆ sc') → Decls sc → Decls sc' → Set

  data WkDef   (τ : sc ⊆ sc') : Def sc   → Def sc'   → Set where
    modl : (ws : WkDecls τ ds ds') → WkDef τ (modl ds) (modl ds')

  variable
    wv wv' wv₀ : WkDef τ v v'

  -- Weakenings are order-preserving embeddings.

  constructor  -- _⊆_
    -- ε : ε ⊆ ε
    -- refl : sc ⊆ sc
    refl-⊆ : sc ⊆ sc
    _▷_  : (τ : sc ⊆ sc') (ws : WkDecls τ ds ds') → (sc ▷ ds) ⊆ (sc' ▷ ds')
    _▷ʳ_ : (τ : sc ⊆ sc') (ds : Decls sc')        → sc        ⊆ (sc' ▷ ds)

  constructor  -- WkDecls
    -- ε     : WkDecls τ ε ε
    -- refl  : WkDecls refl ds ds
    -- wkDecls-refl-⊆  : {ds : Decls sc} → WkDecls (refl-⊆ {sc = sc}) ds ds
    wkDecls-refl-⊆  : WkDecls refl-⊆ ds ds
    _▷_   : (ws : WkDecls τ ds ds') (w : WkDecl (τ ▷ ws) d d') → WkDecls τ (ds ▷ d) (ds' ▷ d')
    _▷ʳ_  : (ws : WkDecls τ ds ds') (d : Decl (_ ▷ ds'))       → WkDecls τ  ds      (ds' ▷ d)

  -- refl-⊆ : sc ⊆ sc

  -- We can prove that the identity weaking leaves a declarations and definitions unchanged.

  wkDecl-refl-⊆  : WkDecl  refl-⊆ d  d

  -- wkDecls-refl-⊆ : WkDecls refl-⊆ ds ds
  -- wkDecls-refl-⊆ {ds = ε}      = ε
  -- wkDecls-refl-⊆ {ds = ds ▷ d} = wkDecls-refl-⊆ {ds = ds} ▷ {! wkDecl-refl-⊆ {d = d} !}
  --   -- refl-⊆ != (refl-⊆ ▷ wkDecls-refl-⊆) of type ((ds.sc ▷ ds) ⊆ (ds.sc ▷ ds))

  wkDef-refl-⊆   : WkDef   refl-⊆ v  v
  wkDef-refl-⊆ {v = modl ds} = modl wkDecls-refl-⊆

  -- refl-⊆ {sc = ε}       = ε
  -- refl-⊆ {sc = sc ▷ ds} = refl-⊆ {sc = sc} ▷ wkDecls-refl-⊆ {ds = ds}

  -- Singleton weaknings.

  -- By another list of declarations.
  wk1 : sc ⊆ (sc ▷ ds)
  wk1 {ds = ds} = refl-⊆ ▷ʳ ds

  -- By a single declaration.
  wk01 : (sc ▷ ds) ⊆ (sc ▷ (ds ▷ d))
  wk01 {d = d} = refl-⊆ ▷ (wkDecls-refl-⊆ ▷ʳ d)

  -- Names resolving in a declaration or a list of declarations.

  data DsName (sc : Scope) : (ds : Decls sc) → Def (sc ▷ ds) → Set -- where
  data DName  (sc : Scope) : Decl sc → Def sc → Set -- where

  variable
    nds nds' : DsName sc ds v
    nd  nd'  : DName  sc d  v

  -- This allows us to define names resolving in a scope

  constructor  -- ScName
    site   :                      (n : DsName sc ds v) → ScName (sc ▷ ds) v
    parent : (w : WkDef wk1 v v') (n : ScName sc    v) → ScName (sc ▷ ds) v'

  -- Weakning names

  data WkScName : (τ : sc ⊆ sc') (w : WkDef τ v v') → ScName sc v → ScName sc' v' → Set

  constructor  -- WkDecl
    def  : (w : WkDef     τ    v   v'  ) → WkDecl τ (def x v) (def x v')
    opn  : (wn : WkScName τ wv nsc nsc') → WkDecl τ (opn nsc) (opn nsc')

  wkScName-refl-⊆ : WkScName refl-⊆ wkDef-refl-⊆ nsc nsc

  wkDecl-refl-⊆ {d = def x v} = def wkDef-refl-⊆
  wkDecl-refl-⊆ {d = opn nsc} = opn wkScName-refl-⊆

  constructor  -- DsName
    here  : (w : WkDef wk01 v v') (n : DName (sc ▷ ds) d v) → DsName sc (ds ▷ d) v'
    there : (w : WkDef wk01 v v') (n : DsName sc      ds v) → DsName sc (ds ▷ d) v'

  constructor  -- DName
    def    : DName sc (def x v) v

    inside : (w : WkDef wk1 v' v) (n : DsName sc ds v)
           → DName sc (def x (modl ds)) v'

    imp    : (w : WkDef wk1 v' v) (nsc : ScName sc (modl ds)) (nds : DsName sc ds v)
           → DName sc (opn nsc) v'

  constructor  -- WkScName
    site   : WkScName τ wv (site nds) (site nds')              -- TODO WkDsName
    -- parent : (w : WkScName τ {!!} nsc nsc') → WkScName τ wv₀ (parent wv nsc) (parent wv' nsc')  -- TODO

  wkScName-refl-⊆ {nsc = nsc} = {!!}
