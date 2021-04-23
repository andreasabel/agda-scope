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
    ds₀ ds ds' : Decls sc

  -- A definition in a scope.
  -- So far, we can only define modules, which hold declarations.

  data Val : (sc : Scope) → Set

  -- We use letter v ("value") for definitions.

  variable
    v v' : Val sc

  -- A well-scoped name pointing to its definition.

  data Name : (sc : Scope) → Val sc → Set

  variable
    n n' : Name sc v

  -- A well-scoped declaration is one of
  --
  --   * A module definition.
  --   * Importing the declarations of another module via `open`.

  data Decl (sc : Scope) : Set where
    modl : (x : C.Name) (ds : Decls sc) → Decl sc
    opn  : (n : Name sc v)              → Decl sc

  variable
    d d' : Decl sc

  -- A scope is a snoc list of lists of declarations.

  constructor  -- Scope
    ε   : Scope
    _▷_ : (sc : Scope) (ds : Decls sc) → Scope

  -- Lists of declarations are also given in snoc-form.

  constructor  -- Decls
    ε   : Decls sc
    _▷_ : (ds : Decls sc) (d : Decl (sc ▷ ds)) → Decls sc

  constructor -- Val
    -- The content of a module.
    content : (ds : Decls sc) → Val sc
    -- Qualifying a value that is taken from inside module x.
    inside  : (x : C.Name) (v : Val ((sc ▷ ds) ▷ ds')) → Val (sc ▷ (ds ▷ modl x ds'))
    imp     : (n : Name (sc ▷ ds₀) (content ds')) (v : Val ((sc ▷ ds₀) ▷ ds'))
            → Val (sc ▷ (ds₀ ▷ opn n))

  -- Weakning from one scope to an extended scope.

  data _⊆_ : (sc sc' : Scope) → Set

  variable
    τ : sc ⊆ sc'

  -- Weakning by a list of declarations or a single declaration.

  wk1  : sc ⊆ (sc ▷ ds)
  wk01 : (sc ▷ ds) ⊆ (sc ▷ (ds ▷ d))

  -- Weakening a definition.

  data WkVal : (τ : sc ⊆ sc') → Val sc → Val sc' → Set

  variable
    wv wv' wv₀ : WkVal τ v v'

  data WkDecl  (τ : sc ⊆ sc') : Decl  sc → Decl  sc' → Set
  variable
    wd wd' : WkDecl τ d d'

  data WkDecls : (τ : sc ⊆ sc') → Decls sc → Decls sc' → Set
  variable
    wds wds' : WkDecls τ ds ds'

  -- Names resolving in a list of declarations.

  data DsName (sc : Scope) : (ds : Decls sc) → Val (sc ▷ ds) → Set -- where
  variable
    nds nds' : DsName sc ds v

  -- Names resolving in a declaration.

  data DName  (sc : Scope) (ds₀ : Decls sc) : (d : Decl (sc ▷ ds₀)) → Val (sc ▷ (ds₀ ▷ d)) → Set where

    modl    : (wds : WkDecls wk01 ds ds') →
              DName sc ds₀ (modl x ds) (content ds')

    inside : -- (w : WkVal wk1 v' v)
             (n : DsName (sc ▷ ds₀) ds' v)
           → DName sc ds₀ (modl x ds') (inside x v)

    imp    : (n : Name (sc ▷ ds₀) (content ds')) (nds : DsName (sc ▷ ds₀) ds' v)
           → DName sc ds₀ (opn n) (imp n v)

  variable
    nd nd' : DName sc ds d  v

  -- This finally allows us to define names resolving in a scope.

  constructor  -- DsName
    here  : (nd  : DName  sc ds d v) → DsName sc (ds ▷ d) v
    there : (w : WkVal wk01 v v') (nds : DsName sc ds   v) → DsName sc (ds ▷ d) v'
    -- here  : (w : WkVal wk01 v v') (nd  : DName  sc ds d v) → DsName sc (ds ▷ d) v'
    -- there : (w : WkVal wk01 v v') (nds : DsName sc ds   v) → DsName sc (ds ▷ d) v'

  constructor  -- Name
    site   :                      (nds : DsName sc ds v) → Name (sc ▷ ds) v
    parent : (w : WkVal wk1 v v') (n   : Name   sc    v) → Name (sc ▷ ds) v'

  ------------------------------------------------------------------------
  -- Relating entities defined in a scope to their weakenings.

  -- Weakenings are order-preserving embeddings.

  constructor  -- _⊆_
    refl-⊆ : sc ⊆ sc
    _▷_  : (τ : sc ⊆ sc') (ws : WkDecls τ ds ds') → (sc ▷ ds) ⊆ (sc' ▷ ds')
    _▷ʳ_ : (τ : sc ⊆ sc') (ds : Decls sc')        → sc        ⊆ (sc' ▷ ds)

  constructor  -- WkDecls
    wkDecls-refl-⊆  : WkDecls refl-⊆ ds ds
    _▷_   : (ws : WkDecls τ ds ds') (w : WkDecl (τ ▷ ws) d d') → WkDecls τ (ds ▷ d) (ds' ▷ d')
    _▷ʳ_  : (ws : WkDecls τ ds ds') (d : Decl (_ ▷ ds'))       → WkDecls τ  ds      (ds' ▷ d)

  -- We can now define the singleton weaknings.

  -- By another list of declarations.
  wk1 {ds = ds} = refl-⊆ ▷ʳ ds

  -- By a single declaration.
  wk01 {d = d} = refl-⊆ ▷ (wkDecls-refl-⊆ ▷ʳ d)

  -- Weakning names

  data WkName : (τ : sc ⊆ sc') (w : WkVal τ v v') → Name sc v → Name sc' v' → Set

  constructor  -- WkDecl
    def  : (w  : WkDecls τ    ds ds') → WkDecl τ (modl x ds) (modl x ds')
    opn  : (wn : WkName  τ wv n  n' ) → WkDecl τ (opn n)   (opn n')

  wkVal-refl-⊆   : WkVal   refl-⊆ v  v
  wkName-refl-⊆ : WkName refl-⊆ wkVal-refl-⊆ n n

  wkDecl-refl-⊆  : WkDecl  refl-⊆ d  d
  wkDecl-refl-⊆ {d = modl x ds} = def wkDecls-refl-⊆
  wkDecl-refl-⊆ {d = opn n    } = opn wkName-refl-⊆

  -- We can prove that the identity weaking leaves definitions unchanged.

  constructor  -- WkVal
    content : (ws : WkDecls τ ds ds') → WkVal τ (content ds) (content ds')
    inside  : (wv : WkVal ((τ ▷ wds) ▷ wds') v  v' ) → WkVal (τ ▷ (wds ▷ def wds')) (inside x v) (inside x v')

  wkVal-refl-⊆ {v = content ds} = content wkDecls-refl-⊆
  wkVal-refl-⊆ {v = inside x v} = {!inside  (wkVal-refl-⊆ {v = v})!}

  data WkDsName : (τ : sc ⊆ sc') (ws : WkDecls τ ds ds') (w : WkVal (τ ▷ ws) v v')
    → DsName sc ds v → DsName sc' ds' v' → Set

  data WkDName (τ : sc ⊆ sc') (ws : WkDecls τ ds ds')
    : (wd : WkDecl (τ ▷ ws) d d') (wv₀ : WkVal (τ ▷ (ws ▷ wd)) v v')
    → DName sc ds d v → DName sc' ds' d' v' → Set
    where
    def    : WkDName τ ws wd wv₀ (modl wds) (modl wds')
    -- inside : WkDName (inside w n) (inside w' n')

  constructor  -- WkName
    site   : WkName τ wv (site nds) (site nds')              -- TODO WkDsName
    -- parent : (w : WkName τ {!!} n n') → WkName τ wv₀ (parent wv n) (parent wv' n')  -- TODO

  wkName-refl-⊆ {n = n} = {!!}
