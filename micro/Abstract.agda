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
  -- So far, we can only define modules, which hold declarations.

  data Def (sc : Scope) : Set where
    modl : (ds : Decls sc) → Def sc

  -- We use letter v ("value") for definitions.

  variable
    v v' : Def sc

  -- A well-scoped name pointing to its definition.

  data Name : (sc : Scope) → Def sc → Set

  variable
    n n' : Name sc v

  -- A well-scoped declaration is one of
  --
  --   * A module definition.
  --   * Importing the declarations of another module via `open`.

  data Decl (sc : Scope) : Set where
    def  : (x : C.Name) (v : Def sc) → Decl sc
    opn  : (n : Name sc (modl ds))   → Decl sc

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

  -- Weakning from one scope to an extended scope.

  data _⊆_ : (sc sc' : Scope) → Set

  variable
    τ : sc ⊆ sc'

  -- Weakning by a list of declarations or a single declaration.

  wk1  : sc ⊆ (sc ▷ ds)
  wk01 : (sc ▷ ds) ⊆ (sc ▷ (ds ▷ d))

  -- Weakening a definition.

  data WkDef (τ : sc ⊆ sc') : Def sc → Def sc' → Set

  variable
    wv wv' wv₀ : WkDef τ v v'

  -- Names resolving in a list of declarations.

  data DsName (sc : Scope) : (ds : Decls sc) → Def (sc ▷ ds) → Set -- where
  variable
    nds nds' : DsName sc ds v

  -- Names resolving in a declaration.

  data DName  (sc : Scope) : Decl sc → Def sc → Set where
    def    : DName sc (def x v) v

    inside : (w : WkDef wk1 v' v) (n : DsName sc ds v)
           → DName sc (def x (modl ds)) v'

    imp    : (w : WkDef wk1 v' v) (n : Name sc (modl ds)) (nds : DsName sc ds v)
           → DName sc (opn n) v'

  variable
    nd nd' : DName  sc d  v

  -- This finally allows us to define names resolving in a scope.

  constructor  -- DsName
    here  : (w : WkDef wk01 v v') (nd  : DName (sc ▷ ds) d v) → DsName sc (ds ▷ d) v'
    there : (w : WkDef wk01 v v') (nds : DsName sc      ds v) → DsName sc (ds ▷ d) v'

  constructor  -- Name
    site   :                      (nds : DsName sc ds v) → Name (sc ▷ ds) v
    parent : (w : WkDef wk1 v v') (n   : Name   sc    v) → Name (sc ▷ ds) v'

  ------------------------------------------------------------------------
  -- Relating entities defined in a scope to their weakenings.

  data WkDecl  (τ : sc ⊆ sc') : Decl  sc → Decl  sc' → Set

  data WkDecls : (τ : sc ⊆ sc') → Decls sc → Decls sc' → Set

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

  -- We can prove that the identity weaking leaves definitions unchanged.

  constructor  -- WkDef
    modl : (ws : WkDecls τ ds ds') → WkDef τ (modl ds) (modl ds')

  wkDef-refl-⊆   : WkDef   refl-⊆ v  v
  wkDef-refl-⊆ {v = modl ds} = modl wkDecls-refl-⊆

  -- Weakning names

  data WkName : (τ : sc ⊆ sc') (w : WkDef τ v v') → Name sc v → Name sc' v' → Set

  constructor  -- WkDecl
    def  : (w  : WkDef  τ    v v') → WkDecl τ (def x v) (def x v')
    opn  : (wn : WkName τ wv n n') → WkDecl τ (opn n)   (opn n')

  wkName-refl-⊆ : WkName refl-⊆ wkDef-refl-⊆ n n

  wkDecl-refl-⊆  : WkDecl  refl-⊆ d  d
  wkDecl-refl-⊆ {d = def x v} = def wkDef-refl-⊆
  wkDecl-refl-⊆ {d = opn n  } = opn wkName-refl-⊆

  constructor  -- WkName
    site   : WkName τ wv (site nds) (site nds')              -- TODO WkDsName
    -- parent : (w : WkName τ {!!} n n') → WkName τ wv₀ (parent wv n) (parent wv' n')  -- TODO

  wkName-refl-⊆ {n = n} = {!!}
