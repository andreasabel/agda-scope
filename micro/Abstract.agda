module Abstract where

import Concrete as C
open C public using (_◇_; Access); open Access public

variable
  x  y  : C.Name
  xs ys : C.QName

mutual

  data Scope : Set where
    ε   : Scope
    _▷_ : (sc : Scope) (ds : Decls sc) → Scope

  data Decls (sc : Scope) : Set where
    ε   : Decls sc
    _▷_ : (ds : Decls sc) (d : Decl (sc ▷ ds)) → Decls sc

  data Decl (sc : Scope) : Set where
    modl : (x : C.Name)   (ds : Decls sc)    → Decl sc
    opn  : (xs : C.QName) (n : ScName sc xs) → Decl sc

  variable
    sc : Scope
    ds : Decls sc
    d  : Decl sc

  data ScName : Scope → C.QName → Set where
    site   : (n : DsName sc ds xs) → ScName (sc ▷ ds) xs
    parent : (n : ScName sc    xs) → ScName (sc ▷ ds) xs

  variable
    nsc : ScName sc xs

  data DsName (sc : Scope) : Decls sc → C.QName → Set where
    here  : (n : DName (sc ▷ ds) d xs) → DsName sc (ds ▷ d) xs
    there : (n : DsName sc      ds xs) → DsName sc ds       xs

  data DName (sc : Scope) : Decl sc → C.QName → Set where
    modl   :                       DName sc (modl x ds) (C.qName x)
    inside : DsName sc ds xs     → DName sc (modl x ds) (C.qual x xs)
    imp    : ScName sc (ys ◇ xs) → DName sc (opn ys nsc) xs
