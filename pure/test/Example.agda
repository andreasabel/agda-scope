-- Andreas, 2019-05-04 small example to test parser

module Example where
  private module M₁ where
  module M₂ where
    module N where
      module O where
        module P where
        module Q where
        module R where
  open M₂.N public
  open M₂.N
  module P where
  open O
  module Q where          -- Agda does not like this (yet)
  private module R where

-- EOF
