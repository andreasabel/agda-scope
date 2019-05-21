-- Andreas, 2019-05-04 small example to test parser

module Example where
  module M₁ where
  module M₂ where
    module N where
  open M₂.N using ()

-- EOF
