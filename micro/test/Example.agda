-- Andreas, 2019-05-04 small example to test parser

module Top where {
  module M₁ where {}
  module M₂ where {
    module N where {}
  }
  module _ = M₂.N
}

-- EOF
