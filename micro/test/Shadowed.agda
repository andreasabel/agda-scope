-- Andreas, 2019-05-08 shadowed module in parent

module Top where {
  module M where {
    module N where {}
    }
  module O where {
    module M where {}
    module _ = M.N  -- not in scope since previous M is shadowed
    }
  }
