-- Andreas, 2019-05-08 shadowed module in parent

module _ where
  module P where
    module M where
      module N where

  module O where
    module M where
      module L where
    open P          -- does not shadow M
    module Z = M.L  -- NOT: not in scope since previous M is shadowed
