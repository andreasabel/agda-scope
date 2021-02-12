-- Andreas, 2021-02-12
-- Private declarations cannot be accessed from a sibling.

module PrivateInSibling where

  module M where
    private
      module O where

  open M.O using ()
