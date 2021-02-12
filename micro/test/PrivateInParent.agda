-- Andreas, 2021-02-12
-- Private declarations can be accessed from a child

module PrivateInParent where

  private
    module O where

  module M where
    open O using ()
