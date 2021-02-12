-- Andreas, 2021-02-12
-- Private declarations can be accessed from within the module.

module PrivateInSelf where

  private
    module O where

  open O using ()
