-- Andreas, 2019-05-08 shadowed module in parent

module Shadowed where
  module M where
    module N where
  module O where
    module M where     -- Agda complains here
    open M.N using ()  -- not in scope since previous M is shadowed
