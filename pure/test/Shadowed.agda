-- Andreas, 2019-05-08 / 2019-08-21 shadowed module in parent

module Shadowed where
  module M where
    module N where
  module O where
    module M where     -- Agda complains here
    open M.N           -- not in scope since previous M is shadowed
