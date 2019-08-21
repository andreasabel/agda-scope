-- Andreas, 2019-05-08 / 2019-08-21 shadowed module in parent

module ShadowedByAmbiguous where
  module M where
    module N where
  open M            -- On the top level, N is unambiguous
  module O where
    module N where  -- Agda complains here
    open M
    open N          -- But here inside O, N is ambiguous
