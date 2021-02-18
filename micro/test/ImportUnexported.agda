module ImportUnexported where
  module O where
    module P where
    private
      module N where
  open O
  open N  -- should fail as O does not export N

-- No module N in scope
-- when scope checking the declaration
--   open N
