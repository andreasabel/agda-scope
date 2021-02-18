module ImportUnexportedOpenPrivate where
  module B where
    module M where
  module O where
    module P where
      open B           -- does not export M from P
      open M
    private
      module N where
  open O
  open P
  open M               -- should fail

-- No module M in scope
-- when scope checking the declaration
--   open M
