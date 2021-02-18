module Import where
  module B where
    module M where
  module O where
    module P where
      open B public -- export M from P
    private
      module N where
  open O
  open P
  open M
