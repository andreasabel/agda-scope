module ShadowPrivate where
  private module M where
  module M where  -- Illegal shadowing even though first def was private.
