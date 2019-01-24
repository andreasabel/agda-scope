-- Andreas, 2019-01-24 small example to test parser

public module Top where {

  public A : Set
  public P : forall (x : A) -> Set

  public module M (x : A) (p : P x) where {

    def y = x
    private module N = Top.M y p using () renaming (y to z)
    open N public

    public module O refine (x = z) where {

      public B : Set
      def B = A

    }

  }
}
