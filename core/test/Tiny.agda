-- Andreas, 2019-04-24 example to test the scope checker

module Top where

public A : Set
public a : A

public module M where {
  public b : A
  public C : Set
}

public d : M.C
