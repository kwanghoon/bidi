# The bidirectional type checking algorithms for higher-ranked polymorphism

- Two bidirectional type checking algorithms for higer-ranked polymorphism.

  * One is proposed by [Jana Dunfield and Neelakantan R. Krishnaswami's ICFP 2013 paper, Complete and easy bidirectional typechecking for higer-order rank polymorphism](https://research.cs.queensu.ca/home/jana/papers/bidir/). 

  * The other algorithm based on so called work list proposed by [Jinxu Zhao, Bruno C. d. S. Oliveira1 , and Tom Schrijvers's ICFP 2019 paper, A Mechanical Formalization of Higher-Ranked Polymorphic Type Inference](https://i.cs.hku.hk/~bruno/papers/icfp2019.pdf) where the original algorithm is simplified and so mechanically proved using Abella. 


- Haskell Implementation of the two algorithms

  * One is [Olle Fredriksson](https://ollef.github.io/blog/)'s
    [implementation](https://github.com/ollef/Bidirectional) of
    Dunfield and Krishnaswami's algorithm, which I have slightly
    revised just to correct some version mismatch error.

  * I myself have implemented Zhao et al's algorithm. 


## How to build and run

```
$ git clone https://github.com/kwanghoon/bidi
$ cd bidi
$ stack build

```

- To run the original DK's algorithm,

```
$ stack exec -- bidi-exe
```

- To run the new Zhao et al's algorithm,

```
$ stack exec -- bidi-exe worklist
```

## A polymorphic location inference algorithm for higher-ranked polymorphism

- In [PolyRPC](https://github.com/kwanghoon/polyrpc), I have
  implemented a location inference algorithm for the predicative
  System F with locations. The algorithms is closely related with the
  two algorithms.
