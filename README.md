# The bidirectional type checking algorithms for higher-ranked polymorphism

- This contains a bidirectional type checking algorithm for higer-ranked polymorphism proposed by [Jana Dunfield and Neelakantan R. Krishnaswami's ICFP 2013 paper, Complete and easy bidirectional typechecking for higer-order rank polymorphism](https://research.cs.queensu.ca/home/jana/papers/bidir/). 

- [Olle Fredriksson](https://ollef.github.io/blog/) implemented this algorithm in Haskell. Here is [his Haskell implementation](https://github.com/ollef/Bidirectional). 

- There is another bidirectional type checking algorithm based on so called work list proposed by [Jinxu Zhao, Bruno C. d. S. Oliveira1 , and Tom Schrijvers's ICFP 2019 paper, A Mechanical Formalization of Higher-Ranked Polymorphic Type Inference](https://i.cs.hku.hk/~bruno/papers/icfp2019.pdf) where the original algorithm is simplified and so mechanically proved using Abella. 

- This repository contains Olle's implementation that I have slightly revised to correct some compilation error due to some version problem. This repository also contains a Haskell implementation of Zhao et al's algorithm. You can compare two algorithms. 


- How to build

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
