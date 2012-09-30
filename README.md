# Installation
> $ cabal install

If compilation fails by GHC's bug, try `cabal clean` and run `cabal install` again.

# Usage
```
$ prover
|- ((P -> Q) -> P) -> P
----------------------
Goal:  |- ((P → Q) → P) → P
> right
----------------------
Goal: (P → Q) → P |- P
> left 0 0
----------------------
Goal:  |- P, P → Q
> right
----------------------
Goal: P |- P, Q
> weakenR
complete: P |- P
----------------------
Goal: P |- 
> :r
----------------------
Goal: (P → Q) → P |- P
> contractR
----------------------
Goal: (P → Q) → P |- P, P
> left 0 
***invalid command: left 0 
----------------------
Goal: (P → Q) → P |- P, P
> left 0 1
----------------------
Goal:  |- P, P → Q
> right
----------------------
Goal: P |- P, Q
> weakenR
complete: P |- P
complete: P |- P
\AxiomC{}\UnaryInfC{$P\vdash{}P$}\RightLabel{\scriptsize{\sc{WeakenR}}}\UnaryInfC{$P\vdash{}P, Q$}\RightLabel{\scriptsize{\sc{$\to$-Right}}}\UnaryInfC{$\vdash{}P, P\to{}Q$}\AxiomC{}\UnaryInfC{$P\vdash{}P$}\RightLabel{\scriptsize{\sc{$\to$-Left}}}\BinaryInfC{$\left({}P\to{}Q\right){}\to{}P\vdash{}P, P$}\RightLabel{\scriptsize{\sc{ContractR}}}\UnaryInfC{$\left({}P\to{}Q\right){}\to{}P\vdash{}P$}\RightLabel{\scriptsize{\sc{$\to$-Right}}}\UnaryInfC{$\vdash{}\left({}\left({}P\to{}Q\right){}\to{}P\right){}\to{}P$}
```

Output tex code can be compiled with [bussproofs.sty](http://www.math.ucsd.edu/~sbuss/ResearchWeb/bussproofs/index.html).
